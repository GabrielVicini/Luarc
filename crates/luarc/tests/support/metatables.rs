//! Shared fixtures for source-level metatable tests.

use luarc::ast::*;
use luarc::check::{Checker, ModuleUnit};
use luarc::diag::SourceMap;
use luarc::native::{adapters::AdapterSet, world::World};
use luarc::parser::parse_module;
use luarc::resolve::{Builtin, Res, Resolution, Resolver};

pub fn checked(src: &str, test: impl FnOnce(&Checker<'_>, &[ModuleUnit])) {
    let mut next = 1;
    let module = parse_module(0, src, &mut next).expect("parse dormant fixture");
    let mut res = Resolution::default();
    let mut resolver = Resolver::new(&mut res);
    resolver.module(&module, next);
    resolver.finish();
    assert!(
        resolver.errors.is_empty(),
        "{:?}",
        resolver.errors
    );
    let mut calls = Vec::new();
    visit_block(&module.body, &mut |expr| {
        if let ExprKind::Call(callee, _) = &expr.kind {
            if matches!(&callee.kind, ExprKind::Name(name) if res.res(name.id) == Some(Res::Builtin(Builtin::SetMetatable))) {
                calls.push(expr.id);
            }
        }
    });
    assert!(!calls.is_empty(), "fixture must contain a resolved attachment");
    let units = vec![ModuleUnit {
        module,
        pseudo_func: next,
        ident: "m0".into(),
        requires: Default::default(),
        rust_requires: Default::default(),
    }];
    let mut sm = SourceMap::default();
    sm.add("metatables.luarc".into(), "metatables.luarc".into(), src.into());
    let world = World::default();
    let adapters = AdapterSet::default();
    let mut checker = Checker::new(&res, &sm, &world, &adapters);
    checker.check_program(&units, &[0]);
    test(&checker, &units);
}

pub fn visit_block(block: &Block, f: &mut impl FnMut(&Expr)) {
    for stat in &block.stats {
        match &stat.kind {
            StatKind::Local(_, es) | StatKind::Return(es) => {
                for e in es {
                    visit_expr(e, f);
                }
            }
            StatKind::Assign(ts, es) => {
                for e in ts.iter().chain(es) {
                    visit_expr(e, f);
                }
            }
            StatKind::LocalFunction(_, body) => visit_block(&body.body, f),
            StatKind::Function(target, body) => {
                visit_expr(target, f);
                visit_block(&body.body, f);
            }
            StatKind::Compound(_, a, b) => {
                visit_expr(a, f);
                visit_expr(b, f);
            }
            StatKind::Call(e) => visit_expr(e, f),
            StatKind::Do(b) => visit_block(b, f),
            StatKind::While(e, b) | StatKind::Repeat(b, e) => {
                visit_expr(e, f);
                visit_block(b, f);
            }
            StatKind::If(arms, other) => {
                for (e, b) in arms {
                    visit_expr(e, f);
                    visit_block(b, f);
                }
                if let Some(b) = other {
                    visit_block(b, f);
                }
            }
            StatKind::NumFor(_, a, b, c, body) => {
                for e in [Some(a), Some(b), c.as_ref()].into_iter().flatten() {
                    visit_expr(e, f);
                }
                visit_block(body, f);
            }
            StatKind::GenFor(_, es, body) => {
                for e in es {
                    visit_expr(e, f);
                }
                visit_block(body, f);
            }
            _ => {}
        }
    }
}

fn visit_expr(expr: &Expr, f: &mut impl FnMut(&Expr)) {
    f(expr);
    match &expr.kind {
        ExprKind::Call(a, es) | ExprKind::Method(a, _, es) => {
            visit_expr(a, f);
            for e in es {
                visit_expr(e, f);
            }
        }
        ExprKind::Function(body) => visit_block(&body.body, f),
        ExprKind::Table(items) => {
            for item in items {
                match item {
                    TableItem::Pos(e) | TableItem::Named(_, e) => visit_expr(e, f),
                    TableItem::Keyed(a, b) => {
                        visit_expr(a, f);
                        visit_expr(b, f);
                    }
                }
            }
        }
        ExprKind::Field(e, _) | ExprKind::Unary(_, e) | ExprKind::Paren(e) => visit_expr(e, f),
        ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
            visit_expr(a, f);
            visit_expr(b, f);
        }
        ExprKind::IfElse(a, b, c) => {
            for e in [a, b, c] {
                visit_expr(e, f);
            }
        }
        ExprKind::Interp(parts) => {
            for part in parts {
                if let InterpPart::Expr(e) = part {
                    visit_expr(e, f);
                }
            }
        }
        _ => {}
    }
}
