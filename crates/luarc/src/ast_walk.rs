//! Mutable pre/post-order walker over the AST (used by `specialize.rs` to find
//! call sites, copy function bodies with fresh node ids and rewrite callee names).

use crate::ast::*;

/// Hooks called while walking; every hook has an empty default.
pub trait VisitMut {
    /// Before the statements of a block are walked.
    fn block(&mut self, _b: &mut Block) {}
    /// Before a statement's children are walked.
    fn stat(&mut self, _s: &mut Stat) {}
    /// After a statement's children were walked.
    fn exit_stat(&mut self, _s: &mut Stat) {}
    /// Before an expression's children are walked.
    fn expr(&mut self, _e: &mut Expr) {}
    /// After an expression's children were walked.
    fn exit_expr(&mut self, _e: &mut Expr) {}
    /// Every `Name` node (identifiers in expressions, declarations, fields, parameters).
    fn name(&mut self, _n: &mut Name) {}
    /// Before a function body's children are walked.
    fn func(&mut self, _f: &mut FuncBody) {}
}

pub fn walk_block<V: VisitMut + ?Sized>(v: &mut V, b: &mut Block) {
    v.block(b);
    for s in b.stats.iter_mut() {
        walk_stat(v, s);
    }
}

pub fn walk_func<V: VisitMut + ?Sized>(v: &mut V, f: &mut FuncBody) {
    v.func(f);
    for g in f.generics.iter_mut() {
        v.name(g);
    }
    for p in f.params.iter_mut() {
        v.name(&mut p.name);
        if let Some(t) = &mut p.ty {
            walk_type(v, t);
        }
    }
    if let Some(rs) = &mut f.rets {
        for t in rs {
            walk_type(v, t);
        }
    }
    if let Some((_, Some(t))) = &mut f.vararg {
        walk_type(v, t);
    }
    walk_block(v, &mut f.body);
}

pub fn walk_type<V: VisitMut + ?Sized>(v: &mut V, t: &mut TypeExpr) {
    match t {
        TypeExpr::Named(..) | TypeExpr::Nil(_) | TypeExpr::Unsupported(..) => {}
        TypeExpr::Optional(x) | TypeExpr::Array(x, _) | TypeExpr::Variadic(x, _) => walk_type(v, x),
        TypeExpr::Map(k, x, _) => {
            walk_type(v, k);
            walk_type(v, x);
        }
        TypeExpr::Record(fs, _) => {
            for (n, x) in fs.iter_mut() {
                v.name(n);
                walk_type(v, x);
            }
        }
        TypeExpr::Func(ps, rs, _) => {
            for x in ps.iter_mut().chain(rs.iter_mut()) {
                walk_type(v, x);
            }
        }
        TypeExpr::Applied(_, args, _) | TypeExpr::Union(args, _) => {
            for x in args {
                walk_type(v, x);
            }
        }
    }
}

pub fn walk_stat<V: VisitMut + ?Sized>(v: &mut V, s: &mut Stat) {
    v.stat(s);
    match &mut s.kind {
        StatKind::Local(names, exprs) => {
            for (n, t) in names.iter_mut() {
                v.name(n);
                if let Some(t) = t {
                    walk_type(v, t);
                }
            }
            for e in exprs {
                walk_expr(v, e);
            }
        }
        StatKind::LocalFunction(n, f) => {
            v.name(n);
            walk_func(v, f);
        }
        StatKind::Function(t, f) => {
            walk_expr(v, t);
            walk_func(v, f);
        }
        StatKind::Assign(ts, es) => {
            for e in ts.iter_mut().chain(es.iter_mut()) {
                walk_expr(v, e);
            }
        }
        StatKind::Compound(_, t, e) => {
            walk_expr(v, t);
            walk_expr(v, e);
        }
        StatKind::Call(e) => walk_expr(v, e),
        StatKind::Do(b) => walk_block(v, b),
        StatKind::While(c, b) => {
            walk_expr(v, c);
            walk_block(v, b);
        }
        StatKind::Repeat(b, c) => {
            walk_block(v, b);
            walk_expr(v, c);
        }
        StatKind::If(arms, els) => {
            for (c, b) in arms.iter_mut() {
                walk_expr(v, c);
                walk_block(v, b);
            }
            if let Some(b) = els {
                walk_block(v, b);
            }
        }
        StatKind::NumFor(n, a, b, c, body) => {
            v.name(n);
            walk_expr(v, a);
            walk_expr(v, b);
            if let Some(c) = c {
                walk_expr(v, c);
            }
            walk_block(v, body);
        }
        StatKind::GenFor(names, exprs, body) => {
            for n in names.iter_mut() {
                v.name(n);
            }
            for e in exprs {
                walk_expr(v, e);
            }
            walk_block(v, body);
        }
        StatKind::Return(es) => {
            for e in es {
                walk_expr(v, e);
            }
        }
        StatKind::Break | StatKind::Continue => {}
        StatKind::TypeAlias(n, gs, t) => {
            v.name(n);
            for g in gs.iter_mut() {
                v.name(g);
            }
            walk_type(v, t);
        }
    }
    v.exit_stat(s);
}

pub fn walk_expr<V: VisitMut + ?Sized>(v: &mut V, e: &mut Expr) {
    v.expr(e);
    match &mut e.kind {
        ExprKind::Nil | ExprKind::Bool(_) | ExprKind::Number(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Vararg => {}
        ExprKind::Interp(parts) => {
            for p in parts {
                if let InterpPart::Expr(x) = p {
                    walk_expr(v, x);
                }
            }
        }
        ExprKind::Name(n) => v.name(n),
        ExprKind::Index(a, b) => {
            walk_expr(v, a);
            walk_expr(v, b);
        }
        ExprKind::Field(o, n) => {
            walk_expr(v, o);
            v.name(n);
        }
        ExprKind::Call(f, args) => {
            walk_expr(v, f);
            for a in args {
                walk_expr(v, a);
            }
        }
        ExprKind::Method(o, n, args) => {
            walk_expr(v, o);
            v.name(n);
            for a in args {
                walk_expr(v, a);
            }
        }
        ExprKind::Function(f) => walk_func(v, f),
        ExprKind::Table(items) => {
            for it in items {
                match it {
                    TableItem::Pos(x) => walk_expr(v, x),
                    TableItem::Named(n, x) => {
                        v.name(n);
                        walk_expr(v, x);
                    }
                    TableItem::Keyed(k, x) => {
                        walk_expr(v, k);
                        walk_expr(v, x);
                    }
                }
            }
        }
        ExprKind::Binary(_, a, b) => {
            walk_expr(v, a);
            walk_expr(v, b);
        }
        ExprKind::Unary(_, a) | ExprKind::Paren(a) => walk_expr(v, a),
        ExprKind::IfElse(c, a, b) => {
            walk_expr(v, c);
            walk_expr(v, a);
            walk_expr(v, b);
        }
        ExprKind::Cast(x, t) => {
            walk_expr(v, x);
            walk_type(v, t);
        }
    }
    v.exit_expr(e);
}
