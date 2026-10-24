//! Dormant class syntax checks; source enabling belongs to the later 1d gate.

use luarc::ast::*;
use luarc::check::ModuleUnit;
use luarc::check_metatable::ClassSyntax;
use luarc::parser::parse_module;
use luarc::resolve::{Resolution, Resolver};

fn analyze(src: &str, test: impl FnOnce(&Resolution, &ModuleUnit, ClassSyntax)) {
    let mut next = 1;
    let module = parse_module(0, src, &mut next).expect("parse syntax fixture");
    let mut res = Resolution::default();
    let mut resolver = Resolver::new(&mut res);
    resolver.module(&module, next);
    resolver.finish();
    assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
    let unit = ModuleUnit {
        module,
        pseudo_func: next,
        ident: "m0".into(),
        requires: Default::default(),
        rust_requires: Default::default(),
    };
    let syntax = ClassSyntax::analyze(&res, std::slice::from_ref(&unit));
    test(&res, &unit, syntax);
}

fn class_use(res: &Resolution, syntax: &ClassSyntax, stat: &Stat) -> Result<u32, luarc::diag::Diagnostic> {
    let StatKind::Call(expr) = &stat.kind else {
        panic!("expected marker call")
    };
    let ExprKind::Call(_, args) = &expr.kind else {
        panic!("expected marker call")
    };
    syntax.class_argument(res, expr.id, args.last().expect("class argument"))
}

#[test]
fn syntax_accepts_direct_and_nested_class_uses_with_distinct_shadowed_symbols() {
    analyze(
        "local C = {} C.__index = C local function make() print({}, C) end do local C = {} C.__index = C print({}, C) end print({}, C)",
        |res, unit, syntax| {
            assert!(syntax.errors.is_empty(), "{:?}", syntax.errors);
            let stats = &unit.module.body.stats;
            let StatKind::LocalFunction(_, body) = &stats[2].kind else {
                panic!()
            };
            let outer = class_use(res, &syntax, &body.body.stats[0]).expect("nested class");
            let StatKind::Do(block) = &stats[3].kind else { panic!() };
            let inner = class_use(res, &syntax, &block.stats[2]).expect("shadowed class");
            assert_ne!(outer, inner);
            assert_eq!(class_use(res, &syntax, &stats[4]).expect("outer class"), outer);
        },
    );
}

#[test]
fn syntax_rejects_every_other_index_write_form_even_in_unused_code() {
    for write in [
        "local Alias = C Alias.__index = C",
        "C[\"__index\"] = C",
        "local t = {[((\"__index\"))] = C}",
        "local t = {} t[(\"__index\")] = C",
        "C.__index += 1",
        "C.__index, C.x = C, 1",
        "local t = {__index = C}",
        "local t = {[\"__index\"] = C}",
        "function C.__index() end",
        "function C:__index() end",
        "local function unused() C.__index = nil end",
        "local unused = function() return {__index = C} end",
        "local unused = {callback = function() C[\"__index\"] = C end}",
        "local unused = `value {({__index = C})}`",
    ] {
        analyze(&format!("local C = {{}} {write}"), |_, _, syntax| {
            assert!(
                syntax
                    .errors
                    .iter()
                    .any(|e| e.msg == "the only supported __index write in step 1 is the statement X.__index = X"),
                "{write}: {:?}",
                syntax.errors
            );
        });
    }
}

#[test]
fn syntax_requires_empty_direct_declaration_and_same_block_initialization() {
    for src in [
        "local C = {x = 1} C.__index = C",
        "local C = {} do C.__index = C end",
        "local C = {} if true then C.__index = C end",
        "local C = {} local function unused() C.__index = C end",
        "local C local function initialize() C.__index = C end",
        "local C = {} local Alias = C Alias.__index = Alias",
    ] {
        analyze(src, |_, _, syntax| {
            assert!(
                syntax
                    .errors
                    .iter()
                    .any(|e| e.msg == "X.__index = X must follow local X = {} in the same block and precede setmetatable(_, X)"),
                "{src}: {:?}",
                syntax.errors
            );
        });
    }
}

#[test]
fn syntax_rejects_class_aliases_rebinding_missing_index_and_early_uses() {
    for (src, message) in [
        (
            "local C = {} C.__index = C local Alias = C print({}, Alias)",
            "setmetatable requires the directly declared local class name in step 1",
        ),
        (
            "local C = {} C.__index = C print({}, (C))",
            "setmetatable requires the directly declared local class name in step 1",
        ),
        (
            "local C = {} C.__index = C C = {} print({}, C)",
            "the local class name passed to setmetatable must not be reassigned in step 1",
        ),
        (
            "local C = {} print({}, C)",
            "step 1 requires the metatable's own __index to be the metatable itself",
        ),
        (
            "local C = {} print({}, C) C.__index = C",
            "X.__index = X must precede every setmetatable(_, X) use in step 1",
        ),
        (
            "local C = {} C.__index = C print({}, C) C.__index = C",
            "X.__index = X must precede every setmetatable(_, X) use in step 1",
        ),
    ] {
        analyze(src, |res, unit, syntax| {
            let call = unit
                .module
                .body
                .stats
                .iter()
                .find(|s| matches!(s.kind, StatKind::Call(_)))
                .expect("marker call");
            assert_eq!(class_use(res, &syntax, call).expect_err("invalid class").msg, message);
        });
    }
}

#[test]
fn syntax_orders_nested_uses_by_the_enclosing_definition_statement() {
    analyze(
        "local C = {} local function make() print({}, C) end C.__index = C",
        |res, unit, syntax| {
            let StatKind::LocalFunction(_, body) = &unit.module.body.stats[1].kind else {
                panic!()
            };
            assert_eq!(
                class_use(res, &syntax, &body.body.stats[0]).expect_err("early nested use").msg,
                "X.__index = X must precede every setmetatable(_, X) use in step 1"
            );
        },
    );
}

#[test]
fn syntax_visits_every_loaded_module() {
    let mut next = 1;
    let first = parse_module(0, "local C = {} C.__index = C", &mut next).expect("first module");
    let second = parse_module(1, "local unused = function() return {__index = {x = 1}} end", &mut next).expect("second module");
    let mut res = Resolution::default();
    let mut resolver = Resolver::new(&mut res);
    resolver.module(&first, next);
    resolver.module(&second, next + 1);
    resolver.finish();
    assert!(resolver.errors.is_empty());
    let units: Vec<_> = [first, second]
        .into_iter()
        .enumerate()
        .map(|(i, module)| ModuleUnit {
            module,
            pseudo_func: next + i as u32,
            ident: format!("m{i}"),
            requires: Default::default(),
            rust_requires: Default::default(),
        })
        .collect();
    let syntax = ClassSyntax::analyze(&res, &units);
    assert_eq!(syntax.errors.len(), 1);
    assert_eq!(syntax.errors[0].span.file, 1);
}

#[test]
fn syntax_orders_repeat_condition_after_its_body_declarations() {
    analyze("repeat local C = {} C.__index = C until print({}, C)", |res, unit, syntax| {
        assert!(syntax.errors.is_empty());
        let StatKind::Repeat(_, expr) = &unit.module.body.stats[0].kind else {
            panic!()
        };
        let ExprKind::Call(_, args) = &expr.kind else { panic!() };
        assert!(syntax.class_argument(res, expr.id, &args[1]).is_ok());
    });
}

#[test]
fn source_gate_resolves_the_class_builtin() {
    let mut next = 1;
    let module = parse_module(0, "local C = {} C.__index = C setmetatable({}, C)", &mut next).expect("parse");
    let mut res = Resolution::default();
    let mut resolver = Resolver::new(&mut res);
    resolver.module(&module, next);
    resolver.finish();
    assert!(
        resolver.errors.is_empty()
            && resolver.r.names.values().any(|r| *r == luarc::resolve::Res::Builtin(luarc::resolve::Builtin::SetMetatable)),
        "{:?}",
        resolver.errors
    );
}
