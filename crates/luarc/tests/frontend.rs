//! Frontend tests (no Cargo builds): lexing, precedence, resolution and type
//! checking rules, through the library API.

use luarc::ast::*;
use luarc::check::{Checker, ModuleUnit};
use luarc::diag::SourceMap;
use luarc::parser::parse_module;
use luarc::resolve::{Resolution, Resolver};

fn parse(src: &str) -> Module {
    let mut id = 1;
    parse_module(0, src, &mut id).unwrap_or_else(|e| panic!("parse error: {:?}", e))
}

/// S-expression rendering of an expression (for precedence tests).
fn sx(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Number(n) => format!("{n}"),
        ExprKind::Name(n) => n.text.clone(),
        ExprKind::Str(s) => format!("{:?}", String::from_utf8_lossy(s)),
        ExprKind::Bool(b) => b.to_string(),
        ExprKind::Nil => "nil".into(),
        ExprKind::Binary(op, a, b) => format!("({} {} {})", op.symbol(), sx(a), sx(b)),
        ExprKind::Unary(op, a) => format!("({:?} {})", op, sx(a)),
        ExprKind::Paren(a) => sx(a),
        ExprKind::Call(f, args) => format!("(call {} {})", sx(f), args.iter().map(sx).collect::<Vec<_>>().join(" ")),
        ExprKind::Field(o, n) => format!("{}.{}", sx(o), n.text),
        ExprKind::IfElse(c, a, b) => format!("(if {} {} {})", sx(c), sx(a), sx(b)),
        _ => "?".into(),
    }
}

fn expr_of(src: &str) -> String {
    let m = parse(&format!("local _ = {src}"));
    match &m.body.stats[0].kind {
        StatKind::Local(_, es) => sx(&es[0]),
        _ => unreachable!(),
    }
}

#[test]
fn luau_precedence_and_associativity() {
    assert_eq!(expr_of("1 + 2 * 3"), "(+ 1 (* 2 3))");
    assert_eq!(expr_of("2 ^ 3 ^ 2"), "(^ 2 (^ 3 2))");
    assert_eq!(expr_of("-x ^ 2"), "(Neg (^ x 2))");
    assert_eq!(expr_of("not a == b"), "(== (Not a) b)");
    assert_eq!(expr_of("a or b and c"), "(or a (and b c))");
    assert_eq!(expr_of("\"a\" .. \"b\" .. \"c\""), "(.. \"a\" (.. \"b\" \"c\"))");
    assert_eq!(expr_of("1 .. 2 + 3"), "(.. 1 (+ 2 3))");
    assert_eq!(expr_of("a < b == true"), "(== (< a b) true)");
    assert_eq!(expr_of("#t + 1"), "(+ (Len t) 1)");
    assert_eq!(expr_of("10 - 2 - 3"), "(- (- 10 2) 3)");
    assert_eq!(expr_of("a // b % c"), "(% (// a b) c)");
    assert_eq!(expr_of("if a then 1 elseif b then 2 else 3"), "(if a 1 (if b 2 3))");
    assert_eq!(expr_of("f\"s\""), "(call f \"s\")");
}

#[test]
fn lexer_literals() {
    assert_eq!(expr_of("0x1F + 0b101 + 1_000"), "(+ (+ 31 5) 1000)");
    assert_eq!(expr_of("1e3"), "1000");
    assert_eq!(expr_of("\"\\u{48}\\x69\\33\""), "\"Hi!\"");
    assert_eq!(expr_of("\"a\\z   \n  b\""), "\"ab\"");
    assert_eq!(expr_of("[==[x]]y]==]"), "\"x]]y\"");
    let m = parse("-- comment\n--[[ block\ncomment ]] local x = 1 --[==[ also ]==]");
    assert_eq!(m.body.stats.len(), 1);
}

#[test]
fn parse_errors_have_locations() {
    let mut id = 1;
    let e = parse_module(0, "local x = = 1", &mut id).unwrap_err();
    assert_eq!((e[0].span.line, e[0].span.col), (1, 11));
    let e = parse_module(0, "if x then\n  y()\n", &mut id).unwrap_err();
    assert!(e[0].msg.contains("expected 'end'"), "{}", e[0].msg);
    let e = parse_module(0, "local s = \"open", &mut id).unwrap_err();
    assert!(e[0].msg.contains("unfinished string"));
}

/// Type checks a single module; returns rendered diagnostics (`L:C: message`).
fn check(src: &str) -> Vec<String> {
    let mut id = 1;
    let module = match parse_module(0, src, &mut id) {
        Ok(m) => m,
        Err(e) => return e.iter().map(|d| d.to_string()).collect(),
    };
    let mut sm = SourceMap::default();
    sm.add("t.luarc".into(), "t.luarc".into(), src.into());
    let mut res = Resolution::default();
    let pseudo = id;
    {
        let mut r = Resolver::new(&mut res);
        r.module(&module, pseudo);
        r.finish();
        if !r.errors.is_empty() {
            return r.errors.iter().map(|d| d.to_string()).collect();
        }
    }
    let units = vec![ModuleUnit {
        module,
        pseudo_func: pseudo,
        ident: "m0".into(),
        requires: Default::default(),
        rust_requires: Default::default(),
    }];
    let world = luarc::native::world::World::default();
    let adapters = luarc::native::adapters::AdapterSet::default();
    let mut ck = Checker::new(&res, &sm, &world, &adapters);
    ck.check_program(&units, &[0]);
    ck.errors.iter().map(|d| d.to_string()).collect()
}

fn ok(src: &str) {
    let e = check(src);
    assert!(e.is_empty(), "unexpected errors for:\n{src}\n{e:#?}");
}

fn fails(src: &str, needle: &str) {
    let e = check(src);
    assert!(e.iter().any(|m| m.contains(needle)), "expected {needle:?} for:\n{src}\ngot {e:#?}");
}

#[test]
fn inference_across_later_uses() {
    ok("local t = {}\ntable.insert(t, 1)\nlocal x: number = t[1]");
    ok("local m = {}\nm[\"k\"] = true\nlocal b: boolean? = m[\"k\"]");
    ok("local r = {}\nr.name = \"x\"\nlocal s: string = r.name");
    ok("local function id(x) return x end\nlocal n: number = id(1)");
    fails("local t = {}\ntable.insert(t, 1)\ntable.insert(t, \"s\")", "type mismatch");
    fails("local function f(x) return x end\nf(1)\nf(\"s\")", "type mismatch");
}

#[test]
fn nil_narrowing_rules() {
    // nil checks narrow; early exit narrows the rest of the block
    ok("local function f(x: number?)\n if x ~= nil then print(x + 1) end\n if not x then return end\n print(x * 2)\nend");
    // narrowing does not survive a later assignment of nil
    fails("local function f(x: number?)\n if x then\n  x = nil\n  print(x + 1)\n end\nend", "may be nil");
    // nor an assignment inside a closure
    fails(
        "local function f(x: number?)\n local reset = function() x = nil end\n if x then reset() print(x + 1) end\nend",
        "may be nil",
    );
    // loops that assign the variable drop the narrowing at loop entry
    fails("local function f(x: number?)\n if x then\n  while true do print(x + 1) x = nil end\n end\nend", "may be nil");
    // using an optional without a check is an error
    fails("local function f(x: number?) return x + 1 end", "may be nil");
}

#[test]
fn pcall_result_narrowing() {
    ok("local ok, v = pcall(function() return 1 end)\nif ok then print(v + 1) else print(v:upper()) end");
    fails("local ok, v = pcall(function() return 1 end)\nprint(v + 1)", "type mismatch");
}

#[test]
fn logical_operators_return_operands() {
    ok("local x: number? = nil\nlocal y: number = x or 5");
    ok("local c = true\nlocal s: string = c and \"a\" or \"b\"");
    fails("local c = true\nlocal s: string = c and \"a\"", "type mismatch");
}

#[test]
fn records_arrays_maps() {
    fails("local t = {1, 2}\nt.x = 1", "array");
    fails("type P = {x: number}\nlocal p: P = {x = 1, y = 2}", "field 'y'");
    fails("local t = {1, x = 2}", "mixed table");
    ok("type P = {x: number, y: number?}\nlocal p: P = {x = 1}\np.y = 2");
    fails("local m: {[string]: number} = {}\nm[1] = 2", "type mismatch");
}

#[test]
fn functions_and_multiple_returns() {
    ok("local function two() return 1, \"a\" end\nlocal a: number, b: string = two()");
    ok("local function two() return 1, 2 end\nlocal t = {two()}\nlocal n: number = #t");
    fails("local function f(a: number) end\nf(\"x\")", "type mismatch");
    fails("local f: (number) -> number = function(a: number, b: number) return a end", "parameter counts differ");
}

#[test]
fn resolution_errors() {
    fails("print(undefined_name)", "unknown variable 'undefined_name'");
    fails("x = 1", "undeclared variable 'x'");
    fails("while true do end\ncontinue", "outside a loop");
    fails("print = 1", "cannot assign to builtin 'print'");
    ok("local t = setmetatable({}, {})");
}
