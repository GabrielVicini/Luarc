//! Runtime-table source boundaries must fail before generated Rust if unsupported.
use luarc::check::{Checker, ModuleUnit};
use luarc::diag::SourceMap;
use luarc::native::{adapters::AdapterSet, world::World};
use luarc::parser::parse_module;
use luarc::resolve::{Resolution, Resolver};

fn errors(source: &str) -> Vec<String> {
    let mut next = 1;
    let module = parse_module(0, source, &mut next).expect("parse source boundary");
    let mut resolution = Resolution::default();
    let mut resolver = Resolver::new(&mut resolution);
    resolver.module(&module, next);
    resolver.finish();
    assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
    let units = vec![ModuleUnit { module, pseudo_func: next, ident: "m0".into(), requires: Default::default(), rust_requires: Default::default() }];
    let mut map = SourceMap::default();
    map.add("runtime.luarc".into(), "runtime.luarc".into(), source.into());
    let world = World::default();
    let adapters = AdapterSet::default();
    let mut checker = Checker::new(&resolution, &map, &world, &adapters);
    checker.check_program(&units, &[0]);
    checker.errors.iter().map(|error| error.msg.clone()).collect()
}

#[test]
fn unsupported_erased_callback_shapes_are_source_diagnostics() {
    for (source, expected) in [
        ("local t=setmetatable({}, {__call=function(self, x:number) return tostring(x) end}) print(t('word'))", "callback parameters must"),
        ("local t=setmetatable({}, {__call=function(a,b,c,d,e,f,g,h,i) return 1 end}) print(t())", "at most eight fixed parameters"),
        ("local function make() return {x=7} end local function run() local t=setmetatable({}, {__call=make}) print(t()) end run()", "callback table results require"),
        ("local function make() return {7} end local function run() local t=setmetatable({}, {__call=make}) local v=t() if type(v)=='table' then print(v[1]) end end run()", "callback table results require"),
        ("local function f():string return 'word' end local a:any=f local function run() local t=setmetatable({}, {__call=a,__metatable=false}) print(t()) end run()", "opaque typed functions flowing into any"),
        ("local t={f=function():string return 'word' end,__metatable=false} local f=(t.f)::(() -> string) print(f())", "casts from any to typed functions are unsupported"),
    ] {
        let found = errors(source);
        assert!(found.iter().any(|message| message.contains(expected)), "{source}: {found:?}");
    }
}

#[test]
fn invalid_raw_operations_and_shape_replacements_are_diagnosed() {
    for (source, expected) in [
        ("print(rawlen(5))", "rawlen requires"),
        ("print(rawlen(true))", "rawlen requires"),
        ("local t={nested={x=7}, __metatable=false} rawset(t,'nested',7) print(t.nested)", "rawset cannot replace"),
        ("local t=setmetatable({}, {__call=function() return 1 end}) local function f() return 1,2 end print(t(f()))", "explicit single-value arguments"),
        ("local t=setmetatable({nested={x=7}}, {__call=function(self) rawset(self,'nested',7) end}) t() print(t.nested)", "statically tracked nested-table data"),
        ("local t={nested={x=7},__metatable=false} local a:any=t if type(a)=='table' then rawset(a,'nested',7) end print(t.nested)", "nested-table data cannot flow into any"),
    ] {
        let found = errors(source);
        assert!(found.iter().any(|message| message.contains(expected)), "{source}: {found:?}");
    }
}

#[test]
fn exact_layout_accepts_sparse_lengths_and_later_metadata_writes() {
    let found = errors("local t={1,2,__metatable=false} print(#t) t[4]=3");
    assert!(found.is_empty(), "{found:?}");
    let found = errors("local mt={__len=function() return 7 end} local t=setmetatable({[1]=1,[3]=3},mt) rawset(mt,'__len',nil) print(#t)");
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn manually_boxed_pack_values_require_runtime_provenance() {
    for (source, expected) in [
        ("local function make() return {value=7} end local values=table.pack(make()) local function run() local marker=setmetatable({}, {__metatable=false}) local v=values[1] if type(v)=='table' then print(v.value) end end run()", "static table is manually boxed"),
        ("local function make() return {7} end local values=table.pack(make()) local function run() local marker=setmetatable({}, {__metatable=false}) local v=values[1] if type(v)=='table' then print(v[1]) end end run()", "static table is manually boxed"),
        ("local function f() return 'word' end local values=table.pack(f) local function run() local t=setmetatable({}, {__call=values[1],__metatable=false}) print(t()) end run()", "opaque typed functions manually boxed"),
        ("local marker=setmetatable({}, {__metatable=false}) local n:integer=7 print(n)", "cannot be converted to 'any'"),
        ("local marker=setmetatable({}, {__metatable=false}) local function log(...:integer) print(...) end log(7)", "cannot be converted to 'any'"),
    ] {
        let found = errors(source);
        assert!(found.iter().any(|message| message.contains(expected)), "{source}: {found:?}");
    }
}
