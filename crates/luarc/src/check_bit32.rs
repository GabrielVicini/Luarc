//! Luau bit32 argument acceptance and result types; coercion happens at runtime.
use crate::ast::*;
use crate::check::*;
use crate::types::ETy;

pub const FUNCTIONS: &[&str] = &["band", "bor", "bxor", "bnot", "btest", "lshift", "rshift", "arshift", "lrotate", "rrotate", "extract", "replace", "countlz", "countrz", "byteswap"];

impl<'a> Checker<'a> {
    pub(crate) fn bit32_call(&mut self, e: &Expr, name: &str, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        let Some(&name) = FUNCTIONS.iter().find(|&&n| n == name) else {
            return self.unsupported_lib(e.span, "bit32", name);
        };
        let (vals, spans) = self.args_values(args);
        for (v, span) in vals.iter().zip(spans) { self.boxable(v.ty, span); }
        self.note_multi_tail(e.id, args, &vals);
        self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::Bit32(name)));
        let value = if name == "btest" { self.bool_() } else { self.num() };
        let mut out = vec![value];
        if let Some(n) = want {
            out.truncate(n);
            while out.len() < n { out.push(self.nil()); }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use crate::{check::*, diag::SourceMap, native::{adapters::AdapterSet, world::World}, parser::parse_module, resolve::{Resolution, Resolver}, types::*};
    fn check(src: &str, test: impl FnOnce(&Checker<'_>)) {
        let mut next = 1;
        let module = parse_module(0, src, &mut next).unwrap();
        let mut sm = SourceMap::default();
        sm.add("test.luarc".into(), "test.luarc".into(), src.into());
        let mut res = Resolution::default();
        let mut resolver = Resolver::new(&mut res);
        resolver.module(&module, next);
        resolver.finish();
        assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
        let u = ModuleUnit { module, pseudo_func: next, ident: "m0".into(), requires: Default::default(), rust_requires: Default::default() };
        let world = World::default();
        let adapters = AdapterSet::default();
        let mut ck = Checker::new(&res, &sm, &world, &adapters);
        ck.check_program(&[u], &[0]);
        test(&ck);
    }
    #[test]
    fn results_and_aliases_have_static_types() {
        check("local band=bit32.band\nlocal n=band('7',3)\nlocal b=bit32.btest(1,2)", |ck| {
            assert!(ck.errors.is_empty(), "{:?}", ck.errors);
            for (name, boolean) in [("n", false), ("b", true)] {
                let sym = ck.res.syms.iter().position(|s| s.name == name).unwrap() as u32;
                let ty = ck.info.sym_slot[&sym].ty;
                assert!(if boolean { matches!(ck.st.node(ty), TyNode::Bool) } else { matches!(ck.st.node(ty), TyNode::Num) });
            }
        });
    }
    #[test]
    fn inferred_unboxable_argument_is_diagnosed() {
        check("local function f(x) return bit32.band(x) end\nlocal n:integer=5\nprint(f(n))", |ck| {
            assert!(ck.errors.iter().any(|e| e.msg == "a value of type integer cannot be converted to 'any'"), "{:?}", ck.errors);
        });
    }
    #[test]
    fn handler_results_are_dynamic_and_find_accepts_them() {
        check("local ok,v=xpcall(function()error('x',0)end,function(e)return e end)\nprint(string.find(v,'x',1,true))", |ck| {
            assert!(ck.errors.is_empty(), "{:?}", ck.errors);
            let sym = ck.res.syms.iter().position(|s| s.name == "v").unwrap() as u32;
            assert!(matches!(ck.st.node(ck.info.sym_slot[&sym].ty), TyNode::Any));
        });
    }
}
