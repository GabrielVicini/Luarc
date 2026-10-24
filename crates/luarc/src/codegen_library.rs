//! Library calls introduced by the benchmark, lowered only through structured rir.
use super::*;

impl<'a> Gen<'a> {
    pub(super) fn library_builtin(&mut self, e: &Expr, b: BuiltinFn, all: &[Arg]) -> Option<(RExpr, Vec<(TyId, bool)>)> {
        if let Some(result) = self.runtime_table_library(e, b, all) { return Some(result); }
        if matches!(b, BuiltinFn::StrFind | BuiltinFn::StrMatch) && all.iter().take(2).any(|a| self.is_any_ty(self.arg_ety(a).ty)) { return Some(self.dynamic_find_code(e, b, all)); }
        if b == BuiltinFn::Xpcall { return Some(self.xpcall_code(e, all)); }
        let name = match b { BuiltinFn::Bit32(n) => n, BuiltinFn::StrSplit => "split", _ => return None };
        let mut pre = Vec::new();
        let mut argv = Vec::new();
        for a in all {
            let v = self.arg_val(a);
            let v = self.box_value(v);
            let t = self.fresh("bit");
            pre.push(rir::let_(t.clone(), v.code));
            argv.push(rir::atom_e(t));
        }
        let path = if name == "btest" { "lr::bit32::call_bool" } else { "lr::bit32::call_num" };
        let call = if b == BuiltinFn::StrSplit {
            rir::call("lr::library::string_split", vec![rir::borrow(RExpr::Array(argv))])
        } else {
            rir::call(path, vec![rir::atom_e(rust_str_lit(name)), rir::borrow(RExpr::Array(argv))])
        };
        let code = rir::block(pre, rir::at(call, &self.loc(e.span)));
        Some((code, vec![(self.ck.info.expr[&e.id].ty, false)]))
    }
}

impl<'a> Gen<'a> {
    fn protected_box(&self, value: RExpr, optional: bool, ty: TyId) -> RExpr {
        if self.ck.info.runtime_tables.enabled && matches!(self.node(ty), TyNode::Func(_)) {
            if optional {
                let adapted = rir::method(value, "map", vec![rir::atom_e("lr::dynamic_fn::function")]);
                rir::method(adapted, "unwrap_or", vec![rir::atom_e("lr::Value::Nil")])
            } else { rir::call("lr::dynamic_fn::function", vec![value]) }
        } else { rir::call("lr::dynamic::to_value", vec![value]) }
    }

    fn protected_values(&self, call: RExpr, rets: &[Slot], first_only: bool) -> RExpr {
        let names: Vec<_> = (0..rets.len()).map(|i| format!("__xp{i}")).collect();
        let pat = match names.as_slice() {
            [name] => rir::RPattern::Name(name.clone()),
            _ => rir::RPattern::Tuple(names.iter().cloned().map(rir::RPattern::Name).collect()),
        };
        let values: Vec<_> = names.iter().zip(rets).map(|(n, slot)| self.protected_box(rir::atom_e(n.clone()), self.is_null(slot.null), slot.ty)).collect();
        let result = if first_only {
            values.first().cloned().unwrap_or_else(|| rir::atom_e("lr::Value::Nil"))
        } else { RExpr::Macro("vec".into(), values) };
        // Underscore-prefixed tuple bindings allow ignored handler results without warnings.
        rir::method(call, "map", vec![RExpr::ClosurePattern(vec![pat], Box::new(result))])
    }

    pub(super) fn xpcall_code(&mut self, e: &Expr, all: &[Arg]) -> (RExpr, Vec<(TyId, bool)>) {
        let ft = self.func_of(self.arg_ety(&all[0]).ty);
        let ht = self.func_of(self.arg_ety(&all[1]).ty);
        let f = self.arg_val(&all[0]);
        let h = self.arg_val(&all[1]);
        let fnm = self.fresh("xpfn");
        let hnm = self.fresh("xph");
        let mut pre = vec![rir::let_(fnm.clone(), f.code), rir::let_(hnm.clone(), h.code)];
        let popt: Vec<_> = ft.params.iter().map(|p| self.is_null(p.null)).collect();
        // Luau evaluates arguments before protection; box each adjusted value, including call tails.
        let mut inputs = Vec::new();
        for (i, arg) in all.iter().skip(2).enumerate() {
            let value = self.arg_val(arg);
            let expected = ft.params.get(i).copied().or(ft.vararg);
            let value = if expected.is_some_and(|s| self.is_any_ty(s.ty)) {
                Val { code: self.protected_box(value.code, value.opt, self.arg_ety(arg).ty), opt: false }
            } else { value };
            let name = self.fresh("xparg");
            pre.push(rir::let_(name.clone(), value.code));
            inputs.push(Arg::V(Val { code: rir::atom_e(name), opt: value.opt }, self.arg_ety(arg), Self::arg_span(arg)));
        }
        for param in ft.params.iter().skip(inputs.len()) {
            let value = if self.is_any_ty(param.ty) { Val { code: rir::atom_e("lr::Value::Nil"), opt: false } } else { Val { code: rir::atom_e("None"), opt: true } };
            inputs.push(Arg::V(value, ETy { ty: param.ty, null: param.null, soft: Soft::No }, e.span));
        }
        let (p, args) = self.args(&inputs, &popt, ft.vararg.is_some());
        pre.extend(p);
        let args = self.bind_call_args(&mut pre, args);
        let function = if f.opt { rir::try_(rir::call("lr::library::protected_callable", vec![rir::atom_e(fnm)])) } else { rir::atom_e(fnm) };
        let handler_name = self.fresh("xph_checked");
        let handler = self.coerce(Val { code: rir::atom_e(hnm), opt: h.opt }, false, e.span, "invalid argument #2 to 'xpcall' (function expected, got nil)");
        pre.push(rir::let_(handler_name.clone(), handler));
        let call = rir::method(function, "call", vec![RExpr::Tuple(args)]);
        let rets = self.ck.st.rets_known(ft.rets).cloned().unwrap_or_default();
        let body = RExpr::ClosurePattern(vec![], Box::new(self.protected_values(call, &rets, false)));
        let mut ha = Vec::new();
        for (i, p) in ht.params.iter().enumerate() {
            let x = if i == 0 {
                let v = rir::atom_e("__xp_error");
                let v = if self.is_any_ty(p.ty) { rir::call("lr::dynamic::to_value", vec![v]) } else { v };
                if self.is_null(p.null) { rir::some(v) } else { v }
            } else if self.is_any_ty(p.ty) { rir::atom_e("lr::Value::Nil") } else { rir::atom_e("None") };
            ha.push(x);
        }
        if let Some(va) = ht.vararg {
            let values = if ht.params.is_empty() {
                let value = rir::atom_e("__xp_error");
                let value = if self.is_any_ty(va.ty) { rir::call("lr::dynamic::to_value", vec![value]) } else { value };
                vec![rir::some(value)]
            } else { vec![] };
            ha.push(RExpr::Macro("vec".into(), values));
        }
        let hcall = rir::method(rir::atom_e(handler_name), "call", vec![RExpr::Tuple(ha)]);
        let hrets = self.ck.st.rets_known(ht.rets).cloned().unwrap_or_default();
        let handler = RExpr::ClosurePattern(vec![rir::RPattern::Name("__xp_error".into())], Box::new(self.protected_values(hcall, &hrets, true)));
        let xs = self.fresh("xpret");
        pre.push(rir::let_(xs.clone(), rir::call("lr::library::xpcall", vec![body, handler])));
        if self.ck.info.pack_calls.contains_key(&e.id) {
            return (rir::block(pre, rir::call("lr::dynamic::result_pack", vec![rir::atom_e(xs)])), vec![]);
        }
        let out = self.ck.info.builtin_outs.get(&e.id).cloned().unwrap_or_default();
        let values: Vec<_> = out.iter().enumerate().map(|(i, _)| {
            let v = rir::call("lr::library::result", vec![rir::borrow(rir::atom_e(xs.clone())), rir::atom_e(i.to_string())]);
            if i == 0 { rir::at(rir::method(v, "as_bool", vec![]), &self.loc(e.span)) } else { v }
        }).collect();
        (rir::block(pre, RExpr::Tuple(values)), out.iter().map(|v| (v.ty, false)).collect())
    }
}

impl<'a> Gen<'a> {
    fn dynamic_find_code(&mut self, e: &Expr, b: BuiltinFn, all: &[Arg]) -> (RExpr, Vec<(TyId, bool)>) {
        let mut pre = Vec::new();
        let mut args = Vec::new();
        for a in all {
            let v = self.arg_val(a);
            let n = self.fresh("findarg");
            pre.push(rir::let_(n.clone(), v.code));
            args.push(Val { code: rir::atom_e(n), opt: v.opt });
        }
        let mut strings = Vec::new();
        let name = if b == BuiltinFn::StrFind { "find" } else { "match" };
        for (i, value) in args.iter().take(2).enumerate() {
            if self.is_any_ty(self.arg_ety(&all[i]).ty) {
                let v = self.box_value(value.clone());
                let mut values = vec![rir::atom_e("lr::Value::Nil"); i];
                values.push(v.code);
                let call = rir::call("lr::library::string_arg", vec![rir::borrow(RExpr::Array(values)), rir::atom_e(i.to_string()), rir::atom_e(rust_str_lit(name))]);
                strings.push(rir::at(call, &self.loc(e.span)));
            } else { strings.push(self.coerce(value.clone(), false, e.span, "string expected")); }
        }
        let init = args.get(2).map(|v| if v.opt { v.code.clone() } else { rir::some(v.code.clone()) }).unwrap_or_else(|| rir::atom_e("None"));
        let plain = args.get(3).map(|v| if v.opt { rir::method(v.code.clone(), "unwrap_or", vec![rir::atom_e("false")]) } else { v.code.clone() }).unwrap_or_else(|| rir::atom_e("false"));
        let mut argv = vec![rir::borrow(strings[0].clone()), rir::borrow(strings[1].clone()), init, plain];
        let path = if self.ck.info.pattern_caps.contains_key(&e.id) { "lr::stdlib::string_find" } else {
            argv.push(rir::atom_e(rust_str_lit(name)));
            argv.push(rir::atom_e(if !self.ck.info.pattern_full.contains(&e.id) { "usize::MAX" } else if b == BuiltinFn::StrFind { "0" } else { "1" }));
            argv.push(rir::atom_e(if b == BuiltinFn::StrMatch { "true" } else { "false" }));
            "lr::stdlib::string_find_dyn"
        };
        let m = self.fresh("found");
        pre.push(rir::let_(m.clone(), rir::at(rir::call(path, argv), &self.loc(e.span))));
        let outs: Vec<_> = self.ck.info.builtin_outs.get(&e.id).into_iter().flatten().map(|s| (s.ty, true)).collect();
        let mut values = Vec::new();
        if b == BuiltinFn::StrFind {
            values.push(rir::field(rir::atom_e(m.clone()), "start"));
            values.push(rir::field(rir::atom_e(m.clone()), "end"));
        }
        let fixed = values.len();
        for (i, (ty, _)) in outs.iter().skip(fixed).enumerate() {
            let method = if matches!(self.node(*ty), TyNode::Num) { "pos" } else { "cap" };
            values.push(rir::method(rir::atom_e(m.clone()), method, vec![rir::atom_e(i.to_string())]));
        }
        let result = if values.len() == 1 { values.remove(0) } else { RExpr::Tuple(values) };
        (rir::block(pre, result), outs)
    }
}
