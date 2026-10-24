//! Value-list lowering through rir nodes.

use super::*;

impl<'a> Gen<'a> {
    /// A value list boxed into optional dynamic slots. Each preceding expression
    /// is bound before lowering the final call, preserving Luau's evaluation order.
    pub(super) fn boxed_list(&mut self, args: &[Expr]) -> RExpr {
        let mut pre = Vec::new();
        let mut fixed = Vec::new();
        for (i, e) in args.iter().enumerate() {
            if i + 1 == args.len() && self.is_pack(e) {
                let (p, vals, src, start) = self.pack_src(e);
                pre.extend(p);
                fixed.extend(vals.into_iter().map(|v| rir::call("lr::packs::slot", vec![v.code])));
                let tail = rir::call("lr::packs::boxed", vec![rir::borrow(src), start]);
                let values = rir::call("lr::va::with_rest", vec![RExpr::Macro("vec".into(), fixed), rir::borrow(tail), rir::atom_e("0")]);
                return rir::block(pre, values);
            }
            if i + 1 == args.len() && matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..)) {
                let (p, vals) = self.multi(e, None);
                pre.extend(p);
                fixed.extend(vals.into_iter().map(|v| rir::call("lr::packs::slot", vec![v.code])));
            } else {
                let value = self.expr(e);
                let name = self.fresh("pack");
                pre.push(rir::let_(name.clone(), rir::call("lr::packs::slot", vec![value.code])));
                fixed.push(rir::atom_e(name));
            }
        }
        rir::block(pre, RExpr::Macro("vec".into(), fixed))
    }

    pub(super) fn pack_builtin(&mut self, e: &Expr, b: BuiltinFn, args: &[Expr]) -> Option<(RExpr, Vec<(TyId, bool)>)> {
        let ty = self.ck.info.expr[&e.id].ty;
        match b {
            BuiltinFn::TPack => {
                let values = self.boxed_list(args);
                Some((rir::call("lr::packs::table", vec![values]), vec![(ty, false)]))
            }
            BuiltinFn::SelectFixedCount | BuiltinFn::SelectFixed => {
                let mut pre = Vec::new();
                let index = if b == BuiltinFn::SelectFixed {
                    let index = self.expr_nn(&args[0], "bad argument #1 to 'select' (number expected)");
                    let name = self.fresh("index");
                    pre.push(rir::let_(name.clone(), index));
                    Some(rir::atom_e(name))
                } else { None };
                let values = self.boxed_list(&args[1..]);
                let name = self.fresh("values");
                pre.push(RStmt::Let(name.clone(), Some("Vec<Option<lr::Value>>".into()), values));
                let values = rir::atom_e(name);
                if let Some(index) = index {
                    let first = rir::at(rir::call("lr::va::select", vec![rir::method(values.clone(), "len", vec![]), index]), &self.loc(e.span));
                    let selected = rir::call("lr::va::rest", vec![rir::borrow(values), first]);
                    Some(self.adjust_boxed_results(e, pre, selected))
                } else {
                    Some((rir::block(pre, rir::cast(rir::method(values, "len", vec![]), "f64")), vec![(ty, false)]))
                }
            }
            BuiltinFn::PcallPack => Some(self.pcall_pack_code(e, args)),
            BuiltinFn::TUnpack if args.first().is_some_and(|a| matches!(self.node(self.ck.info.expr[&a.id].ty), TyNode::Table(t) if self.ck.st.tab(t).sparse)) => {
                let mut pre = Vec::new();
                let mut inputs = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let value = if i == 0 { self.expr_nn(a, "bad argument #1 to 'unpack' (table expected, got nil)") } else { self.expr_to(a, true) };
                    let name = self.fresh("unpack");
                    pre.push(rir::let_(name.clone(), value));
                    inputs.push(rir::atom_e(name));
                }
                let table = rir::borrow(inputs[0].clone());
                let first = inputs.get(1).cloned().unwrap_or_else(|| rir::atom_e("None"));
                let last = inputs.get(2).cloned().unwrap_or_else(|| rir::atom_e("None"));
                let call = rir::call("lr::packs::unpack", vec![table, first, last, rir::atom_e(args.len().to_string())]);
                Some((rir::block(pre, rir::at(call, &self.loc(e.span))), vec![]))
            }
            _ => None,
        }
    }

    fn adjust_boxed_results(&mut self, e: &Expr, mut pre: Vec<RStmt>, values: RExpr) -> (RExpr, Vec<(TyId, bool)>) {
        if self.ck.info.pack_calls.contains_key(&e.id) { return (rir::block(pre, values), vec![]); }
        let count = self.ck.info.builtin_outs.get(&e.id).map(|v| v.len()).unwrap_or(0);
        let name = self.fresh("selected");
        pre.push(rir::let_(name.clone(), values));
        let vals: Vec<RExpr> = (0..count).map(|i| {
            let read = va_get(&rir::atom_e(name.clone()), &rir::atom_e("0"), i);
            let value = rir::method(read, "unwrap_or", vec![rir::atom_e("lr::Value::Nil")]);
            if let Some(ty) = self.ck.info.packs.select_elem.get(&e.id).copied() {
                let ty = RType::Named(self.rust_ty(ty));
                let cast = rir::call_generic("lr::dynamic::cast_opt", &ty, vec![rir::borrow(value), rir::atom_e(rust_str_lit("select result"))]);
                rir::at(cast, &self.loc(e.span))
            } else { value }
        }).collect();
        let result = match vals.len() { 1 => vals[0].clone(), _ => RExpr::Tuple(vals) };
        let ty = self.ck.info.expr[&e.id].ty;
        (rir::block(pre, result), vec![(ty, self.ck.info.packs.select_elem.contains_key(&e.id)); count])
    }

    fn pcall_pack_code(&mut self, e: &Expr, args: &[Expr]) -> (RExpr, Vec<(TyId, bool)>) {
        let f = self.expr_nn(&args[0], "attempt to call a nil value");
        let ft = self.func_of(self.ck.info.expr[&args[0].id].ty);
        let function = self.fresh("protected");
        let mut pre = vec![rir::let_(function.clone(), f)];
        let popt: Vec<bool> = ft.params.iter().map(|p| self.is_null(p.null)).collect();
        let (p, argv) = self.args_e(&args[1..], &popt, ft.vararg.is_some());
        pre.extend(p);
        let mut bound = Vec::new();
        for arg in argv {
            let name = self.fresh("pa");
            pre.push(rir::let_(name.clone(), arg));
            bound.push(rir::atom_e(name));
        }
        let call = rir::try_(rir::method(rir::atom_e(function), "call", vec![RExpr::Tuple(bound)]));
        let rets = self.ck.st.rets_known(ft.rets).cloned().unwrap_or_default();
        let tail = self.ck.st.rets_tail(ft.rets);
        let result = self.fresh("result");
        let body_pre = vec![rir::let_(result.clone(), call)];
        let count = rets.len() + usize::from(tail.is_some());
        let component = |index: usize| {
            if count == 1 { rir::atom_e(result.clone()) }
            else { rir::field(rir::atom_e(result.clone()), index.to_string()) }
        };
        let fixed = (0..rets.len()).map(|index| rir::call("lr::packs::slot", vec![component(index)])).collect();
        let fixed = RExpr::Macro("vec".into(), fixed);
        let values = if tail.is_some() {
            let values = rir::call("lr::packs::boxed", vec![rir::borrow(component(rets.len())), rir::atom_e("0")]);
            rir::call("lr::va::with_rest", vec![fixed, rir::borrow(values), rir::atom_e("0")])
        } else { fixed };
        let closure = rir::closure("", rir::block(body_pre, rir::call("Ok", vec![values])));
        let call = rir::call("lr::packs::protected", vec![closure]);
        self.adjust_boxed_results(e, pre, call)
    }
}
