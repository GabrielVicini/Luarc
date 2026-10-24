//! Structured lowering of generalized table and function iteration.
use super::*;

impl<'a> Gen<'a> {
    pub(super) fn uses_next_table(&self, tab: TabId) -> bool {
        let root = self.ck.st.tab_root(tab);
        self.ck.info.next_tables.iter().any(|ty| matches!(self.node(*ty), TyNode::Table(table) if self.ck.st.tab_root(table) == root))
    }
    pub(super) fn table_layout(&self, expr: &Expr) -> (usize, usize) {
        self.ck.info.table_layouts.get(&expr.id).copied().unwrap_or_default()
    }
    pub(super) fn layout_args(&self, expr: &Expr) -> Vec<RExpr> {
        let (array, hash) = self.table_layout(expr);
        vec![rir::atom_e(array.to_string()), rir::atom_e(hash.to_string())]
    }
    pub(super) fn inferred_table_constructor(&mut self, ty: TyId, init: RExpr) -> RExpr {
        let name = self.fresh("table");
        let ty = self.rust_ty(ty);
        rir::block(vec![RStmt::Let(name.clone(), Some(ty), init)], rir::atom_e(name))
    }
    pub(super) fn dynamic_map(&self, tab: TabId) -> bool {
        self.ck.st.tab(tab).key.is_some_and(|key| self.is_any_ty(key.ty))
    }
    pub(super) fn raw_map_key(&mut self, key: &Expr) -> RExpr {
        let value = self.expr(key);
        self.box_value(value).code
    }
    pub(super) fn dynamic_map_read(&self, value: RExpr, map: &str) -> RExpr {
        let key = rir::method(rir::call("lr::dynamic::Key::new", vec![value]), "ok", vec![]);
        rir::method(key, "and_then", vec![rir::closure("k", rir::method(rir::atom_e(map), "get", vec![rir::borrow(rir::atom_e("k"))]))])
    }
    pub(super) fn map_key_for(&mut self, key: &Expr, tab: TabId) -> RExpr {
        if !self.dynamic_map(tab) { return self.map_key(key); }
        let value = self.raw_map_key(key);
        rir::at(rir::call("lr::dynamic::Key::new", vec![value]), &self.loc(key.span))
    }
    pub(super) fn map_key_read_for(&mut self, key: &Expr, map: &str, tab: TabId) -> RExpr {
        if !self.dynamic_map(tab) { return self.map_key_read(key, map); }
        let value = self.raw_map_key(key);
        self.dynamic_map_read(value, map)
    }
    pub(super) fn named_map_key(&mut self, obj: &Expr, name: &str) -> RExpr {
        let value = self.str_lit(name.as_bytes());
        let tab = match self.node(self.ck.info.expr[&obj.id].ty) { TyNode::Table(tab) => tab, _ => unreachable!() };
        if self.dynamic_map(tab) {
            let value = rir::call("lr::dynamic::to_value", vec![value]);
            rir::at(rir::call("lr::dynamic::Key::new", vec![value]), &self.loc(obj.span))
        } else { value }
    }
    pub(super) fn runtime_sort_code(&mut self, e: &Expr, args: &[Expr]) -> RExpr {
        let table = self.expr_nn(&args[0], "bad argument #1 to 'sort' (table expected, got nil)");
        let name = self.fresh("sort_table");
        let pre = vec![rir::let_(name.clone(), table)];
        let compare = args.get(1).map(|f| {
            let v = self.expr(f);
            if matches!(self.node(self.ck.info.expr[&f.id].ty), TyNode::Func(_)) && v.opt {
                return rir::method(v.code, "map", vec![rir::atom_e("lr::dynamic_fn::function")]);
            }
            let value = if matches!(self.node(self.ck.info.expr[&f.id].ty), TyNode::Func(_)) {
                let value = self.coerce(v, false, f.span, "bad argument #2 to 'sort'");
                rir::call("lr::dynamic_fn::function", vec![value])
            } else { self.any_present(v).code };
            rir::some(value)
        }).unwrap_or_else(|| rir::atom_e("None"));
        let call = rir::call("lr::traversal::sort_table", vec![rir::borrow(rir::atom_e(name)), compare]);
        rir::block(pre, rir::at(call, &self.loc(e.span)))
    }

    pub(super) fn iteration_builtin(&mut self, e: &Expr, b: BuiltinFn, args: &[Expr]) -> (RExpr, Vec<(TyId, bool)>) {
        let t = self.expr_nn(&args[0], "table expected, got nil");
        let tab = match self.node(self.ck.info.expr[&args[0].id].ty) { TyNode::Table(t) => t, _ => unreachable!() };
        let runtime = self.ck.st.tab(tab).runtime;
        if b == BuiltinFn::TClear {
            let clear = rir::method(t, "clear", vec![]);
            return (if runtime { rir::at(clear, &self.loc(e.span)) } else { clear }, vec![]);
        }
        let tv = self.fresh("next");
        let pre = vec![rir::let_(tv.clone(), t)];
        if runtime {
            let key = args.get(1).map(|k| {
                let value = self.expr(k);
                if self.is_any_ty(self.ck.info.expr[&k.id].ty) { self.any_present(value).code } else { self.box_value(value).code }
            }).unwrap_or_else(|| rir::atom_e("lr::Value::Nil"));
            let call = rir::at(rir::method(rir::atom_e(tv), "next_entry", vec![key]), &self.loc(e.span));
            let out = self.ck.info.builtin_outs[&e.id].iter().map(|o| (o.ty, false)).collect();
            return (rir::block(pre, call), out);
        }
                let dynamic = self.dynamic_map(tab);
        let key = args.get(1).map(|k| if dynamic {
            let value = self.expr(k);
            self.box_value(value).code
        } else { self.expr_to(k, true) }).unwrap_or_else(|| if dynamic { rir::atom_e("lr::Value::Nil") } else { rir::atom_e("None") });
        let map = self.ck.st.tab(tab).kind == TKind::Map;
        let out = self.ck.info.builtin_outs[&e.id].clone();
        let numeric = map && matches!(self.node(out[0].ty), TyNode::Num);
        let path = if dynamic { "lr::traversal::next_dynamic_map" } else if numeric { "lr::traversal::next_number_map" } else if map { "lr::traversal::next_map" } else { "lr::traversal::next_array" };
        let result = rir::at(rir::call(path, vec![rir::borrow(rir::atom_e(tv)), key]), &self.loc(e.span));
        (rir::block(pre, result), out.iter().map(|o| (o.ty, true)).collect())
    }

    pub(super) fn general_for_code(&mut self, s: &Stat, names: &[Name], exprs: &[Expr], body: &Block) -> RStmt {
        let info = self.ck.info.iteration[&s.id].clone();
        let kind = self.ck.info.fors[&s.id];
        let exprs = if info.mode != crate::check_iteration::IterationMode::General {
            match &exprs[0].kind { ExprKind::Call(_, args) => args.as_slice(), _ => exprs }
        } else { exprs };
        let (mut pre, vals) = self.values(exprs, info.inputs.len(), s.span);
        let mut inputs = Vec::new();
        for (i, v) in vals.into_iter().enumerate() {
            let name = self.fresh("iter");
            let value = self.coerce(v, i > 0, s.span, "cannot iterate over nil");
            pre.push(rir::let_(name.clone(), value));
            inputs.push(rir::atom_e(name));
        }
        self.loop_enter(body);
        let ctx = self.loops.last().expect("entered loop");
        let (loop_id, labeled, break_label) = (ctx.id, ctx.labeled, ctx.break_label);
        let mut inner = Vec::new();
        let mut values = Vec::new();
        match kind {
            ForKind::Runtime => {
                let iter = self.fresh("runtime_iter");
                let mode = info.mode;
                let init = match mode {
                    crate::check_iteration::IterationMode::General => rir::at(rir::call("lr::traversal::GeneralIterator::new", vec![inputs[0].clone()]), &self.loc(s.span)),
                    crate::check_iteration::IterationMode::Pairs => rir::call("lr::traversal::GeneralIterator::pairs", vec![inputs[0].clone()]),
                    crate::check_iteration::IterationMode::Ipairs => rir::call("lr::traversal::GeneralIterator::ipairs", vec![inputs[0].clone()]),
                };
                pre.push(RStmt::LetMut(iter.clone(), None, init));
                let result = self.fresh("results");
                let call = rir::at(rir::method(rir::atom_e(iter), "next_values", vec![]), &self.loc(s.span));
                inner.push(rir::let_(result.clone(), RExpr::Match(Box::new(call), vec![("Some(v)".into(), rir::atom_e("v")), ("None".into(), rir::block(vec![RStmt::Break(None)], rir::atom_e("")))])));
                for i in 0..names.len() {
                    let get = rir::method(rir::atom_e(result.clone()), "get", vec![rir::atom_e(i.to_string())]);
                    let get = rir::method(rir::method(get, "cloned", vec![]), "unwrap_or", vec![rir::atom_e("lr::Value::Nil")]);
                    let target = self.ck.info.sym_slot[&self.res.decl(names[i].id)].ty;
                    let node = self.node(target);
                    let proven = matches!(node, TyNode::Num | TyNode::Int | TyNode::Str | TyNode::Bool) || matches!(node, TyNode::Table(tab) if self.ck.st.tab(tab).runtime);
                    if proven {
                        let ty = RType::Named(self.rust_ty(target));
                        let label = rust_str_lit(&self.ck.show(target));
                        let cast = rir::call_generic("lr::dynamic::cast_opt", &ty, vec![rir::borrow(get), rir::atom_e(label)]);
                        values.push(Val { code: rir::at(cast, &self.loc(s.span)), opt: true });
                    } else {
                        let get = if i == 0 && mode == crate::check_iteration::IterationMode::Ipairs { rir::at(rir::method(get, "as_num", vec![]), &self.loc(s.span)) } else { get };
                        values.push(Val { code: get, opt: false });
                    }
                }
            }
            ForKind::PairsArray | ForKind::Ipairs => {
                let any = matches!(self.node(info.inputs[0].ty), TyNode::Table(tab) if self.ck.st.tab(tab).elem.is_some_and(|slot| self.is_any_ty(slot.ty)));
                if any && kind == ForKind::PairsArray {
                    let control = self.fresh("index");
                    pre.push(RStmt::LetMut(control.clone(), Some("Option<f64>".into()), rir::atom_e("None")));
                    let result = self.fresh("entry");
                    let call = rir::at(rir::call("lr::traversal::next_array", vec![rir::borrow(inputs[0].clone()), rir::atom_e(control.clone())]), &self.loc(s.span));
                    inner.push(rir::let_(result.clone(), call));
                    let key = self.fresh("key");
                    let first = rir::field(rir::atom_e(result.clone()), "0");
                    inner.push(rir::let_(key.clone(), RExpr::Match(Box::new(first), vec![("Some(k)".into(), rir::atom_e("k")), ("None".into(), rir::block(vec![RStmt::Break(None)], rir::atom_e("")))])));
                    inner.push(RStmt::Assign(rir::atom_e(control), rir::some(rir::atom_e(key.clone()))));
                    values.push(Val { code: rir::atom_e(key), opt: false });
                    values.push(Val { code: rir::field(rir::atom_e(result), "1"), opt: true });
                } else {
                let n = self.fresh("index");
                pre.push(RStmt::LetMut(n.clone(), Some("usize".into()), rir::atom_e("0")));
                let value = self.fresh("value");
                let read = rir::method(inputs[0].clone(), "get_at", vec![rir::atom_e(n.clone())]);
                let end = rir::block(vec![RStmt::Break(None)], rir::atom_e(""));
                inner.push(rir::let_(value.clone(), RExpr::Match(Box::new(read), vec![("Some(v)".into(), rir::atom_e("v")), ("None".into(), end)])));
                inner.push(RStmt::Assign(rir::atom_e(n.clone()), rir::bin(ROp::Add, rir::atom_e(n.clone()), rir::atom_e("1"))));
                values.push(Val { code: rir::cast(rir::atom_e(n), "f64"), opt: false });
                values.push(Val { code: rir::atom_e(value), opt: false });
                }
            }
            ForKind::PairsMap => {
                let keys = self.fresh("keys");
                pre.push(RStmt::LetMut(keys.clone(), None, rir::method(rir::method(inputs[0].clone(), "keys", vec![]), "into_iter", vec![])));
                let key = self.fresh("key");
                let read = rir::method(rir::atom_e(keys), "next", vec![]);
                inner.push(rir::let_(key.clone(), RExpr::Match(Box::new(read), vec![("Some(k)".into(), rir::atom_e("k")), ("None".into(), rir::block(vec![RStmt::Break(None)], rir::atom_e("")))])));
                let value = self.fresh("value");
                let read = rir::method(inputs[0].clone(), "get", vec![rir::borrow(rir::atom_e(key.clone()))]);
                inner.push(rir::let_(value.clone(), RExpr::Match(Box::new(read), vec![("Some(v)".into(), rir::atom_e("v")), ("None".into(), rir::block(vec![RStmt::Continue(None)], rir::atom_e("")))])));
                let kt = self.ck.info.sym_slot[&self.res.decl(names[0].id)].ty;
                let key = match self.node(kt) { TyNode::Num => rir::method(rir::atom_e(key), "get", vec![]), TyNode::Any => rir::method(rir::atom_e(key), "value", vec![]), _ => rir::atom_e(key) };
                values.push(Val { code: key, opt: false });
                values.push(Val { code: rir::atom_e(value), opt: false });
            }
            ForKind::Function => {
                let ft = self.func_of(info.inputs[0].ty);
                let control = self.fresh("control");
                let initial = inputs.get(2).cloned().unwrap_or_else(|| rir::atom_e("None"));
                if ft.params.len() == 2 {
                    pre.push(RStmt::LetMut(control.clone(), None, initial));
                }
                let mut args = Vec::new();
                for (i, p) in ft.params.iter().enumerate() {
                    let code = if i == 0 { inputs.get(1).cloned().unwrap_or_else(|| rir::atom_e("None")) } else { rir::atom_e(control.clone()) };
                    let value = Val { code: rir::method(code, "clone", vec![]), opt: true };
                    if self.is_any_ty(p.ty) {
                        args.push(self.any_present(value).code);
                    } else {
                        args.push(self.coerce(value, self.ck.st.is_null(p.null), s.span, "iterator argument is nil"));
                    }
                }
                let call = rir::at(rir::method(inputs[0].clone(), "call", vec![RExpr::Tuple(args)]), &self.loc(s.span));
                let result = self.fresh("result");
                inner.push(rir::let_(result.clone(), call));
                for (i, r) in info.outputs.iter().enumerate() {
                    let code = if info.outputs.len() == 1 { rir::atom_e(result.clone()) } else { rir::field(rir::atom_e(result.clone()), i.to_string()) };
                    values.push(Val { code, opt: self.ck.st.is_null(r.null) });
                }
                let first = self.coerce(values[0].clone(), true, s.span, "iterator control is nil");
                let first = if self.is_any_ty(info.outputs[0].ty) {
                    RExpr::Match(Box::new(first), vec![
                        ("Some(lr::Value::Nil) | None".into(), rir::atom_e("None")),
                        ("Some(v)".into(), rir::some(rir::atom_e("v"))),
                    ])
                } else { first };
                let first = rir::method(first, "clone", vec![]);
                if ft.params.len() == 2 {
                    inner.push(RStmt::Assign(rir::atom_e(control.clone()), first));
                } else {
                    inner.push(rir::let_(control.clone(), first));
                }
                inner.push(RStmt::If(vec![(rir::method(rir::atom_e(control.clone()), "is_none", vec![]), vec![RStmt::Break(None)])], None));
                values[0] = Val { code: rir::method(rir::atom_e(control), "clone", vec![]), opt: true };
            }
            _ => unreachable!("only generalized loops use this path"),
        }
        for (i, name) in names.iter().enumerate() {
            let sym = self.res.decl(name.id);
            let value = values.get(i).cloned().unwrap_or(Val { code: rir::atom_e("None"), opt: true });
            let value = self.coerce(value, self.sym_opt(sym), name.span, "iterator result is nil");
            self.declare_local(sym, value, &mut inner);
        }
        let body = self.block(body);
        if labeled { inner.push(RStmt::Labeled(format!("'c{}", loop_id), body)); } else { inner.extend(body); }
        pre.push(RStmt::Loop { label: break_label.then(|| format!("'l{}", loop_id)), cond: None, body: inner });
        self.loops.pop();
        RStmt::Block(pre)
    }
}




