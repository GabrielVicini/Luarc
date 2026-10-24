//! Runtime table lowering through structured rir expressions.

use super::*;
use crate::check_runtime_table::RuntimeCall;

impl<'a> Gen<'a> {
    pub(crate) fn erase_function(&mut self, value: RExpr, ty: TyId) -> RExpr {
        match self.node(ty) {
            TyNode::Func(_) => rir::call("lr::dynamic_fn::function", vec![value]),
            TyNode::Any => value,
            _ => rir::call("lr::dynamic::to_value", vec![value]),
        }
    }

    pub(super) fn runtime_constructor_code(&mut self, expr: &Expr, items: &[TableItem]) -> RExpr {
        let mut pre = Vec::new();
        let mut entries = Vec::new();
        let mut position = 0usize;
        for item in items {
            let (key, value) = match item {
                TableItem::Named(name, value) => {
                    let key = self.str_lit(name.text.as_bytes());
                    (rir::call("lr::dynamic::to_value", vec![key]), value)
                }
                TableItem::Keyed(key, value) => (self.expr_nn(key, "table index is nil"), value),
                TableItem::Pos(value) => {
                    position += 1;
                    (rir::call("lr::Value::Num", vec![rir::cast(rir::atom_e(position.to_string()), "f64")]), value)
                }
            };
            let key_name = self.fresh("key");
            pre.push(rir::let_(key_name.clone(), key));
            let val = self.expr(value);
            let val = self.any_present(val);
            let value_name = self.fresh("value");
            pre.push(rir::let_(value_name.clone(), val.code));
            entries.push(RExpr::Tuple(vec![rir::atom_e(key_name), rir::atom_e(value_name)]));
        }
        let entries = RExpr::Macro("vec".into(), entries);
        let init = if !items.is_empty() && items.len() <= 32 && items.iter().all(|item| matches!(item, TableItem::Named(..))) {
            rir::call("lr::Table::from_record_entries", vec![entries])
        } else {
            let mut args = vec![entries]; args.extend(self.layout_args(expr));
            rir::call("lr::Table::from_entries_with_layout", args)
        };
        rir::block(pre, rir::at(init, &self.loc(expr.span)))
    }

    pub(super) fn runtime_field_code(&mut self, expr: &Expr, obj: &Expr, name: &str) -> RExpr {
        let table = self.expr_nn(obj, "attempt to index a nil value");
        let key = self.str_lit(name.as_bytes());
        let key = rir::call("lr::dynamic::to_value", vec![key]);
        let value = rir::at(rir::method(table, "get", vec![rir::borrow(key)]), &self.loc(expr.span));
        self.runtime_read_value(expr, value)
    }

    pub(super) fn runtime_index_code(&mut self, expr: &Expr, obj: &Expr, key: &Expr) -> RExpr {
        let table = self.expr_nn(obj, "attempt to index a nil value");
        let table_name = self.fresh("table");
        let index = self.expr_nn(key, "table index is nil");
        let ty = self.ck.info.expr[&key.id].ty;
        let index = if self.ck.info.dynamic.boxed.contains(&key.id) || self.is_any_ty(ty) { index } else { rir::call("lr::dynamic::to_value", vec![index]) };
        let read = rir::method(rir::atom_e(table_name.clone()), "get", vec![rir::borrow(index)]);
        let read = rir::at(read, &self.loc(expr.span));
        let read = self.runtime_read_value(expr, read);
        rir::block(vec![rir::let_(table_name, table)], read)
    }

    fn runtime_read_value(&mut self, expr: &Expr, value: RExpr) -> RExpr {
        let ty = self.ck.info.expr[&expr.id].ty;
        if !self.ck.runtime_type(ty) { return value; }
        let target = RType::Named("lr::Table".into());
        rir::at(rir::call_generic("lr::dynamic::cast_opt", &target, vec![rir::borrow(value), rir::atom_e(rust_str_lit("table"))]), &self.loc(expr.span))
    }

    pub(super) fn runtime_call_code(&mut self, expr: &Expr, call: RuntimeCall) -> (RExpr, Vec<(TyId, bool)>) {
        let ExprKind::Call(callee, args) = &expr.kind else { return (rir::atom_e("()"), vec![]) };
        let outputs = self.ck.info.runtime_tables.outputs.get(&expr.id).cloned().unwrap_or_default();
        let out_types = outputs.iter().map(|value| (value.ty, self.ety_opt(*value))).collect();
        if matches!(call, RuntimeCall::Print) {
            let mut pre = Vec::new();
            let mut values = Vec::new();
            let mut tail = None;
            for (position, arg) in args.iter().enumerate() {
                let (prefix, items) = if position + 1 == args.len() && self.is_pack(arg) {
                    let (prefix, fixed, source, start) = self.pack_src(arg);
                    tail = Some((source, start));
                    (prefix, fixed)
                } else if position + 1 == args.len() && matches!(arg.kind, ExprKind::Call(..) | ExprKind::Method(..)) {
                    self.multi(arg, None)
                } else { (Vec::new(), vec![self.expr(arg)]) };
                pre.extend(prefix);
                for value in items {
                    let value = self.box_value(value);
                    let name = self.fresh("print");
                    pre.push(rir::let_(name.clone(), value.code));
                    values.push(rir::atom_e(name));
                }
            }
            let values = RExpr::Macro("vec".into(), values);
            let print = match tail {
                Some((source, start)) => rir::call("lr::dynamic::print_tail", vec![values, rir::borrow(source), start]),
                None => rir::call("lr::dynamic::print", vec![values]),
            };
            let print = rir::at(print, &self.loc(expr.span));
            return (rir::block(pre, print), out_types);
        }
        let mut pre = Vec::new();
        let mut values = Vec::new();
        let mut callable = None;
        if matches!(call, RuntimeCall::Invoke) {
            let value = self.expr_nn(callee, "attempt to call a nil value");
            let ty = self.ck.info.expr[&callee.id].ty;
            let value = self.erase_function(value, ty);
            let name = self.fresh("callable");
            pre.push(rir::let_(name.clone(), value));
            callable = Some(rir::atom_e(name));
        }
        for arg in args {
            let value = self.expr(arg);
            let name = self.fresh("argument");
            pre.push(rir::let_(name.clone(), value.code));
            values.push((rir::atom_e(name), value.opt));
        }
        let get = |index: usize| values.get(index).map_or_else(|| rir::atom_e("lr::Value::Nil"), |v| v.0.clone());
        let code = match call {
            RuntimeCall::Attach => {
                let meta = if args.get(1).is_some_and(|arg| matches!(arg.kind, ExprKind::Nil)) { rir::atom_e("None") } else { rir::some(get(1)) };
                rir::at(rir::method(get(0), "set_metatable", vec![meta]), &self.loc(expr.span))
            }
            RuntimeCall::RawGet(Some(name)) => {
                let ty = self.ck.info.expr[&args[0].id].ty;
                let TyNode::Table(tab) = self.node(ty) else { return (rir::atom_e("()"), vec![]) };
                if self.ck.st.tab(tab).fields.contains_key(&name) {
                    let raw = Self::record_read(get(0), &name);
                    rir::call("lr::dynamic::to_value", vec![raw])
                } else { rir::atom_e("lr::Value::Nil") }
            }
            RuntimeCall::RawGet(None) => rir::method(get(0), "raw_get", vec![rir::borrow(get(1))]),
            RuntimeCall::RawSet => {
                pre.push(RStmt::Semi(rir::at(rir::method(get(0), "raw_set", vec![get(1), get(2)]), &self.loc(expr.span))));
                get(0)
            }
            RuntimeCall::RawEqual => rir::call("lr::show::eq", vec![rir::borrow(get(0)), rir::borrow(get(1))]),
            RuntimeCall::RawLen => {
                let ty = self.ck.info.expr[&args[0].id].ty;
                match self.node(ty) {
                    TyNode::Str => rir::method(get(0), "len", vec![]),
                    TyNode::Table(tab) if self.ck.st.tab(tab).runtime => rir::at(rir::method(get(0), "raw_len", vec![]), &self.loc(expr.span)),
                    TyNode::Table(tab) if self.ck.st.tab(tab).kind == TKind::Record => rir::atom_e("0.0"),
                    _ => rir::method(get(0), "len", vec![]),
                }
            }
            RuntimeCall::GetMetatable => {
                let ty = self.ck.info.expr[&args[0].id].ty;
                if let TyNode::Table(tab) = self.node(ty) {
                    let table = self.ck.st.tab(tab);
                    if table.runtime { rir::method(get(0), "get_metatable", vec![]) }
                    else if table.parent.is_some() || table.metatable.is_some() {
                        rir::call("lr::dynamic::to_value", vec![rir::method(get(0), "parent", vec![])])
                    } else { rir::atom_e("lr::Value::Nil") }
                } else { rir::atom_e("lr::Value::Nil") }
            }
            RuntimeCall::ToString => {
                rir::at(rir::call("lr::dynamic::tostring", vec![rir::borrow(get(0))]), &self.loc(expr.span))
            }
            RuntimeCall::Clone => {
                let table = self.coerce(Val { code: get(0), opt: values[0].1 }, false, expr.span, "bad argument #1 to 'clone' (table expected, got nil)");
                rir::at(rir::method(table, "checked_clone", vec![]), &self.loc(expr.span))
            }
            RuntimeCall::Print => unreachable!("handled before argument lowering"),
            RuntimeCall::Create => {
                let fill = if args.len() > 1 { get(1) } else { rir::atom_e("lr::Value::Nil") };
                let size = self.coerce(Val { code: get(0), opt: values[0].1 }, false, expr.span, "bad argument #1 to 'create' (number expected, got nil)");
                rir::at(rir::call("lr::Table::create", vec![size, fill]), &self.loc(expr.span))
            }
            RuntimeCall::Invoke => {
                let args = RExpr::Macro("vec".into(), values.into_iter().map(|v| v.0).collect());
                let code = rir::at(rir::call("lr::dynamic::call", vec![rir::borrow(callable.unwrap_or_else(|| rir::atom_e("lr::Value::Nil"))), args]), &self.loc(expr.span));
                if self.ck.info.pack_calls.contains_key(&expr.id) {
                    rir::call("lr::dynamic::result_pack", vec![code])
                } else if outputs.is_empty() {
                    pre.push(RStmt::Semi(code)); rir::atom_e("()")
                } else {
                    let results = self.fresh("results");
                    pre.push(rir::let_(results.clone(), code));
                    let items: Vec<_> = (0..outputs.len()).map(|index| {
                        let item = rir::method(rir::atom_e(results.clone()), "get", vec![rir::atom_e(index.to_string())]);
                        let item = rir::method(item, "cloned", vec![]);
                        rir::method(item, "unwrap_or", vec![rir::atom_e("lr::Value::Nil")])
                    }).collect();
                    if items.len() == 1 { items[0].clone() } else { RExpr::Tuple(items) }
                }
            }
        };
        (rir::block(pre, code), out_types)
    }
}
