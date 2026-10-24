//! Generalized iteration and table traversal, checked without changing the
//! existing pairs/ipairs lowering.
use crate::ast::*;
use crate::check::*;
use crate::diag::Span;
use crate::types::*;

#[derive(Clone, Debug)]
pub struct Iteration {
    pub inputs: Vec<ETy>,
    pub outputs: Vec<Slot>,
    pub mode: IterationMode,
    pub source_count: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IterationMode { General, Pairs, Ipairs }

impl<'a> Checker<'a> {
    pub(crate) fn finish_any_array_loops(&mut self) {
        for (node, table) in self.info.array_loop_tables.clone() {
            if self.info.fors.get(&node) != Some(&ForKind::PairsArray) { continue; }
            let TyNode::Table(tab) = self.st.node(table.ty) else { continue };
            if self.st.tab(*tab).elem.is_some_and(|slot| self.is_any(slot.ty)) {
                self.info.iteration.entry(node).or_insert(Iteration { inputs: vec![table], outputs: vec![], mode: IterationMode::Pairs, source_count: 1 });
            }
        }
    }
    pub(crate) fn runtime_create_clone(&mut self, expr: &Expr, args: &[Expr], create: bool, want: Option<usize>) -> Vec<ETy> {
        use crate::check_runtime_table::RuntimeCall;
        let (values, spans) = self.args_values(args);
        let name = if create { "table.create" } else { "table.clone" };
        if !self.arity(expr.span, name, &values, 1, if create { 2 } else { 1 }) { return vec![self.fresh_result()]; }
        if values.len() != args.len() || args.last().is_some_and(|arg| self.info.pack_calls.contains_key(&arg.id)) {
            self.error(expr.span, "runtime table.create/clone require explicit single-value arguments (parenthesize calls to select one value)");
        }
        if create {
            self.expect(values[0], TyNode::Num, spans[0], "bad argument #1 to 'create' (number expected)");
            let value = self.runtime_value(expr.span);
            if let TyNode::Table(tab) = self.st.node(value.ty).clone() {
                self.st.tab_mut(tab).ctors.push(vec![]);
                if let Some(fill) = values.get(1).filter(|fill| self.runtime_type(fill.ty)) {
                    self.st.tab_mut(tab).elem = Some(Slot { ty: fill.ty, null: fill.null });
                }
            }
            if let (Some(arg), Some(fill)) = (args.get(1), values.get(1)) { self.runtime_box(arg, *fill); }
            self.runtime_out(expr, RuntimeCall::Create, vec![value], want)
        } else {
            self.need(values[0], expr.span, "bad argument #1 to 'clone' (table expected, got nil)");
            if !self.runtime_type(values[0].ty) { self.error(args[0].span, "runtime table.clone requires a runtime-table producer"); }
            let output = self.val(values[0].ty);
            self.runtime_out(expr, RuntimeCall::Clone, vec![output], want)
        }
    }
    pub(crate) fn constructor_map_key(&mut self, tab: TabId, value: ETy, expected_any: bool, span: Span) -> Slot {
        let slot = self.key_slot(tab);
        let class = |node: &TyNode| match node {
            TyNode::Num | TyNode::NumVar | TyNode::Int => 1,
            TyNode::Str => 2,
            TyNode::Bool => 3,
            TyNode::Var | TyNode::Nil => 0,
            _ => 4,
        };
        let (a, b) = (class(self.st.node(slot.ty)), class(self.st.node(value.ty)));
        if expected_any || self.is_any(value.ty) || (a != 0 && b != 0 && a != b) {
            let any = self.prim(TyNode::Any);
            let slot = Slot { ty: any, ..slot };
            self.st.tab_mut(tab).key = Some(slot);
            self.boxable(value.ty, span);
            slot
        } else { slot }
    }
    pub(crate) fn runtime_sort_sig(&mut self, a: &[ETy], span: Span) -> Vec<ETy> {
        if !self.arity(span, "table.sort", a, 1, 2) { return vec![]; }
        self.need(a[0], span, "bad argument #1 to 'sort' (table expected, got nil)");
        if let Some(compare) = a.get(1) {
            match self.st.node(compare.ty).clone() {
                TyNode::Any => {}
                TyNode::Func(f) => {
                    if f.vararg.is_some() || self.st.rets_tail(f.rets).is_some() || f.params.len() > 8 {
                        self.error(span, "runtime table sort comparators require a fixed signature with at most eight parameters");
                    }
                    for p in &f.params {
                        if matches!(self.st.node(p.ty), TyNode::Var) {
                            let any = self.prim(TyNode::Any);
                            self.unify(p.ty, any, span);
                        } else if !(matches!(self.st.node(p.ty), TyNode::Any) || matches!(self.st.node(p.ty), TyNode::Table(tab) if self.st.tab(*tab).runtime)) {
                            self.error(span, "runtime table sort comparator parameters must be any or runtime tables");
                        }
                    }
                }
                _ => self.error(span, "runtime table sort comparator must be a function or any"),
            }
        }
        vec![]
    }

    pub(crate) fn general_for(&mut self, s: &Stat, names: &[Name], exprs: &[Expr], body: &Block) {
        let inputs = self.exprs_all(exprs, None);
        let Some(&t) = inputs.first() else { return };
        self.info.packs.restricted.push((t.ty, s.span, "generalized iteration over a nil-preserving array is unsupported"));
        self.need(t, s.span, "cannot iterate over nil");
        self.info.iteration.insert(s.id, Iteration { inputs, outputs: vec![], mode: IterationMode::General, source_count: exprs.len() });
        self.kill_assigned(body);
        self.push_frame();
        let native = matches!(self.st.node(t.ty), TyNode::Native(_));
        let vars = names.iter().enumerate().map(|(i, n)| {
            let slot = self.declare(n, None);
            // Iterator results after the control slot can be absent. Like table
            // reads, retain nil for observation and check it when a value is used.
            if i > 0 && !native { self.late_init.insert(self.res.decl(n.id)); }
            slot
        }).collect();
        self.try_or_defer(Op::NativeFor { node: s.id, t, vars, span: s.span });
        self.block(body);
        self.pop_frame();
    }

    pub(crate) fn runtime_pairs(&mut self, node: NodeId, table: ETy, k: Slot, v: Slot, mode: IterationMode, span: Span) {
        let key = self.prim(if mode == IterationMode::Ipairs { TyNode::Num } else { TyNode::Any });
        let any = self.prim(TyNode::Any);
        self.unify(k.ty, key, span);
        let element = match self.st.node(table.ty).clone() {
            TyNode::Table(tab) => self.runtime_iteration_element(tab).unwrap_or(any),
            _ => any,
        };
        self.unify(v.ty, element, span);
        self.info.iteration.insert(node, Iteration { inputs: vec![table], outputs: vec![], mode, source_count: 1 });
        self.info.fors.insert(node, ForKind::Runtime);
    }

    fn runtime_iteration_element(&self, tab: TabId) -> Option<TyId> {
        if self.runtime_metatable(tab).is_some() { return None; }
        let table = self.st.tab(tab);
        table.elem.or(table.val).and_then(|slot| match self.st.node(slot.ty) {
            TyNode::Table(child) if self.st.tab(*child).runtime => Some(slot.ty),
            _ => None,
        })
    }

    pub(crate) fn attempt_general_for(&mut self, node: NodeId, t: ETy, vars: &[Slot], span: Span) -> bool {
        match self.st.node(t.ty).clone() {
            TyNode::Table(tab) => {
                if self.st.tab(tab).sparse {
                    self.error(span, "generalized iteration over a nil-preserving array is unsupported");
                    return true;
                }
                if self.st.tab(tab).runtime {
                    let any = self.prim(TyNode::Any);
                    let element = self.runtime_iteration_element(tab).unwrap_or(any);
                    let results = self.runtime_iterator_results(tab);
                    if results.is_none() && !self.defaults_round { return false; }
                    for (i, v) in vars.iter().enumerate() {
                        let fallback = if i == 1 { element } else { any };
                        let ty = results.as_ref().and_then(|results| results.get(i)).map(|result| result.ty).filter(|ty| {
                            matches!(self.st.node(*ty), TyNode::Num | TyNode::NumVar | TyNode::Int | TyNode::Str | TyNode::Bool | TyNode::Any) || matches!(self.st.node(*ty), TyNode::Table(tab) if self.st.tab(*tab).runtime)
                        }).unwrap_or(fallback);
                        self.unify(v.ty, ty, span);
                    }
                    self.info.fors.insert(node, ForKind::Runtime);
                    return true;
                }
                if vars.len() > 2 {
                    self.error(span, "table iteration binds at most two variables");
                    return true;
                }
                let v = vars.get(1).copied().unwrap_or_else(|| { let t = self.st.var(); self.st.slot(t) });
                self.attempt(&Op::Pairs { node, t, k: vars[0], v, span })
            }
            TyNode::Func(f) => {
                if f.vararg.is_some() {
                    self.error(span, "variadic iterator functions are unsupported");
                    return true;
                }
                let Some(outputs) = self.st.rets_known(f.rets).cloned() else { return false };
                if outputs.is_empty() {
                    self.error(span, "an iterator function must return a control value");
                    return true;
                }
                if self.st.rets_tail(f.rets).is_some() {
                    self.error(span, "iterator functions with a result pack are unsupported");
                    return true;
                }
                let inputs = self.info.iteration[&node].inputs.clone();
                if f.params.len() > 2 {
                    self.error(span, "an iterator function takes at most state and control parameters");
                    return true;
                }
                for (i, p) in f.params.iter().enumerate() {
                    let input = inputs.get(i + 1).copied().unwrap_or_else(|| self.nil());
                    self.flow(input, *p, span);
                    if i == 1 {
                        let output = self.of_slot(outputs[0]);
                        self.flow(output, *p, span);
                    }
                }
                for (i, &v) in vars.iter().enumerate() {
                    if let Some(r) = outputs.get(i) {
                        self.unify(v.ty, r.ty, span);
                        // Luau stops on a nil control value. Later results retain
                        // nil in soft storage and are checked when a value is used.
                    } else {
                        let nil = self.prim(TyNode::Nil);
                        self.unify(v.ty, nil, span);
                        self.st.edge(self.st.null_true, v.null, span);
                    }
                }
                if let Some(info) = self.info.iteration.get_mut(&node) { info.outputs = outputs; }
                self.info.fors.insert(node, ForKind::Function);
                true
            }
            _ => false,
        }
    }

    pub(crate) fn clear_sig(&mut self, a: &[ETy], span: Span) -> Vec<ETy> {
        if self.arity(span, "table.clear", a, 1, 1) {
            self.info.packs.restricted.push((a[0].ty, span, "table.clear on a nil-preserving array is unsupported"));
            let (ty, _) = self.new_table_var(span);
            self.unify(a[0].ty, ty, span);
            self.need(a[0], span, "bad argument #1 to 'clear' (table expected, got nil)");
            self.try_or_defer(Op::Clear { table: a[0], span });
        }
        vec![]
    }

    pub(crate) fn attempt_clear(&mut self, table: ETy, span: Span) -> bool {
        match self.st.node(table.ty).clone() {
            TyNode::Var => false,
            TyNode::Table(tab) if self.st.tab(tab).sparse => { self.error(span, "table.clear on a nil-preserving array is unsupported"); true }
            TyNode::Table(tab) if self.st.tab(tab).runtime => true,
            TyNode::Table(tab) => match self.st.tab(tab).kind {
                TKind::Unknown if !self.defaults_round => false,
                TKind::Record => { self.error(span, "table.clear() requires an array, map or runtime table"); true }
                _ => true,
            },
            _ => true, // clear_sig already diagnoses non-table arguments.
        }
    }

    pub(crate) fn next_call(&mut self, e: &Expr, args: &[Expr], _want: Option<usize>) -> Vec<ETy> {
        let (a, _) = self.args_values(args);
        if !self.arity(e.span, "next", &a, 1, 2) { return vec![self.fresh_result()] }
        if a.len() != args.len() || args.last().is_some_and(|arg| self.info.pack_calls.contains_key(&arg.id)) {
            self.error(e.span, "next requires explicit single-value arguments (parenthesize calls to select one value)");
        }
        if let (Some(table), Some(key)) = (args.first(), args.get(1)) { self.info.next_key_checks.push((table.clone(), key.clone())); }
        self.need(a[0], e.span, "bad argument #1 to 'next' (table expected, got nil)");
        self.info.packs.restricted.push((a[0].ty, e.span, "next on a nil-preserving array is unsupported"));
        let out: Vec<_> = (0..2).map(|_| { let ty = self.st.var(); ETy { ty, null: self.st.null_true, soft: Soft::No } }).collect();
        self.try_or_defer(Op::Next { table: a[0], key: a.get(1).copied(), results: out.clone(), span: e.span });
        self.info.builtin_outs.insert(e.id, out.clone());
        self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::Next));
        out
    }

    pub(crate) fn attempt_next(&mut self, table: ETy, key: Option<ETy>, results: &[ETy], span: Span) -> bool {
        if !self.info.next_tables.contains(&table.ty) { self.info.next_tables.push(table.ty); }
        let out = match self.st.node(table.ty).clone() {
            TyNode::Table(tab) if self.st.tab(tab).sparse => { self.error(span, "next on a nil-preserving array is unsupported"); return true; }
            TyNode::Table(tab) if self.st.tab(tab).runtime => {
                let any = self.prim(TyNode::Any);
                vec![any, any]
            }
            TyNode::Table(tab) => match self.st.tab(tab).kind {
                TKind::Array => { let n = self.num(); let v = self.elem_slot(tab); vec![n.ty, v.ty] }
                TKind::Map => { let k = self.key_slot(tab); let v = self.val_slot(tab); vec![k.ty, v.ty] }
                TKind::Unknown if !self.defaults_round => return false,
                _ => { self.error(span, "next() requires an array or map with known element types"); return true; }
            },
            TyNode::Var => return false,
            _ => { self.error(span, "next() expects an array or map"); return true; }
        };
        if let Some(key) = key {
            if !matches!(self.st.node(out[0]), TyNode::Any) && !matches!(self.st.node(key.ty), TyNode::Nil) { self.unify(key.ty, out[0], span); }
        }
        for (r, ty) in results.iter().zip(out) { self.unify(r.ty, ty, span); }
        true
    }
}
