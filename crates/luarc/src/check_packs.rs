//! Nil-preserving value lists and table.pack.

use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::check::*;
use crate::types::*;
use crate::diag::Span;

#[derive(Default)]
pub struct PackInfo {
    pub count_reads: HashSet<NodeId>,
    pub select_elem: HashMap<NodeId, TyId>,
    pub restricted: Vec<(TyId, Span, &'static str)>,
    pub unpack_bounds: Vec<(TyId, Option<ETy>, Span)>,
    pub boxed: Vec<(TyId, Span)>,
}

impl<'a> Checker<'a> {
    pub(crate) fn validate_sparse_uses(&mut self) {
        for (ty, span) in self.info.packs.boxed.clone() {
            self.boxable(ty, span);
        }
        for (ty, span, message) in std::mem::take(&mut self.info.packs.restricted) {
            if matches!(self.st.node(ty), TyNode::Table(t) if self.st.tab(*t).sparse) {
                self.error(span, message);
            }
        }
        for (ty, bound, span) in std::mem::take(&mut self.info.packs.unpack_bounds) {
            if matches!(self.st.node(ty), TyNode::Table(t) if self.st.tab(*t).sparse)
                && bound.is_none_or(|v| self.st.is_null(v.null) || self.soft(v.soft))
            {
                self.error(span, "table.unpack on a nil-preserving array requires an explicit non-nil end index (its '#' boundary is not supported)");
            }
        }
    }

    pub(crate) fn pack_boxable(&mut self, ty: TyId, span: Span) {
        self.boxable(ty, span);
        self.info.packs.boxed.push((ty, span));
    }

    /// Every list item is one value except an unparenthesized final call/pack.
    pub(crate) fn pack_items(&mut self, args: &[Expr]) -> (Vec<ETy>, Option<ETy>) {
        let old = std::mem::replace(&mut self.exact_pcall, true);
        let result = self.pack_items_inner(args);
        self.exact_pcall = old;
        result
    }

    fn pack_items_inner(&mut self, args: &[Expr]) -> (Vec<ETy>, Option<ETy>) {
        if let Some(last) = args.last().filter(|e| self.is_pack(e)) {
            let fixed = args[..args.len() - 1].iter().map(|e| self.expr(e)).collect();
            return (fixed, Some(self.pack_value(last)));
        }
        self.allow_pack = true;
        let fixed = self.exprs_all(args, None);
        let tail = args.last().and_then(|e| self.info.pack_calls.get(&e.id).copied());
        (fixed, tail)
    }

    pub(crate) fn pack_call(&mut self, e: &Expr, args: &[Expr]) -> ETy {
        let (values, tail) = self.pack_items(args);
        for v in values.iter().chain(tail.iter()) {
            self.pack_boxable(v.ty, e.span);
        }
        let (ty, tab) = self.new_table_var(e.span);
        self.st.tab_mut(tab).kind = TKind::Array;
        self.st.tab_mut(tab).sparse = true;
        self.st.tab_mut(tab).packed = true;
        let any = self.st.ty(TyNode::Any);
        let elem = self.st.slot(any);
        self.st.tab_mut(tab).elem = Some(elem);
        self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::TPack));
        self.val(ty)
    }

    pub(crate) fn call_array_candidate(&self, items: &[TableItem]) -> bool {
        items.iter().all(|i| matches!(i, TableItem::Pos(_)))
            && items.iter().any(|i| matches!(i, TableItem::Pos(e) if matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..) | ExprKind::Vararg)))
    }

    pub(crate) fn call_array(&mut self, e: &Expr, items: &[TableItem]) -> ETy {
        let args: Vec<Expr> = items.iter().filter_map(|i| match i { TableItem::Pos(e) => Some(e.clone()), _ => None }).collect();
        let (values, tail) = self.pack_items(&args);
        let all: Vec<ETy> = values.iter().chain(tail.iter()).copied().collect();
        let concrete: Vec<_> = all.iter().filter_map(|v| match self.st.node(v.ty) {
            TyNode::Var | TyNode::Nil => None,
            TyNode::Num | TyNode::NumVar => Some(0),
            TyNode::Str => Some(1),
            TyNode::Bool => Some(2),
            TyNode::Any => Some(3),
            _ => Some(4),
        }).collect();
        let mixed = concrete.first().is_some_and(|k| concrete.iter().any(|other| k != other));
        let sparse = mixed || all.iter().any(|v| self.pack_may_be_nil(v.null) || self.is_any(v.ty) || self.soft(v.soft));
        let (ty, tab) = self.new_table_var(e.span);
        self.st.tab_mut(tab).kind = TKind::Array;
        if sparse {
            self.st.tab_mut(tab).sparse = true;
            let any = self.st.ty(TyNode::Any);
            let elem = self.st.slot(any);
            self.st.tab_mut(tab).elem = Some(elem);
            for v in all { self.pack_boxable(v.ty, e.span); }
        } else {
            let el = self.elem_slot(tab);
            let expectation = self.table_expectation(e.id);
            if expectation.elem_any {
                let any = self.st.ty(TyNode::Any);
                self.unify(el.ty, any, e.span);
            }
            for (i, v) in values.into_iter().enumerate() {
                let source = args.get(i).or_else(|| args.last());
                self.flow_node(source.map(|x| x.id), v, el, source.map(|x| x.span).unwrap_or(e.span));
            }
            if let Some(v) = tail { self.flow(v, el, e.span); }
        }
        self.st.tab_mut(tab).ctors.push(vec![]);
        self.val(ty)
    }

    /// Null edges are solved after constraint generation; inspect reachability
    /// here without forcing unrelated slots or reporting diagnostics early.
    fn pack_may_be_nil(&self, null: NullId) -> bool {
        if null == self.st.null_false { return false; }
        let target = self.st.null_root(null);
        let mut queue: Vec<NullId> = self.st.nulls.iter().enumerate().filter_map(|(i, node)| node.forced.map(|_| self.st.null_root(i as NullId))).collect();
        let mut seen = HashSet::new();
        while let Some(node) = queue.pop() {
            if node == target { return true; }
            if seen.insert(node) {
                queue.extend(self.st.nulls[node as usize].edges.iter().map(|(to, _)| self.st.null_root(*to)));
            }
        }
        false
    }

    /// Fixed select inputs are boxed independently; nil retains its list position.
    pub(crate) fn select_fixed(&mut self, e: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        let Some(selector) = args.first() else {
            self.error(e.span, "select expects an index or '#'");
            return vec![self.fresh_result(); want.unwrap_or(1)];
        };
        let count = matches!(&selector.kind, ExprKind::Str(s) if s.as_slice() == b"#");
        let index = self.expr(selector);
        if !count { self.expect(index, TyNode::Num, selector.span, "bad argument #1 to 'select' (number expected)"); }
        let (values, tail) = self.pack_items(&args[1..]);
        for v in values.iter().chain(tail.iter()) { self.pack_boxable(v.ty, e.span); }
        self.select_common_type(e.id, &values);
        self.select_fixed_result(e, count, want)
    }

    pub(crate) fn select_common_type(&mut self, node: NodeId, values: &[ETy]) {
        let concrete: Vec<TyId> = values.iter().filter(|v| v.null != self.st.null_true).map(|v| v.ty).collect();
        if let Some(&first) = concrete.first() {
            let kind = |t| match self.st.node(t) { TyNode::Num | TyNode::NumVar => 0, TyNode::Str => 1, TyNode::Bool => 2, _ => 3 };
            if kind(first) != 3 && concrete.iter().all(|t| kind(*t) == kind(first)) {
                self.info.packs.select_elem.insert(node, first);
            }
        }
    }

    pub(crate) fn select_fixed_result(&mut self, e: &Expr, count: bool, want: Option<usize>) -> Vec<ETy> {
        self.info.calls.insert(e.id, CallKind::Builtin(if count { BuiltinFn::SelectFixedCount } else { BuiltinFn::SelectFixed }));
        if count {
            let mut out = vec![self.num()];
            if let Some(n) = want {
                out.truncate(n);
                while out.len() < n { out.push(self.nil()); }
            }
            out
        } else {
            let el = if let Some(ty) = self.info.packs.select_elem.get(&e.id).copied().filter(|_| want.is_some()) {
                ETy { ty, null: self.st.null_false, soft: Soft::Yes }
            } else { self.any_val() };
            match want {
                None => { self.info.pack_calls.insert(e.id, el); vec![] }
                Some(n) => {
                    let out = vec![el; n];
                    self.info.builtin_outs.insert(e.id, out.clone());
                    out
                }
            }
        }
    }
}
