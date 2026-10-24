//! Restrictions for GC-sensitive `next` continuation identities.
//! Luau may collect an interned string after a key is deleted. Rebuilding its
//! bytes then produces a different identity; Rust allocation cannot guess that
//! virtual-GC timing. Primitive/constant keys and retained traversal keys are safe.
use std::collections::{HashMap, HashSet};
use crate::ast::*;
use crate::ast_walk::{self, VisitMut};
use crate::check::*;
use crate::resolve::{Res, Resolution, SymId};
use crate::types::*;

#[derive(Clone)]
pub enum KeySource { Expr(Expr), Nil, Unknown, Iteration(NodeId, Expr) }

pub fn sources(block: &Block, res: &Resolution) -> HashMap<SymId, Vec<KeySource>> {
    struct Collect<'a> { res: &'a Resolution, out: HashMap<SymId, Vec<KeySource>> }
    impl Collect<'_> {
        fn add(&mut self, sym: SymId, source: KeySource) { self.out.entry(sym).or_default().push(source); }
        fn value(exprs: &[Expr], index: usize) -> KeySource {
            if let Some(expr) = exprs.get(index) { return KeySource::Expr(expr.clone()); }
            if exprs.last().is_some_and(|expr| matches!(expr.kind, ExprKind::Call(..) | ExprKind::Method(..) | ExprKind::Vararg)) { KeySource::Unknown } else { KeySource::Nil }
        }
    }
    impl VisitMut for Collect<'_> {
        fn stat(&mut self, stat: &mut Stat) {
            match &stat.kind {
                StatKind::Local(names, values) => { for (index, (name, _)) in names.iter().enumerate() { self.add(self.res.decl(name.id), Self::value(values, index)); } }
                StatKind::Assign(targets, values) => { for (index, target) in targets.iter().enumerate() { if let ExprKind::Name(name) = &target.kind { if let Some(Res::Local(sym)) = self.res.res(name.id) { self.add(sym, Self::value(values, index)); } } } }
                StatKind::Compound(_, target, _) | StatKind::Function(target, _) => { if let ExprKind::Name(name) = &target.kind { if let Some(Res::Local(sym)) = self.res.res(name.id) { self.add(sym, KeySource::Unknown); } } }
                StatKind::LocalFunction(name, _) | StatKind::NumFor(name, ..) => self.add(self.res.decl(name.id), KeySource::Unknown),
                StatKind::GenFor(names, exprs, _) => {
                    for (index, name) in names.iter().enumerate() {
                        let source = if index == 0 && exprs.len() == 1 { KeySource::Iteration(stat.id, exprs[0].clone()) } else { KeySource::Unknown };
                        self.add(self.res.decl(name.id), source);
                    }
                }
                _ => {}
            }
        }
        fn func(&mut self, func: &mut FuncBody) { for param in &func.params { self.add(self.res.decl(param.name.id), KeySource::Unknown); } }
    }
    let mut collect = Collect { res, out: HashMap::new() };
    ast_walk::walk_block(&mut collect, &mut block.clone());
    collect.out
}

impl Checker<'_> {
    fn source_local(&self, expr: &Expr) -> Option<SymId> {
        match &expr.kind {
            ExprKind::Paren(expr) | ExprKind::Cast(expr, _) => self.source_local(expr),
            ExprKind::Name(name) => match self.res.res(name.id) { Some(Res::Local(sym)) => Some(sym), _ => None },
            _ => None,
        }
    }
    fn table_identity(&self, expr: &Expr, seen: &mut HashSet<SymId>) -> Option<SymId> {
        let sym = self.source_local(expr)?;
        if self.res.sym(sym).assigned || !seen.insert(sym) { return None; }
        if let Some(sources) = self.info.next_key_sources.get(&sym) {
            if let [KeySource::Expr(value)] = sources.as_slice() {
                if self.source_local(value).is_some() { return self.table_identity(value, seen); }
            }
        }
        Some(sym)
    }
    fn same_table(&self, left: &Expr, right: &Expr) -> bool {
        let a = self.table_identity(left, &mut HashSet::new());
        a.is_some() && a == self.table_identity(right, &mut HashSet::new())
    }
    fn next_key_safe(&self, table: &Expr, key: &Expr, seen: &mut HashSet<SymId>) -> bool {
        // Luau only roots computed constant strings in the prototype at O1/O2.
        if self.info.rooted_constant_string_files.contains(&key.span.file) && self.info.constant_strings.contains_key(&key.id) { return true; }
        if self.info.expr.get(&key.id).is_some_and(|value| matches!(self.st.node(value.ty), TyNode::Num | TyNode::NumVar | TyNode::Int | TyNode::Bool | TyNode::Nil)) { return true; }
        match &key.kind {
            ExprKind::Nil | ExprKind::Bool(_) | ExprKind::Number(_) | ExprKind::Int(_) | ExprKind::Str(_) => true,
            ExprKind::Paren(inner) | ExprKind::Cast(inner, _) => self.next_key_safe(table, inner, seen),
            ExprKind::IfElse(_, left, right) | ExprKind::Binary(BinOp::And | BinOp::Or, left, right) => self.next_key_safe(table, left, seen) && self.next_key_safe(table, right, seen),
            ExprKind::Call(_, args) if matches!(self.info.calls.get(&key.id), Some(CallKind::Builtin(BuiltinFn::Next))) => args.first().is_some_and(|source| self.same_table(table, source)),
            ExprKind::Name(_) => {
                let Some(sym) = self.source_local(key) else { return false };
                if !seen.insert(sym) { return true; } // a self-assignment preserves its other producers
                let Some(sources) = self.info.next_key_sources.get(&sym) else { return false };
                let safe = !sources.is_empty() && sources.iter().all(|source| match source {
                    KeySource::Nil => true,
                    KeySource::Expr(value) => self.next_key_safe(table, value, seen),
                    KeySource::Unknown => false,
                    KeySource::Iteration(node, expr) => {
                        let source = match (&self.info.fors.get(node), &expr.kind) {
                            (Some(ForKind::PairsMap | ForKind::PairsArray | ForKind::Ipairs), ExprKind::Call(_, args)) => args.first().unwrap_or(expr),
                            (Some(ForKind::PairsMap | ForKind::PairsArray), _) => expr,
                            (Some(ForKind::Runtime), _) if self.info.iteration.get(node).is_some_and(|iter| iter.mode == crate::check_iteration::IterationMode::Pairs || iter.mode == crate::check_iteration::IterationMode::Ipairs) => match &expr.kind { ExprKind::Call(_, args) => args.first().unwrap_or(expr), _ => expr },
                            _ => return false,
                        };
                        self.same_table(table, source)
                    }
                });
                seen.remove(&sym);
                safe
            }
            _ => false,
        }
    }
    pub(crate) fn validate_next_key_identity(&mut self) {
        for (table, key) in std::mem::take(&mut self.info.next_key_checks) {
            if !self.next_key_safe(&table, &key, &mut HashSet::new()) {
                self.error(key.span, "next continuation key has GC-sensitive identity that cannot be proven safe; use a numeric/boolean key, a literal/constant string, or a retained key from next on this table");
            }
        }
    }
}
