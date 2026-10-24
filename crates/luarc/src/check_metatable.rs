//! Static class-record parents.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ast::*;
use crate::check::{Checker, ModuleUnit, Op};
use crate::diag::{Diagnostic, Span};
use crate::resolve::{Builtin, Res, Resolution, SymId};
use crate::types::*;

const INDEX_WRITE: &str = "the only supported __index write in step 1 is the statement X.__index = X";
const INDEX_INIT: &str = "X.__index = X must follow local X = {} in the same block and precede setmetatable(_, X)";
const CLASS_ARG: &str = "setmetatable requires the directly declared local class name in step 1";
const SELF_INDEX: &str = "step 1 requires the metatable's own __index to be the metatable itself";
const CHAIN: &str = "record parent chains are not supported in step 1";
const CYCLE: &str = "cyclic static record parent types are not supported";
const NATIVE: &str = "metatables on native-converted records are not supported in this step";

#[derive(Default)]
struct ClassDecl {
    block: usize,
    statement: usize,
    writes: Vec<usize>,
}

/// Syntactic eligibility only: no alias, object-origin or execution-order analysis.
#[derive(Default)]
pub struct ClassSyntax {
    classes: HashMap<SymId, ClassDecl>,
    calls: HashMap<NodeId, Vec<(usize, usize)>>,
    pub errors: Vec<Diagnostic>,
    call_arguments: Vec<(NodeId, Expr, Option<Expr>)>,
    blocks: usize,
}

impl ClassSyntax {
    pub fn analyze(res: &Resolution, units: &[ModuleUnit]) -> Self {
        let mut syntax = Self::default();
        for unit in units {
            syntax.block(res, &unit.module.body, &mut Vec::new());
        }
        syntax
    }

    pub fn class_argument(&self, res: &Resolution, call: NodeId, arg: &Expr) -> Result<SymId, Diagnostic> {
        let Some(sym) = local(res, arg) else {
            return Err(Diagnostic::new(arg.span, CLASS_ARG));
        };
        let Some(class) = self.classes.get(&sym) else {
            return Err(Diagnostic::new(arg.span, CLASS_ARG));
        };
        if res.sym(sym).assigned {
            return Err(Diagnostic::new(
                arg.span,
                "the local class name passed to setmetatable must not be reassigned in step 1",
            ));
        }
        if class.writes.is_empty() {
            return Err(Diagnostic::new(arg.span, SELF_INDEX));
        }
        let use_at = self.calls.get(&call).and_then(|path| path.iter().find(|(b, _)| *b == class.block));
        // A nested use is ordered by its enclosing statement in the class's block.
        if !use_at.is_some_and(|(_, i)| class.writes.iter().all(|w| *w < *i)) {
            return Err(Diagnostic::new(
                arg.span,
                "X.__index = X must precede every setmetatable(_, X) use in step 1",
            ));
        }
        Ok(sym)
    }

    fn block(&mut self, res: &Resolution, block: &Block, path: &mut Vec<(usize, usize)>) {
        let id = self.blocks;
        self.blocks += 1;
        for (i, stat) in block.stats.iter().enumerate() {
            path.push((id, i));
            match &stat.kind {
                StatKind::Local(names, values) => {
                    if let ([(name, _)], [value]) = (names.as_slice(), values.as_slice()) {
                        if matches!(&value.kind, ExprKind::Table(items) if items.is_empty()) {
                            if let Some(&sym) = res.decls.get(&name.id) {
                                self.classes.insert(
                                    sym,
                                    ClassDecl {
                                        block: id,
                                        statement: i,
                                        writes: Vec::new(),
                                    },
                                );
                            }
                        }
                    }
                    for value in values {
                        self.expr(res, value, path);
                    }
                }
                StatKind::Assign(targets, values) => {
                    for target in targets {
                        if index_target(target) {
                            let sym = match (targets.as_slice(), values.as_slice(), &target.kind) {
                                ([_], [value], ExprKind::Field(obj, _)) if local(res, obj) == local(res, value) => local(res, obj),
                                _ => None,
                            };
                            match sym.and_then(|s| self.classes.get_mut(&s)) {
                                Some(class) if class.block == id && class.statement < i => class.writes.push(i),
                                _ => {
                                    let message = if sym.is_some() { INDEX_INIT } else { INDEX_WRITE };
                                    self.errors.push(Diagnostic::new(target.span, message));
                                }
                            }
                        }
                        self.expr(res, target, path);
                    }
                    for value in values {
                        self.expr(res, value, path);
                    }
                }
                StatKind::Function(target, body) => {
                    self.reject_write(target);
                    self.expr(res, target, path);
                    self.block(res, &body.body, path);
                }
                StatKind::LocalFunction(_, body) => self.block(res, &body.body, path),
                StatKind::Compound(_, target, value) => {
                    self.reject_write(target);
                    self.expr(res, target, path);
                    self.expr(res, value, path);
                }
                StatKind::Call(value) => self.expr(res, value, path),
                StatKind::Do(body) => self.block(res, body, path),
                StatKind::While(value, body) => {
                    self.expr(res, value, path);
                    self.block(res, body, path);
                }
                StatKind::Repeat(body, value) => {
                    let body_id = self.blocks;
                    self.block(res, body, path);
                    // The until condition shares the body's local scope.
                    path.push((body_id, body.stats.len()));
                    self.expr(res, value, path);
                    path.pop();
                }
                StatKind::If(arms, other) => {
                    for (condition, body) in arms {
                        self.expr(res, condition, path);
                        self.block(res, body, path);
                    }
                    if let Some(body) = other {
                        self.block(res, body, path);
                    }
                }
                StatKind::NumFor(_, start, end, step, body) => {
                    for value in [Some(start), Some(end), step.as_ref()].into_iter().flatten() {
                        self.expr(res, value, path);
                    }
                    self.block(res, body, path);
                }
                StatKind::GenFor(_, values, body) => {
                    for value in values {
                        self.expr(res, value, path);
                    }
                    self.block(res, body, path);
                }
                StatKind::Return(values) => {
                    for value in values {
                        self.expr(res, value, path);
                    }
                }
                StatKind::Break | StatKind::Continue | StatKind::TypeAlias(..) => {}
            }
            path.pop();
        }
    }

    fn reject_write(&mut self, target: &Expr) {
        if index_target(target) {
            self.errors.push(Diagnostic::new(target.span, INDEX_WRITE));
        }
    }

    fn expr(&mut self, res: &Resolution, expr: &Expr, path: &mut Vec<(usize, usize)>) {
        match &expr.kind {
            ExprKind::Call(callee, args) => {
                self.calls.insert(expr.id, path.clone());
                self.call_arguments.push((expr.id, (**callee).clone(), args.get(1).cloned()));
                self.expr(res, callee, path);
                for arg in args {
                    self.expr(res, arg, path);
                }
            }
            ExprKind::Method(obj, _, args) => {
                self.expr(res, obj, path);
                for arg in args {
                    self.expr(res, arg, path);
                }
            }
            ExprKind::Table(items) => {
                for item in items {
                    match item {
                        TableItem::Named(name, value) => {
                            if name.text == "__index" {
                                self.errors.push(Diagnostic::new(name.span, INDEX_WRITE));
                            }
                            self.expr(res, value, path);
                        }
                        TableItem::Keyed(key, value) => {
                            if index_key(key) {
                                self.errors.push(Diagnostic::new(key.span, INDEX_WRITE));
                            }
                            self.expr(res, key, path);
                            self.expr(res, value, path);
                        }
                        TableItem::Pos(value) => self.expr(res, value, path),
                    }
                }
            }
            ExprKind::Function(body) => self.block(res, &body.body, path),
            ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) => {
                self.expr(res, a, path);
                self.expr(res, b, path);
            }
            ExprKind::Field(value, _) | ExprKind::Unary(_, value) | ExprKind::Paren(value) => self.expr(res, value, path),
            ExprKind::IfElse(c, a, b) => {
                for value in [c, a, b] {
                    self.expr(res, value, path);
                }
            }
            ExprKind::Interp(parts) => {
                for part in parts {
                    if let InterpPart::Expr(value) = part {
                        self.expr(res, value, path);
                    }
                }
            }
            _ => {}
        }
    }
}

fn local(res: &Resolution, expr: &Expr) -> Option<SymId> {
    if let ExprKind::Name(name) = &expr.kind {
        if let Some(Res::Local(sym)) = res.res(name.id) {
            return Some(sym);
        }
    }
    None
}

fn index_key(expr: &Expr) -> bool {
    if let ExprKind::Paren(inner) = &expr.kind {
        return index_key(inner);
    }
    matches!(&expr.kind, ExprKind::Str(key) if key == b"__index")
}

fn index_target(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Field(_, name) => name.text == "__index",
        ExprKind::Index(_, key) => index_key(key),
        _ => false,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordLookup {
    pub tab: TabId,
    pub own: Option<Slot>,
    pub fallback: Option<(TabId, Slot)>,
    pub result: Slot,
    pub may_miss: bool,
    pub levels: Vec<crate::check_metatable_general::LookupLevel>,
}

#[derive(Clone)]
pub(crate) struct RecordRead {
    pub tab: TabId,
    pub name: String,
    pub result: ETy,
    pub span: Span,
}

#[derive(Default)]
pub(crate) struct MetaState {
    pub enabled: bool,
    pub general: bool,
    pub general_source: bool,
    pub general_attachments: Vec<(NodeId, ETy, ETy, Span)>,
    pub receivers: Vec<(TyId, TyId, Span)>,
    pub index_writes: Vec<(ETy, Span)>,
    pub syntax: ClassSyntax,
    pub reads: BTreeMap<NodeId, RecordRead>,
    pub attachments: Vec<(NodeId, ETy, SymId, Span)>,
    pub clones: Vec<(TyId, Span)>,
    pub parent_calls: HashSet<NodeId>,
}

impl<'a> Checker<'a> {
    pub(crate) fn prepare_source_metatables(&mut self, units: &[ModuleUnit]) {
        if self.metatables.enabled {
            return;
        }
        let syntax = ClassSyntax::analyze(self.res, units);
        let used = self.res.names.values().any(|r| *r == Res::Builtin(Builtin::SetMetatable))
            || syntax.classes.values().any(|class| !class.writes.is_empty());
        // Preserve the lowering of proven class-only programs; other index writes use general typed checking.
        let general = !syntax.errors.is_empty() || syntax.call_arguments.iter().any(|(node, callee, argument)| {
            let builtin = match &callee.kind {
                ExprKind::Name(name) => match self.res.res(name.id) {
                    Some(Res::Builtin(Builtin::SetMetatable)) => true,
                    Some(Res::Local(sym)) => self.info.builtin_aliases.get(&sym).is_some_and(|b| *b == (Builtin::SetMetatable, None)),
                    _ => false,
                },
                _ => false,
            };
            builtin && argument.as_ref().map_or(true, |arg| syntax.class_argument(self.res, *node, arg).is_err())
        });
        self.metatables.syntax = syntax;
        self.metatables.general = general;
        self.metatables.general_source = true;
        self.metatables.enabled = used || general;
    }

    /// Register an explicit attachment call for compiler API tests.
    pub fn register_record_parent_call(&mut self, node: NodeId) {
        self.metatables.parent_calls.insert(node);
    }

    pub(crate) fn record_parent_call(&mut self, e: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        let (values, _) = self.args_values(args);
        if let Some(out) = self.runtime_attach(e, args, &values, want) { return out; }
        if args.len() < 2 {
            let message = if values.len() < 2 {
                format!("setmetatable expects at least two arguments, got {}", values.len())
            } else {
                if self.metatables.general { "setmetatable requires two explicit source arguments".into() } else { CLASS_ARG.into() }
            };
            self.error(e.span, message);
            return (0..want.unwrap_or(1)).map(|_| self.fresh_result()).collect();
        }
        let Some(child) = values.first().copied() else {
            self.error(e.span, "setmetatable requires a statically known record as its first argument");
            return (0..want.unwrap_or(1)).map(|_| self.fresh_result()).collect();
        };
        // This API requires a directly declared class.
        if !self.metatables.general && matches!(args[1].kind, ExprKind::Table(_)) {
            self.error(args[1].span, "anonymous metatables are not supported in step 1 (use the directly declared local class name)");
            return vec![child; want.unwrap_or(1)];
        }
        // This record-attachment subset does not support removal.
        if matches!(args[1].kind, ExprKind::Nil) {
            self.error(args[1].span, "removing a metatable is not supported in this step");
            return vec![child; want.unwrap_or(1)];
        }
        self.need(child, args[0].span, "bad argument #1 to 'setmetatable' (table expected, got nil)");
        if self.metatables.general {
            let meta = values.get(1).copied().unwrap_or_else(|| self.nil());
            self.need(meta, args[1].span, "bad argument #2 to 'setmetatable' (table expected, got nil)");
            self.general_record_parent(e.id, child, meta, e.span);
        } else {
            self.record_parent(e.id, child, &args[1], e.span);
        }
        self.info.calls.insert(e.id, crate::check::CallKind::RecordParent);
        let mut results = vec![child];
        if let Some(n) = want {
            results.truncate(n);
            while results.len() < n {
                results.push(self.nil());
            }
        }
        results
    }

    /// Receiver inference only; class-argument and __index permissions remain syntactic.
    pub(crate) fn is_record_class(&self, ty: TyId) -> bool {
        if !self.metatables.enabled {
            return false;
        }
        let TyNode::Table(tab) = self.st.node(ty) else { return false };
        self.metatables
            .syntax
            .classes
            .iter()
            .filter(|(sym, class)| !class.writes.is_empty() && !self.res.sym(**sym).assigned)
            .any(|(sym, _)| {
                self.info.sym_slot.get(sym).is_some_and(
                    |slot| matches!(self.st.node(slot.ty), TyNode::Table(class) if self.st.tab_root(*class) == self.st.tab_root(*tab)),
                )
            })
    }

    pub(crate) fn prepare_record_method(&mut self, node: NodeId, obj: ETy, name: &str, span: Span) -> Option<ETy> {
        if !self.metatables.enabled {
            return None;
        }
        if let Some(result) = self.info.record_methods.get(&node) {
            return Some(*result);
        }
        let TyNode::Table(tab) = self.st.node(obj.ty) else { return None };
        let tab = *tab;
        if self.st.tab(tab).native.is_some() || !matches!(self.st.tab(tab).kind, TKind::Record | TKind::Unknown) {
            return None;
        }
        self.ensure_kind(tab, TKind::Record, span);
        let result = self.deferred_result();
        self.metatables.reads.insert(
            node,
            RecordRead {
                tab,
                name: name.into(),
                result,
                span,
            },
        );
        self.info.record_methods.insert(node, result);
        Some(result)
    }

    pub(crate) fn record_method_slot(&self, obj: ETy, name: &str) -> Option<Slot> {
        if !self.metatables.enabled {
            return None;
        }
        let TyNode::Table(tab) = self.st.node(obj.ty) else { return None };
        self.metatables
            .reads
            .values()
            .find(|read| read.name == name && self.st.tab_root(read.tab) == self.st.tab_root(*tab))
            .map(|read| Slot {
                ty: read.result.ty,
                null: read.result.null,
            })
    }

    pub(crate) fn settle_record_calls(&mut self) {
        if !self.metatables.enabled {
            return;
        }
        loop {
            let before = self.record_links();
            let count = self.pending_count();
            self.solve_pending_quick();
            let reads = self.solve_record_reads();
            if !reads && before == self.record_links() && count == self.pending_count() {
                break;
            }
        }
    }

    /// Explicit compiler API entry point; source programs enable checking only when needed.
    pub fn prepare_record_metatables(&mut self, units: &[ModuleUnit]) {
        self.metatables.enabled = true;
        self.metatables.syntax = ClassSyntax::analyze(self.res, units);
        self.errors.extend(self.metatables.syntax.errors.iter().cloned());
    }

    /// The caller supplies a resolved builtin call, after checking its argument list.
    pub fn record_parent(&mut self, node: NodeId, child: ETy, class_arg: &Expr, span: Span) {
        match self.metatables.syntax.class_argument(self.res, node, class_arg) {
            Ok(class) => {
                self.metatables.attachments.push((node, child, class, span));
                self.try_or_defer(Op::RecordParent { node, child, class, span });
            }
            Err(error) => self.errors.push(error),
        }
    }

    pub(crate) fn attempt_record_parent(&mut self, node: NodeId, child: ETy, class: SymId, span: Span) -> bool {
        let Some(class_slot) = self.info.sym_slot.get(&class).copied() else {
            return false;
        };
        if self.metatables.general {
            return self.attempt_record_metatable(node, child, self.of_slot(class_slot), span);
        }
        let parent = match self.st.node(class_slot.ty) {
            TyNode::Var => return false,
            TyNode::Table(tab) => *tab,
            _ => {
                self.error(span, "setmetatable requires a statically known record as its second argument");
                return true;
            }
        };
        let tab = match self.st.node(child.ty) {
            TyNode::Var => return false,
            TyNode::Table(tab) => *tab,
            _ => {
                self.error(span, "setmetatable requires a statically known record as its first argument");
                return true;
            }
        };
        for role in [tab, parent] {
            if !matches!(self.st.tab(role).kind, TKind::Unknown | TKind::Record) {
                self.error(span, "setmetatable does not support arrays or maps");
                return true;
            }
            if self.st.tab(role).native.is_some() {
                self.error(span, NATIVE);
                return true;
            }
            self.ensure_kind(role, TKind::Record, span);
        }
        let Some(index) = self.st.tab(parent).fields.get("__index").copied() else {
            if !self.defaults_round {
                return false;
            }
            self.error(span, SELF_INDEX);
            return true;
        };
        if matches!(self.st.node(index.ty), TyNode::Var) {
            return false;
        }
        if !self.valid_class(parent, span) {
            return true;
        }
        if let Some(old) = self.st.tab(tab).parent {
            if !self.unify_tabs(old, parent, span) {
                return true;
            }
        }
        if let Some(message) = self.record_graph_error(&[], Some((tab, parent))) {
            if message == CHAIN && self.metatables.general_source {
                self.activate_general_record_metatables();
                return true;
            }
            self.error(span, message);
            return true;
        }
        // Luau 0.743: attachment preserves child identity; this edge records only its possible lookup type.
        self.st.tab_mut(tab).parent = Some(self.st.tab_root(parent));
        true
    }

    fn valid_class(&mut self, parent: TabId, span: Span) -> bool {
        let tab = self.st.tab(parent);
        let valid = tab.fields.get("__index").is_some_and(
            |slot| matches!(self.st.node(slot.ty), TyNode::Table(index) if self.st.tab_root(*index) == self.st.tab_root(parent)),
        );
        if !valid {
            self.error(span, SELF_INDEX);
            return false;
        }
        self.valid_metatable_fields(parent, span)
    }

    pub(crate) fn valid_metatable_fields(&mut self, parent: TabId, span: Span) -> bool {
        let tab = self.st.tab(parent);
        // No other metamethods can be implemented by this static lookup-only subset.
        const UNSUPPORTED: &[&str] = &[
            "__newindex",
            "__call",
            "__tostring",
            "__metatable",
            "__mode",
            "__iter",
            "__add",
            "__sub",
            "__mul",
            "__div",
            "__idiv",
            "__mod",
            "__pow",
            "__unm",
            "__len",
            "__eq",
            "__lt",
            "__le",
            "__concat",
        ];
        let bad = UNSUPPORTED.iter().find(|name| tab.fields.contains_key(**name)).copied();
        if let Some(name) = bad {
            self.error(span, format!("metamethod '{name}' is not supported in this step"));
            return false;
        }
        true
    }

    /// Simulate unions without changing the store, so a rejected merge cannot corrupt the parent graph.
    fn record_graph_error(&self, unions: &[(TabId, TabId)], edge: Option<(TabId, TabId)>) -> Option<&'static str> {
        let mut roots: Vec<_> = (0..self.st.tabs.len()).map(|i| self.st.tab_root(i as TabId)).collect();
        for &(a, b) in unions {
            let (a, b) = (roots[a as usize], roots[b as usize]);
            for root in &mut roots {
                if *root == a {
                    *root = b;
                }
            }
        }
        let mut graph = HashMap::new();
        for (i, tab) in self.st.tabs.iter().enumerate().filter(|(_, t)| t.link.is_none()) {
            if let Some(parent) = tab.parent {
                graph.insert(roots[i], roots[parent as usize]);
            }
        }
        if let Some((child, parent)) = edge {
            graph.insert(roots[child as usize], roots[parent as usize]);
        }
        for &start in graph.keys() {
            let mut seen = HashSet::new();
            let mut current = start;
            while let Some(&parent) = graph.get(&current) {
                if !seen.insert(current) {
                    return Some(CYCLE);
                }
                current = parent;
            }
        }
        if graph.values().any(|parent| graph.contains_key(parent)) {
            return Some(CHAIN);
        }
        let roles: HashSet<_> = graph.keys().chain(graph.values()).copied().collect();
        for (i, tab) in self.st.tabs.iter().enumerate().filter(|(_, t)| t.link.is_none()) {
            if roles.contains(&roots[i]) {
                if tab.native.is_some() {
                    return Some(NATIVE);
                }
                if !matches!(tab.kind, TKind::Unknown | TKind::Record) {
                    return Some("setmetatable does not support arrays or maps");
                }
            }
        }
        None
    }

    pub(crate) fn preflight_record_merge(&mut self, a: TabId, b: TabId, span: Span) -> bool {
        let (a, b) = (self.st.tab_root(a), self.st.tab_root(b));
        if self.metatables.general {
            return match self.general_record_graph_error(&[(a, b)], None) {
                Some(message) => { self.error(span, message); false }
                None => true,
            };
        }
        let mut unions = vec![(a, b)];
        if let (Some(p), Some(q)) = (self.st.tab(a).parent, self.st.tab(b).parent) {
            unions.push((p, q));
        }
        if self.metatables.general_source && self.record_graph_error(&unions, None) == Some(CHAIN) {
            self.activate_general_record_metatables();
            return self.preflight_record_merge(a, b, span);
        }
        match self.record_graph_error(&unions, None) {
            Some(message) => {
                self.error(span, message);
                false
            }
            None => true,
        }
    }

    pub(crate) fn solve_record_reads(&mut self) -> bool {
        if !self.metatables.enabled {
            return false;
        }
        if self.metatables.general { return self.solve_general_record_reads(); }
        let before = self.record_links();
        let previous_nulls = self.st.solved.clone();
        self.st.solve_nulls();
        let mut changed = previous_nulls != self.st.solved;
        let mut groups = HashMap::new();
        let reads = self.metatables.reads.clone();
        for (node, read) in reads {
            let tab = self.st.tab_root(read.tab);
            let own = self.st.tab(tab).fields.get(&read.name).copied();
            let present = own.is_some_and(|s| self.field_always_init(tab, &read.name) && !self.st.is_null(s.null));
            let parent = self.st.tab(tab).parent.map(|p| self.st.tab_root(p));
            // Luau 0.743: only nil misses; false, zero and empty strings stop lookup.
            let fallback = if present {
                None
            } else {
                parent.and_then(|p| self.st.tab(p).fields.get(&read.name).copied().map(|s| (p, s)))
            };
            if own.is_none() && parent.is_none() && self.st.tab(tab).closed {
                self.field_slot(tab, &read.name, read.span);
            }
            for slot in own.into_iter().chain(fallback.map(|(_, slot)| slot)) {
                self.unify(read.result.ty, slot.ty, read.span);
            }
            if let Some(previous) = groups.insert((tab, read.name.clone()), read.result.ty) {
                self.unify(previous, read.result.ty, read.span);
            }
            let plan = RecordLookup {
                tab,
                own,
                fallback,
                result: Slot {
                    ty: read.result.ty,
                    null: read.result.null,
                },
                may_miss: !present,
                levels: Vec::new(),
            };
            self.set_soft(&read.result, if plan.may_miss { Soft::Yes } else { Soft::No });
            changed |= self.info.record_lookups.get(&node) != Some(&plan);
            self.info.record_lookups.insert(node, plan);
        }
        changed || before != self.record_links()
    }

    pub(crate) fn record_links(&self) -> usize {
        self.st.tys.iter().filter(|t| matches!(t, TyNode::Link(_))).count() + self.st.tabs.iter().filter(|t| t.link.is_some()).count()
    }

    pub(crate) fn finish_record_reads(&mut self) {
        if !self.metatables.enabled {
            return;
        }
        // Apply missing-field storage rules to terminal ordinary reads.
        // Delay this until attachments and unions settle, so inherited fields never become own fields.
        let null = self.st.null_false;
        for read in self.metatables.reads.values() {
            let tab = self.st.tab_mut(read.tab);
            if tab.parent.is_none() && tab.metatable.is_none() && !tab.closed {
                tab.fields.entry(read.name.clone()).or_insert(Slot { ty: read.result.ty, null });
            }
        }
    }

    pub(crate) fn validate_record_parents(&mut self) {
        if !self.metatables.enabled {
            return;
        }
        if self.metatables.general {
            self.validate_general_record_metadata();
            return;
        }
        if let Some(message) = self.record_graph_error(&[], None) {
            self.error(Span::default(), message);
        }
        let parents: Vec<_> = self
            .st
            .tabs
            .iter()
            .enumerate()
            .filter(|(_, tab)| tab.link.is_none())
            .filter_map(|(i, tab)| tab.parent.map(|p| (i, self.st.tab_root(p))))
            .collect();
        for (i, parent) in parents {
            self.st.tabs[i].parent = Some(parent);
        }
        for (_, child, class, span) in self.metatables.attachments.clone() {
            if let TyNode::Table(tab) = self.st.node(child.ty) {
                if let Some(parent) = self.st.tab(*tab).parent {
                    self.valid_class(parent, span);
                }
            }
            if let Some(slot) = self.info.sym_slot.get(&class).copied() {
                if let TyNode::Table(tab) = self.st.node(slot.ty) {
                    self.valid_class(*tab, span);
                }
            }
        }
        for (ty, span) in self.metatables.clones.clone() {
            if let TyNode::Table(tab) = self.st.node(ty) {
                if self.st.tab(*tab).parent.is_some() {
                    self.error(span, "table.clone on records with a static parent type is not supported in step 1");
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::SourceMap;
    use crate::native::adapters::AdapterSet;
    use crate::native::world::World;
    use crate::parser::parse_module;
    use crate::resolve::Resolver;

    fn fixture(src: &str, test: impl FnOnce(&mut Checker<'_>, &ModuleUnit)) {
        let mut next = 1;
        let module = parse_module(0, src, &mut next).expect("parse checker fixture");
        let mut sm = SourceMap::default();
        sm.add("metatables.luarc".into(), "metatables.luarc".into(), src.into());
        let mut res = Resolution::default();
        let mut resolver = Resolver::new(&mut res);
        resolver.module(&module, next);
        resolver.finish();
        assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
        let unit = ModuleUnit {
            module,
            pseudo_func: next,
            ident: "m0".into(),
            requires: Default::default(),
            rust_requires: Default::default(),
        };
        let world = World::default();
        let adapters = AdapterSet::default();
        let mut checker = Checker::new(&res, &sm, &world, &adapters);
        checker.prepare_record_metatables(std::slice::from_ref(&unit));
        checker.info.module_value = vec![None];
        checker.check_module(&unit, 0);
        test(&mut checker, &unit);
    }

    fn slot(checker: &Checker<'_>, name: &str) -> Slot {
        let sym = checker.res.syms.iter().position(|s| s.name == name).expect("fixture symbol") as SymId;
        checker.info.sym_slot[&sym]
    }

    fn tab(checker: &Checker<'_>, name: &str) -> TabId {
        match checker.st.node(slot(checker, name).ty) {
            TyNode::Table(tab) => checker.st.tab_root(*tab),
            other => panic!("expected record for {name}: {other:?}"),
        }
    }

    fn attach_marker(checker: &mut Checker<'_>, unit: &ModuleUnit) {
        // Register a dormant attachment at a marker call; the source resolver gate stays closed.
        let StatKind::Call(expr) = &unit.module.body.stats.last().expect("marker statement").kind else {
            panic!()
        };
        let ExprKind::Call(_, args) = &expr.kind else { panic!() };
        checker.record_parent(expr.id, checker.info.expr[&args[0].id], &args[1], expr.span);
    }

    fn finish(checker: &mut Checker<'_>) {
        checker.solve_pending();
        checker.finish();
    }

    fn good(checker: &Checker<'_>) {
        assert!(checker.errors.is_empty(), "{:?}", checker.errors);
    }

    #[test]
    fn late_attachment_promotes_shared_roots_without_flattening_parent_fields() {
        fixture("local C = {} C.__index = C C.extra = 7 local function read(t) return t.extra end local child = {} local plain = {x = 9} local alias = plain local isolated = {x = 11} local a = read(child) local b = read(plain) print(child, C)", |checker, unit| {
            attach_marker(checker, unit);
            finish(checker);
            good(checker);
            let (child, class) = (tab(checker, "child"), tab(checker, "C"));
            assert_eq!(child, tab(checker, "plain"));
            assert_eq!(child, tab(checker, "alias"));
            assert_eq!(child, tab(checker, "t"));
            assert_ne!(child, class);
            assert_ne!(child, tab(checker, "isolated"));
            assert_eq!(checker.st.tab(child).parent, Some(class));
            assert!(checker.st.tab(class).parent.is_none());
            assert!(checker.st.tab(tab(checker, "isolated")).parent.is_none());
            assert!(!checker.st.tab(child).fields.contains_key("extra"));
            let plan = checker.info.record_lookups.values().find(|p| p.tab == child).expect("inherited read");
            assert!(plan.own.is_none());
            assert_eq!(plan.fallback.map(|(p, _)| p), Some(class));
            assert!(plan.may_miss);
            assert!(matches!(checker.st.node(slot(checker, "a").ty), TyNode::Num));
        });
    }

    #[test]
    fn literal_key_read_before_attachment_uses_the_record_parent() {
        fixture(
            "local C = {} C.__index = C C.x = 7 local child = {} local value = child[\"x\"] print(child, C)",
            |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                good(checker);
                assert_eq!(checker.st.tab(tab(checker, "child")).kind, TKind::Record);
                assert!(matches!(checker.st.node(slot(checker, "value").ty), TyNode::Num));
                assert!(!checker.st.tab(tab(checker, "child")).fields.contains_key("x"));
            },
        );
    }

    #[test]
    fn read_constraints_resume_pending_function_calls() {
        fixture(
            "local C = {} C.__index = C function C.answer() return 7 end local child = {} local result = child.answer() print(child, C)",
            |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                good(checker);
                assert!(matches!(checker.st.node(slot(checker, "result").ty), TyNode::Num));
                assert!(!checker.st.tab(tab(checker, "child")).fields.contains_key("answer"));
            },
        );
    }

    #[test]
    fn unresolved_attachment_is_diagnosed_instead_of_guessing_a_shape() {
        fixture("local C = {} C.__index = C local child print(child, C)", |checker, unit| {
            attach_marker(checker, unit);
            finish(checker);
            assert!(
                checker
                    .errors
                    .iter()
                    .any(|e| e.msg == "cannot infer the record types passed to setmetatable here; add a type annotation"),
                "{:?}",
                checker.errors
            );
            assert!(matches!(checker.st.node(slot(checker, "child").ty), TyNode::Var));
        });
    }

    #[test]
    fn closed_annotations_limit_own_writes_but_allow_inherited_reads() {
        fixture(
            "local C = {} C.__index = C C.x = 7 local child: {own: number} = {own = 1} local x = child.x print(child, C)",
            |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                good(checker);
                assert_eq!(checker.st.tab(tab(checker, "child")).fields.len(), 1);
                assert!(matches!(checker.st.node(slot(checker, "x").ty), TyNode::Num));
            },
        );
        fixture(
            "local C = {} C.__index = C C.x = 7 local child: {own: number} = {own = 1} child.x = 2 print(child, C)",
            |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                assert!(
                    checker.errors.iter().any(|e| e.msg.contains("field 'x' does not exist")),
                    "{:?}",
                    checker.errors
                );
                assert!(!checker.st.tab(tab(checker, "child")).fields.contains_key("x"));
            },
        );
    }

    #[test]
    fn non_nil_own_storage_stops_lookup_without_unifying_unreachable_types() {
        fixture(
            "local C = {} C.__index = C C.x = \"parent\" local child = {x = 3} local x = child.x print(child, C)",
            |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                good(checker);
                let plan = checker.info.record_lookups.values().next().expect("own read");
                assert!(plan.own.is_some());
                assert!(plan.fallback.is_none());
                assert!(!plan.may_miss);
                assert!(matches!(checker.st.node(slot(checker, "x").ty), TyNode::Num));
            },
        );
    }

    #[test]
    fn nil_writes_and_omitted_constructors_make_fallback_types_reachable() {
        for src in [
            "local C = {} C.__index = C C.x = \"parent\" local child = {x = 3} local x = child.x child.x = nil print(child, C)",
            "local C = {} C.__index = C C.x = \"parent\" local function same(t) return t end local child = same({x = 3}) local empty = same({}) local x = child.x print(child, C)",
        ] {
            fixture(src, |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                assert!(checker.errors.iter().any(|e| e.msg.starts_with("type mismatch:")), "{:?}", checker.errors);
                assert!(checker.info.record_lookups.values().any(|p| p.own.is_some() && p.fallback.is_some() && p.may_miss));
            });
        }
    }

    #[test]
    fn lookup_plans_are_rechecked_after_late_constructor_and_root_changes() {
        fixture(
            "local C = {} C.__index = C C.x = \"parent\" local child = {x = 3} local result = child.x print(child, C)",
            |checker, unit| {
                attach_marker(checker, unit);
                checker.solve_pending();
                good(checker);
                let old = tab(checker, "child");
                let late = checker.st.new_tab(TKind::Record, Span::default());
                checker.st.tab_mut(late).ctors.push(vec![]);
                assert!(checker.unify_tabs(old, late, Span::default()));
                finish(checker);
                assert!(checker.errors.iter().any(|e| e.msg.starts_with("type mismatch:")));
                assert!(checker
                    .info
                    .record_lookups
                    .values()
                    .any(|p| p.tab == tab(checker, "child") && p.fallback.is_some() && p.may_miss));
            },
        );
    }

    #[test]
    fn false_zero_and_empty_string_own_values_stop_before_incompatible_parent_types() {
        for own in ["false", "0", "\"\""] {
            let parent = if own == "\"\"" { "1" } else { "\"parent\"" };
            let src =
                format!("local C = {{}} C.__index = C C.x = {parent} local child = {{x = {own}}} local value = child.x print(child, C)");
            fixture(&src, |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                good(checker);
                assert!(checker.info.record_lookups.values().all(|p| p.fallback.is_none() && !p.may_miss));
            });
        }
    }

    #[test]
    fn own_writes_are_separate_and_nil_reads_still_have_a_missing_path() {
        fixture("local C = {} C.__index = C C.flag = true local child = {flag = false} local alias = child alias.flag = nil local value = child.flag local missing = child.absent print(child, C)", |checker, unit| {
            attach_marker(checker, unit);
            finish(checker);
            good(checker);
            let child = tab(checker, "child");
            let own = checker.st.tab(child).fields["flag"];
            let parent = checker.st.tab(tab(checker, "C")).fields["flag"];
            assert!(checker.st.is_null(own.null));
            assert!(!checker.st.is_null(parent.null));
            assert!(checker.info.record_lookups.values().any(|p| p.own == Some(own) && p.fallback.is_some()));
            assert!(!checker.st.tab(child).fields.contains_key("absent"));
            assert!(checker.info.record_lookups.values().any(|p| p.own.is_none() && p.fallback.is_none() && p.may_miss));
        });
    }

    #[test]
    fn parent_edge_survives_unions_in_both_directions_and_compatible_reattachment() {
        for reverse in [false, true] {
            fixture(
                "local C = {} C.__index = C C.x = 7 local child = {} local plain = {} print(child, C)",
                |checker, unit| {
                    attach_marker(checker, unit);
                    checker.solve_pending();
                    let (child_ty, plain_ty) = (slot(checker, "child").ty, slot(checker, "plain").ty);
                    let class = tab(checker, "C");
                    let (a, b) = if reverse { (plain_ty, child_ty) } else { (child_ty, plain_ty) };
                    assert!(checker.unify(a, b, Span::default()));
                    assert_eq!(checker.st.tab(tab(checker, "plain")).parent, Some(class));
                    let second = checker.st.new_tab(TKind::Record, Span::default());
                    let second_ty = checker.table_ty(second);
                    let index = checker.st.slot(second_ty);
                    checker.st.tab_mut(second).fields.insert("__index".into(), index);
                    assert!(checker.unify_tabs(class, second, Span::default()));
                    checker.validate_record_parents();
                    good(checker);
                    assert_eq!(
                        checker.st.tab_root(checker.st.tab(tab(checker, "child")).parent.expect("parent")),
                        checker.st.tab_root(second)
                    );
                },
            );
        }
    }

    #[test]
    fn preflight_rejects_parent_child_union_without_linking_either_root() {
        fixture("local C = {} C.__index = C local child = {} print(child, C)", |checker, unit| {
            attach_marker(checker, unit);
            checker.solve_pending();
            let (child, class) = (tab(checker, "child"), tab(checker, "C"));
            assert!(!checker.unify(slot(checker, "child").ty, slot(checker, "C").ty, Span::default()));
            assert_eq!(checker.st.tab_root(child), child);
            assert_eq!(checker.st.tab_root(class), class);
            assert!(checker.errors.iter().any(|e| e.msg == CYCLE));
        });
    }

    #[test]
    fn late_chain_and_native_or_container_promotion_are_diagnosed() {
        for kind in [TKind::Array, TKind::Map] {
            fixture("local C = {} C.__index = C local child = {} print(child, C)", |checker, unit| {
                attach_marker(checker, unit);
                checker.solve_pending();
                let other = checker.st.new_tab(kind, Span::default());
                let ty = checker.table_ty(other);
                assert!(!checker.unify(slot(checker, "child").ty, ty, Span::default()));
                assert!(checker
                    .errors
                    .iter()
                    .any(|e| e.msg == "setmetatable does not support arrays or maps"));
            });
        }
        fixture("local C = {} C.__index = C local child = {} print(child, C)", |checker, unit| {
            attach_marker(checker, unit);
            checker.solve_pending();
            let other = checker.st.new_tab(TKind::Record, Span::default());
            let grandparent = checker.st.new_tab(TKind::Record, Span::default());
            checker.st.tab_mut(other).parent = Some(grandparent);
            assert!(!checker.unify_tabs(tab(checker, "C"), other, Span::default()));
            assert!(checker.errors.iter().any(|e| e.msg == CHAIN));
        });
        fixture("local C = {} C.__index = C local child = {} print(child, C)", |checker, unit| {
            attach_marker(checker, unit);
            checker.solve_pending();
            let other = checker.st.new_tab(TKind::Record, Span::default());
            checker.st.tab_mut(other).native = Some(crate::check_native::NativeRec::Tuple(0));
            assert!(!checker.unify_tabs(tab(checker, "child"), other, Span::default()));
            assert!(checker.errors.iter().any(|e| e.msg == NATIVE));
        });
    }

    #[test]
    fn finish_rechecks_clone_native_links_and_new_metamethod_fields() {
        fixture(
            "local C = {} C.__index = C local child = {} local copy = table.clone(child) print(child, C)",
            |checker, unit| {
                attach_marker(checker, unit);
                finish(checker);
                assert!(
                    checker
                        .errors
                        .iter()
                        .any(|e| e.msg == "table.clone on records with a static parent type is not supported in step 1"),
                    "{:?}",
                    checker.errors
                );
            },
        );
        for native in [false, true] {
            fixture("local C = {} C.__index = C local child = {} print(child, C)", |checker, unit| {
                attach_marker(checker, unit);
                checker.solve_pending();
                let class = tab(checker, "C");
                if native {
                    checker.st.tab_mut(class).native = Some(crate::check_native::NativeRec::Tuple(0));
                } else {
                    let ty = checker.prim(TyNode::Num);
                    let slot = checker.st.slot(ty);
                    checker.st.tab_mut(class).fields.insert("__newindex".into(), slot);
                }
                checker.finish();
                let expected = if native {
                    NATIVE
                } else {
                    "metamethod '__newindex' is not supported in this step"
                };
                assert!(checker.errors.iter().any(|e| e.msg == expected), "{:?}", checker.errors);
            });
        }
    }
}
