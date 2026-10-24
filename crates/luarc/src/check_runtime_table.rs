//! Selective runtime-table checking; static __index records keep their path.

use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::ast_walk::{self, VisitMut};
use crate::check::*;
use crate::diag::Span;
use crate::resolve::{Builtin, Res};
use crate::types::*;

#[derive(Clone, Debug)]
pub enum RuntimeCall {
    Attach,
    RawGet(Option<String>),
    RawSet,
    RawEqual,
    RawLen,
    GetMetatable,
    Invoke,
    ToString,
    Print,
    Clone,
    Create,
}

#[derive(Default)]
pub struct RuntimeInfo {
    pub constructors: HashSet<NodeId>,
    pub function_values: HashSet<NodeId>,
    pub callbacks: HashSet<NodeId>,
    pub safe_boxed: HashSet<NodeId>,
    pub parameter_tables: HashMap<NodeId, HashSet<usize>>,
    pub calls: HashMap<NodeId, RuntimeCall>,
    pub outputs: HashMap<NodeId, Vec<ETy>>,
    pub lengths: HashSet<NodeId>,
    pub metamethods: HashMap<TabId, TabId>,
    pub metadata_writes: HashSet<TabId>,
    pub iterator_proofs: HashSet<TabId>,
    pub may_sparse: HashSet<TabId>,
    pub index_keys: HashMap<NodeId, NodeId>,
    pub binary: HashSet<NodeId>,
    pub enabled: bool,
    pub narrowing: bool,
}

struct Region<'a> {
    res: &'a crate::resolve::Resolution,
    tables: Vec<NodeId>,
    children: Vec<FuncBody>,
    roles: Vec<(NodeId, String)>,
    selected: bool,
    table_tests: HashSet<crate::resolve::SymId>,
    fields: HashSet<crate::resolve::SymId>,
}

fn method_name(e: &Expr) -> Option<&str> {
    match &e.kind {
        ExprKind::Field(_, name) => Some(&name.text),
        ExprKind::Index(_, key) => match &key.kind {
            ExprKind::Str(s) => std::str::from_utf8(s).ok(),
            _ => None,
        },
        _ => None,
    }
}

fn advanced(name: &str) -> bool {
    matches!(name, "__newindex" | "__add" | "__sub" | "__mul" | "__div" | "__idiv" | "__mod" | "__pow" | "__unm" | "__eq" | "__lt" | "__le" | "__call" | "__concat" | "__tostring" | "__len" | "__iter")
}

impl Region<'_> {
    fn role(&mut self, name: &str, value: &Expr) {
        if let ExprKind::Function(f) = &value.kind {
            if advanced(name) {
                self.selected = true;
                self.roles.push((f.id, name.to_string()));
            }
        }
        if advanced(name) {
            if let ExprKind::Name(value) = &value.kind {
                if let Some(Res::Local(sym)) = self.res.res(value.id) {
                    if let Some(function) = self.res.sym(sym).func_body {
                        self.selected = true;
                        self.roles.push((function, name.to_string()));
                    }
                }
            }
        }
        if name == "__metatable" { self.selected = true; }
    }
}

impl VisitMut for Region<'_> {
    fn func(&mut self, function: &mut FuncBody) {
        self.children.push(function.clone());
        // Each lexical function is analyzed independently, so a feature in one
        // benchmark callback does not promote the other callbacks' tables.
        function.body.stats.clear();
    }

    fn stat(&mut self, stat: &mut Stat) {
        match &stat.kind {
            StatKind::Assign(targets, values) => {
                for (target, value) in targets.iter().zip(values) {
                    if let Some(name) = method_name(target) { self.role(name, value); }
                }
            }
            StatKind::Function(target, function) => {
                if let Some(name) = method_name(target) {
                    if advanced(name) {
                        self.selected = true;
                        self.roles.push((function.id, name.to_string()));
                    }
                }
            }
            _ => {}
        }
    }

    fn expr(&mut self, expr: &mut Expr) {
        match &expr.kind {
            ExprKind::Table(items) => {
                self.tables.push(expr.id);
                for item in items {
                    match item {
                        TableItem::Named(name, value) => self.role(&name.text, value),
                        TableItem::Keyed(key, value) => {
                            if let ExprKind::Str(s) = &key.kind {
                                if let Ok(name) = std::str::from_utf8(s) { self.role(name, value); }
                            }
                        }
                        _ => {}
                    }
                }
            }
            ExprKind::Call(callee, _) => {
                if matches!(&callee.kind, ExprKind::Field(lib, name) if is_lib(lib, self.res) == Some(Builtin::Table) && matches!(name.text.as_str(), "create" | "clone")) {
                    self.tables.push(expr.id);
                }
                if matches!(&callee.kind, ExprKind::Field(lib, name) if is_lib(lib, self.res) == Some(Builtin::Table) && matches!(name.text.as_str(), "freeze" | "isfrozen" | "move")) {
                    self.selected = true;
                }
                if is_lib(callee, self.res) == Some(Builtin::RawSet) { self.selected = true; }
            }
            ExprKind::Binary(BinOp::Eq | BinOp::Ne, a, b) => {
                let (call, literal) = match (&a.kind, &b.kind) {
                    (ExprKind::Call(..), ExprKind::Str(_)) => (a, b),
                    (ExprKind::Str(_), ExprKind::Call(..)) => (b, a), _ => return,
                };
                if !matches!(&literal.kind, ExprKind::Str(s) if s == b"table") { return; }
                if let ExprKind::Call(callee, args) = &call.kind {
                    if is_lib(callee, self.res) == Some(Builtin::Type) {
                        if let Some(Expr { kind: ExprKind::Name(name), .. }) = args.first() {
                            if let Some(Res::Local(sym)) = self.res.res(name.id) { self.table_tests.insert(sym); }
                        }
                    }
                }
            }
            ExprKind::Field(obj, _) | ExprKind::Index(obj, _) => {
                if let ExprKind::Name(name) = &obj.kind {
                    if let Some(Res::Local(sym)) = self.res.res(name.id) { self.fields.insert(sym); }
                }
            }
            _ => {}
        }
    }
}

impl<'a> Checker<'a> {
    pub(crate) fn unify_runtime_tables(&mut self, left: TabId, right: TabId, span: Span) -> bool {
        let (left, right) = (self.st.tab_root(left), self.st.tab_root(right));
        let (left_runtime, right_runtime) = (self.st.tab(left).runtime, self.st.tab(right).runtime);
        if left_runtime != right_runtime {
            let (plain, dynamic) = if left_runtime { (right, left) } else { (left, right) };
            let plain_table = self.st.tab(plain);
            if !plain_table.ctors.is_empty() || !plain_table.fields.is_empty() || plain_table.closed || plain_table.native.is_some() {
                self.error(span, "a static table cannot flow into a runtime-table slot (its producer must use the runtime representation)");
                return false;
            }
            self.st.tabs[plain as usize].link = Some(dynamic);
            return true;
        }
        let previous = self.st.tab(left).clone();
        self.st.tabs[left as usize].link = Some(right);
        for (name, slot) in previous.fields {
            self.st.tab_mut(right).fields.entry(name).or_insert(slot);
        }
        if self.st.tab(right).elem.is_none() { self.st.tab_mut(right).elem = previous.elem; }
        true
    }

    pub(crate) fn runtime_invoke(&mut self, expr: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        for arg in args {
            if matches!(arg.kind, ExprKind::Call(..) | ExprKind::Method(..) | ExprKind::Vararg) {
                self.error(arg.span, "runtime-table calls require explicit single-value arguments (parenthesize a call to select its first result)");
            }
            let value = self.expr(arg);
            if self.runtime_has_table_data(value.ty) {
                self.error(arg.span, "runtime callbacks cannot receive tables with statically tracked nested-table data");
            }
            self.runtime_box(arg, value);
        }
        let outputs = match want {
            Some(count) => (0..count).map(|_| self.any_val()).collect(),
            None => {
                let any = self.any_val();
                self.info.pack_calls.insert(expr.id, any);
                vec![]
            }
        };
        self.runtime_out(expr, RuntimeCall::Invoke, outputs, want)
    }

    pub(crate) fn prepare_runtime_tables(&mut self, units: &[ModuleUnit]) {
        for unit in units { self.runtime_region(&unit.module.body, false); }
    }

    fn runtime_region(&mut self, block: &Block, inherited: bool) {
        let mut block = block.clone();
        let mut scan = Region { res: self.res, tables: Vec::new(), children: Vec::new(), roles: Vec::new(), selected: inherited, table_tests: HashSet::new(), fields: HashSet::new() };
        ast_walk::walk_block(&mut scan, &mut block);
        self.info.runtime_tables.narrowing |= !scan.table_tests.is_disjoint(&scan.fields);
        scan.selected |= !scan.table_tests.is_disjoint(&scan.fields);
        if scan.selected {
            self.info.runtime_tables.enabled = true;
            self.info.runtime_tables.constructors.extend(scan.tables);
            for (function, role) in scan.roles {
                self.info.runtime_functions.insert(function);
                self.info.runtime_tables.callbacks.insert(function);
                let tables: &[usize] = match role.as_str() {
                    "__eq" | "__lt" | "__le" => &[0, 1],
                    "__newindex" | "__call" | "__tostring" | "__len" | "__unm" | "__iter" => &[0],
                    _ => &[],
                };
                self.info.runtime_tables.parameter_tables.insert(function, tables.iter().copied().collect());
            }
        }
        for function in scan.children { self.runtime_region(&function.body, scan.selected); }
    }

    pub(crate) fn runtime_type(&self, ty: TyId) -> bool {
        matches!(self.st.node(ty), TyNode::Table(tab) if self.st.tab(*tab).runtime)
    }

    fn runtime_has_table_data(&self, ty: TyId) -> bool {
        let TyNode::Table(tab) = self.st.node(ty) else { return false };
        self.st.tab(*tab).runtime && (self.st.tab(*tab).elem.is_some_and(|slot| self.runtime_type(slot.ty))
            || self.st.tab(*tab).fields.iter().any(|(name, slot)| !name.starts_with("__") && self.runtime_type(slot.ty)))
    }

    pub(crate) fn runtime_metatable(&self, tab: TabId) -> Option<TabId> {
        let root = self.st.tab_root(tab);
        self.info.runtime_tables.metamethods.iter().find_map(|(child, meta)| {
            (self.st.tab_root(*child) == root).then_some(self.st.tab_root(*meta))
        })
    }

    pub fn runtime_iterator_results(&mut self, tab: TabId) -> Option<Vec<ETy>> {
        let meta = self.runtime_metatable(tab)?;
        if self.info.runtime_tables.metadata_writes.iter().any(|written| self.st.tab_root(*written) == meta) { return None; }
        let factory = self.st.tab(meta).fields.get("__iter")?;
        let TyNode::Func(factory) = self.st.node(factory.ty) else { return None };
        let iterator = self.st.rets_known(factory.rets)?.first()?;
        let TyNode::Func(iterator) = self.st.node(iterator.ty) else { return None };
        let results = self.st.rets_known(iterator.rets)?.iter().map(|slot| ETy { ty: slot.ty, null: slot.null, soft: Soft::Yes }).collect();
        self.info.runtime_tables.iterator_proofs.insert(tab);
        Some(results)
    }

    pub(crate) fn prepare_runtime_sort_callback(&mut self, table: ETy, callback: &Expr) {
        if !self.runtime_type(table.ty) { return; }
        self.check_runtime_length(table, callback.span, false);
        let ExprKind::Function(function) = &callback.kind else { return };
        self.info.runtime_functions.insert(function.id);
        self.info.runtime_tables.callbacks.insert(function.id);
        if matches!(self.st.node(table.ty), TyNode::Table(tab) if self.st.tab(*tab).elem.is_some_and(|slot| self.runtime_type(slot.ty))) {
            self.info.runtime_tables.parameter_tables.insert(function.id, [0, 1].into_iter().collect());
        }
    }

    pub(crate) fn runtime_value(&mut self, span: Span) -> ETy {
        let (ty, tab) = self.new_table_var(span);
        self.st.tab_mut(tab).runtime = true;
        self.st.tab_mut(tab).kind = TKind::Record;
        self.val(ty)
    }

    pub(crate) fn runtime_parameter(&mut self, function: &FuncBody, index: usize) -> Option<Slot> {
        if !self.info.runtime_functions.contains(&function.id) { return None; }
        let param = &function.params[index];
        if param.ty.is_some() { return None; }
        let value = if self.info.runtime_tables.parameter_tables.get(&function.id).is_some_and(|set| set.contains(&index)) {
            self.runtime_value(param.name.span)
        } else { self.any_val() };
        Some(self.st.slot(value.ty))
    }

    pub(crate) fn runtime_box(&mut self, expr: &Expr, value: ETy) {
        if matches!(self.st.node(value.ty), TyNode::Func(_)) {
            self.info.runtime_tables.function_values.insert(expr.id);
        }
        let any = self.any_val();
        self.flow_node(Some(expr.id), value, Slot { ty: any.ty, null: any.null }, expr.span);
    }

    pub(crate) fn runtime_constructor(&mut self, expr: &Expr, items: &[TableItem]) -> ETy {
        let value = self.runtime_value(expr.span);
        let TyNode::Table(tab) = self.st.node(value.ty).clone() else { return value };
        let mut names = Vec::new();
        let mut table_element: Option<Slot> = None;
        let mut only_table_elements = true;
        for (position, item) in items.iter().enumerate() {
            match item {
                TableItem::Named(name, expr) => {
                    let item = self.expr(expr);
                    self.runtime_box(expr, item);
                    let slot = self.st.slot(item.ty);
                    self.st.edge(item.null, slot.null, expr.span);
                    self.st.tab_mut(tab).fields.insert(name.text.clone(), slot);
                    names.push(name.text.clone());
                }
                TableItem::Keyed(key, expr) => {
                    let k = self.expr(key);
                    self.runtime_box(key, k);
                    let item = self.expr(expr);
                    self.runtime_box(expr, item);
                    if let ExprKind::Str(s) = &key.kind {
                        if let Ok(name) = std::str::from_utf8(s) {
                            let slot = self.st.slot(item.ty);
                            self.st.edge(item.null, slot.null, expr.span);
                            self.st.tab_mut(tab).fields.insert(name.to_string(), slot);
                            names.push(name.to_string());
                        }
                    } else { self.info.runtime_tables.may_sparse.insert(tab); }
                }
                TableItem::Pos(expr) => {
                    if position + 1 == items.len() && matches!(expr.kind, ExprKind::Call(..) | ExprKind::Method(..) | ExprKind::Vararg) {
                        self.error(expr.span, "call tails in runtime-table constructors are not supported yet (use the nil-preserving pack representation)");
                    }
                    let item = self.expr(expr);
                    self.runtime_box(expr, item);
                    if self.runtime_type(item.ty) {
                        match table_element {
                            Some(slot) => { self.unify(slot.ty, item.ty, expr.span); }
                            None => {
                                let slot = self.st.slot(item.ty);
                                self.st.edge(item.null, slot.null, expr.span);
                                table_element = Some(slot);
                            }
                        }
                    } else { only_table_elements = false; }
                    if self.st.is_null(item.null) { self.info.runtime_tables.may_sparse.insert(tab); }
                }
            }
        }
        if only_table_elements { self.st.tab_mut(tab).elem = table_element; }
        self.st.tab_mut(tab).ctors.push(names);
        value
    }

    pub(crate) fn runtime_access(&mut self, node: NodeId, obj: ETy, name: Option<&str>, result: ETy, write: Option<ETy>, span: Span) -> bool {
        if !self.runtime_type(obj.ty) { return false; }
        self.info.access.insert(node, Access::Runtime);
        let TyNode::Table(tab) = self.st.node(obj.ty).clone() else { return false };
        let known = name.and_then(|name| self.st.tab(tab).fields.get(name).copied())
            .or_else(|| if name.is_none() { self.st.tab(tab).elem } else { None });
        let known = known.filter(|slot| self.runtime_type(slot.ty) && name.is_none_or(|name| !name.starts_with("__")));
        let any = self.any_val();
        if let Some(slot) = known {
            self.link_result(result, ETy { ty: slot.ty, null: slot.null, soft: Soft::Yes }, span);
        } else { self.link_result(result, any, span); }
        if let Some(value) = write {
            if name.is_none_or(|name| matches!(name, "__iter" | "__len")) {
                self.info.runtime_tables.metadata_writes.insert(tab);
            }
            let source = self.dynamic.write_nodes.get(&node).copied();
            if let Some(source) = source {
                if matches!(self.st.node(value.ty), TyNode::Func(_)) { self.info.runtime_tables.function_values.insert(source); }
                if let Some(slot) = known { self.flow_node(Some(source), value, slot, span); }
                else { self.flow_node(Some(source), value, Slot { ty: any.ty, null: any.null }, span); }
            }
            if let TyNode::Table(tab) = self.st.node(obj.ty).clone() {
                if let Some(name) = name {
                    self.st.tab_mut(tab).fields.insert(name.to_string(), Slot { ty: value.ty, null: value.null });
                } else { self.info.runtime_tables.may_sparse.insert(self.st.tab_root(tab)); }
            }
        }
        true
    }

    pub(crate) fn runtime_out(&mut self, expr: &Expr, call: RuntimeCall, outputs: Vec<ETy>, want: Option<usize>) -> Vec<ETy> {
        self.info.calls.insert(expr.id, CallKind::Value);
        self.info.runtime_tables.calls.insert(expr.id, call);
        self.info.runtime_tables.outputs.insert(expr.id, outputs.clone());
        let mut adjusted = outputs;
        if let Some(want) = want {
            adjusted.truncate(want);
            while adjusted.len() < want { adjusted.push(self.nil()); }
        }
        adjusted
    }

    pub(crate) fn runtime_attach(&mut self, expr: &Expr, args: &[Expr], values: &[ETy], want: Option<usize>) -> Option<Vec<ETy>> {
        let child = *values.first()?;
        if !self.runtime_type(child.ty) { return None; }
        if self.runtime_has_table_data(child.ty) {
            self.error(args[0].span, "runtime metatables on tables with statically tracked nested-table data are unsupported");
        }
        if args.len() < 2 {
            self.error(expr.span, "setmetatable requires two explicit source arguments");
        } else if !matches!(args[1].kind, ExprKind::Nil) {
            if !self.runtime_type(values[1].ty) {
                self.error(args[1].span, "runtime metatables require a runtime table (the metatable producer must use the runtime representation)");
            } else if let (TyNode::Table(child), TyNode::Table(meta)) = (self.st.node(child.ty).clone(), self.st.node(values[1].ty).clone()) {
                self.info.runtime_tables.metamethods.insert(self.st.tab_root(child), self.st.tab_root(meta));
            }
        }
        Some(self.runtime_out(expr, RuntimeCall::Attach, vec![child], want))
    }

    pub(crate) fn runtime_builtin(&mut self, expr: &Expr, builtin: Builtin, args: &[Expr], want: Option<usize>) -> Option<Vec<ETy>> {
        let call = match builtin {
            Builtin::RawGet => RuntimeCall::RawGet(None), Builtin::RawSet => RuntimeCall::RawSet,
            Builtin::RawEqual => RuntimeCall::RawEqual, Builtin::RawLen => RuntimeCall::RawLen,
            Builtin::GetMetatable => RuntimeCall::GetMetatable, _ => return None,
        };
        let values: Vec<_> = args.iter().map(|arg| self.expr(arg)).collect();
        let required = match builtin { Builtin::RawSet => 3, Builtin::RawGet | Builtin::RawEqual => 2, _ => 1 };
        if args.len() < required {
            self.error(expr.span, format!("runtime table operation expects at least {required} arguments, got {}", args.len()));
            return Some(vec![self.fresh_result(); want.unwrap_or(1)]);
        }
        let output = match builtin {
            Builtin::RawEqual => {
                self.info.runtime_tables.safe_boxed.extend(args.iter().take(2).map(|arg| arg.id));
                self.runtime_box(&args[0], values[0]); self.runtime_box(&args[1], values[1]); self.bool_()
            }
            Builtin::RawGet => {
                self.runtime_box(&args[1], values[1]);
                if !self.runtime_type(values[0].ty) {
                    let (TyNode::Table(tab), ExprKind::Str(key)) = (self.st.node(values[0].ty).clone(), &args[1].kind) else {
                        self.error(args[0].span, "rawget requires a runtime table or a static record with a literal string key");
                        return Some(vec![self.fresh_result(); want.unwrap_or(1)]);
                    };
                    if self.st.tab(tab).kind != TKind::Record {
                        self.error(args[0].span, "rawget on a static array or map is not supported yet");
                    }
                    let name = String::from_utf8_lossy(key).into_owned();
                    let any = self.any_val();
                    return Some(self.runtime_out(expr, RuntimeCall::RawGet(Some(name)), vec![any], want));
                }
                self.any_val()
            }
            Builtin::RawSet => {
                if !self.runtime_type(values[0].ty) { self.error(args[0].span, "rawset requires a runtime table (its producer must use the runtime representation)"); }
                self.runtime_box(&args[1], values[1]); self.runtime_box(&args[2], values[2]);
                if let TyNode::Table(tab) = self.st.node(values[0].ty).clone() {
                    let field = match &args[1].kind { ExprKind::Str(name) => String::from_utf8(name.clone()).ok(), _ => None };
                    if field.as_deref().is_none_or(|name| matches!(name, "__iter" | "__len")) {
                        self.info.runtime_tables.metadata_writes.insert(tab);
                    }
                    let constrained = self.st.tab(tab).fields.iter().any(|(name, slot)| self.runtime_type(slot.ty) && field.as_ref().is_none_or(|field| field == name));
                    if constrained && !self.runtime_type(values[2].ty) && !matches!(self.st.node(values[2].ty), TyNode::Nil) {
                        self.error(args[2].span, "rawset cannot replace a known runtime-table field with an opaque or non-table value");
                    }
                }
                if !matches!(args[1].kind, ExprKind::Str(_)) {
                    if let TyNode::Table(tab) = self.st.node(values[0].ty) { self.info.runtime_tables.may_sparse.insert(self.st.tab_root(*tab)); }
                }
                values[0]
            }
            Builtin::RawLen => {
                match self.st.node(values[0].ty) {
                    TyNode::Str => {}
                    TyNode::Table(tab) if self.st.tab(*tab).runtime || matches!(self.st.tab(*tab).kind, TKind::Array | TKind::Record) => {}
                    _ => self.error(args[0].span, "rawlen requires a string, a static array/record or a known runtime table"),
                }
                self.check_runtime_length(values[0], expr.span, false); self.num()
            }
            Builtin::GetMetatable => {
                if !matches!(self.st.node(values[0].ty), TyNode::Table(_)) { self.error(args[0].span, "getmetatable requires a table in this version of luarc"); }
                if self.info.runtime_tables.narrowing && !self.runtime_type(values[0].ty) {
                    self.error(args[0].span, "table narrowing of getmetatable requires a runtime-table producer");
                }
                self.any_val()
            }
            _ => return None,
        };
        Some(self.runtime_out(expr, call, vec![output], want))
    }

    pub(crate) fn check_runtime_length(&mut self, _value: ETy, _span: Span, _allow_method: bool) {
        // Runtime tables carry Luau allocation and boundary history. Sparse
        // storage and later metadata writes no longer require a dense proof.
    }

    /// Check a manually boxed value without requiring an expression ID (packs and
    /// coroutine bridges can box several results from one source expression).
    /// `erased_function` means the bridge uses IntoDynamic rather than ToValue.
    pub(crate) fn validate_runtime_manual_box(&mut self, ty: TyId, span: Span, erased_function: bool) {
        if !self.info.runtime_tables.enabled { return; }
        self.validate_runtime_manual_box_inner(ty, span, erased_function, &mut HashSet::new());
    }

    fn validate_runtime_manual_box_inner(&mut self, ty: TyId, span: Span, erased_function: bool, seen: &mut HashSet<TyId>) {
        if !seen.insert(self.st.root(ty)) { return; }
        match self.st.node(ty).clone() {
            TyNode::FalseOr(inner) => self.validate_runtime_manual_box_inner(inner, span, erased_function, seen),
            TyNode::Pcall(slot) => self.validate_runtime_manual_box_inner(slot.ty, span, erased_function, seen),
            TyNode::Func(function) => {
                if !erased_function {
                    self.error(span, "opaque typed functions manually boxed into any cannot be used with runtime-table features");
                } else {
                    // The bridge validates its own argument/result ABI. This gate
                    // checks only the provenance of values it exposes dynamically.
                    let results = self.st.rets_known(function.rets).cloned().unwrap_or_default();
                    for result in results { self.validate_runtime_manual_box_inner(result.ty, span, true, seen); }
                    if let Some(tail) = self.st.rets_tail(function.rets) {
                        self.validate_runtime_manual_box_inner(tail.ty, span, true, seen);
                    }
                }
            }
            TyNode::Table(_) => {
                if self.runtime_has_table_data(ty) {
                    self.error(span, "tables with statically tracked nested-table data cannot be manually boxed into any");
                }
                if self.info.runtime_tables.narrowing && !self.runtime_type(ty) {
                    self.error(span, "table narrowing from any requires runtime-table producers; a static table is manually boxed here");
                }
            }
            _ => {}
        }
    }

    /// Runtime print uses Value formatting, but its arguments do not escape into
    /// user code. Check the conversion without applying escaping-value rules.
    pub(crate) fn runtime_printable(&mut self, ty: TyId, span: Span) {
        match self.st.node(ty).clone() {
            TyNode::Pcall(slot) => self.runtime_printable(slot.ty, span),
            _ => { self.boxable(ty, span); }
        }
    }
    pub(crate) fn validate_runtime_provenance(&mut self) {
        for tab in self.info.runtime_tables.iterator_proofs.clone() {
            if self.runtime_metatable(tab).is_some_and(|meta| self.info.runtime_tables.metadata_writes.iter().any(|written| self.st.tab_root(*written) == meta)) {
                self.error(Span::default(), "runtime iterator result proof is invalidated by a dynamic metatable write");
            }
        }
        if !self.info.runtime_tables.enabled { return; }
        for (ty, span) in self.info.packs.boxed.clone() {
            self.validate_runtime_manual_box(ty, span, false);
        }
        let mut functions: Vec<_> = self.info.runtime_tables.function_values.iter().filter_map(|node| self.info.expr.get(node).map(|v| v.ty)).collect();
        functions.extend(self.info.runtime_tables.callbacks.iter().filter_map(|id| self.info.funcs.get(id).copied()));
        let mut seen = HashSet::new();
        for ty in functions { self.validate_runtime_function(ty, &mut seen); }
        if self.info.runtime_tables.enabled {
            let casts: Vec<_> = self.info.dynamic.casts.iter().filter_map(|(node, kind)| {
                matches!(kind, crate::check_dynamic::CastKind::FromAny { .. }).then_some(*node)
            }).collect();
            for node in casts {
                if self.info.expr.get(&node).is_some_and(|value| matches!(self.st.node(value.ty), TyNode::Func(_))) {
                    self.error(Span::default(), "casts from any to typed functions are unsupported with erased runtime-table callbacks");
                }
            }
            let boxed: Vec<_> = self.info.dynamic.boxed.iter().copied().collect();
            for node in boxed {
                if let Some(value) = self.info.expr.get(&node).copied() {
                    if matches!(self.st.node(value.ty), TyNode::Pcall(_) | TyNode::FalseOr(_)) {
                        // Protected/conditional results use ToValue on their payload, retaining its provenance limits.
                        self.validate_runtime_manual_box(value.ty, Span::default(), false);
                    }
                }
                if !self.info.runtime_tables.safe_boxed.contains(&node) && self.info.expr.get(&node).is_some_and(|value| self.runtime_has_table_data(value.ty)) {
                    self.error(Span::default(), "tables with statically tracked nested-table data cannot flow into any");
                }
                if !self.info.runtime_tables.function_values.contains(&node)
                    && self.info.expr.get(&node).is_some_and(|value| matches!(self.st.node(value.ty), TyNode::Func(_)))
                {
                    self.error(Span::default(), "opaque typed functions flowing into any cannot be used with runtime-table features; pass a direct function to the metatable instead");
                }
            }
        }
        if self.info.runtime_tables.narrowing {
            let boxed: Vec<_> = self.info.dynamic.boxed.iter().copied().collect();
            for node in boxed {
                if let Some(value) = self.info.expr.get(&node).copied() {
                    if matches!(self.st.node(value.ty), TyNode::Table(_)) && !self.runtime_type(value.ty) {
                        self.error(Span::default(), "table narrowing from any requires runtime-table producers; a static table flows into any here (use a runtime-table producer or an explicit static cast)");
                    }
                }
            }
        }
    }

    pub(crate) fn validate_runtime_function(&mut self, ty: TyId, seen: &mut HashSet<TyId>) {
        if !self.info.runtime_tables.enabled { return; }
        let root = self.st.root(ty);
        if !seen.insert(root) { return; }
        let TyNode::Func(function) = self.st.node(root).clone() else { return };
        let span = Span::default();
        if function.params.len() > 8 || function.vararg.is_some() && function.params.len() > 7 {
            self.error(span, "runtime-table callbacks support at most eight fixed parameters (seven with varargs)");
        }
        for param in &function.params {
            if !self.runtime_type(param.ty) && !matches!(self.st.node(param.ty), TyNode::Any) {
                self.error(span, "runtime-table callback parameters must be unannotated dynamic values or known runtime tables");
            }
        }
        if function.vararg.is_some_and(|slot| !matches!(self.st.node(slot.ty), TyNode::Any)) {
            self.error(span, "runtime-table callback varargs require dynamic any elements");
        }
        let returns = self.st.rets_known(function.rets).cloned().unwrap_or_default();
        if returns.len() > 8 || self.st.rets_tail(function.rets).is_some() && returns.len() > 7 {
            self.error(span, "runtime-table callbacks support at most eight fixed results (seven with a result tail)");
        }
        if self.st.rets_tail(function.rets).is_some_and(|slot| !matches!(self.st.node(slot.ty), TyNode::Any)) {
            self.error(span, "runtime-table callback result tails require dynamic any elements");
        }
        for slot in returns {
            match self.st.node(slot.ty).clone() {
                TyNode::Func(_) => self.validate_runtime_function(slot.ty, seen),
                TyNode::Table(_) if self.runtime_type(slot.ty) => {
                    if self.runtime_has_table_data(slot.ty) {
                        self.error(span, "runtime callback results cannot expose statically tracked nested-table data");
                    }
                }
                TyNode::Table(tab) if self.st.tab(tab).kind == TKind::Array && !self.info.runtime_tables.narrowing => {}
                TyNode::Table(_) => self.error(span, "runtime-table callback table results require runtime-table producers (static records/maps and narrowed static arrays are unsupported)"),
                TyNode::Any | TyNode::Num | TyNode::NumVar | TyNode::Str | TyNode::Bool | TyNode::Nil => {}
                TyNode::Var if self.st.is_null(slot.null) => {}
                _ => self.error(span, "runtime-table callback result type has no dynamic adapter"),
            }
        }
    }
}
