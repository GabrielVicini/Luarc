//! General static record metadata and chained lookup.

use std::collections::{HashMap, HashSet};

use crate::ast::NodeId;
use crate::check::{Checker, ModuleUnit, Op};
use crate::check_metatable::{ClassSyntax, RecordLookup};
use crate::diag::Span;
use crate::types::*;

const INDEX: &str = "setmetatable __index must have a statically known record type";
const ARRAY: &str = "setmetatable does not support arrays or maps";
const NATIVE: &str = "metatables on native-converted records are not supported in this step";
const CYCLE: &str = "cyclic static record parent types are not supported";
const META_CYCLE: &str = "cyclic static metatable type expansion is not supported";
const DEPTH: &str = "static record parent chains must have fewer than 100 links";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupLevel {
    pub tab: TabId,
    pub own: Option<Slot>,
    pub metadata: Option<(TabId, Option<Slot>)>,
}

impl<'a> Checker<'a> {
    pub(crate) fn activate_general_record_metatables(&mut self) {
        if self.metatables.general {
            return;
        }
        self.metatables.general = true;
        // Preserve the original class attachments when a late chain or clone selects live metadata.
        for (node, child, class, span) in self.metatables.attachments.clone() {
            if let Some(slot) = self.info.sym_slot.get(&class).copied() {
                self.general_record_parent(node, child, self.of_slot(slot), span);
            }
        }
    }

    /// Explicit general checker entry point for type and graph tests.
    pub fn prepare_general_record_metatables(&mut self, units: &[ModuleUnit]) {
        self.metatables.enabled = true;
        self.metatables.general = true;
        self.metatables.syntax = ClassSyntax::analyze(self.res, units);
    }

    pub(crate) fn general_record_parent(
        &mut self,
        node: NodeId,
        child: ETy,
        metatable: ETy,
        span: Span,
    ) {
        self.metatables
            .general_attachments
            .push((node, child, metatable, span));
        self.info
            .record_attachments
            .insert(node, (child, metatable));
        self.try_or_defer(Op::RecordMetatable {
            node,
            child,
            metatable,
            span,
        });
    }

    pub(crate) fn attempt_record_metatable(
        &mut self,
        _node: NodeId,
        child: ETy,
        metatable: ETy,
        span: Span,
    ) -> bool {
        let mut roles = Vec::new();
        for (value, message) in [
            (
                child,
                "setmetatable requires a statically known record as its first argument",
            ),
            (
                metatable,
                "setmetatable requires a statically known record as its second argument",
            ),
        ] {
            match self.st.node(value.ty) {
                TyNode::Var => return false,
                TyNode::Table(tab) => roles.push(self.st.tab_root(*tab)),
                _ => {
                    self.error(span, message);
                    return true;
                }
            }
        }
        let (child, metatable) = (roles[0], roles[1]);
        for role in roles {
            if !self.general_record_role(role, span) {
                return true;
            }
        }
        if let Some(message) = self.general_record_graph_error(&[], Some((child, metatable))) {
            self.error(span, message);
            return true;
        }
        if let Some(previous) = self.st.tab(child).metatable {
            if !self.unify_tabs(previous, metatable, span) {
                return true;
            }
        }
        // Luau 0.743: the actual metatable stays attached; raw __index is read live.
        self.st.tab_mut(child).metatable = Some(self.st.tab_root(metatable));
        self.refresh_record_metadata();
        true
    }

    fn general_record_role(&mut self, tab: TabId, span: Span) -> bool {
        // General lookup requires named own slots and record handles in every role.
        if !matches!(self.st.tab(tab).kind, TKind::Unknown | TKind::Record) {
            self.error(span, ARRAY);
            return false;
        }
        // Native conversions have no metatable transport in this stage.
        if self.st.tab(tab).native.is_some() {
            self.error(span, NATIVE);
            return false;
        }
        self.ensure_kind(tab, TKind::Record, span)
    }

    pub(crate) fn refresh_record_metadata(&mut self) -> bool {
        let roots: Vec<_> = self
            .st
            .tabs
            .iter()
            .enumerate()
            .filter(|(_, t)| t.link.is_none())
            .filter_map(|(i, t)| t.metatable.map(|m| (i as TabId, self.st.tab_root(m))))
            .collect();
        let mut changed = false;
        for (tab, meta) in roots {
            let parent =
                self.st
                    .tab(meta)
                    .fields
                    .get("__index")
                    .and_then(|s| match self.st.node(s.ty) {
                        TyNode::Table(p) => Some(self.st.tab_root(*p)),
                        _ => None,
                    });
            if let Some(parent) = parent {
                self.general_record_role(parent, self.st.tab(tab).span);
            }
            changed |=
                self.st.tab(tab).parent != parent || self.st.tab(tab).metatable != Some(meta);
            self.st.tab_mut(tab).parent = parent;
            self.st.tab_mut(tab).metatable = Some(meta);
        }
        changed
    }

    /// Include table unions induced by data/function slots, without following data edges as lookup edges.
    fn induced_record_unions(
        &self,
        a: TyId,
        b: TyId,
        queue: &mut Vec<(TabId, TabId)>,
        seen: &mut HashSet<(TyId, TyId)>,
        types: &mut [TyId],
    ) {
        let (a, b) = (types[a as usize], types[b as usize]);
        if a == b || !seen.insert((a.min(b), a.max(b))) {
            return;
        }
        match (self.st.node(a), self.st.node(b)) {
            (TyNode::Var, _) => {
                for root in types {
                    if *root == a {
                        *root = b;
                    }
                }
            }
            (_, TyNode::Var) => {
                for root in types {
                    if *root == b {
                        *root = a;
                    }
                }
            }
            (TyNode::Table(a), TyNode::Table(b)) => queue.push((*a, *b)),
            (TyNode::Func(a), TyNode::Func(b)) => {
                for (a, b) in a.params.iter().zip(&b.params) {
                    self.induced_record_unions(a.ty, b.ty, queue, seen, types);
                }
                if let (Some(a), Some(b)) = (a.vararg, b.vararg) {
                    self.induced_record_unions(a.ty, b.ty, queue, seen, types);
                }
                if let (Some(ar), Some(br)) =
                    (self.st.rets_known(a.rets), self.st.rets_known(b.rets))
                {
                    for (a, b) in ar.iter().zip(br) {
                        self.induced_record_unions(a.ty, b.ty, queue, seen, types);
                    }
                }
                if let (Some(a), Some(b)) = (self.st.rets_tail(a.rets), self.st.rets_tail(b.rets)) {
                    self.induced_record_unions(a.ty, b.ty, queue, seen, types);
                }
            }
            (TyNode::FalseOr(a), TyNode::FalseOr(b)) => {
                self.induced_record_unions(*a, *b, queue, seen, types)
            }
            (TyNode::Pcall(a), TyNode::Pcall(b)) => {
                self.induced_record_unions(a.ty, b.ty, queue, seen, types)
            }
            _ => {}
        }
    }

    /// Preflight the entire induced union closure before changing any store links.
    pub(crate) fn general_record_graph_error(
        &self,
        unions: &[(TabId, TabId)],
        edge: Option<(TabId, TabId)>,
    ) -> Option<&'static str> {
        self.record_graph_after_types(unions, edge, &[])
    }

    pub(crate) fn general_record_type_error(&self, a: TyId, b: TyId) -> Option<&'static str> {
        self.record_graph_after_types(&[], None, &[(a, b)])
    }

    fn record_graph_after_types(
        &self,
        unions: &[(TabId, TabId)],
        edge: Option<(TabId, TabId)>,
        type_unions: &[(TyId, TyId)],
    ) -> Option<&'static str> {
        let mut types: Vec<_> = (0..self.st.tys.len())
            .map(|i| self.st.root(i as TyId))
            .collect();
        let mut roots: Vec<_> = (0..self.st.tabs.len())
            .map(|i| self.st.tab_root(i as TabId))
            .collect();
        let mut queue = unions.to_vec();
        let mut seen_types = HashSet::new();
        let mut metadata = HashMap::new();
        for &(a, b) in type_unions {
            self.induced_record_unions(a, b, &mut queue, &mut seen_types, &mut types);
        }
        loop {
            while let Some((a, b)) = queue.pop() {
                let (a, b) = (roots[a as usize], roots[b as usize]);
                if a != b {
                    for root in &mut roots {
                        if *root == a {
                            *root = b;
                        }
                    }
                }
            }
            metadata.clear();
            let mut fields = HashMap::new();
            for (i, tab) in self
                .st
                .tabs
                .iter()
                .enumerate()
                .filter(|(_, t)| t.link.is_none())
            {
                let root = roots[i];
                for (name, slot) in &tab.fields {
                    if let Some(previous) = fields.insert((root, 0, name.as_str()), slot.ty) {
                        self.induced_record_unions(
                            previous,
                            slot.ty,
                            &mut queue,
                            &mut seen_types,
                            &mut types,
                        );
                    }
                }
                for (key, slot) in [(1, tab.elem), (2, tab.key), (3, tab.val)] {
                    if let Some(slot) = slot {
                        if let Some(previous) = fields.insert((root, key, ""), slot.ty) {
                            self.induced_record_unions(
                                previous,
                                slot.ty,
                                &mut queue,
                                &mut seen_types,
                                &mut types,
                            );
                        }
                    }
                }
                if let Some(meta) = tab.metatable {
                    let meta = roots[meta as usize];
                    if let Some(previous) = metadata.insert(root, meta) {
                        if previous != meta {
                            queue.push((previous, meta));
                        }
                    }
                }
            }
            if let Some((child, meta)) = edge {
                let (child, meta) = (roots[child as usize], roots[meta as usize]);
                if let Some(previous) = metadata.insert(child, meta) {
                    if previous != meta {
                        queue.push((previous, meta));
                    }
                }
            }
            if queue.is_empty() {
                break;
            }
        }
        let mut parents = HashMap::new();
        for (&child, &meta) in &metadata {
            for (i, tab) in self
                .st
                .tabs
                .iter()
                .enumerate()
                .filter(|(_, t)| t.link.is_none())
            {
                if roots[i] == meta {
                    if let Some(slot) = tab.fields.get("__index") {
                        if let TyNode::Table(parent) = self.st.node(types[slot.ty as usize]) {
                            parents.insert(child, roots[*parent as usize]);
                        }
                    }
                }
            }
        }
        // Reject static cycles and 100 links: Luau can fail on misses, and no dynamic lookup path is emitted.
        for (&start, _) in &parents {
            let mut seen = HashSet::new();
            let mut current = start;
            while let Some(&parent) = parents.get(&current) {
                if !seen.insert(current) {
                    return Some(CYCLE);
                }
                current = parent;
            }
            if seen.len() >= 100 {
                return Some(DEPTH);
            }
        }
        // Recursive metadata handles would require an infinitely expanded Rust generic type.
        for (&start, _) in &metadata {
            let mut seen = HashSet::new();
            let mut current = start;
            while let Some(&meta) = metadata.get(&current) {
                if !seen.insert(current) {
                    return Some(META_CYCLE);
                }
                current = meta;
            }
        }
        let roles: HashSet<_> = metadata
            .keys()
            .chain(metadata.values())
            .chain(parents.values())
            .copied()
            .collect();
        for (i, tab) in self
            .st
            .tabs
            .iter()
            .enumerate()
            .filter(|(_, t)| t.link.is_none())
        {
            if roles.contains(&roots[i]) {
                if tab.native.is_some() {
                    return Some(NATIVE);
                }
                if !matches!(tab.kind, TKind::Unknown | TKind::Record) {
                    return Some(ARRAY);
                }
            }
        }
        None
    }

    pub(crate) fn solve_general_record_reads(&mut self) -> bool {
        let mut changed = self.refresh_record_metadata();
        let before = self.record_links();
        let previous_nulls = self.st.solved.clone();
        self.st.solve_nulls();
        changed |= previous_nulls != self.st.solved;
        if self.general_record_graph_error(&[], None).is_some() {
            return changed;
        }
        let mut groups = HashMap::new();
        for (node, read) in self.metatables.reads.clone() {
            let tab = self.st.tab_root(read.tab);
            let mut current = tab;
            let mut levels = Vec::new();
            let mut candidates = Vec::new();
            loop {
                let own = self.st.tab(current).fields.get(&read.name).copied();
                let present = own.is_some_and(|s| {
                    self.field_always_init(current, &read.name) && !self.st.is_null(s.null)
                });
                candidates.extend(own);
                let metadata = self.st.tab(current).metatable.map(|m| {
                    let m = self.st.tab_root(m);
                    (m, self.st.tab(m).fields.get("__index").copied())
                });
                levels.push(LookupLevel {
                    tab: current,
                    own,
                    metadata,
                });
                // Luau 0.743: non-nil own storage stops the chain, including false/zero/empty string.
                if present {
                    break;
                }
                match self.st.tab(current).parent {
                    Some(parent) => current = self.st.tab_root(parent),
                    None => break,
                }
            }
            if levels[0].own.is_none()
                && self.st.tab(tab).metatable.is_none()
                && self.st.tab(tab).closed
            {
                self.field_slot(tab, &read.name, read.span);
            }
            for slot in candidates {
                self.unify(read.result.ty, slot.ty, read.span);
            }
            if let Some(previous) = groups.insert((tab, read.name.clone()), read.result.ty) {
                self.unify(previous, read.result.ty, read.span);
            }
            let own = levels[0].own;
            let present = own.is_some_and(|s| {
                self.field_always_init(tab, &read.name) && !self.st.is_null(s.null)
            });
            let fallback = levels
                .iter()
                .skip(1)
                .find_map(|l| l.own.map(|s| (l.tab, s)));
            let plan = RecordLookup {
                tab,
                own,
                fallback,
                result: Slot {
                    ty: read.result.ty,
                    null: read.result.null,
                },
                may_miss: !present,
                levels,
            };
            self.set_soft(
                &read.result,
                if plan.may_miss { Soft::Yes } else { Soft::No },
            );
            changed |= self.info.record_lookups.get(&node) != Some(&plan);
            self.info.record_lookups.insert(node, plan);
        }
        changed || before != self.record_links()
    }

    pub(crate) fn finish_general_record_receivers(&mut self) -> bool {
        let mut parents = HashSet::new();
        for tab in self.st.tabs.iter().filter(|t| t.link.is_none()) {
            if let Some(slot) = tab.fields.get("__index") {
                if let TyNode::Table(parent) = self.st.node(slot.ty) {
                    parents.insert(self.st.tab_root(*parent));
                }
            }
        }
        let mut changed = false;
        for (owner, receiver, span) in std::mem::take(&mut self.metatables.receivers) {
            let parent = matches!(self.st.node(owner), TyNode::Table(t) if parents.contains(&self.st.tab_root(*t)));
            // A general parent stores the method; inherited callers supply the original instance as self.
            if !parent {
                changed |= self.unify(receiver, owner, span);
            }
        }
        changed
    }

    pub(crate) fn validate_general_record_metadata(&mut self) {
        self.refresh_record_metadata();
        if let Some(message) = self.general_record_graph_error(&[], None) {
            self.error(Span::default(), message);
        }
        // Function/scalar index values need runtime behaviors outside record-only inheritance.
        for (value, span) in self.metatables.index_writes.clone() {
            match self.st.node(value.ty) {
                TyNode::Table(parent) => {
                    self.general_record_role(*parent, span);
                }
                TyNode::Nil => {}
                TyNode::Var if self.st.is_null(value.null) => {}
                _ => self.error(span, INDEX),
            }
        }
        let roots: Vec<_> = self
            .st
            .tabs
            .iter()
            .enumerate()
            .filter(|(_, t)| t.link.is_none())
            .map(|(i, _)| i as TabId)
            .collect();
        for tab in roots {
            let span = self.st.tab(tab).span;
            if let Some(index) = self.st.tab(tab).fields.get("__index").copied() {
                match self.st.node(index.ty) {
                    TyNode::Table(parent) => {
                        self.general_record_role(*parent, span);
                    }
                    TyNode::Nil => {}
                    TyNode::Var if self.st.is_null(index.null) => {}
                    _ => self.error(span, INDEX),
                }
            }
            if let Some(meta) = self.st.tab(tab).metatable {
                self.general_record_role(tab, span);
                self.general_record_role(meta, span);
                self.valid_metatable_fields(meta, span);
            }
        }
    }
}
