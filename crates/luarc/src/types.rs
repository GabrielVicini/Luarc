//! Type store: union-find over structural types, table shapes, function result
//! lists and per-slot nullability.
//!
//! Nullability is tracked separately from structure: every storage location (local,
//! parameter, field, array element, function result) is a `Slot` = structure +
//! nullability variable. A nil-capable value flowing into a slot adds an implication
//! edge; annotations fix a slot as non-nil. The solver propagates edges to a fixpoint.

use std::collections::BTreeMap;
use std::rc::Rc;

use crate::check_native::NativeRec;
use crate::diag::Span;
use crate::native::world::ItemRef;

/// A native type instantiation: definition identity plus type arguments.
#[derive(Clone, Debug)]
pub struct NativeTy {
    /// Package identity and definition path (`wgpu-types@30.0.0::TextureFormat`).
    pub key: String,
    pub item: ItemRef,
    /// Type and const arguments (lifetimes are not part of source types).
    pub args: Vec<TyId>,
}

pub type TyId = u32;
pub type NullId = u32;
pub type TabId = u32;
pub type RetsId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Slot {
    pub ty: TyId,
    pub null: NullId,
}

/// Softness: a table read that may be absent at runtime without the static type
/// being optional (Lua's "missing reads return nil").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Soft {
    No,
    Yes,
    /// Record field read; soft when not every constructor initializes the field.
    Field(u32),
    /// Decided when a deferred operation resolves.
    Deferred(u32),
}

/// Type of an expression value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ETy {
    pub ty: TyId,
    pub null: NullId,
    pub soft: Soft,
}

#[derive(Clone, Debug)]
pub struct FuncTy {
    pub params: Vec<Slot>,
    pub rets: RetsId,
    /// Element slot of a variadic function's `...` (extra arguments).
    pub vararg: Option<Slot>,
}

#[derive(Clone, Debug)]
pub enum TyNode {
    Var,
    Link(TyId),
    Num,
    /// Exact integer (`integer`): native i64/u64/i128/u128 values (runtime `i128`).
    Int,
    /// An integral literal's type: `number` or `integer`, decided by its uses
    /// (`number` when nothing requires an integer).
    NumVar,
    Str,
    Bool,
    Nil,
    Table(TabId),
    Func(Rc<FuncTy>),
    /// Native handle type (with its type arguments).
    Native(Rc<NativeTy>),
    /// A native primitive used as a generic argument (`u32` in `PhysicalSize<u32>`);
    /// as a value it is an ordinary number, string or boolean.
    NPrim(Rc<str>),
    FalseOr(TyId),
    Pcall(Slot),
    /// Compile-time namespace: a module, type or trait of an imported Rust crate.
    Namespace(ItemRef),
    /// A native future: awaiting it yields these results.
    Future(Rc<Vec<Slot>>),
    /// A spawned task.
    Task,
    /// The dynamic type `any`: a run-time tagged `lr::Value`. A value flows into
    /// it freely (boxed); out of it only through `type(x) == "..."` narrowing, `::`
    /// casts and builtins that accept any value.
    Any,
}

#[derive(Clone, Debug)]
pub enum RetsNode {
    Unknown,
    Link(RetsId),
    Known(Vec<Slot>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TKind {
    Unknown,
    Array,
    Map,
    Record,
}

#[derive(Clone, Debug)]
pub struct TabNode {
    /// Runtime identity for dynamic fields, metatables and frozen tables.
    pub runtime: bool,
    pub link: Option<TabId>,
    /// Static lookup edge, distinct from ordinary record-valued data fields.
    pub parent: Option<TabId>,
    /// Actual metatable handle type, distinct from its raw __index parent type.
    pub metatable: Option<TabId>,
    pub kind: TKind,
    /// Nil-preserving array storage; `packed` also exposes table.pack's n.
    pub sparse: bool,
    pub packed: bool,
    pub elem: Option<Slot>,
    pub key: Option<Slot>,
    pub val: Option<Slot>,
    pub fields: BTreeMap<String, Slot>,
    pub closed: bool,
    /// Field sets of every construction site (literal, native conversion).
    pub ctors: Vec<Vec<String>>,
    /// Native record this table converts to/from.
    pub native: Option<NativeRec>,
    /// Type alias name, used for readable generated struct names.
    pub hint: Option<String>,
    pub span: Span,
}

#[derive(Clone, Debug, Default)]
pub struct NullNode {
    pub parent: NullId,
    pub forced: Option<Span>,
    /// Slot that must not hold nil (annotation or native signature) and why.
    pub fixed: Option<(Span, String)>,
    pub edges: Vec<(NullId, Span)>,
}

#[derive(Default)]
pub struct Store {
    pub tys: Vec<TyNode>,
    pub rets: Vec<RetsNode>,
    /// Result tails: the element slot of the values after the fixed results
    /// of a function that returns `...`, by root of a `Known` result node.
    pub rets_tail: std::collections::HashMap<RetsId, Slot>,
    pub tabs: Vec<TabNode>,
    pub nulls: Vec<NullNode>,
    /// Constant nodes for expression values (never equated with other nodes).
    pub null_true: NullId,
    pub null_false: NullId,
    pub solved: Vec<bool>,
}

impl Store {
    pub fn new() -> Store {
        let mut s = Store::default();
        s.null_true = s.new_null();
        s.nulls[s.null_true as usize].forced = Some(Span::default());
        s.null_false = s.new_null();
        s
    }

    pub fn ty(&mut self, n: TyNode) -> TyId {
        self.tys.push(n);
        (self.tys.len() - 1) as TyId
    }
    pub fn var(&mut self) -> TyId {
        self.ty(TyNode::Var)
    }
    pub fn root(&self, mut t: TyId) -> TyId {
        while let TyNode::Link(n) = self.tys[t as usize] {
            t = n;
        }
        t
    }
    pub fn node(&self, t: TyId) -> &TyNode {
        &self.tys[self.root(t) as usize]
    }

    pub fn new_rets(&mut self, r: RetsNode) -> RetsId {
        self.rets.push(r);
        (self.rets.len() - 1) as RetsId
    }
    pub fn rets_root(&self, mut r: RetsId) -> RetsId {
        while let RetsNode::Link(n) = self.rets[r as usize] {
            r = n;
        }
        r
    }
    /// Element slot of the run-time-counted values after the fixed results.
    pub fn rets_tail(&self, r: RetsId) -> Option<Slot> {
        self.rets_tail.get(&self.rets_root(r)).copied()
    }
    /// Fixed results (a function with a tail also returns `rets_tail` values).
    pub fn rets_known(&self, r: RetsId) -> Option<&Vec<Slot>> {
        match &self.rets[self.rets_root(r) as usize] {
            RetsNode::Known(v) => Some(v),
            _ => None,
        }
    }

    pub fn new_tab(&mut self, kind: TKind, span: Span) -> TabId {
        self.tabs.push(TabNode {
            runtime: false,
            link: None,
            parent: None,
            metatable: None,
            kind,
            sparse: false,
            packed: false,
            elem: None,
            key: None,
            val: None,
            fields: BTreeMap::new(),
            closed: false,
            ctors: Vec::new(),
            native: None,
            hint: None,
            span,
        });
        (self.tabs.len() - 1) as TabId
    }
    pub fn tab_root(&self, mut t: TabId) -> TabId {
        while let Some(n) = self.tabs[t as usize].link {
            t = n;
        }
        t
    }
    pub fn tab(&self, t: TabId) -> &TabNode {
        &self.tabs[self.tab_root(t) as usize]
    }
    pub fn tab_mut(&mut self, t: TabId) -> &mut TabNode {
        let r = self.tab_root(t);
        &mut self.tabs[r as usize]
    }

    // Nullability

    pub fn new_null(&mut self) -> NullId {
        let id = self.nulls.len() as NullId;
        self.nulls.push(NullNode { parent: id, ..Default::default() });
        id
    }
    pub fn null_root(&self, mut n: NullId) -> NullId {
        while self.nulls[n as usize].parent != n {
            n = self.nulls[n as usize].parent;
        }
        n
    }
    /// Fresh slot nullability: nil allowed only if something nil flows in.
    pub fn slot(&mut self, ty: TyId) -> Slot {
        let null = self.new_null();
        Slot { ty, null }
    }
    pub fn fixed_slot(&mut self, ty: TyId, span: Span, what: &str) -> Slot {
        let null = self.new_null();
        self.nulls[null as usize].fixed = Some((span, what.to_string()));
        Slot { ty, null }
    }
    pub fn optional_slot(&mut self, ty: TyId, span: Span) -> Slot {
        let null = self.new_null();
        self.nulls[null as usize].forced = Some(span);
        Slot { ty, null }
    }
    pub fn force(&mut self, n: NullId, span: Span) {
        if n == self.null_false {
            return;
        }
        let r = self.null_root(n);
        if self.nulls[r as usize].forced.is_none() {
            self.nulls[r as usize].forced = Some(span);
        }
    }
    pub fn edge(&mut self, from: NullId, to: NullId, span: Span) {
        if from == self.null_false || from == to {
            return;
        }
        if from == self.null_true {
            self.force(to, span);
            return;
        }
        let r = self.null_root(from);
        self.nulls[r as usize].edges.push((to, span));
    }
    /// Equates two slot nullabilities (nested positions are invariant).
    pub fn equate(&mut self, a: NullId, b: NullId) -> Result<(), (Span, String)> {
        debug_assert!(a != self.null_true && a != self.null_false && b != self.null_true && b != self.null_false);
        let (ra, rb) = (self.null_root(a), self.null_root(b));
        if ra == rb {
            return Ok(());
        }
        let na = std::mem::take(&mut self.nulls[ra as usize]);
        self.nulls[ra as usize].parent = rb;
        let nb = &mut self.nulls[rb as usize];
        nb.edges.extend(na.edges);
        if nb.forced.is_none() {
            nb.forced = na.forced;
        }
        if nb.fixed.is_none() {
            nb.fixed = na.fixed;
        }
        if let (Some(f), Some(s)) = (&nb.fixed, nb.forced) {
            return Err((s, format!("nil is not allowed here: {}", f.1)));
        }
        Ok(())
    }

    /// Propagates forced nullability along edges; returns violations of fixed slots.
    pub fn solve_nulls(&mut self) -> Vec<(Span, String)> {
        let n = self.nulls.len();
        let mut errs = Vec::new();
        let mut solved = vec![false; n];
        let mut queue = Vec::new();
        for i in 0..n {
            let r = self.null_root(i as NullId) as usize;
            if self.nulls[r].forced.is_some() && !solved[r] {
                solved[r] = true;
                queue.push(r);
                if let Some((_, what)) = &self.nulls[r].fixed {
                    if r != self.null_true as usize {
                        errs.push((self.nulls[r].forced.unwrap(), format!("nil is not allowed here: {what}")));
                    }
                }
            }
        }
        while let Some(r) = queue.pop() {
            let edges = self.nulls[r].edges.clone();
            for (to, span) in edges {
                let t = self.null_root(to) as usize;
                if !solved[t] {
                    solved[t] = true;
                    if let Some((_, what)) = &self.nulls[t].fixed {
                        errs.push((span, format!("value may be nil, but {what}")));
                    }
                    queue.push(t);
                }
            }
        }
        self.solved = solved;
        errs
    }

    pub fn is_null(&self, n: NullId) -> bool {
        if n == self.null_true {
            return true;
        }
        if n == self.null_false {
            return false;
        }
        let r = self.null_root(n) as usize;
        self.solved.get(r).copied().unwrap_or(false)
    }
}
