//! Generics, unions, casts and the dynamic type `any`.
//!
//! * `function f<T>` and `type Pair<T, U>`: a type parameter is a fresh inference
//!   variable per checked function copy (`specialize.rs` makes one copy per call
//!   site) and the argument type in an applied alias.
//! * `A | B` (two or more non-nil members) is `any`. `T | nil` stays an optional.
//! * A value flows into `any` through [`Checker::flow_expr`], which marks the source
//!   expression as *boxed*; code generation wraps it in `lr::Value`.
//! * Out of `any` only through a cast (`x :: T`, checked at run time) or a
//!   `type(x) == "..."` test. Operators on `any` operands are dynamic
//!   (`lr::dynamic`), with Luau's run-time error messages.

use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::check::*;
use crate::diag::Span;
use crate::resolve::{Builtin, Res, SymId};
use crate::types::*;

/// Internal protected results can hide nil/false behind conditional wrappers.
pub(crate) fn has_protected_union(st: &Store, mut ty: TyId) -> bool {
    let mut seen = HashSet::new();
    while seen.insert(st.root(ty)) {
        match st.node(ty) {
            TyNode::Pcall(_) => return true,
            TyNode::FalseOr(inner) => ty = *inner,
            _ => return false,
        }
    }
    false
}

#[derive(Default)]
pub struct DynState {
    /// Type parameters in scope, innermost last.
    pub tparams: Vec<HashMap<String, TyId>>,
    /// The type parameters of each generic function copy, by function body id.
    pub fn_tparams: HashMap<NodeId, HashMap<String, TyId>>,
    /// Generic aliases: (file, name) → parameter names and body.
    pub generic_aliases: HashMap<(u32, String), (Vec<String>, TypeExpr)>,
    alias_cache: HashMap<(u32, String, Vec<String>), TyId>,
    alias_depth: u32,
    /// The annotation of the local a table constructor initializes, by constructor
    /// node: items of a `{any}` array or an `any` field are boxed.
    pub table_ann: HashMap<NodeId, TypeExpr>,
    /// For an assignment to a field or an element: the target node → the node of the
    /// value written (to box it when the field or element is `any`).
    pub write_nodes: HashMap<NodeId, NodeId>,
    /// Boxing a parameter may be checked before its call sites determine its type.
    pub box_checks: Vec<(TyId, Span)>,
}

/// What a cast does at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastKind {
    /// Nothing: the operand is the value (a boxing, if any, is on the operand).
    Pass,
    /// `any` to a static type: checked unboxing; `opt` when the target accepts nil.
    FromAny { opt: bool },
}

/// The level of an `error(msg, level)` call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorLevel {
    /// `error(msg, 0)`: no position.
    Zero,
    /// `error(msg)` / `error(msg, 1)`: the position of the `error` call.
    One,
    /// `error(msg, 2)`: the line of the call that made this function run. Known
    /// statically because the function is a copy made for exactly one call site.
    Two(Span),
}

/// The `any` positions of the type a table constructor initializes.
#[derive(Default, Clone)]
pub struct Expect {
    pub elem_any: bool,
    pub val_any: bool,
    pub key_any: bool,
    pub any_fields: HashSet<String>,
}

/// Where an `and`/`or` sits: what the checker needs when it resolves the operator.
#[derive(Clone, Copy, Debug)]
pub struct LogicSite {
    pub a_node: NodeId,
    pub b_node: NodeId,
    pub a_span: Span,
    pub b_span: Span,
    /// The left operand is a boolean literal.
    pub lit: Option<bool>,
    /// The left operand can never be nil.
    pub const_left: bool,
}

/// Dynamic operations recorded for code generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynBin {
    Arith(BinOp),
    Concat,
    Compare(BinOp),
    Eq(bool),
}

#[derive(Default)]
pub struct DynInfo {
    /// Expressions whose value is converted to `lr::Value` after evaluation.
    pub boxed: HashSet<NodeId>,
    pub casts: HashMap<NodeId, CastKind>,
    pub error_levels: HashMap<NodeId, ErrorLevel>,
    /// Binary operators with an `any` operand (the other operand is boxed if needed).
    pub dyn_bin: HashMap<NodeId, DynBin>,
    /// Unary minus on an `any` operand.
    pub dyn_neg: HashSet<NodeId>,
    /// Symbol reads narrowed by `type(x) == "..."`: node → the tag proven.
    pub unboxed: HashMap<NodeId, Tag>,
}

/// A `type()` result a narrowing proves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tag {
    Number,
    String,
    Boolean,
    Table,
}

impl<'a> Checker<'a> {
    pub(crate) fn is_any(&self, t: TyId) -> bool {
        matches!(self.st.node(t), TyNode::Any)
    }

    /// An `any` value that is never the internal nil: plain, non-null.
    pub(crate) fn any_val(&mut self) -> ETy {
        let t = self.st.ty(TyNode::Any);
        self.val(t)
    }

    // Type parameters

    pub(crate) fn tparam(&self, name: &str) -> Option<TyId> {
        self.dynamic.tparams.iter().rev().find_map(|f| f.get(name).copied())
    }

    /// Opens the type-parameter frame of a generic function while its signature is built.
    pub(crate) fn push_generics(&mut self, f: &FuncBody) -> bool {
        if f.generics.is_empty() {
            return false;
        }
        let mut frame = HashMap::new();
        for g in &f.generics {
            let v = self.st.var();
            frame.insert(g.text.clone(), v);
        }
        self.dynamic.fn_tparams.insert(f.id, frame.clone());
        self.dynamic.tparams.push(frame);
        true
    }

    /// Re-opens the frame while the function body is checked.
    pub(crate) fn enter_generics(&mut self, f: &FuncBody) -> bool {
        match self.dynamic.fn_tparams.get(&f.id).cloned() {
            Some(frame) => {
                self.dynamic.tparams.push(frame);
                true
            }
            None => false,
        }
    }

    // Applied aliases and unions

    pub(crate) fn applied_type(&mut self, name: &str, args: &[TypeExpr], sp: Span) -> TyId {
        let key = (self.cur_file, name.to_string());
        let Some((params, body)) = self.dynamic.generic_aliases.get(&key).cloned() else {
            if self.tparam(name).is_some() {
                self.error(sp, format!("type parameter '{name}' takes no type arguments"));
            } else if matches!(name, "number" | "string" | "boolean" | "any" | "integer") {
                self.error(sp, format!("type '{name}' takes no type arguments"));
            } else {
                self.error(sp, format!("unknown generic type '{name}'"));
            }
            return self.st.var();
        };
        if params.len() != args.len() {
            self.error(sp, format!("type '{name}' takes {} type argument(s), found {}", params.len(), args.len()));
            return self.st.var();
        }
        let tys: Vec<TyId> = args.iter().map(|a| self.type_ty_nonopt(a, "type arguments cannot be optional")).collect();
        let shown: Vec<String> = tys.iter().map(|t| self.show(*t)).collect();
        // an argument still being inferred (`unknown`, `{}`) has no stable name
        let cacheable = shown.iter().all(|s| !s.contains("unknown") && !s.contains("{}") && !s.contains("..."));
        let ckey = (self.cur_file, name.to_string(), shown);
        if cacheable {
            if let Some(t) = self.dynamic.alias_cache.get(&ckey) {
                return *t;
            }
        }
        if self.dynamic.alias_depth > 64 {
            self.error(sp, format!("type '{name}' expands without end (a generic alias applied to itself)"));
            return self.st.var();
        }
        let placeholder = self.st.var();
        if cacheable {
            self.dynamic.alias_cache.insert(ckey, placeholder);
        }
        // the body sees its own parameters only, not those of the code using it
        let frame: HashMap<String, TyId> = params.into_iter().zip(tys).collect();
        let outer = std::mem::replace(&mut self.dynamic.tparams, vec![frame]);
        self.dynamic.alias_depth += 1;
        let t = self.type_ty(&body);
        self.dynamic.alias_depth -= 1;
        self.dynamic.tparams = outer;
        if let TyNode::Table(tb) = self.st.node(t).clone() {
            if self.st.tab(tb).hint.is_none() {
                self.st.tab_mut(tb).hint = Some(name.to_string());
            }
        }
        self.unify(placeholder, t, sp);
        t
    }

    pub(crate) fn union_type(&mut self, members: &[TypeExpr], _sp: Span) -> TyId {
        // members are resolved for their diagnostics; the union itself is dynamic
        for m in members {
            self.type_ty_nonopt(m, "union members cannot be optional");
        }
        self.st.ty(TyNode::Any)
    }

    // Table constructors with `any` elements

    /// Which items of the constructor `node` are expected to be `any`, from the
    /// annotation of the local it initializes (empty when there is none).
    pub(crate) fn table_expectation(&mut self, node: NodeId) -> Expect {
        let Some(te) = self.dynamic.table_ann.get(&node).cloned() else { return Expect::default() };
        let te = match te {
            TypeExpr::Optional(inner) => *inner,
            other => other,
        };
        // the annotation is resolved again by the declaration: report nothing twice
        let mark = self.errors.len();
        let t = self.type_ty(&te);
        self.errors.truncate(mark);
        let mut ex = Expect::default();
        if let TyNode::Table(tb) = self.st.node(t).clone() {
            let tn = self.st.tab(tb).clone();
            match tn.kind {
                TKind::Array => ex.elem_any = tn.elem.is_some_and(|s| self.is_any(s.ty)),
                TKind::Map => { ex.val_any = tn.val.is_some_and(|s| self.is_any(s.ty)); ex.key_any = tn.key.is_some_and(|s| self.is_any(s.ty)); }
                TKind::Record => {
                    ex.any_fields = tn.fields.iter().filter(|(_, s)| self.is_any(s.ty)).map(|(k, _)| k.clone()).collect();
                }
                TKind::Unknown => {}
            }
        }
        ex
    }

    // Flowing into `any`

    /// Whether a value of this type can be converted to `lr::Value`.
    pub(crate) fn boxable(&mut self, mut ty: TyId, span: Span) -> bool {
        let mut seen = HashSet::new();
        loop {
            // Recursive static result wrappers have no finite Rust representation.
            if !seen.insert(self.st.root(ty)) {
                self.error(span, "a recursive result type cannot be converted to 'any'");
                return false;
            }
            match self.st.node(ty).clone() {
                TyNode::Var | TyNode::NumVar => { self.dynamic.box_checks.push((ty, span)); return true; }
                TyNode::FalseOr(t) => ty = t,
                // Luau exposes either the protected result or its error string as a value.
                TyNode::Pcall(slot) => ty = slot.ty,
                TyNode::Num | TyNode::Str | TyNode::Bool | TyNode::Nil | TyNode::Any | TyNode::Table(_) | TyNode::Func(_) | TyNode::Native(_) => return true,
                _ => {
                    let s = self.show(ty);
                    self.error(span, format!("a value of type {s} cannot be converted to 'any'"));
                    return false;
                }
            }
        }
    }

    /// `flow`, except that a value flowing into an `any` slot is boxed: the source
    /// expression `node` is converted to `lr::Value` when it is evaluated. Without a
    /// source expression (`None`) only `any` itself can flow into `any`.
    pub(crate) fn flow_node(&mut self, node: Option<NodeId>, v: ETy, dst: Slot, span: Span) -> bool {
        if let Some(id) = node {
            if self.is_any(dst.ty) && !self.is_any(v.ty) {
                if matches!(self.st.node(v.ty), TyNode::Var) && v.null != self.st.null_true {
                    // Luau's annotation does not change a deferred producer's type.
                    self.try_or_defer(Op::FlowAny { node: id, value: v, dst, span });
                    return true;
                }
                // a bare `nil` (an unconstrained type that is always nil) is `Value::Nil`
                self.boxable(v.ty, span);
                self.info.dynamic.boxed.insert(id);
                return true;
            }
        }
        self.flow(v, dst, span)
    }

    pub(crate) fn attempt_any_flow(&mut self, node: NodeId, value: ETy, dst: Slot, span: Span) -> bool {
        if matches!(self.st.node(value.ty), TyNode::Var) {
            if !self.defaults_round { return false; }
            // Only a genuinely unconstrained producer takes the dynamic type.
            return self.flow(value, dst, span);
        }
        self.flow_node(Some(node), value, dst, span)
    }

    /// A value written to a record field (`t.f = v`): boxed when the field is `any`.
    pub(crate) fn flow_write(&mut self, target: NodeId, v: ETy, dst: Slot, span: Span) -> bool {
        let node = self.dynamic.write_nodes.get(&target).copied();
        self.flow_node(node, v, dst, span)
    }

    /// A value written to an array or map element (`t[k] = v`): boxed when the
    /// elements are `any`; otherwise the types must be equal.
    pub(crate) fn unify_write(&mut self, target: NodeId, v: ETy, elem: TyId, span: Span) {
        if let Some(id) = self.dynamic.write_nodes.get(&target).copied() {
            if self.is_any(elem) && !self.is_any(v.ty) && !matches!(self.st.node(v.ty), TyNode::Var) {
                self.boxable(v.ty, span);
                self.info.dynamic.boxed.insert(id);
                return;
            }
        }
        self.unify(v.ty, elem, span);
    }

    /// Marks an operand of a dynamic operation as boxed when it is not `any` itself.
    fn box_node(&mut self, id: NodeId, span: Span, v: ETy) {
        if !self.is_any(v.ty) {
            self.boxable(v.ty, span);
            self.info.dynamic.boxed.insert(id);
        }
    }

    fn box_operand(&mut self, e: &Expr, v: ETy) {
        if !self.is_any(v.ty) {
            self.boxable(v.ty, e.span);
            self.info.dynamic.boxed.insert(e.id);
        }
    }

    // Narrowing out of `any`

    /// `type(x) == "number"` (either side of `==`/`~=`): the local and the tag proven.
    /// Only `number`, `string` and `boolean` have a static type to narrow to.
    pub(crate) fn type_test(&self, a: &Expr, b: &Expr) -> Option<(SymId, Tag)> {
        let (call, lit) = match (&a.kind, &b.kind) {
            (ExprKind::Call(..), ExprKind::Str(_)) => (a, b),
            (ExprKind::Str(_), ExprKind::Call(..)) => (b, a),
            _ => return None,
        };
        let (ExprKind::Call(f, args), ExprKind::Str(t)) = (&call.kind, &lit.kind) else { return None };
        if is_lib(f, self.res) != Some(Builtin::Type) || args.len() != 1 {
            return None;
        }
        let ExprKind::Name(n) = &args[0].kind else { return None };
        let Some(Res::Local(s)) = self.res.res(n.id) else { return None };
        let tag = match t.as_slice() {
            b"number" => Tag::Number,
            b"string" => Tag::String,
            b"boolean" => Tag::Boolean,
            b"table" if self.info.runtime_tables.narrowing => Tag::Table,
            _ => return None,
        };
        Some((s, tag))
    }

    /// The type of an `any` local inside a branch that proved its tag.
    pub(crate) fn narrowed_any(&mut self, tag: Tag) -> ETy {
        match tag {
            Tag::Number => self.num(),
            Tag::String => self.str_(),
            Tag::Boolean => self.bool_(),
            Tag::Table => self.runtime_value(Span::default()),
        }
    }

    // Error levels

    /// `error(msg, level)`: levels 0, 1 and 2 with Luau's position rules.
    pub(crate) fn note_error_level(&mut self, e: &Expr, args: &[Expr]) {
        let Some(lv) = args.get(1) else {
            self.info.dynamic.error_levels.insert(e.id, ErrorLevel::One);
            return;
        };
        let lit = match &lv.kind {
            ExprKind::Number(n) if n.fract() == 0.0 && *n >= 0.0 && *n < 1e6 => Some(*n as u32),
            _ => None,
        };
        let level = match lit {
            Some(0) => ErrorLevel::Zero,
            Some(1) => ErrorLevel::One,
            Some(2) => match self.fns.last().and_then(|f| f.call_site) {
                Some(site) => ErrorLevel::Two(site),
                None => {
                    self.error(
                        lv.span,
                        "error level 2 reports the line of the caller, which is only known inside a local function that is only called by name; use level 1, or call this function directly",
                    );
                    ErrorLevel::One
                }
            },
            Some(n) => {
                self.error(lv.span, format!("error level {n} is not supported (levels 0, 1 and 2 are)"));
                ErrorLevel::One
            }
            None => {
                self.error(lv.span, "the level of error() must be a number literal (0, 1 or 2)");
                ErrorLevel::One
            }
        };
        self.info.dynamic.error_levels.insert(e.id, level);
    }

    // Casts

    pub(crate) fn cast_expr(&mut self, e: &Expr, inner: &Expr, te: &TypeExpr) -> ETy {
        let v = self.expr(inner);
        let opt = matches!(te, TypeExpr::Optional(_));
        let dst = self.type_slot(te);
        let (src_any, dst_any) = (self.is_any(v.ty), self.is_any(dst.ty));
        match (src_any, dst_any) {
            (true, true) => {
                self.info.dynamic.casts.insert(e.id, CastKind::Pass);
                v
            }
            (false, true) => {
                // a static value converted to `any`
                self.box_operand(inner, v);
                self.info.dynamic.casts.insert(e.id, CastKind::Pass);
                self.any_val()
            }
            (true, false) => {
                if matches!(self.st.node(dst.ty), TyNode::Int | TyNode::Nil | TyNode::Var) {
                    let s = self.show(dst.ty);
                    self.error(te.span(), format!("cannot cast 'any' to {s}"));
                }
                self.info.dynamic.casts.insert(e.id, CastKind::FromAny { opt });
                let null = if opt { self.st.null_true } else { self.st.null_false };
                ETy { ty: dst.ty, null, soft: Soft::No }
            }
            (false, false) => {
                // a cast between static types only restates the type (or drops `nil`)
                self.unify(v.ty, dst.ty, e.span);
                self.info.dynamic.casts.insert(e.id, CastKind::Pass);
                if opt {
                    ETy { ty: dst.ty, null: v.null, soft: v.soft }
                } else {
                    // dropping `nil` is a run-time check (an error if it was nil)
                    ETy { ty: dst.ty, null: self.st.null_false, soft: Soft::No }
                }
            }
        }
    }

    // Operators on `any`

    /// Binary operators where an operand is `any`: dynamic at run time. Returns the
    /// result type, or `None` when neither operand is `any` (the usual rules apply).
    pub(crate) fn dyn_binary(&mut self, e: &Expr, op: BinOp, a: &Expr, b: &Expr, x: ETy, y: ETy) -> Option<ETy> {
        let (ax, ay) = (self.is_any(x.ty) || self.runtime_type(x.ty), self.is_any(y.ty) || self.runtime_type(y.ty));
        if !ax && !ay {
            return None;
        }
        // a bare nil never needs a boxing decision: `x == nil` tests the tag
        let kind = match op {
            BinOp::Eq | BinOp::Ne => DynBin::Eq(op == BinOp::Eq),
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::IDiv | BinOp::Mod | BinOp::Pow => DynBin::Arith(op),
            BinOp::Concat => DynBin::Concat,
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => DynBin::Compare(op),
            BinOp::And | BinOp::Or => return None,
        };
        self.box_operand(a, x);
        self.box_operand(b, y);
        self.info.dynamic.dyn_bin.insert(e.id, kind);
        if self.info.runtime_tables.enabled { self.info.runtime_tables.binary.insert(e.id); }
        Some(match kind {
            DynBin::Arith(_) => self.any_val(),
            DynBin::Concat if self.info.runtime_tables.enabled => self.any_val(),
            DynBin::Concat => self.str_(),
            DynBin::Compare(_) | DynBin::Eq(_) => self.bool_(),
        })
    }

    /// The kind of value a type holds, for telling whether `a or b` mixes kinds.
    fn value_class(&self, t: TyId) -> Option<String> {
        match self.st.node(t) {
            TyNode::Num | TyNode::NumVar | TyNode::Int => Some("number".into()),
            TyNode::Str => Some("string".into()),
            TyNode::Bool => Some("boolean".into()),
            TyNode::Table(_) => Some("table".into()),
            TyNode::Func(_) => Some("function".into()),
            TyNode::Native(n) => Some(n.key.clone()),
            _ => None,
        }
    }

    /// Whether two operand types are known and of different kinds (`false | T` counts
    /// as `T` and `boolean`).
    fn kinds_differ(&self, x: TyId, y: TyId) -> bool {
        let inner = |t: TyId| match self.st.node(t) {
            TyNode::FalseOr(i) => (self.value_class(*i), true),
            _ => (self.value_class(t), false),
        };
        let ((cx, fx), (cy, fy)) = (inner(x), inner(y));
        let (Some(cx), Some(cy)) = (cx, cy) else { return false };
        match (fx, fy) {
            (true, true) => cx != cy,
            (true, false) => cx != cy && cy != "boolean",
            (false, true) => cx != cy && cx != "boolean",
            (false, false) => cx != cy,
        }
    }

    /// `and`/`or` that need more than the ordinary rules, when a program mixes kinds:
    /// * an operand is `any`, or the operands are of known different kinds in an `or`
    ///   (`flag or "x"`, `(c and 1) or "two"`): the result is `any`, both sides boxed;
    /// * a boolean literal on the left of an operand of another kind (`false and f()`,
    ///   `true or f()`, `true and "x"`), or a non-nil number/string/table/function on the
    ///   left of an `or` (`0 or f()`): the left operand decides statically, so the result
    ///   is one of the operands, not a union (the dead one is checked but never runs).
    ///
    /// Operands of one kind (`false or true`, `1 or 2`) keep the ordinary path, so
    /// programs that already worked generate the same code.
    pub(crate) fn logic_site(&self, a: &Expr, b: &Expr, x: ETy) -> LogicSite {
        let mut inner = a;
        while let ExprKind::Paren(p) = &inner.kind {
            inner = p;
        }
        LogicSite {
            a_node: a.id,
            b_node: b.id,
            a_span: a.span,
            b_span: b.span,
            lit: match &inner.kind {
                ExprKind::Bool(v) => Some(*v),
                _ => None,
            },
            // a value that can never be nil (a literal, an arithmetic result)
            const_left: x.null == self.st.null_false && x.soft == Soft::No,
        }
    }

    /// Runs when an `and`/`or` is resolved (its operand types are known, or defaulted).
    /// `None`: the ordinary rules apply. `Some(done)`: handled here (`false`: wait).
    pub(crate) fn logic_dynamic(&mut self, node: NodeId, and: bool, a: ETy, b: ETy, result: ETy, span: Span, s: LogicSite) -> Option<bool> {
        let (ax, ay) = (self.is_any(a.ty), self.is_any(b.ty));
        let protected_left = has_protected_union(&self.st, a.ty);
        let protected_right = has_protected_union(&self.st, b.ty);
        let differ = self.kinds_differ(a.ty, b.ty);
        let truthy_const = s.const_left
            && matches!(self.st.node(a.ty), TyNode::Num | TyNode::NumVar | TyNode::Int | TyNode::Str | TyNode::Table(_) | TyNode::Func(_) | TyNode::Native(_));
        // does the left operand decide the result?
        let decided = match (s.lit, truthy_const) {
            (Some(l), _) if (differ || protected_right) && !ax && !ay => Some(if and { !l } else { l }),
            (None, true) if (differ || protected_right) && !and && !ax && !ay => Some(true),
            _ => None,
        };
        match decided {
            Some(true) => {
                // the result is the left operand: `false and f()`, `true or f()`, `0 or f()`
                self.info.logic.insert(node, LogicKind::LeftOnly);
                if s.lit.is_some() {
                    let bt = self.prim(TyNode::Bool);
                    self.unify(result.ty, bt, span);
                } else {
                    self.unify(result.ty, a.ty, span);
                }
                Some(true)
            }
            Some(false) => {
                // the result is the right operand: `true and "x"`, `false or "x"`
                self.info.logic.insert(node, LogicKind::RightOnly);
                self.unify(result.ty, b.ty, span);
                self.st.edge(b.null, result.null, span);
                if b.soft != Soft::No {
                    self.st.force(result.null, span);
                }
                Some(true)
            }
            None if ax || ay || protected_left || (differ && !and) => {
                // operands of different kinds: the result is dynamic
                // Protected unions may contain nil/false inside their runtime wrapper.
                self.box_node(s.a_node, s.a_span, a);
                self.box_node(s.b_node, s.b_span, b);
                self.info.logic.insert(node, LogicKind::AnyLeft);
                let any = self.st.ty(TyNode::Any);
                self.unify(result.ty, any, span);
                Some(true)
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::ModuleUnit;
    use crate::diag::SourceMap;
    use crate::native::adapters::AdapterSet;
    use crate::native::world::World;
    use crate::parser::parse_module;
    use crate::resolve::{Resolution, Resolver};

    /// Checks one module and hands the checker to `test`.
    fn run(src: &str, test: impl FnOnce(&Checker<'_>, &ModuleUnit)) {
        let mut next = 1;
        let module = parse_module(0, src, &mut next).expect("parse");
        let mut sm = SourceMap::default();
        sm.add("t.luarc".into(), "t.luarc".into(), src.into());
        let mut res = Resolution::default();
        let mut resolver = Resolver::new(&mut res);
        resolver.module(&module, next);
        resolver.finish();
        assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
        let unit = ModuleUnit { module, pseudo_func: next, ident: "m0".into(), requires: Default::default(), rust_requires: Default::default() };
        let world = World::default();
        let adapters = AdapterSet::default();
        let mut ck = Checker::new(&res, &sm, &world, &adapters);
        ck.check_program(std::slice::from_ref(&unit), &[0]);
        test(&ck, &unit);
    }

    fn errors(ck: &Checker<'_>) -> Vec<String> {
        ck.errors.iter().map(|d| d.msg.clone()).collect()
    }

    fn local_slot(ck: &Checker<'_>, name: &str) -> Slot {
        let sym = ck.res.syms.iter().position(|s| s.name == name).expect("symbol");
        ck.info.sym_slot[&(sym as u32)]
    }

    #[test]
    fn any_and_unions_are_the_dynamic_type() {
        run("local a: any = 1\ntype P = number | string\nlocal p: P = 'x'\nlocal q: number | string | boolean = true", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            for n in ["a", "p", "q"] {
                assert!(matches!(ck.st.node(local_slot(ck, n).ty), TyNode::Any), "{n}");
            }
            // each value flowing in is boxed
            assert_eq!(ck.info.dynamic.boxed.len(), 3);
        });
    }

    #[test]
    fn nil_union_stays_an_optional() {
        run("local a: number | nil = nil\nlocal b: string? = nil", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(matches!(ck.st.node(local_slot(ck, "a").ty), TyNode::Num));
            assert!(ck.info.dynamic.boxed.is_empty());
        });
    }

    #[test]
    fn generic_aliases_are_applied_per_argument_list() {
        run("type Pair<T, U> = { left: T, right: U }\nlocal a: Pair<number, string> = { left = 1, right = 's' }\nlocal b: Pair<string, number> = { left = 's', right = 1 }\nlocal l = a.left\nlocal r = b.left", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(matches!(ck.st.node(local_slot(ck, "l").ty), TyNode::Num | TyNode::NumVar));
            assert!(matches!(ck.st.node(local_slot(ck, "r").ty), TyNode::Str));
        });
    }

    #[test]
    fn any_conversion_preserves_deferred_record_and_logic_types() {
        run("type Pair<T, U> = { left: T, right: U }\nlocal pair: Pair<number, string> = { left = 11, right = 'signal' }\nlocal payload: any = pair.right\nlocal fallback: any = nil or 'fallback'\nlocal other = setmetatable({}, { __index = { value = 3 } })\nlocal value = other.value", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(matches!(ck.st.node(local_slot(ck, "payload").ty), TyNode::Any));
            assert!(matches!(ck.st.node(local_slot(ck, "fallback").ty), TyNode::Any));
            let TyNode::Table(pair) = ck.st.node(local_slot(ck, "pair").ty) else { panic!("pair table") };
            assert!(matches!(ck.st.node(ck.st.tab(*pair).fields["right"].ty), TyNode::Str));
            assert_eq!(ck.info.dynamic.boxed.len(), 2);
        });
    }

    #[test]
    fn generic_alias_mistakes_are_diagnosed() {
        run("type P<T> = { a: T }\nlocal x: P<number, string> = nil\nlocal y: P = nil\nlocal z: Q<number> = nil", |ck, _| {
            let e = errors(ck);
            assert!(e.iter().any(|m| m == "type 'P' takes 1 type argument(s), found 2"), "{e:?}");
            assert!(e.iter().any(|m| m == "generic type 'P' needs type arguments"), "{e:?}");
            assert!(e.iter().any(|m| m == "unknown generic type 'Q'"), "{e:?}");
        });
    }

    #[test]
    fn a_generic_function_has_fresh_type_variables() {
        run("local function id<T>(x: T): T return x end\nlocal n = id(1)\nlocal s = id('a')", |ck, _| {
            // one checked function, one T: the second call conflicts without copies
            assert!(errors(ck).iter().any(|m| m.starts_with("type mismatch")), "{:?}", errors(ck));
        });
    }

    #[test]
    fn mixed_kinds_in_or_become_any_but_equal_kinds_do_not() {
        run("local flag = true\nlocal a = flag or 'x'\nlocal b = 1 or 2\nlocal c: string? = nil\nlocal d = c or 'y'", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(matches!(ck.st.node(local_slot(ck, "a").ty), TyNode::Any));
            assert!(matches!(ck.st.node(local_slot(ck, "b").ty), TyNode::Num | TyNode::NumVar));
            assert!(matches!(ck.st.node(local_slot(ck, "d").ty), TyNode::Str));
            assert_eq!(ck.info.logic.values().filter(|k| **k == LogicKind::AnyLeft).count(), 1);
        });
    }

    #[test]
    fn literal_and_non_nil_left_operands_decide_statically() {
        run("local function f(): string return 'r' end\nlocal a = false and f()\nlocal b = true or f()\nlocal c = true and f()\nlocal d = false or f()\nlocal e = 0 or f()", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            let kinds: Vec<LogicKind> = {
                let mut v: Vec<_> = ck.info.logic.iter().collect();
                v.sort_by_key(|(id, _)| **id);
                v.into_iter().map(|(_, k)| *k).collect()
            };
            assert_eq!(kinds, [LogicKind::LeftOnly, LogicKind::LeftOnly, LogicKind::RightOnly, LogicKind::RightOnly, LogicKind::LeftOnly]);
            assert!(matches!(ck.st.node(local_slot(ck, "a").ty), TyNode::Bool));
            assert!(matches!(ck.st.node(local_slot(ck, "c").ty), TyNode::Str));
            assert!(matches!(ck.st.node(local_slot(ck, "e").ty), TyNode::Num | TyNode::NumVar));
        });
    }

    #[test]
    fn type_tests_narrow_an_any_local() {
        run("local a: any = 1\nif type(a) == 'number' then local n = a + 1 end\nif type(a) ~= 'string' then return end\nlocal s = a", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            let tags: Vec<Tag> = ck.info.dynamic.unboxed.values().copied().collect();
            assert!(tags.contains(&Tag::Number) && tags.contains(&Tag::String), "{tags:?}");
        });
    }

    #[test]
    fn casts_out_of_any_are_checked_casts() {
        run("local a: any = 1\nlocal n = a :: number\nlocal m = a :: number?\nlocal b = 1 :: any", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(matches!(ck.st.node(local_slot(ck, "n").ty), TyNode::Num));
            assert!(matches!(ck.st.node(local_slot(ck, "b").ty), TyNode::Any));
            let kinds: Vec<CastKind> = ck.info.dynamic.casts.values().copied().collect();
            assert_eq!(kinds.iter().filter(|k| matches!(k, CastKind::FromAny { .. })).count(), 2);
            assert!(kinds.contains(&CastKind::FromAny { opt: true }));
        });
    }

    #[test]
    fn error_levels() {
        run("error('a')\nerror('b', 0)\nerror('c', 1)", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            let mut levels: Vec<_> = ck.info.dynamic.error_levels.iter().collect();
            levels.sort_by_key(|(id, _)| **id);
            let levels: Vec<ErrorLevel> = levels.into_iter().map(|(_, l)| *l).collect();
            assert_eq!(levels, [ErrorLevel::One, ErrorLevel::Zero, ErrorLevel::One]);
        });
        run("local n = 2\nerror('x', n)\nerror('y', 3)\nerror('z', 2)", |ck, _| {
            let e = errors(ck);
            assert!(e.iter().any(|m| m.starts_with("the level of error() must be a number literal")), "{e:?}");
            assert!(e.iter().any(|m| m == "error level 3 is not supported (levels 0, 1 and 2 are)"), "{e:?}");
            assert!(e.iter().any(|m| m.starts_with("error level 2 reports the line of the caller")), "{e:?}");
        });
    }

    #[test]
    fn a_value_that_cannot_be_boxed_is_diagnosed() {
        run("local n: integer = 5\nlocal a: any = n", |ck, _| {
            assert!(errors(ck).iter().any(|m| m.contains("cannot be converted to 'any'")), "{:?}", errors(ck));
        });
    }

    #[test]
    fn protected_results_can_flow_into_any_when_their_inner_type_can() {
        run("local ok, value = pcall(function(): number return 7 end)\nlocal boxed: any = value", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(matches!(ck.st.node(local_slot(ck, "boxed").ty), TyNode::Any));
            assert!(!ck.info.dynamic.boxed.is_empty());
        });
        run("local ok, value = pcall(function(): integer return 7 end)\nlocal boxed: any = value", |ck, _| {
            assert!(errors(ck).iter().any(|m| m == "a value of type integer cannot be converted to 'any'"), "{:?}", errors(ck));
        });
        run("local function produce() return 7 end\nlocal ok, value = pcall(produce)\nlocal boxed: any = value\nlocal exact: integer = produce()", |ck, _| {
            assert!(errors(ck).iter().any(|m| m == "a value of type integer cannot be converted to 'any'"), "{:?}", errors(ck));
        });
        run("local function recur() local ok, value = pcall(recur) return value end\nlocal function boxed() local ok, value = pcall(recur) local result: any = value return result end", |ck, _| {
            assert!(errors(ck).iter().any(|m| m == "a recursive result type cannot be converted to 'any'"), "{:?}", errors(ck));
        });
    }

    #[test]
    fn operators_on_any_are_dynamic() {
        run("local a: any = 1\nlocal b = a + 1\nlocal c = a .. 's'\nlocal d = a < 2\nlocal e = a == 'x'\nlocal f = -a", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(matches!(ck.st.node(local_slot(ck, "b").ty), TyNode::Any));
            assert!(matches!(ck.st.node(local_slot(ck, "c").ty), TyNode::Str));
            assert!(matches!(ck.st.node(local_slot(ck, "d").ty), TyNode::Bool));
            assert!(matches!(ck.st.node(local_slot(ck, "e").ty), TyNode::Bool));
            assert!(matches!(ck.st.node(local_slot(ck, "f").ty), TyNode::Any));
            assert_eq!(ck.info.dynamic.dyn_bin.len(), 4);
            assert_eq!(ck.info.dynamic.dyn_neg.len(), 1);
        });
    }

    #[test]
    fn protected_short_circuits_and_typed_integer_nil_tests_check() {
        run("local _, value = pcall(function(): number? return nil end)\nlocal a = value or 'fallback'\nlocal b = value and 'rhs'\nlocal c = false or value\nlocal d = true and value\nlocal e = 'lhs' or value\nlocal f = true and value\nlocal flag = true\nlocal conditional = flag and value\nlocal g = conditional or 'fallback'\nlocal h = conditional and 'rhs'", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
        });
        run("local _, value = pcall(function(): integer? return nil end)\nlocal nil_alias = nil\nlocal same = value == nil\nlocal reverse = nil == value\nlocal alias = value == nil_alias\nlocal falsey = not value", |ck, _| {
            assert!(errors(ck).is_empty(), "{:?}", errors(ck));
            assert!(ck.info.dynamic.boxed.is_empty());
        });
    }
}
