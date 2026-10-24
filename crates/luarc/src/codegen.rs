//! Lowering of the checked program to Rust source.
//!
//! Output layout (one Cargo package per entry point):
//! * `src/main.rs`    — entry, record structs, module declarations;
//! * `src/m_<name>.rs` — one file per source module (`require()` + `init()`);
//! * `src/natives.rs` — generated wrappers for the imported Rust items used.
//!
//! Representation: `number` → `f64`, `string` → `lr::LStr`, `boolean` → `bool`,
//! optional → `Option<T>`, arrays/maps/records → shared `Gc` handles (`lr::Arr`, `lr::LMap`, `lr::Rec`), functions →
//! `lr::LFn<Args, Ret>` (generated `Callable` environments), native objects → `lr::Handle<T>`.
//! A local captured by a closure and reassigned lives in an `lr::Cell`.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;

use crate::ast::*;
use crate::check::*;
use crate::diag::{SourceMap, Span};
use crate::fmtspec::{Conv, FmtPiece};
use crate::resolve::{Res, Resolution, SymId, SymKind};
use crate::rir::{self, atom, RExpr, RStmt, ROp, RType};
pub(crate) use crate::rir::strip;
use crate::types::*;

// the dynamic type `any`; a child module so it can use the private helpers below
#[path = "codegen_dynamic.rs"]
mod dynamic;
#[path = "codegen_library.rs"]
mod library;

#[path = "codegen_runtime_table.rs"]
mod runtime_table;
#[path = "codegen_iteration.rs"]
mod iteration;

#[path = "codegen_packs.rs"]
mod packs;
#[path = "codegen_coroutine.rs"]
mod coroutine;
#[path = "codegen_table_library.rs"]
mod table_library;

pub struct Output {
    pub files: Vec<(String, String)>,
    /// Line ranges of each native wrapper in `src/natives.rs` → source span.
    pub wrapper_lines: Vec<(usize, usize, Span, String)>,
}

pub struct Gen<'a> {
    pub ck: &'a Checker<'a>,
    pub res: &'a Resolution,
    pub sm: &'a SourceMap,
    pub units: &'a [ModuleUnit],
    pub records: BTreeMap<TabId, String>,
    record_queue: Vec<TabId>,
    tmp: u32,
    loops: Vec<LoopCtx>,
    /// Static functions hoisted to module level.
    hoisted: Vec<String>,
    static_values: BTreeMap<SymId, String>,
    strs: Vec<Vec<u8>>,
    str_index: HashMap<Vec<u8>, usize>,
    /// Return slots of the function being generated (None: module top level).
    fn_rets: Vec<FnRets>,
    pub natives_used: BTreeMap<usize, String>,
    /// Bounds of the generic parameters of the native item being wrapped.
    pub(crate) cur_bounds: HashMap<String, Vec<rustdoc_types::GenericBound>>,
    /// Generic parameters converted into a borrowed type by `Into` / reversed
    /// `From` bounds (`where Option<&'a BindGroup>: From<BG>`).
    pub(crate) cur_into: HashMap<String, rustdoc_types::Type>,
    pub handle_makers: BTreeMap<String, String>,
    /// Generated trait implementations (naming counter).
    pub impl_count: usize,
    cur_module: usize,
    /// Per closure being generated: captures bound by reference in its body.
    ref_caps: Vec<HashSet<SymId>>,
    /// Statements releasing this module's thread-local values at shutdown.
    module_releases: Vec<String>,
}

/// An argument of a builtin call: a source expression, or a value already
/// evaluated into a temporary (the receiver and leading arguments of a call whose
/// last argument expands to several values, and those values).
#[derive(Clone)]
enum Arg<'x> {
    E(&'x Expr),
    V(Val, ETy, Span),
}

struct LoopCtx {
    id: u32,
    /// The body contains `continue`: it is wrapped in a `'c` block and every
    /// `break` must name the loop.
    labeled: bool,
    /// The loop itself needs its `'l` label (labeled and contains `break`).
    break_label: bool,
    /// `repeat` with `continue`: the `until` condition, evaluated at each `continue`.
    until: Option<RExpr>,
}

#[derive(Clone)]
enum FnRets {
    Module,
    /// Fixed result slots, result tail, function body.
    Func(Vec<Slot>, Option<Slot>, NodeId),
}

const RUST_KEYWORDS: &[&str] = &[
    "as", "async", "await", "box", "const", "crate", "dyn", "enum", "extern", "fn", "impl", "let", "loop", "match", "mod",
    "move", "mut", "priv", "pub", "ref", "self", "Self", "static", "struct", "super", "trait", "type", "unsafe", "use",
    "where", "abstract", "become", "final", "macro", "override", "typeof", "unsized", "virtual", "yield", "try", "gen",
    // a contextual keyword in Luau, so a valid source identifier
    "continue",
];

/// Rust spelling of a source identifier (locals, parameters, source record fields).
///
/// The mapping is injective and its image never starts with `_`, so it cannot
/// collide with generated names (`__tmp`, `__fn_…`, the `_x` spelling of unread
/// locals) nor with another source name: names starting with `_` or
/// `v_`, and names Rust reserves or the generated code relies on, get a `v_`
/// prefix; other keywords become raw identifiers.
pub fn rust_ident(name: &str) -> String {
    if name.starts_with('_')
        || name.starts_with("v_")
        || matches!(name, "self" | "Self" | "crate" | "super" | "Some" | "None" | "Ok" | "Err" | "lr")
    {
        return format!("v_{name}");
    }
    if RUST_KEYWORDS.contains(&name) {
        return format!("r#{name}");
    }
    name.to_string()
}

/// Rust spelling of a field of a native (Rust) struct or enum variant: the real
/// name, raw when it is a keyword.
pub fn native_ident(name: &str) -> String {
    if RUST_KEYWORDS.contains(&name) {
        format!("r#{name}")
    } else {
        name.to_string()
    }
}

fn rust_bytes_lit(b: &[u8]) -> String {
    let mut s = String::from("b\"");
    for &c in b {
        match c {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'\n' => s.push_str("\\n"),
            b'\t' => s.push_str("\\t"),
            b'\r' => s.push_str("\\r"),
            0x20..=0x7e => s.push(c as char),
            _ => {
                let _ = write!(s, "\\x{c:02x}");
            }
        }
    }
    s.push('"');
    s
}

pub fn rust_str_lit(s: &str) -> String {
    format!("{s:?}")
}

fn num_lit(n: f64) -> String {
    if n.is_infinite() {
        return if n > 0.0 { "f64::INFINITY".into() } else { "f64::NEG_INFINITY".into() };
    }
    if n.is_nan() {
        return "f64::NAN".into();
    }
    let s = format!("{n:?}");
    if s.contains('.') || s.contains('e') || s.contains("inf") || s.contains("NaN") {
        s
    } else {
        format!("{s}.0")
    }
}

/// An expression value as generated: code and whether it is an `Option`.
#[derive(Clone)]
struct Val {
    code: RExpr,
    opt: bool,
}

enum Place {
    Runtime { obj: String, key: RExpr },
    Local(SymId),
    Field { obj: String, name: String, store_opt: bool },
    Array { obj: String, key: String },
    Map { obj: String, key: RExpr },
    DynamicMap { obj: String, key: RExpr, key_span: Span },
    /// Native handle field: getter and setter wrapper instances (generated on use).
    NativeField { obj: String, get: usize, set: Option<usize> },
}

impl<'a> Gen<'a> {
    pub fn new(ck: &'a Checker<'a>, units: &'a [ModuleUnit]) -> Self {
        Gen {
            ck,
            res: ck.res,
            sm: ck.sm,
            units,
            records: BTreeMap::new(),
            record_queue: Vec::new(),
            tmp: 0,
            loops: Vec::new(),
            hoisted: Vec::new(),
            static_values: BTreeMap::new(),
            strs: Vec::new(),
            str_index: HashMap::new(),
            fn_rets: Vec::new(),
            natives_used: BTreeMap::new(),
            cur_bounds: HashMap::new(),
            cur_into: HashMap::new(),
            handle_makers: BTreeMap::new(),
            impl_count: 0,
            cur_module: 0,
            ref_caps: Vec::new(),
            module_releases: Vec::new(),
        }
    }

    pub(crate) fn fresh(&mut self, base: &str) -> String {
        self.tmp += 1;
        format!("__{base}{}", self.tmp)
    }

    pub(crate) fn loc(&self, sp: Span) -> String {
        rust_str_lit(&self.sm.loc(sp))
    }

    // Types

    pub(crate) fn is_null(&self, n: NullId) -> bool {
        self.ck.st.is_null(n)
    }
    pub(crate) fn ety_opt(&self, e: ETy) -> bool {
        self.ck.st.is_null(e.null) || self.ck.soft(e.soft)
    }
    fn expr_opt(&self, e: &Expr) -> bool {
        self.ety_opt(self.ck.info.expr[&e.id])
    }
    fn sym_opt(&self, s: SymId) -> bool {
        let slot = self.ck.info.sym_slot[&s];
        self.is_null(slot.null) || self.ck.late_init.contains(&s)
    }

    pub(crate) fn node(&self, t: TyId) -> TyNode {
        self.ck.st.node(t).clone()
    }

    pub(crate) fn rust_ty(&mut self, t: TyId) -> String {
        match self.node(t) {
            TyNode::Num => "f64".into(),
            TyNode::Int => "i128".into(),
            TyNode::NumVar => "f64".into(),
            TyNode::Task => "lr::task::Task".into(),
            TyNode::Any => "lr::Value".into(),
            TyNode::Future(r) => format!("lr::task::Fut<{}>", self.rets_ty(&r)),
            TyNode::Str => "lr::LStr".into(),
            TyNode::Bool => "bool".into(),
            TyNode::Var | TyNode::Nil | TyNode::Link(_) | TyNode::Namespace(..) => "()".into(),
            TyNode::Native(nt) => match self.handle_inner_ty(nt.item, &nt.args) {
                Ok(t) => format!("lr::Handle<{t}>"),
                Err(_) => "lr::Handle<()>".into(),
            },
            TyNode::NPrim(p) => match &*p {
                "bool" => "bool".into(),
                "char" | "str" => "lr::LStr".into(),
                p if crate::check::is_int_prim(p) => "i128".into(),
                _ => "f64".into(),
            },
            TyNode::FalseOr(x) => format!("lr::FalseOr<{}>", self.rust_ty(x)),
            TyNode::Pcall(s) => format!("lr::PcallVal<{}>", self.slot_ty(s)),
            TyNode::Func(f) => self.fn_ty(&f),
            TyNode::Table(tab) => {
                let root = self.ck.st.tab_root(tab);
                let tn = self.ck.st.tab(root).clone();
                if tn.runtime { return "lr::Table".into(); }

                if tn.sparse { return RType::Apply("lr::Arr".into(), vec![RType::Apply("Option".into(), vec![RType::Named("lr::Value".into())])]).print(); }
                match tn.kind {
                    TKind::Array | TKind::Unknown => {
                        let el = tn.elem.map(|s| self.rust_ty(s.ty)).unwrap_or_else(|| "()".into());
                        format!("lr::Arr<{el}>")
                    }
                    TKind::Map => {
                        let k = match tn.key.map(|s| self.node(s.ty)) {
                            Some(TyNode::Num) => "lr::NumKey".to_string(),
                            Some(TyNode::Int) => "i128".to_string(),
                            Some(TyNode::Str) => "lr::LStr".to_string(),
                            Some(TyNode::Bool) => "bool".to_string(),
                            Some(TyNode::Any) => "lr::dynamic::Key".to_string(),
                            _ => "()".to_string(),
                        };
                        let v = tn.val.map(|s| self.rust_ty(s.ty)).unwrap_or_else(|| "()".into());
                        format!("lr::LMap<{k}, {v}>")
                    }
                    TKind::Record => {
                        if tn.metatable.is_some() { return self.record_handle_type(root).print(); }
                        if let Some(parent) = tn.parent {
                            let data = RType::Named(self.record_name(root));
                            let parent = RType::Apply("lr::Rec".into(), vec![RType::Named(self.record_name(parent))]);
                            return RType::Apply("lr::MetaRec".into(), vec![data, parent]).print();
                        }
                        format!("lr::Rec<{}>", self.record_name(root))
                    }
                }
            }
        }
    }

    fn record_handle_type(&mut self, root: TabId) -> RType {
        let root = self.ck.st.tab_root(root);
        let data = RType::Named(self.record_name(root));
        match self.ck.st.tab(root).metatable {
            Some(meta) => {
                let meta = self.record_handle_type(meta);
                RType::Apply("lr::MetaRec".into(), vec![data, meta])
            }
            None => RType::Apply("lr::Rec".into(), vec![data]),
        }
    }

    pub(crate) fn slot_ty(&mut self, s: Slot) -> String {
        let t = self.rust_ty(s.ty);
        if self.is_null(s.null) {
            format!("Option<{t}>")
        } else {
            t
        }
    }

    fn opt_ty(&mut self, t: TyId, opt: bool) -> String {
        let r = self.rust_ty(t);
        if opt {
            format!("Option<{r}>")
        } else {
            r
        }
    }

    /// Rust type of a variadic function's `...`.
    fn va_ty(&mut self, s: Slot) -> String {
        format!("Vec<Option<{}>>", self.rust_ty(s.ty))
    }

    /// Rust result type of a function: its fixed results, then the vector of
    /// its run-time-counted results when it returns `...`.
    fn result_ty(&mut self, rets: &[Slot], tail: Option<Slot>) -> String {
        let Some(t) = tail else { return self.rets_ty(rets) };
        let mut items: Vec<String> = rets.iter().map(|s| self.slot_ty(*s)).collect();
        items.push(self.va_ty(t));
        if items.len() == 1 {
            items.remove(0)
        } else {
            format!("({})", items.join(", "))
        }
    }

    pub(crate) fn rets_ty(&mut self, rets: &[Slot]) -> String {
        match rets.len() {
            0 => "()".into(),
            1 => self.slot_ty(rets[0]),
            _ => {
                let v: Vec<String> = rets.iter().map(|s| self.slot_ty(*s)).collect();
                format!("({})", v.join(", "))
            }
        }
    }

    fn fn_sig_parts(&mut self, f: &FuncTy) -> (Vec<String>, String, Vec<Slot>) {
        let mut ps: Vec<String> = f.params.iter().map(|p| self.slot_ty(*p)).collect();
        if let Some(v) = f.vararg {
            ps.push(self.va_ty(v));
        }
        let rets = self.ck.st.rets_known(f.rets).cloned().unwrap_or_default();
        let r = self.result_ty(&rets, self.ck.st.rets_tail(f.rets));
        (ps, r, rets)
    }

    /// `(argument tuple, result)` type arguments of `lr::LFn` for a function type.
    pub(crate) fn fn_args(&mut self, f: &FuncTy) -> (String, String) {
        let (ps, r, _) = self.fn_sig_parts(f);
        (tuple_ty(&ps), r)
    }

    pub(crate) fn fn_ty(&mut self, f: &FuncTy) -> String {
        let (a, r) = self.fn_args(f);
        format!("lr::LFn<{a}, {r}>")
    }

    fn func_of(&self, t: TyId) -> std::rc::Rc<FuncTy> {
        match self.node(t) {
            TyNode::Func(f) => f,
            _ => panic!("luarc internal error: expected a function type"),
        }
    }

    pub(crate) fn record_name(&mut self, root: TabId) -> String {
        if let Some(n) = self.records.get(&root) {
            return n.clone();
        }
        let hint = self.ck.st.tab(root).hint.clone().filter(|h| h.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'));
        let name = match hint {
            Some(h) => format!("R{}{}", self.records.len(), h[..1].to_uppercase() + &h[1..]),
            None => format!("R{}", self.records.len()),
        };
        self.records.insert(root, name.clone());
        self.record_queue.push(root);
        name
    }

    /// Record field storage: `Option` when the field may be nil or is not set by
    /// every constructor.
    pub(crate) fn field_store_opt(&self, root: TabId, name: &str) -> bool {
        let tn = self.ck.st.tab(root);
        let s = tn.fields[name];
        self.is_null(s.null) || !self.ck.field_always_init(root, name)
    }

    fn record_defs(&mut self) -> String {
        let mut out = String::new();
        let mut i = 0;
        while i < self.record_queue.len() {
            let root = self.record_queue[i];
            i += 1;
            let name = self.records[&root].clone();
            let tn = self.ck.st.tab(root).clone();
            let mut fields = String::new();
            for (f, s) in &tn.fields {
                let opt = self.field_store_opt(root, f);
                let t = self.opt_ty(s.ty, opt);
                let _ = writeln!(fields, "    pub {}: {},", rust_ident(f), t);
            }
            let desc: Vec<String> = tn.fields.keys().cloned().collect();
            let _ = writeln!(out, "/// Record `{{{}}}`.", desc.join(", "));
            // A source program may store fields it never reads back.
            let _ = writeln!(
                out,
                "#[derive(Clone, lr::Trace)]\n#[dumpster(crate = lr::gc::dumpster)]\n#[allow(dead_code)]\npub struct {name} {{\n{fields}}}\n"
            );
        }
        out
    }

    // Conversions

    /// Converts a value to the requested representation.
    fn coerce(&mut self, v: Val, to_opt: bool, span: Span, what: &str) -> RExpr {
        match (v.opt, to_opt) {
            (false, false) | (true, true) => v.code,
            (false, true) => rir::some(v.code),
            (true, false) => {
                let msg = format!("{}: {}", self.sm.loc(span), what);
                rir::try_(rir::call("lr::present", vec![v.code, rir::atom_e(rust_str_lit(&msg))]))
            }
        }
    }

    fn expr_to(&mut self, e: &Expr, to_opt: bool) -> RExpr {
        let v = self.expr(e);
        self.coerce(v, to_opt, e.span, "attempt to use a nil value")
    }

    /// Value that must not be nil (operands etc.).
    fn expr_nn(&mut self, e: &Expr, what: &str) -> RExpr {
        let v = self.expr(e);
        self.coerce(v, false, e.span, what)
    }

    fn str_lit(&mut self, b: &[u8]) -> RExpr {
        let idx = match self.str_index.get(b) {
            Some(i) => *i,
            None => {
                self.strs.push(b.to_vec());
                self.str_index.insert(b.to_vec(), self.strs.len() - 1);
                self.strs.len() - 1
            }
        };
        let preview = String::from_utf8_lossy(b);
        if b.len() <= 24 && preview.chars().all(|c| !c.is_control() && c != '*' && c != '/') {
            rir::atom_e(format!("__str({idx}) /* {:?} */", preview))
        } else {
            rir::atom_e(format!("__str({idx})"))
        }
    }

    // Names

    pub(crate) fn sym_name(&self, s: SymId) -> String {
        let sym = self.res.sym(s);
        // read by an `until` that is also evaluated at `continue` sites, where a
        // nested block could shadow the source name
        if self.res.until_locals.contains(&s) {
            return format!("__until{s}");
        }
        let base = rust_ident(&sym.name);
        if sym.name == "_" && !sym.read {
            return "_".into();
        }
        // unread: `_` + an identifier image (which never starts with `_`)
        if !sym.read && !sym.is_static {
            if base.starts_with("r#") {
                return format!("_{}", &base[2..]);
            }
            return format!("_{base}");
        }
        base
    }

    fn static_fn_name(&self, s: SymId) -> String {
        let sym = self.res.sym(s);
        let clean: String = sym.name.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect();
        format!("__fn_{}_{}", clean.trim_start_matches('_'), s)
    }

    fn is_copy_ty(&self, t: TyId) -> bool {
        matches!(self.node(t), TyNode::Num | TyNode::Bool | TyNode::Var | TyNode::Nil | TyNode::Namespace(..))
    }

    fn read_sym(&mut self, s: SymId) -> RExpr {
        let sym = self.res.sym(s).clone();
        let name = self.sym_access(s);
        if sym.is_cell() {
            return rir::method(name, "get", vec![]);
        }
        let slot = self.ck.info.sym_slot[&s];
        if self.is_copy_ty(slot.ty) {
            name
        } else {
            rir::method(name, "clone", vec![])
        }
    }

    // Expressions

    fn expr(&mut self, e: &Expr) -> Val {
        self.expr_mode(e, false)
    }

    /// `borrowed`: the value is only borrowed (`&x`, `x.len()`), so a plain local
    /// can be referenced without cloning its handle.
    fn expr_mode(&mut self, e: &Expr, borrowed: bool) -> Val {
        // an `any` local read where `type(x) == "..."` proved its kind
        if let Some(tag) = self.ck.info.dynamic.unboxed.get(&e.id).copied() {
            if let Some(v) = self.unboxed_read(e, tag) {
                if self.ck.info.dynamic.boxed.contains(&e.id) { return self.box_value(v); }
                return v;
            }
        }
        // flowing into `any`: the plain value, converted to `lr::Value`
        if self.ck.info.dynamic.boxed.contains(&e.id) {
            let v = self.expr_mode_plain(e, false);
            if self.ck.info.runtime_tables.function_values.contains(&e.id) {
                let code = if v.opt {
                    let adapted = rir::method(v.code, "map", vec![rir::atom_e("lr::dynamic_fn::function")]);
                    rir::method(adapted, "unwrap_or", vec![rir::atom_e("lr::Value::Nil")])
                } else { rir::call("lr::dynamic_fn::function", vec![v.code]) };
                return Val { code, opt: false };
            }
            return self.box_value(v);
        }
        let any = self.ck.info.expr.get(&e.id).is_some_and(|t| self.is_any_ty(t.ty));
        if any && self.expr_opt(e) {
            // an absent `any` is nil
            let v = self.expr_mode_plain(e, false);
            return self.any_present(v);
        }
        self.expr_mode_plain(e, borrowed)
    }

    fn expr_mode_plain(&mut self, e: &Expr, borrowed: bool) -> Val {
        let opt = self.expr_opt(e);
        if borrowed {
            if let ExprKind::Name(n) = &e.kind {
                if let Some(Res::Local(s)) = self.res.res(n.id) {
                    let sym = self.res.sym(s);
                    if !sym.is_cell() && !sym.is_static && !self.ck.info.narrowed.contains_key(&e.id) && !self.is_ns_sym(s) {
                        return Val { code: self.sym_access(s), opt };
                    }
                }
            }
        }
        let code = self.expr_code(e, opt);
        Val { code, opt }
    }

    /// Like `expr_nn`, for a value that is only borrowed.
    fn expr_ref(&mut self, e: &Expr, what: &str) -> RExpr {
        let v = self.expr_mode(e, true);
        self.coerce(v, false, e.span, what)
    }

    /// Like `expr`, for a value that is only borrowed.
    fn expr_ref_val(&mut self, e: &Expr) -> Val {
        self.expr_mode(e, true)
    }

    // Builtin arguments (source expressions or evaluated values)

    fn arg_val(&mut self, a: &Arg) -> Val {
        match a {
            Arg::E(e) => self.expr(e),
            Arg::V(v, ..) => v.clone(),
        }
    }

    fn arg_ref_val(&mut self, a: &Arg) -> Val {
        match a {
            Arg::E(e) => self.expr_ref_val(e),
            Arg::V(v, ..) => v.clone(),
        }
    }

    fn arg_nn(&mut self, a: &Arg, what: &str) -> RExpr {
        match a {
            Arg::E(e) => self.expr_nn(e, what),
            Arg::V(v, _, sp) => self.coerce(v.clone(), false, *sp, what),
        }
    }

    fn arg_ref(&mut self, a: &Arg, what: &str) -> RExpr {
        match a {
            Arg::E(e) => self.expr_ref(e, what),
            Arg::V(v, _, sp) => self.coerce(v.clone(), false, *sp, what),
        }
    }

    fn arg_to(&mut self, a: &Arg, to_opt: bool) -> RExpr {
        match a {
            Arg::E(e) => self.expr_to(e, to_opt),
            Arg::V(v, _, sp) => self.coerce(v.clone(), to_opt, *sp, "attempt to use a nil value"),
        }
    }

    fn arg_ety(&self, a: &Arg) -> ETy {
        match a {
            Arg::E(e) => self.ck.info.expr[&e.id],
            Arg::V(_, t, _) => *t,
        }
    }

    fn arg_is_int(&self, a: &Arg) -> bool {
        self.ty_is_int(self.arg_ety(a).ty)
    }

    fn arg_is_str(&self, a: &Arg) -> bool {
        matches!(self.node(self.arg_ety(a).ty), TyNode::Str)
    }

    /// `...` or `select(i, ...)` passed on with its run-time number of values
    /// (the checker's `is_pack`).
    fn is_pack(&self, e: &Expr) -> bool {
        matches!(e.kind, ExprKind::Vararg)
            || matches!(self.ck.info.calls.get(&e.id), Some(CallKind::Builtin(BuiltinFn::Select)))
            || self.ck.info.pack_calls.contains_key(&e.id)
    }

    /// A pack: statements to run first, values that come before its vector (the
    /// fixed results of a call), the vector, and the index of its first value.
    fn pack_src(&mut self, e: &Expr) -> (Vec<RStmt>, Vec<Val>, RExpr, RExpr) {
        match &e.kind {
            ExprKind::Vararg => (vec![], vec![], rir::atom_e(VA), rir::atom_e("0")),
            _ if matches!(self.ck.info.calls.get(&e.id), Some(CallKind::Builtin(BuiltinFn::Select))) => {
                let ExprKind::Call(_, args) = &e.kind else { unreachable!() };
                let n = self.expr_nn(&args[0], "bad argument #1 to 'select' (number expected)");
                let nv = self.fresh("n");
                let mut pre = vec![rir::let_(nv.clone(), n)];
                let (p, src) = self.select_src(&Arg::E(&args[1]));
                pre.extend(p);
                let st = self.fresh("s");
                let first = rir::at(rir::call("lr::va::select", vec![rir::method(src.clone(), "len", vec![]), rir::atom_e(nv)]), &self.loc(e.span));
                pre.push(rir::let_(st.clone(), first));
                (pre, vec![], src, rir::atom_e(st))
            }
            _ => {
                let (pre, vals, t) = self.multi_pack(e);
                (pre, vals, t, rir::atom_e("0"))
            }
        }
    }

    /// The list `select` counts or indexes: `...`, or all values of a call
    /// returning `...` (its fixed results joined to its result vector).
    fn select_src(&mut self, a: &Arg) -> (Vec<RStmt>, RExpr) {
        match a {
            Arg::E(e) if matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..)) => {
                let (mut pre, pvals, t, _) = self.pack_src(e);
                if pvals.is_empty() {
                    return (pre, t);
                }
                let fixed: Vec<RExpr> = pvals.into_iter().map(|v| self.coerce(v, true, e.span, "")).collect();
                let all = self.fresh("l");
                pre.push(rir::let_(all.clone(), rir::call("lr::va::with_rest", vec![RExpr::Macro("vec".into(), fixed), rir::borrow(t), rir::atom_e("0")])));
                (pre, rir::atom_e(all))
            }
            _ => (vec![], rir::atom_e(VA)),
        }
    }

    /// The call expression of an argument that may expand to several values.
    fn arg_call<'x>(a: &Arg<'x>) -> Option<&'x Expr> {
        match a {
            Arg::E(e) if matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..)) => Some(e),
            _ => None,
        }
    }

    fn arg_span(a: &Arg) -> Span {
        match a {
            Arg::E(e) => e.span,
            Arg::V(_, _, sp) => *sp,
        }
    }

    fn expr_code(&mut self, e: &Expr, opt: bool) -> RExpr {
        let info = &self.ck.info;
        match &e.kind {
            ExprKind::Nil => {
                let t = info.expr[&e.id].ty;
                let rt = self.rust_ty(t);
                rir::atom_e(format!("None::<{rt}>"))
            }
            ExprKind::Bool(b) => rir::atom_e(b.to_string()),
            ExprKind::Int(i) => rir::token(format!("{i}i128")),
            ExprKind::Number(n) => {
                if matches!(self.node(info.expr[&e.id].ty), TyNode::Int) {
                    rir::token(format!("{}i128", *n as i128))
                } else {
                    rir::token(num_lit(*n))
                }
            }
            ExprKind::Str(s) => self.str_lit(s),
            ExprKind::Vararg => va_get(&rir::atom_e(VA), &rir::atom_e("0"), 0),
            ExprKind::Interp(parts) => {
                let mut ps = Vec::new();
                for p in parts {
                    match p {
                        InterpPart::Lit(b) => match std::str::from_utf8(b) {
                            Ok(s) => ps.push(rir::borrow(rir::atom_e(rust_str_lit(s)))),
                            Err(_) => {
                                let k = self.str_lit(b);
                                ps.push(rir::borrow(k))
                            }
                        },
                        InterpPart::Expr(x) => {
                            let v = self.expr(x);
                            ps.push(rir::borrow(v.code));
                        }
                    }
                }
                if let Some(first) = ps.first_mut() {
                    *first = rir::cast(first.clone(), "&dyn lr::LuaDisplay");
                }
                rir::call("lr::stdlib::interp", vec![rir::borrow(RExpr::Array(ps))])
            }
            _ if self.ck.info.builtin_values.contains_key(&e.id) => self.builtin_value_code(e).into(),
            ExprKind::Name(n) => self.name_expr(e, n),
            ExprKind::Paren(x) => {
                let v = self.expr(x);
                self.coerce(v, opt, x.span, "attempt to use a nil value")
            }
            ExprKind::Cast(x, _) => self.cast_code(e, x, opt),
            ExprKind::Function(f) => self.closure(f, None).into(),
            ExprKind::Table(items) => self.table(e, items),
            ExprKind::Field(obj, name) => self.field_read(e, obj, &name.text),
            ExprKind::Index(obj, key) => self.index_read(e, obj, key),
            ExprKind::Call(..) | ExprKind::Method(..) => {
                let (pre, vals) = self.multi(e, Some(1));
                let v = vals.into_iter().next().unwrap();
                let code = self.coerce(v, opt, e.span, "attempt to use a nil value");
                rir::block(pre, code)
            }
            ExprKind::Binary(op, a, b) => self.binary(e, *op, a, b, opt),
            ExprKind::Unary(op, a) => match op {
                UnOp::Neg if self.ck.info.dynamic.dyn_neg.contains(&e.id) => {
                    let x = self.expr_nn(a, "attempt to use a nil value");
                    rir::at(rir::call("lr::dynamic::neg", vec![rir::borrow(x)]), &self.loc(e.span))
                }
                UnOp::Neg => {
                    let int = self.is_int_expr(a);
                    let x = self.expr_nn(a, "attempt to perform arithmetic on a nil value");
                    if int {
                        rir::at(rir::call("lr::int::neg", vec![x]), &self.loc(e.span))
                    } else {
                        rir::unary("-", x)
                    }
                }
                UnOp::Not => {
                    let c = self.cond(a);
                    rir::unary("!", c)
                }
                UnOp::Len => {
                    let x = self.expr_ref(a, "attempt to get length of a nil value");
                    if self.ck.info.runtime_tables.lengths.contains(&e.id) {
                        return rir::at(rir::method(x, "len", vec![]), &self.loc(e.span));
                    }
                    rir::method(x, "len", vec![])
                }
            },
            ExprKind::IfElse(c, a, b) => {
                let cc = self.cond(c);
                let x = self.expr_to(a, opt);
                let y = self.expr_to(b, opt);
                rir::if_(cc, x, y)
            }
        }
    }
    fn name_expr(&mut self, e: &Expr, n: &Name) -> RExpr {
        match self.res.res(n.id) {
            Some(Res::Local(s)) => {
                let sym = self.res.sym(s);
                if sym.is_static {
                    return rir::atom_e(self.static_value(s));
                }
                let read = self.read_sym(s);
                match self.ck.info.narrowed.get(&e.id) {
                    Some(Narrow::NonNil) if self.sym_opt(s) => rir::call("lr::narrowed", vec![read]),
                    Some(Narrow::PcallOk) => {
                        let read = if self.sym_opt(s) { rir::call("lr::narrowed", vec![read]) } else { read };
                        rir::method(read, "ok_value", vec![])
                    }
                    Some(Narrow::PcallErr) => {
                        let read = if self.sym_opt(s) { rir::call("lr::narrowed", vec![read]) } else { read };
                        rir::method(read, "err_value", vec![])
                    }
                    _ => read,
                }
            }
            Some(Res::Builtin(_)) => rir::atom_e("lr::program_args()"),
            None => rir::atom_e("()"),
        }
    }

    /// Singleton function value for a static function (keeps identity stable).
    fn static_value(&mut self, s: SymId) -> String {
        let fname = self.static_fn_name(s);
        let vname = format!("{}_VALUE", fname.to_uppercase());
        if !self.static_values.contains_key(&s) {
            let slot = self.ck.info.sym_slot[&s];
            let f = self.func_of(slot.ty);
            let (args, ret) = self.fn_args(&f);
            let n = f.params.len() + usize::from(f.vararg.is_some());
            let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
            let def = format!(
                "thread_local! {{\n    static {vname}: std::cell::RefCell<Option<lr::LFn<{args}, {ret}>>> = const {{ std::cell::RefCell::new(None) }};\n}}\n\n/// The function value of `{fname}` (one identity per program run).\nfn {}() -> lr::LFn<{args}, {ret}> {{\n    {vname}.with(|v| v.borrow_mut().get_or_insert_with(|| lr::LFn::from_fn(|{}| {fname}({}))).clone())\n}}\n",
                vname.to_lowercase(),
                tuple_ty(&names),
                names.join(", ")
            );
            self.static_values.insert(s, def);
            self.module_releases.push(format!("{vname}.with(|v| v.borrow_mut().take());"));
        }
        format!("{}()", vname.to_lowercase())
    }

    fn table(&mut self, e: &Expr, items: &[TableItem]) -> RExpr {
        let t = self.ck.info.expr[&e.id].ty;
        let TyNode::Table(tab) = self.node(t) else { return rir::atom_e("()") };
        let root = self.ck.st.tab_root(tab);
        let tn = self.ck.st.tab(root).clone();
        if tn.runtime { return self.runtime_constructor_code(e, items); }

        if tn.sparse {
            let args: Vec<Expr> = items.iter().filter_map(|i| match i { TableItem::Pos(e) => Some(e.clone()), _ => None }).collect();
            let values = self.boxed_list(&args);
            return rir::call("lr::packs::table", vec![values]);
        }
        match tn.kind {
            TKind::Array | TKind::Unknown => {
                if items.is_empty() {
                    // Any-array length and mutation observe Luau's predicted allocation too.
                    let any_layout = tn.elem.is_some_and(|slot| self.is_any_ty(slot.ty)) && self.table_layout(e) != (0, 0);
                    if self.uses_next_table(tab) || any_layout {
                        let init = rir::call("lr::Arr::with_layout", self.layout_args(e));
                        return self.inferred_table_constructor(t, init);
                    }
                    let ty = self.rust_ty(t);
                    return rir::atom_e(format!("<{ty}>::new()"));
                }
                let mut elems: Vec<RExpr> = Vec::new();
                let mut pre: Vec<RStmt> = Vec::new();
                for (i, it) in items.iter().enumerate() {
                    let TableItem::Pos(x) = it else { continue };
                    if i + 1 == items.len() && self.is_pack(x) {
                        let (p, pvals, src, start) = self.pack_src(x);
                        if !p.is_empty() {
                            let mut bound = Vec::new();
                            for el in elems.drain(..) {
                                let tv = self.fresh("e");
                                pre.push(rir::let_(tv.clone(), el));
                                bound.push(rir::atom_e(tv));
                            }
                            elems = bound;
                            pre.extend(p);
                        }
                        for v in pvals {
                            elems.push(self.coerce(v, false, x.span, "arrays cannot contain nil"));
                        }
                        let fixed = RExpr::Macro("vec".into(), std::mem::take(&mut elems));
                        let arr = rir::call("lr::va::array", vec![fixed, rir::borrow(src), start]);
                        return rir::block(pre, rir::at(arr, &self.loc(x.span)));
                    }
                    if i + 1 == items.len() && matches!(x.kind, ExprKind::Call(..) | ExprKind::Method(..)) {
                        let (p, vals) = self.multi(x, None);
                        if !p.is_empty() {
                            // keep evaluation order: earlier items first
                            let mut bound = Vec::new();
                            for el in elems.drain(..) {
                                let tv = self.fresh("e");
                                pre.push(rir::let_(tv.clone(), el));
                                bound.push(rir::atom_e(tv));
                            }
                            elems = bound;
                            pre.extend(p);
                        }
                        for v in vals {
                            elems.push(self.coerce(v, false, x.span, "arrays cannot contain nil"));
                        }
                    } else {
                        elems.push(self.expr_to(x, false));
                    }
                }
                let values = RExpr::Macro("vec".into(), elems);
                let init = if self.uses_next_table(tab) {
                    let mut args = vec![values]; args.extend(self.layout_args(e));
                    rir::call("lr::Arr::from_vec_with_layout", args)
                } else { rir::call("lr::Arr::from_vec", vec![values]) };
                rir::block(pre, init)
            }
            TKind::Map => {
                let m = self.fresh("m");
                let ty = self.rust_ty(t);
                let dynamic = tn.key.is_some_and(|key| self.is_any_ty(key.ty));
                let hinted = dynamic || self.uses_next_table(tab);
                if items.is_empty() {
                    if hinted {
                        let mut args = self.layout_args(e);
                        let path = if dynamic { args.push(rir::atom_e("lr::dynamic::Key::layout_key")); "lr::LMap::with_key_layout" } else { "lr::LMap::with_layout" };
                        return self.inferred_table_constructor(t, rir::call(path, args));
                    }
                    return rir::atom_e(format!("<{ty}>::new()"));
                }
                let init = if hinted {
                    let mut args = self.layout_args(e);
                    let path = if dynamic { args.push(rir::atom_e("lr::dynamic::Key::layout_key")); "lr::LMap::with_key_layout" } else { "lr::LMap::with_layout" };
                    rir::call(path, args)
                } else { rir::call(format!("<{ty}>::new"), vec![]) };
                let mut stmts = vec![if hinted { RStmt::Let(m.clone(), Some(ty), init) } else { rir::let_(m.clone(), init) }];
                for it in items {
                    let TableItem::Keyed(k, v) = it else { continue };
                    if dynamic {
                        let key = self.raw_map_key(k);
                        let key_name = self.fresh("key");
                        stmts.push(rir::let_(key_name.clone(), key));
                        let value = self.expr_to(v, false);
                        let value_name = self.fresh("value");
                        stmts.push(rir::let_(value_name.clone(), value));
                        let key = rir::at(rir::call("lr::dynamic::Key::new", vec![rir::atom_e(key_name)]), &self.loc(k.span));
                        stmts.push(RStmt::Semi(rir::method(rir::atom_e(m.clone()), "set", vec![key, rir::atom_e(value_name)])));
                        continue;
                    }
                    let kc = self.map_key_for(k, tab);
                    let vc = self.expr_to(v, false);
                    stmts.push(RStmt::Semi(rir::method(rir::atom_e(m.clone()), "set", vec![kc, vc])));
                }
                rir::block(stmts, rir::atom_e(m))
            }
            TKind::Record => {
                let name = self.record_name(root);
                let mut fields = Vec::new();
                let mut seen = HashSet::new();
                for it in items {
                    let (field, x) = match it {
                        TableItem::Named(n, x) => (n.text.clone(), x),
                        TableItem::Keyed(key, x) => match self.ck.info.record_keys.get(&key.id) {
                            Some(field) => (field.clone(), x),
                            None => continue,
                        },
                        _ => continue,
                    };
                    let opt = self.field_store_opt(root, &field);
                    let v = self.expr_to(x, opt);
                    fields.push((rust_ident(&field), v));
                    seen.insert(field);
                }
                for f in tn.fields.keys() {
                    if !seen.contains(f) {
                        fields.push((rust_ident(f), rir::atom_e("None")));
                    }
                }
                let constructor = if tn.parent.is_some() || tn.metatable.is_some() { "lr::MetaRec::new" } else { "lr::Rec::new" };
                rir::call(constructor, vec![RExpr::Struct(name, fields)])
            }
        }
    }

    fn map_key(&mut self, k: &Expr) -> RExpr {
        let kt = self.ck.info.expr[&k.id].ty;
        let code = self.expr_nn(k, "table index is nil");
        match self.node(kt) {
            TyNode::Num => rir::at(rir::call("lr::NumKey::new", vec![code]), &self.loc(k.span)),
            _ => code,
        }
    }

    fn map_key_read(&mut self, k: &Expr, map: &str) -> RExpr {
        let kt = self.ck.info.expr[&k.id].ty;
        let code = self.expr_nn(k, "table index is nil");
        let map = rir::atom_e(map);
        match self.node(kt) {
            TyNode::Num => {
                let key = rir::method(rir::call("lr::NumKey::new", vec![code]), "ok", vec![]);
                rir::method(key, "and_then", vec![rir::closure("k", rir::method(map, "get", vec![rir::borrow(rir::atom_e("k"))]))])
            }
            _ => rir::method(map, "get", vec![rir::borrow(code)]),
        }
    }

    /// `obj.read(|__r| __r.field.clone())`: a record field's value.
    fn record_read(obj: RExpr, field: &str) -> RExpr {
        let f = rir::method(rir::field(rir::atom_e("__r"), rust_ident(field)), "clone", vec![]);
        rir::method(obj, "read", vec![rir::closure("__r", f)])
    }

    fn promoted_lookup(&self, node: NodeId) -> Option<crate::check_metatable::RecordLookup> {
        self.ck.info.record_lookups.get(&node).filter(|plan| self.ck.st.tab(plan.tab).parent.is_some() || self.ck.st.tab(plan.tab).metatable.is_some()).cloned()
    }

    fn nil_lookup(&mut self, ty: TyId) -> RExpr {
        RExpr::Generic("None".into(), vec![RType::Named(self.rust_ty(ty))])
    }

    fn lookup_read(&mut self, plan: crate::check_metatable::RecordLookup, obj: RExpr, name: &str) -> Val {
        if !plan.levels.is_empty() {
            return self.general_lookup_read(&plan.levels, obj, name, plan.result.ty);
        }
        let receiver = self.fresh("o");
        let own = plan.own.map(|_| Val {
            code: Self::record_read(rir::atom_e(receiver.clone()), name), opt: self.field_store_opt(plan.tab, name),
        });
        if let Some(value) = own.as_ref().filter(|v| !v.opt) {
            return Val { code: rir::block(vec![rir::let_(receiver, obj)], value.code.clone()), opt: false };
        }
        // Luau 0.743: nil alone falls back; each parent access uses a live handle after the borrow ends.
        let fallback = match plan.fallback {
            Some((parent, _)) => {
                let read = Self::record_read(rir::atom_e("__parent"), name);
                let read = if self.field_store_opt(parent, name) { read } else { rir::some(read) };
                rir::match_(rir::method(rir::atom_e(receiver.clone()), "parent", vec![]), vec![
                    ("Some(__parent)".into(), read), ("None".into(), self.nil_lookup(plan.result.ty)),
                ])
            }
            None => self.nil_lookup(plan.result.ty),
        };
        let read = match own {
            Some(value) => rir::match_(value.code, vec![("Some(__value)".into(), rir::some(rir::atom_e("__value"))), ("None".into(), fallback)]),
            None => fallback,
        };
        Val { code: rir::block(vec![rir::let_(receiver, obj)], read), opt: true }
    }

    fn general_lookup_read(&mut self, levels: &[crate::check_metatable_general::LookupLevel], obj: RExpr, name: &str, result: TyId) -> Val {
        let Some(level) = levels.first() else { return Val { code: self.nil_lookup(result), opt: true }; };
        let receiver = self.fresh("o");
        let own = level.own.map(|_| Val {
            code: Self::record_read(rir::atom_e(receiver.clone()), name),
            opt: self.field_store_opt(level.tab, name),
        });
        if let Some(value) = own.as_ref().filter(|v| !v.opt) {
            return Val { code: rir::block(vec![rir::let_(receiver, obj)], value.code.clone()), opt: false };
        }
        // Luau 0.743: on an own miss, read only the actual metatable's raw __index, then continue lookup.
        let fallback = match (level.metadata, levels.get(1)) {
            (Some((meta, Some(_))), Some(_)) => {
                let next = self.general_lookup_read(&levels[1..], rir::atom_e("__parent"), name, result);
                let next = if next.opt { next.code } else { rir::some(next.code) };
                let index = Self::record_read(rir::atom_e("__metatable"), "__index");
                let inherited = if self.field_store_opt(meta, "__index") {
                    rir::match_(index, vec![("Some(__parent)".into(), next), ("None".into(), self.nil_lookup(result))])
                } else {
                    rir::block(vec![rir::let_("__parent", index)], next)
                };
                rir::match_(rir::method(rir::atom_e(receiver.clone()), "parent", vec![]), vec![
                    ("Some(__metatable)".into(), inherited), ("None".into(), self.nil_lookup(result)),
                ])
            }
            _ => self.nil_lookup(result),
        };
        let read = match own {
            Some(value) => rir::match_(value.code, vec![("Some(__value)".into(), rir::some(rir::atom_e("__value"))), ("None".into(), fallback)]),
            None => fallback,
        };
        Val { code: rir::block(vec![rir::let_(receiver, obj)], read), opt: true }
    }

    fn field_read(&mut self, e: &Expr, obj: &Expr, name: &str) -> RExpr {
        if matches!(self.ck.info.access.get(&e.id), Some(Access::Runtime)) {
            return self.runtime_field_code(e, obj, name);
        }
        if self.ck.info.packs.count_reads.contains(&e.id) {
            let object = self.expr_ref(obj, "attempt to index a nil value");
            return rir::method(object, "len", vec![]);
        }
        if let Some(plan) = self.promoted_lookup(e.id) {
            let receiver = self.expr_nn(obj, &format!("attempt to index nil with '{name}'"));
            let value = self.lookup_read(plan, receiver, name);
            return self.coerce(value, self.expr_opt(e), e.span, "attempt to use a nil value");
        }
        match self.ck.info.access.get(&e.id).cloned() {
            Some(Access::MathPi) => rir::atom_e("std::f64::consts::PI"),
            Some(Access::MathHuge) => rir::atom_e("f64::INFINITY"),
            Some(Access::Field(_)) => {
                let o = self.expr_ref(obj, "attempt to index a nil value");
                Self::record_read(o, name)
            }
            Some(Access::Map) => {
                let o = self.expr_ref(obj, "attempt to index a nil value");
                let k = self.named_map_key(obj, name);
                rir::method(o, "get", vec![rir::borrow(k)])
            }
            Some(Access::NativeField(get, _)) => {
                let o = self.expr_ref(obj, "attempt to index a nil value");
                let getter = self.native_wrapper(get);
                rir::try_(rir::call(getter, vec![rir::borrow(o)]))
            }
            Some(Access::NativeConst(inst)) => {
                let w = self.native_wrapper(inst);
                rir::try_(rir::call(w, vec![]))
            }
            Some(Access::Namespace) => rir::atom_e("()"),
            _ => rir::atom_e("()"),
        }
    }

    fn index_read(&mut self, e: &Expr, obj: &Expr, key: &Expr) -> RExpr {
        if matches!(self.ck.info.access.get(&e.id), Some(Access::Runtime)) {
            return self.runtime_index_code(e, obj, key);
        }
        match self.ck.info.access.get(&e.id).cloned() {
            Some(Access::Array) => {
                let o = self.expr_ref(obj, "attempt to index a nil value");
                let k = self.expr_nn(key, "table index is nil");
                let read = rir::method(o, "get", vec![k]);
                if matches!(self.node(self.ck.info.expr[&obj.id].ty), TyNode::Table(t) if self.ck.st.tab(t).sparse) {
                    rir::method(read, "flatten", vec![])
                } else { read }
            }
            Some(Access::Map) => {
                let o = self.expr_nn(obj, "attempt to index a nil value");
                let m = self.fresh("m");
                let tab = match self.node(self.ck.info.expr[&obj.id].ty) { TyNode::Table(tab) => tab, _ => unreachable!() };
                let read = self.map_key_read_for(key, &m, tab);
                rir::block(vec![rir::let_(m, o)], read)
            }
            Some(Access::Field(f)) => {
                if let Some(plan) = self.promoted_lookup(e.id) {
                    let receiver = self.expr_nn(obj, &format!("attempt to index nil with '{f}'"));
                    let value = self.lookup_read(plan, receiver, &f);
                    return self.coerce(value, self.expr_opt(e), e.span, "attempt to use a nil value");
                }
                let o = self.expr_ref(obj, "attempt to index a nil value");
                Self::record_read(o, &f)
            }
            _ => rir::atom_e("()"),
        }
    }
    // Operators

    fn binary(&mut self, e: &Expr, op: BinOp, a: &Expr, b: &Expr, opt: bool) -> RExpr {
        if let Some(kind) = self.ck.info.dynamic.dyn_bin.get(&e.id).copied() {
            return self.dyn_binary_code(e, kind, a, b);
        }
        let arith = "attempt to perform arithmetic on a nil value";
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::IDiv | BinOp::Mod | BinOp::Div | BinOp::Pow if self.is_int_expr(a) => {
                let x = self.expr_nn(a, arith);
                let y = self.expr_nn(b, arith);
                self.int_arith(op, x, y, e.span)
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                let x = self.expr_nn(a, arith);
                let y = self.expr_nn(b, arith);
                rir::bin(rop(op), x, y)
            }
            BinOp::IDiv | BinOp::Mod => {
                let x = self.expr_nn(a, arith);
                let y = self.expr_nn(b, arith);
                let f = if op == BinOp::IDiv { "floor_div" } else { "modulo" };
                rir::call(format!("lr::stdlib::{f}"), vec![x, y])
            }
            BinOp::Pow => {
                let x = self.expr_nn(a, arith);
                let y = self.expr_nn(b, arith);
                rir::call("f64::powf", vec![x, y])
            }
            BinOp::Concat => {
                let mut parts = Vec::new();
                self.concat_parts(e, &mut parts);
                concat_call(parts)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let x = self.expr_nn(a, "attempt to compare a nil value");
                let y = self.expr_nn(b, "attempt to compare a nil value");
                rir::bin(rop(op), x, y)
            }
            BinOp::Eq | BinOp::Ne => {
                let neg = op == BinOp::Ne;
                let a_nil = matches!(a.kind, ExprKind::Nil);
                let b_nil = matches!(b.kind, ExprKind::Nil);
                // Build the negation alongside each form to preserve the expression's structure.
                if a_nil && b_nil {
                    rir::atom_e(if neg { "false" } else { "true" })
                } else if a_nil || b_nil {
                    let x = if a_nil { b } else { a };
                    let v = self.expr(x);
                    if crate::check_dynamic::has_protected_union(&self.ck.st, self.ck.info.expr[&x.id].ty) {
                        // Luau compares the payload, not just an internal wrapper's presence.
                        let nil = rir::call("lr::show::is_nil", vec![rir::borrow(v.code)]);
                        if neg { rir::unary("!", nil) } else { nil }
                    } else if v.opt {
                        rir::method(v.code, if neg { "is_some" } else { "is_none" }, vec![])
                    } else {
                        rir::block(vec![rir::let_("_", v.code)], rir::atom_e(neg.to_string()))
                    }
                } else {
                    let ta = self.ck.info.expr[&a.id].ty;
                    let any_opt = self.expr_opt(a) || self.expr_opt(b);
                    let x = self.expr_to(a, any_opt);
                    let y = self.expr_to(b, any_opt);
                    match self.node(ta) {
                        TyNode::Num | TyNode::Bool if !any_opt => rir::bin(if neg { ROp::Ne } else { ROp::Eq }, x, y),
                        _ => {
                            let eq = rir::call("lr::show::eq", vec![rir::borrow(x), rir::borrow(y)]);
                            if neg {
                                rir::unary("!", eq)
                            } else {
                                eq
                            }
                        }
                    }
                }
            }
            BinOp::And | BinOp::Or => self.logic(e, op == BinOp::And, a, b, opt),
        }
    }

    fn concat_parts(&mut self, e: &Expr, out: &mut Vec<RExpr>) {
        match &e.kind {
            ExprKind::Binary(BinOp::Concat, a, b) if !self.ck.info.dynamic.dyn_bin.contains_key(&e.id) => {
                self.concat_parts(a, out);
                self.concat_parts(b, out);
            }
            _ => out.push(self.expr_ref(e, "attempt to concatenate a nil value")),
        }
    }
    fn logic(&mut self, e: &Expr, and: bool, a: &Expr, b: &Expr, opt: bool) -> RExpr {
        let kind = self.ck.info.logic.get(&e.id).copied().unwrap_or(LogicKind::ValueLeft);
        if matches!(kind, LogicKind::LeftOnly | LogicKind::RightOnly | LogicKind::AnyLeft) {
            return self.dyn_logic_code(kind, and, a, b, opt);
        }
        let av = self.expr(a);
        let x = self.fresh("a");
        let xv = || rir::atom_e(x.clone());
        let rt = self.ck.info.expr[&e.id].ty;
        let truthy = |v: RExpr| rir::call("lr::show::truthy", vec![rir::borrow(v)]);
        match (and, kind) {
            (false, LogicKind::ValueLeft) => {
                if !av.opt {
                    return self.coerce(av, opt, a.span, "");
                }
                let bv = self.expr_to(b, opt);
                let some = if opt { rir::some(xv()) } else { xv() };
                rir::match_(av.code, vec![(format!("Some({x})"), some), ("None".into(), bv)])
            }
            (false, LogicKind::BoolLeft) => {
                let t = rir::atom_e(if opt { "Some(true)" } else { "true" });
                let bv = self.expr_to(b, opt);
                rir::if_(truthy(av.code), t, bv)
            }
            (false, LogicKind::FalseOrLeft) => {
                let bv = self.expr_to(b, opt);
                let some = if opt { rir::some(xv()) } else { xv() };
                if av.opt {
                    rir::match_(av.code, vec![(format!("Some(lr::FalseOr::Val({x}))"), some), ("_".into(), bv)])
                } else {
                    rir::match_(av.code, vec![(format!("lr::FalseOr::Val({x})"), some), ("lr::FalseOr::False".into(), bv)])
                }
            }
            (true, LogicKind::ValueLeft) => {
                let bv = self.expr_to(b, opt);
                if av.opt {
                    let rty = self.rust_ty(rt);
                    rir::match_(av.code, vec![("Some(_)".into(), bv), ("None".into(), rir::atom_e(format!("None::<{rty}>")))])
                } else {
                    rir::block(vec![rir::let_("_", av.code)], bv)
                }
            }
            (true, LogicKind::BoolLeft) | (true, LogicKind::FalseOrLeft) => {
                let is_bool = matches!(self.node(rt), TyNode::Bool);
                if is_bool {
                    let bv = self.expr_to(b, opt);
                    let falsy = if !av.opt && opt { rir::some(xv()) } else { xv() };
                    rir::block(vec![rir::let_(x.clone(), av.code)], rir::if_(truthy(xv()), bv, falsy))
                } else {
                    // false | T
                    let bv = self.expr(b);
                    let val = if bv.opt {
                        if opt {
                            rir::method(bv.code, "map", vec![rir::atom_e("lr::FalseOr::Val")])
                        } else {
                            let c = self.coerce(bv, false, b.span, "attempt to use a nil value");
                            rir::call("lr::FalseOr::Val", vec![c])
                        }
                    } else if opt {
                        rir::some(rir::call("lr::FalseOr::Val", vec![bv.code]))
                    } else {
                        rir::call("lr::FalseOr::Val", vec![bv.code])
                    };
                    let f = rir::atom_e(if opt { "Some(lr::FalseOr::False)" } else { "lr::FalseOr::False" });
                    if av.opt && opt {
                        rir::match_(av.code, vec![("Some(true)".into(), val), ("Some(false)".into(), f), ("None".into(), rir::atom_e("None"))])
                    } else {
                        rir::if_(truthy(av.code), val, f)
                    }
                }
            }
            // lowered before the left operand is evaluated (the early return above)
            (_, LogicKind::LeftOnly | LogicKind::RightOnly | LogicKind::AnyLeft) => unreachable!("dynamic logic is lowered by dyn_logic_code"),
        }
    }
    /// Boolean Rust expression for a condition's truthiness.
    fn cond(&mut self, e: &Expr) -> RExpr {
        let et = self.ck.info.expr[&e.id];
        let v = self.expr(e);
        match self.node(et.ty) {
            TyNode::Bool if !v.opt => v.code,
            TyNode::Bool => rir::bin(ROp::Eq, v.code, rir::some(rir::atom_e("true"))),
            // before the plain-optional arm: `Some(FalseOr::False)` is falsy
            TyNode::FalseOr(_) | TyNode::Pcall(_) | TyNode::Any => rir::call("lr::show::truthy", vec![rir::borrow(v.code)]),
            _ if v.opt => rir::method(v.code, "is_some", vec![]),
            _ => rir::block(vec![rir::let_("_", v.code)], rir::atom_e("true")),
        }
    }
    // Calls

    /// Generates a call producing several values. Returns statements to run first
    /// (binding temporaries) and the value expressions.
    fn multi(&mut self, e: &Expr, want: Option<usize>) -> (Vec<RStmt>, Vec<Val>) {
        if let Some(tail) = self.call_tail(e) {
            // results after the fixed ones come from the result vector
            if want == Some(0) {
                let (code, _) = self.call_raw(e);
                return (vec![RStmt::Semi(code)], vec![]);
            }
            let (pre, mut vals, t) = self.multi_pack(e);
            let n = vals.len();
            let want = want.unwrap_or(n);
            vals.truncate(want);
            for k in vals.len()..want {
                let code = va_get(&t, &rir::atom_e("0"), k - n);
                if self.is_any_ty(tail.ty) {
                    vals.push(Val { code: rir::method(code, "unwrap_or", vec![rir::atom_e("lr::Value::Nil")]), opt: false });
                } else {
                    vals.push(Val { code, opt: true });
                }
            }
            return (pre, vals);
        }
        let (code, outs) = self.call_raw(e);
        let n = outs.len();
        let want = want.unwrap_or(n);
        let mut vals = Vec::new();
        let mut pre = Vec::new();
        match n {
            0 => pre.push(RStmt::Semi(code)),
            1 => {
                if want > 0 {
                    vals.push(Val { code, opt: outs[0].1 });
                } else {
                    pre.push(RStmt::Semi(code));
                }
            }
            _ => {
                if want == 1 {
                    vals.push(Val { code: rir::field(code, "0"), opt: outs[0].1 });
                } else if want == 0 {
                    pre.push(RStmt::Semi(code));
                } else {
                    let names: Vec<String> = (0..n).map(|_| self.fresh("r")).collect();
                    pre.push(rir::let_(format!("({})", names.join(", ")), code));
                    for (i, nm) in names.into_iter().enumerate().take(want) {
                        vals.push(Val { code: rir::atom_e(nm), opt: outs[i].1 });
                    }
                }
            }
        }
        // missing values are nil
        let exp = self.ck.info.expr.get(&e.id).copied();
        while vals.len() < want {
            let t = exp.map(|x| x.ty).unwrap_or(0);
            // The first value has the call's type; later values infer their types
            // from their destinations.
            let code = if vals.is_empty() { format!("None::<{}>", self.rust_ty(t)) } else { "None".to_string() };
            vals.push(Val { code: rir::atom_e(code), opt: true });
        }
        (pre, vals)
    }

    /// A call returning a run-time number of values: statements binding its fixed
    /// results and its result vector, the fixed values, the vector.
    fn multi_pack(&mut self, e: &Expr) -> (Vec<RStmt>, Vec<Val>, RExpr) {
        let (code, outs) = self.call_raw(e);
        let t = self.fresh("t");
        if outs.is_empty() {
            return (vec![rir::let_(t.clone(), code)], vec![], rir::atom_e(t));
        }
        let names: Vec<String> = outs.iter().map(|_| self.fresh("r")).collect();
        let pat = format!("({}, {t})", names.join(", "));
        let vals = names.into_iter().zip(&outs).map(|(n, o)| Val { code: rir::atom_e(n), opt: o.1 }).collect();
        (vec![rir::let_(pat, code)], vals, rir::atom_e(t))
    }

    /// Result tail of the function a call calls.
    fn call_tail(&self, e: &Expr) -> Option<Slot> {
        if self.ck.info.runtime_tables.calls.contains_key(&e.id)
            || matches!(self.ck.info.calls.get(&e.id), Some(CallKind::Builtin(BuiltinFn::SelectFixed | BuiltinFn::PcallPack))) {
            return self.ck.info.pack_calls.get(&e.id).map(|value| Slot { ty: value.ty, null: value.null });
        }
        if let Some(tail) = self.ck.info.coroutines.tails.get(&e.id) { return Some(*tail); }
        match (&e.kind, self.ck.info.calls.get(&e.id)) {
            (ExprKind::Call(..), Some(CallKind::Static(s))) => self.ck.callee_tail(self.ck.info.sym_slot[s].ty),
            (ExprKind::Call(f, _), Some(CallKind::Value)) => self.ck.callee_tail(self.ck.info.expr[&f.id].ty),
            (ExprKind::Method(o, name, _), Some(CallKind::RecordMethod(_))) => self.ck.method_tail(self.ck.info.expr[&o.id], &name.text),
            // `table.unpack`: the array's element slot
            (ExprKind::Call(_, args), Some(CallKind::Builtin(BuiltinFn::TUnpack))) => match self.node(self.ck.info.expr[&args[0].id].ty) {
                TyNode::Table(tab) => self.ck.st.tab(self.ck.st.tab_root(tab)).elem,
                _ => None,
            },
            (_, Some(CallKind::Builtin(_))) => self.ck.info.pack_calls.get(&e.id).map(|v| Slot { ty: v.ty, null: v.null }),
            _ => None,
        }
    }

    /// Code of a call (with `?` applied) and its result types (type, is_optional).
    fn call_raw(&mut self, e: &Expr) -> (RExpr, Vec<(TyId, bool)>) {
        if let Some(call) = self.ck.info.runtime_tables.calls.get(&e.id).cloned() {
            return self.runtime_call_code(e, call);
        }
        let kind = self.ck.info.calls.get(&e.id).cloned();
        match (&e.kind, kind) {
            (ExprKind::Call(_, args), Some(CallKind::RecordParent)) => {
                let (mut pre, values) = self.args_e(args, &[false, false], false);
                let mut bound = Vec::new();
                for value in values {
                    let name = self.fresh("meta");
                    pre.push(rir::let_(name.clone(), value));
                    bound.push(rir::atom_e(name));
                }
                let attach = rir::method(bound[0].clone(), "attach", vec![bound[1].clone()]);
                (rir::block(pre, attach), vec![(self.ck.info.expr[&args[0].id].ty, false)])
            }
            (ExprKind::Call(_, args), Some(CallKind::Builtin(b))) => self.builtin(e, b, None, args),
            (ExprKind::Method(o, _, args), Some(CallKind::Builtin(b))) => self.builtin(e, b, Some(o), args),
            (ExprKind::Call(_, _), Some(CallKind::Require(mi))) => {
                let id = self.units[mi].ident.clone();
                let outs = match self.ck.info.module_value[mi] {
                    Some(v) => vec![(v.ty, self.ety_opt(v))],
                    None => vec![],
                };
                (rir::try_(rir::call(format!("crate::{id}::require"), vec![])), outs)
            }
            (ExprKind::Call(_, _), Some(CallKind::RequireRust)) => (rir::atom_e("()"), vec![(0, false)]),
            (ExprKind::Call(_, args), Some(CallKind::Task(name))) => {
                let (code, outs) = self.task_call_code(e, &name, args);
                (code.into(), outs)
            }
            (ExprKind::Call(_, args), Some(CallKind::Coroutine(name))) => self.coroutine_call_code(e, &name, args),
            (ExprKind::Call(_, args), Some(CallKind::Await)) => {
                let mut f = self.expr_nn(&args[0], "attempt to await a nil value");
                let mut ft = self.ck.info.expr[&args[0].id].ty;
                let loc = self.loc(e.span);
                if let Some(&inst) = self.ck.info.await_native.get(&e.id) {
                    // a native value implementing Future: consumed into a future
                    let w = self.native_wrapper(inst);
                    f = rir::at(rir::call(w, vec![rir::borrow(f)]), &loc);
                    ft = self.ck.info.natives[inst].rets[0].ty;
                }
                let outs: Vec<(TyId, bool)> = match self.node(ft) {
                    TyNode::Future(r) => r.iter().map(|s| (s.ty, self.is_null(s.null))).collect(),
                    _ => vec![],
                };
                (rir::at(rir::field(rir::call("lr::task::wait", vec![f]), "await"), &loc), outs)
            }
            (ExprKind::Call(_, args), Some(CallKind::Native(inst))) => {
                let w = self.native_wrapper(inst);
                let ni = self.ck.info.natives[inst].clone();
                let (pre, argv) = self.args_e(args, &ni.params.iter().map(|p| self.is_null(p.null)).collect::<Vec<_>>(), false);
                let outs: Vec<(TyId, bool)> = ni.rets.iter().map(|s| (s.ty, self.is_null(s.null))).collect();
                (rir::block(pre, rir::at(rir::call(w, argv), &self.loc(e.span))), outs)
            }
            (ExprKind::Method(o, _, args), Some(CallKind::Native(inst))) => {
                let w = self.native_wrapper(inst);
                let ni = self.ck.info.natives[inst].clone();
                let obj = self.expr_nn(o, "attempt to call a method on a nil value");
                let ob = self.fresh("o");
                let (pre, argv) = self.args_e(args, &ni.params.iter().map(|p| self.is_null(p.null)).collect::<Vec<_>>(), false);
                let outs: Vec<(TyId, bool)> = ni.rets.iter().map(|s| (s.ty, self.is_null(s.null))).collect();
                let mut all = vec![rir::borrow(rir::atom_e(ob.clone()))];
                all.extend(argv);
                let mut stmts = vec![rir::let_(ob, obj)];
                stmts.extend(pre);
                (rir::block(stmts, rir::at(rir::call(w, all), &self.loc(e.span))), outs)
            }
            (ExprKind::Method(o, name, args), Some(CallKind::RecordMethod(_))) => {
                if let (Some(method), Some(plan)) = (self.ck.info.record_methods.get(&e.id).copied(), self.ck.info.record_lookups.get(&e.id).cloned()) {
                    return self.record_method_call(e, o, name, args, method, plan);
                }
                let obj = self.expr_nn(o, "attempt to call a method on a nil value");
                let ot = self.ck.info.expr[&o.id].ty;
                let TyNode::Table(tab) = self.node(ot) else { unreachable!() };
                let root = self.ck.st.tab_root(tab);
                let fslot = self.ck.st.tab(root).fields[&name.text];
                let f = self.func_of(fslot.ty);
                let ob = self.fresh("o");
                let fv = self.fresh("f");
                let store_opt = self.field_store_opt(root, &name.text);
                let read = Self::record_read(rir::atom_e(ob.clone()), &name.text);
                let fcode = self.coerce(
                    Val { code: read, opt: store_opt },
                    false,
                    name.span,
                    &format!("attempt to call missing method '{}'", name.text),
                );
                let popt: Vec<bool> = f.params.iter().map(|p| self.is_null(p.null)).collect();
                let (pre, mut argv) = self.args_e(args, &popt[1.min(popt.len())..], f.vararg.is_some());
                let this = rir::method(rir::atom_e(ob.clone()), "clone", vec![]);
                let self_arg = if popt.first().copied().unwrap_or(false) { rir::some(this) } else { this };
                argv.insert(0, self_arg);
                let rets = self.ck.st.rets_known(f.rets).cloned().unwrap_or_default();
                let outs = rets.iter().map(|s| (s.ty, self.is_null(s.null))).collect();
                let mut stmts = vec![rir::let_(ob, obj), rir::let_(fv.clone(), fcode)];
                stmts.extend(pre);
                (rir::block(stmts, rir::try_(rir::method(rir::atom_e(fv), "call", vec![RExpr::Tuple(argv)]))), outs)
            }
            (ExprKind::Call(_, args), Some(CallKind::Static(s))) => {
                let slot = self.ck.info.sym_slot[&s];
                let ft = self.func_of(slot.ty);
                let popt: Vec<bool> = ft.params.iter().map(|p| self.is_null(p.null)).collect();
                let (pre, argv) = self.args_e(args, &popt, ft.vararg.is_some());
                let rets = self.ck.st.rets_known(ft.rets).cloned().unwrap_or_default();
                let outs = rets.iter().map(|s| (s.ty, self.is_null(s.null))).collect();
                (rir::block(pre, rir::try_(rir::call(self.static_fn_name(s), argv))), outs)
            }
            (ExprKind::Call(f, args), _) => {
                let ft_id = self.ck.info.expr[&f.id].ty;
                let ft = self.func_of(ft_id);
                if self.promoted_callee(f) {
                    return self.record_dot_call(e, f, args, &ft);
                }
                let fc = self.expr_ref(f, "attempt to call a nil value");
                let popt: Vec<bool> = ft.params.iter().map(|p| self.is_null(p.null)).collect();
                let (pre, argv) = self.args_e(args, &popt, ft.vararg.is_some());
                let rets = self.ck.st.rets_known(ft.rets).cloned().unwrap_or_default();
                let outs = rets.iter().map(|s| (s.ty, self.is_null(s.null))).collect();
                if pre.is_empty() {
                    (self.coroutine_source_call(e, &ft, rir::method(fc, "call", vec![RExpr::Tuple(argv)])), outs)
                } else {
                    let fv = self.fresh("f");
                    let mut stmts = vec![rir::let_(fv.clone(), fc)];
                    stmts.extend(pre);
                    (rir::block(stmts, self.coroutine_source_call(e, &ft, rir::method(rir::atom_e(fv), "call", vec![RExpr::Tuple(argv)]))), outs)
                }
            }
            _ => (rir::atom_e("()"), vec![]),
        }
    }

    fn args_e(&mut self, args: &[Expr], params: &[bool], vararg: bool) -> (Vec<RStmt>, Vec<RExpr>) {
        let args: Vec<Arg> = args.iter().map(Arg::E).collect();
        self.args(&args, params, vararg)
    }

    fn promoted_callee(&self, expr: &Expr) -> bool {
        self.promoted_lookup(expr.id).is_some() || matches!(&expr.kind, ExprKind::Paren(inner) if self.promoted_callee(inner))
    }

    fn local_method_receiver(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Paren(inner) => self.local_method_receiver(inner),
            ExprKind::Name(name) => {
                let func = match self.fn_rets.last() {
                    Some(FnRets::Func(_, _, func)) => *func,
                    _ => self.units[self.cur_module].pseudo_func,
                };
                matches!(self.res.res(name.id), Some(Res::Local(sym)) if self.res.sym(sym).func == func)
            }
            _ => false,
        }
    }

    fn bind_call_args(&mut self, pre: &mut Vec<RStmt>, args: Vec<RExpr>) -> Vec<RExpr> {
        args.into_iter().map(|arg| {
            let name = self.fresh("arg");
            pre.push(rir::let_(name.clone(), arg));
            rir::atom_e(name)
        }).collect()
    }

    fn record_dot_call(&mut self, e: &Expr, callee: &Expr, args: &[Expr], ft: &FuncTy) -> (RExpr, Vec<(TyId, bool)>) {
        // Luau 0.743: snapshot dot lookup before arguments, but raise a nil-call error after them.
        let value = self.expr(callee);
        let name = self.fresh("f");
        let mut stmts = vec![rir::let_(name.clone(), value.code)];
        let params: Vec<_> = ft.params.iter().map(|p| self.is_null(p.null)).collect();
        let (pre, argv) = self.args_e(args, &params, ft.vararg.is_some());
        stmts.extend(pre);
        let argv = self.bind_call_args(&mut stmts, argv);
        let f = self.coerce(Val { code: rir::atom_e(name), opt: value.opt }, false, e.span, "attempt to call a nil value");
        let outs = self.ck.st.rets_known(ft.rets).into_iter().flatten().map(|s| (s.ty, self.is_null(s.null))).collect();
        (rir::block(stmts, self.coroutine_source_call(e, ft, rir::method(f, "call", vec![RExpr::Tuple(argv)]))), outs)
    }

    fn record_method_call(&mut self, e: &Expr, obj: &Expr, name: &Name, args: &[Expr], method: ETy, plan: crate::check_metatable::RecordLookup) -> (RExpr, Vec<(TyId, bool)>) {
        // Luau 0.743: colon arguments precede live method lookup, including its nil errors.
        let receiver = self.expr(obj);
        let ob = self.fresh("o");
        let binding = rir::let_(ob.clone(), receiver.code);
        // Luau 0.743 NAMECALL: a current-function local is read after arguments; upvalues and expressions are saved first.
        let (mut stmts, delayed) = if self.local_method_receiver(obj) { (vec![], Some(binding)) } else { (vec![binding], None) };
        let ft = self.func_of(method.ty);
        let params: Vec<_> = ft.params.iter().skip(1).map(|p| self.is_null(p.null)).collect();
        let (pre, argv) = self.args_e(args, &params, ft.vararg.is_some());
        stmts.extend(pre);
        let mut argv = self.bind_call_args(&mut stmts, argv);
        stmts.extend(delayed);
        let receiver = self.coerce(Val { code: rir::atom_e(ob), opt: receiver.opt }, false, obj.span, &format!("attempt to index nil with '{}'", name.text));
        let saved = self.fresh("self");
        stmts.push(rir::let_(saved.clone(), receiver));
        let this = rir::method(rir::atom_e(saved.clone()), "clone", vec![]);
        if let Some(param) = ft.params.first() {
            argv.insert(0, if self.is_null(param.null) { rir::some(this) } else { this });
        } else if ft.vararg.is_some() {
            let rest = argv.remove(0);
            argv.push(rir::call("lr::va::with_rest", vec![RExpr::Macro("vec".into(), vec![rir::some(this)]), rir::borrow(rest), rir::atom_e("0")]));
        }
        let read = self.lookup_read(plan, rir::borrow(rir::atom_e(saved)), &name.text);
        let f = self.coerce(read, false, e.span, &format!("attempt to call missing method '{}' of table", name.text));
        let outs = self.ck.st.rets_known(ft.rets).into_iter().flatten().map(|s| (s.ty, self.is_null(s.null))).collect();
        (rir::block(stmts, rir::try_(rir::method(f, "call", vec![RExpr::Tuple(argv)]))), outs)
    }

    /// Argument list with Lua adjustment; `params` gives each parameter's
    /// optionality. A variadic callee (`vararg`) gets its extra arguments as one
    /// more argument, the vector of its `...`.
    fn args(&mut self, args: &[Arg], params: &[bool], vararg: bool) -> (Vec<RStmt>, Vec<RExpr>) {
        let mut out = Vec::new();
        let mut pre = Vec::new();
        let mut vals: Vec<(Val, Span)> = Vec::new();
        // a trailing `...` passes its run-time number of values
        let (args, pack) = match args.last() {
            Some(Arg::E(e)) if self.is_pack(e) => (&args[..args.len() - 1], Some(*e)),
            _ => (args, None),
        };
        for (i, a) in args.iter().enumerate() {
            match Self::arg_call(a) {
                // (before a trailing pack an argument is one value)
                Some(c) if i + 1 == args.len() && pack.is_none() => {
                    let remaining = params.len().saturating_sub(vals.len());
                    // a variadic callee takes all the results
                    let want = if vararg { None } else { Some(remaining.max(if params.len() > vals.len() { 1 } else { 0 })) };
                    let (p, vs) = self.multi(c, want);
                    if !p.is_empty() {
                        // evaluate earlier arguments first
                        let mut bound = Vec::new();
                        for (v, sp) in vals.drain(..) {
                            let t = self.fresh("x");
                            pre.push(rir::let_(t.clone(), v.code));
                            bound.push((Val { code: rir::atom_e(t), opt: v.opt }, sp));
                        }
                        vals = bound;
                        pre.extend(p);
                    }
                    for v in vs {
                        vals.push((v, c.span));
                    }
                }
                _ => {
                    let v = self.arg_val(a);
                    vals.push((v, Self::arg_span(a)));
                }
            }
        }
        // the trailing `...` fills the remaining parameters (nil when it runs out),
        // the rest of it goes to the callee's `...`
        let mut pack_rest = None;
        if let Some(p) = pack {
            let (p_pre, pvals, src, start) = self.pack_src(p);
            if !p_pre.is_empty() {
                for (v, _) in vals.iter_mut() {
                    let t = self.fresh("x");
                    let c = std::mem::replace(&mut v.code, rir::atom_e(t.clone()));
                    pre.push(rir::let_(t, c));
                }
                pre.extend(p_pre);
            }
            vals.extend(pvals.into_iter().map(|v| (v, p.span)));
            let mut k = 0;
            while vals.len() < params.len() {
                vals.push((Val { code: va_get(&src, &start, k), opt: true }, p.span));
                k += 1;
            }
            pack_rest = Some((src, va_index(&start, k)));
        }
        let extra: Vec<(Val, Span)> = if vals.len() > params.len() { vals.split_off(params.len()) } else { Vec::new() };
        if vararg {
            for (i, (v, sp)) in vals.into_iter().enumerate() {
                out.push(self.coerce(v, params[i], sp, "attempt to use a nil value"));
            }
            for _ in out.len()..params.len() {
                out.push(rir::atom_e("None"));
            }
            let items: Vec<RExpr> = extra.into_iter().map(|(v, sp)| self.coerce(v, true, sp, "")).collect();
            let fixed = RExpr::Macro("vec".into(), items);
            out.push(match pack_rest {
                Some((src, i)) => rir::call("lr::va::with_rest", vec![fixed, rir::borrow(src), i]),
                None => fixed,
            });
            return (pre, out);
        }
        if !extra.is_empty() {
            // Extra arguments are evaluated in `pre`; the kept ones must run before
            // them, left to right, so they are bound first.
            for (v, _) in vals.iter_mut() {
                let t = self.fresh("x");
                let c = std::mem::replace(&mut v.code, rir::atom_e(t.clone()));
                pre.push(rir::let_(t, c));
            }
        }
        for (i, (v, sp)) in vals.into_iter().enumerate() {
            out.push(self.coerce(v, params[i], sp, "attempt to use a nil value"));
        }
        for _ in out.len()..params.len() {
            out.push(rir::atom_e("None"));
        }
        // Extra arguments are evaluated (for their effects) and discarded.
        for (v, _) in extra {
            pre.push(rir::let_("_", v.code));
        }
        (pre, out)
    }

    fn builtin(&mut self, e: &Expr, b: BuiltinFn, recv: Option<&Expr>, args: &[Expr]) -> (RExpr, Vec<(TyId, bool)>) {
        if let Some(result) = self.pack_builtin(e, b, args) { return result; }
        if b == BuiltinFn::TClone && args.first().is_some_and(|arg| self.ck.runtime_type(self.ck.info.expr[&arg.id].ty)) {
            let table = self.expr_nn(&args[0], "bad argument #1 to 'clone' (table expected, got nil)");
            return (rir::at(rir::method(table, "checked_clone", vec![]), &self.loc(e.span)), vec![(self.ck.info.expr[&e.id].ty, false)]);
        }
        if b == BuiltinFn::TSort && args.first().is_some_and(|t| matches!(self.node(self.ck.info.expr[&t.id].ty), TyNode::Table(tab) if self.ck.st.tab(tab).runtime)) {
            return (self.runtime_sort_code(e, args), vec![]);
        }
        if matches!(b, BuiltinFn::TClear | BuiltinFn::Next) {
            return self.iteration_builtin(e, b, args);
        }
        // Luau 0.743: a clone shares live metadata and owns its copied storage/attachment state.
        if b == BuiltinFn::TClone && matches!(self.node(self.ck.info.expr[&e.id].ty), TyNode::Table(t) if self.ck.st.tab(t).metatable.is_some()) {
            if let Some(arg) = args.first() {
                let value = self.expr_nn(arg, "bad argument #1 to 'clone' (table expected, got nil)");
                return (rir::method(value, "shallow_clone", vec![]), vec![(self.ck.info.expr[&e.id].ty, false)]);
            }
        }
        let mut all: Vec<Arg> = Vec::new();
        if let Some(r) = recv {
            all.push(Arg::E(r));
        }
        let Some(tail_tys) = self.ck.info.multi_tail.get(&e.id).cloned() else {
            all.extend(args.iter().map(Arg::E));
            if let Some(result) = self.library_builtin(e, b, &all) { return result; }
            let (code, outs) = self.builtin_args(e, b, all);
            return (code.into(), outs);
        };
        // The last argument is a call giving zero or several values.
        // The other arguments are evaluated first, left to right, into
        // temporaries; then the call's results are destructured and passed as
        // separate argument values.
        let (last, kept) = args.split_last().expect("multi_tail has a last argument");
        all.extend(kept.iter().map(Arg::E));
        let mut pre = Vec::new();
        for a in all.iter_mut() {
            let x: &Expr = match a {
                Arg::E(x) => x,
                Arg::V(..) => continue,
            };
            if matches!(x.kind, ExprKind::Nil | ExprKind::Bool(_) | ExprKind::Number(_) | ExprKind::Int(_) | ExprKind::Str(_)) {
                continue; // no side effects to order
            }
            let v = self.expr(x);
            let t = self.fresh("x");
            pre.push(rir::let_(t.clone(), v.code));
            *a = Arg::V(Val { code: rir::atom_e(t), opt: v.opt }, self.ck.info.expr[&x.id], x.span);
        }
        let (p, vals) = self.multi(last, Some(tail_tys.len()));
        pre.extend(p);
        for (t, v) in tail_tys.iter().zip(vals) {
            all.push(Arg::V(v, *t, last.span));
        }
        if let Some((code, outs)) = self.library_builtin(e, b, &all) { return (rir::block(pre, code), outs); }
        let (code, outs) = self.builtin_args(e, b, all);
        (rir::block(pre, code), outs)
    }
    /// Code of builtin `b` applied to the argument expressions `all` (receiver first).
    fn builtin_args(&mut self, e: &Expr, b: BuiltinFn, all: Vec<Arg>) -> (String, Vec<(TyId, bool)>) {
        use BuiltinFn::*;
        let num = |t: &mut Self| (t.ck.st.tys.len() as TyId, false);
        let _ = num;
        let sty = self.ck.info.expr[&e.id].ty;
        let loc = self.loc(e.span);
        match b {
            Bit32(_) | StrSplit | Xpcall | TFreeze | TIsFrozen | TMove => unreachable!("new libraries are lowered by library_builtin"),
            TPack | SelectFixedCount | SelectFixed | PcallPack => unreachable!("pack builtins use rir lowering"),
            TClear | Next => unreachable!("lowered through structured traversal nodes"),
            Print => {
                let mut pre = String::new();
                let mut items: Vec<RExpr> = Vec::new();
                let (all, pack) = match all.last() {
                    Some(Arg::E(x)) if self.is_pack(x) => (&all[..all.len() - 1], Some(*x)),
                    _ => (&all[..], None),
                };
                for (i, a) in all.iter().enumerate() {
                    if let (true, Some(c)) = (i + 1 == all.len() && pack.is_none(), Self::arg_call(a)) {
                        let (p, vs) = self.multi(c, None);
                        if !p.is_empty() {
                            let mut bound = Vec::new();
                            for it in items.drain(..) {
                                let t = self.fresh("p");
                                let _ = write!(pre, "let {t} = {}; ", strip(it));
                                bound.push(rir::atom_e(t));
                            }
                            items = bound;
                            pre.push_str(&stmts_text(&p));
                        }
                        items.extend(vs.into_iter().map(|v| v.code));
                    } else {
                        items.push(self.arg_ref_val(a).code);
                    }
                }
                let start = match pack {
                    Some(x) => {
                        let (p, pvals, src, start) = self.pack_src(x);
                        if !p.is_empty() {
                            let mut bound = Vec::new();
                            for it in items.drain(..) {
                                let t = self.fresh("p");
                                let _ = write!(pre, "let {t} = {}; ", strip(it));
                                bound.push(rir::atom_e(t));
                            }
                            items = bound;
                            pre.push_str(&stmts_text(&p));
                        }
                        items.extend(pvals.into_iter().map(|v| v.code));
                        Some((src, start))
                    }
                    None => None,
                };
                let mut refs: Vec<String> = items.into_iter().map(|c| format!("&{}", atom(c))).collect();
                if let Some(f) = refs.first_mut() {
                    *f = format!("{f} as &dyn lr::LuaDisplay");
                }
                let call = match start {
                    Some((src, st)) => format!("lr::va::print(&[{}], &{}, {})", refs.join(", "), atom(src), strip(st)),
                    None if refs.is_empty() => "lr::stdlib::print(&[])".to_string(),
                    None => format!("lr::stdlib::print(&[{}])", refs.join(", ")),
                };
                (if pre.is_empty() { call } else { format!("{{ {pre}{call} }}") }, vec![])
            }
            ToString => {
                let v = self.arg_ref_val(&all[0]);
                (format!("lr::show::tostring(&{})", atom(v.code)), vec![(sty, false)])
            }
            Type => {
                let v = self.arg_ref_val(&all[0]);
                (format!("lr::LStr::from(lr::LuaType::lua_type(&{}))", atom(v.code)), vec![(sty, false)])
            }
            ToNumber => {
                if self.arg_is_int(&all[0]) {
                    let v = self.arg_nn(&all[0], "bad argument to 'tonumber'");
                    return (format!("lr::at(lr::int::to_number({}), {loc})?", strip(v)), vec![(sty, false)]);
                }
                let v = self.arg_nn(&all[0], "bad argument to 'tonumber'");
                if let Some(b) = all.get(1) {
                    let base = self.arg_nn(b, "bad argument #2 to 'tonumber'");
                    return (format!("lr::at(lr::stdlib::tonumber_base(&{}, {}), {loc})?", atom(v), strip(base)), vec![(sty, true)]);
                }
                (format!("lr::stdlib::tonumber(&{})", atom(v)), vec![(sty, true)])
            }
            Assert => {
                let v = self.arg_val(&all[0]);
                let x = self.fresh("v");
                let msg = match all.get(1) {
                    // optional only when it comes from a trailing call
                    Some(m) => match self.arg_val(m) {
                        c if c.opt => strip(c.code),
                        c => format!("Some({})", strip(c.code)),
                    },
                    None => "None".into(),
                };
                let at = self.arg_ety(&all[0]).ty;
                let fail = format!("return Err(lr::stdlib::assert_failed({msg}).with_loc({loc}))");
                let code = if v.opt {
                    if matches!(self.node(at), TyNode::Bool) {
                        format!("match {} {{ Some(true) => true, _ => {fail} }}", strip(v.code))
                    } else if matches!(self.node(at), TyNode::FalseOr(_)) {
                        format!("match {} {{ Some(lr::FalseOr::Val({x})) => lr::FalseOr::Val({x}), _ => {fail} }}", strip(v.code))
                    } else {
                        format!("match {} {{ Some({x}) => {x}, None => {fail} }}", strip(v.code))
                    }
                } else if matches!(self.node(at), TyNode::Bool) {
                    format!("{{ let {x} = {}; if !{x} {{ {fail} }} {x} }}", strip(v.code))
                } else if matches!(self.node(at), TyNode::FalseOr(_)) {
                    format!("match {} {{ lr::FalseOr::Val({x}) => lr::FalseOr::Val({x}), lr::FalseOr::False => {fail} }}", strip(v.code))
                } else {
                    v.code.full()
                };
                (code, vec![(at, false)])
            }
            CollectGarbage => {
                let opt = match all.first() {
                    Some(o) => {
                        let c = self.arg_nn(o, "bad argument #1 to 'collectgarbage'");
                        format!("Some(&{})", atom(c))
                    }
                    None => "None".into(),
                };
                (format!("lr::at(lr::stdlib::collectgarbage({opt}), {loc})?"), vec![(sty, false)])
            }
            Error => {
                let v = self.arg_val(&all[0]);
                let msg = format!("lr::show::tostring(&{})", atom(v.code));
                // Luau levels: 0 no position, 1 this call (default), 2 the line of the
                // call that made this function run (known: the function is a copy made
                // for that one call, `specialize.rs`)
                let code = match self.ck.info.dynamic.error_levels.get(&e.id).copied() {
                    Some(crate::check_dynamic::ErrorLevel::Zero) => format!("lr::error::raise_unlocated::<()>({msg})?"),
                    Some(crate::check_dynamic::ErrorLevel::Two(sp)) => format!("lr::error::raise::<()>({msg}, {})?", self.loc(sp)),
                    _ => format!("lr::error::raise::<()>({msg}, {loc})?"),
                };
                (code, vec![])
            }
            Pcall => {
                let f = self.arg_nn(&all[0], "attempt to call a nil value");
                let ft = self.arg_ety(&all[0]).ty;
                let fty = self.func_of(ft);
                let rets = self.ck.st.rets_known(fty.rets).cloned().unwrap_or_default();
                let fv = self.fresh("f");
                // the arguments are evaluated before the protected call (an error
                // while evaluating them is not caught), like Lua
                let popt: Vec<bool> = fty.params.iter().map(|p| self.is_null(p.null)).collect();
                let (pre, argv) = self.args(&all[1..], &popt, fty.vararg.is_some());
                let mut pre = stmts_text(&pre);
                let mut bound = Vec::new();
                for a in argv {
                    let t = self.fresh("pa");
                    let _ = write!(pre, "let {t} = {}; ", strip(a));
                    bound.push(t);
                }
                let call = format!("{fv}.call({})", tuple_ty(&bound));
                let mut outs = vec![(0, false), (0, false)];
                let code = match rets.len() {
                    0 => format!("lr::stdlib::pcall(|| {call}.map(|()| None::<()>))"),
                    1 => format!("lr::stdlib::pcall(|| {call})"),
                    n => {
                        // (ok, first-or-error, rest...): the rest are nil on failure
                        let xs: Vec<String> = (0..n).map(|i| format!("__x{i}")).collect();
                        let mut okv = vec!["true".to_string(), "lr::PcallVal::Ok(__x0)".to_string()];
                        let mut errv = vec!["false".to_string(), "lr::PcallVal::Err(__e)".to_string()];
                        for (i, s) in rets.iter().enumerate().skip(1) {
                            let already_opt = self.is_null(s.null);
                            okv.push(if already_opt { xs[i].clone() } else { format!("Some({})", xs[i]) });
                            errv.push("None".into());
                            outs.push((s.ty, true));
                        }
                        format!(
                            "match lr::stdlib::pcall(|| {call}) {{ (_, lr::PcallVal::Ok({})) => ({}), (_, lr::PcallVal::Err(__e)) => ({}) }}",
                            tuple_ty(&xs),
                            okv.join(", "),
                            errv.join(", ")
                        )
                    }
                };
                (format!("{{ let {fv} = {}; {pre}{code} }}", strip(f)), outs)
            }
            StrLen => {
                let s = self.arg_ref(&all[0], "bad argument #1 to 'len'");
                (format!("{}.len()", atom(s)), vec![(sty, false)])
            }
            StrUpper | StrLower | StrReverse => {
                let s = self.arg_ref(&all[0], "bad argument #1 (string expected, got nil)");
                let f = match b {
                    StrUpper => "string_upper",
                    StrLower => "string_lower",
                    _ => "string_reverse",
                };
                (format!("lr::stdlib::{f}(&{})", atom(s)), vec![(sty, false)])
            }
            StrSub => {
                let s = self.arg_ref(&all[0], "bad argument #1 to 'sub'");
                let i = self.arg_nn(&all[1], "bad argument #2 to 'sub'");
                let j = match all.get(2) {
                    Some(j) => self.arg_to(j, true),
                    None => "None".into(),
                };
                (format!("lr::stdlib::string_sub(&{}, {}, {})", atom(s), strip(i), strip(j)), vec![(sty, false)])
            }
            StrRep => {
                let s = self.arg_nn(&all[0], "bad argument #1 to 'rep'");
                let n = self.arg_nn(&all[1], "bad argument #2 to 'rep'");
                (format!("lr::at(lr::stdlib::string_rep(&{}, {}), {loc})?", atom(s), strip(n)), vec![(sty, false)])
            }
            StrByte => {
                let s = self.arg_nn(&all[0], "bad argument #1 to 'byte'");
                let i = match all.get(1) {
                    Some(j) => self.arg_to(j, true),
                    None => "None".into(),
                };
                (format!("lr::stdlib::string_byte(&{}, {})", atom(s), strip(i)), vec![(sty, true)])
            }
            StrChar => {
                let cs: Vec<String> = all.iter().map(|a| self.arg_nn(a, "bad argument to 'char'")).map(strip).collect();
                (format!("lr::at(lr::stdlib::string_char(&[{}]), {loc})?", cs.join(", ")), vec![(sty, false)])
            }
            StrFormat => {
                let pieces = self.ck.info.formats.get(&e.id).cloned().unwrap_or_default();
                let buf = self.fresh("b");
                let mut s = format!("{{ let mut {buf} = Vec::new(); ");
                let mut ai = 1;
                for p in pieces {
                    let d = match p {
                        FmtPiece::Lit(l) => {
                            let _ = write!(s, "lr::fmt::lit(&mut {buf}, {}); ", rust_str_lit(&l));
                            continue;
                        }
                        FmtPiece::Arg(d) => d,
                    };
                    let spec = d.spec_expr();
                    let arg = &all[ai];
                    ai += 1;
                    // a numeric string given to a number directive is converted first
                    let num = |this: &mut Self, arg: &Arg| {
                        let v = strip(this.arg_nn(arg, "bad argument to 'format'"));
                        if this.arg_is_str(arg) { format!("lr::at(lr::fmt::number_arg(&{v}, {ai}), {loc})?") } else { v }
                    };
                    match d.conv {
                        Conv::Signed => {
                            let v = num(self, arg);
                            let _ = write!(s, "lr::fmt::signed(&mut {buf}, {spec}, {v}); ");
                        }
                        Conv::Unsigned(c) => {
                            let v = num(self, arg);
                            let _ = write!(s, "lr::fmt::unsigned(&mut {buf}, {spec}, b'{}', {v}); ", c as char);
                        }
                        Conv::Char => {
                            let v = num(self, arg);
                            let _ = write!(s, "lr::fmt::char_(&mut {buf}, {spec}, {v}); ");
                        }
                        Conv::Float(c) => {
                            let v = self.arg_nn(arg, "bad argument to 'format'");
                            let _ = write!(s, "lr::fmt::float(&mut {buf}, {spec}, b'{}', {}); ", c as char, strip(v));
                        }
                        Conv::Str => {
                            let v = self.arg_val(arg);
                            let _ = write!(s, "lr::fmt::string(&mut {buf}, {spec}, &{}); ", atom(v.code));
                        }
                        Conv::Quoted => {
                            let v = self.arg_val(arg);
                            let _ = write!(s, "lr::fmt::quoted(&mut {buf}, &{}); ", atom(v.code));
                        }
                    }
                }
                let _ = write!(s, "lr::LStr::from_vec({buf}) }}");
                (s, vec![(sty, false)])
            }
            MFloor | MCeil | MSqrt | MAbs => {
                let x = self.arg_nn(&all[0], "bad argument #1 (number expected, got nil)");
                let f = match b {
                    MFloor => "floor",
                    MCeil => "ceil",
                    MSqrt => "sqrt",
                    _ => "abs",
                };
                (format!("f64::{f}({})", strip(x)), vec![(sty, false)])
            }
            MFn(name, _, _) => {
                let xs: Vec<String> =
                    all.iter().enumerate().map(|(i, a)| strip(self.arg_nn(a, &format!("bad argument #{} to '{name}'", i + 1)))).collect();
                let code = match (name, xs.as_slice()) {
                    ("log", [x, b]) => format!("lr::stdlib::math_log({x}, Some({b}))"),
                    ("log", [x]) => format!("lr::stdlib::math_log({x}, None)"),
                    ("atan2", [y, x]) => format!("f64::atan2({y}, {x})"),
                    ("fmod", [a, b]) => format!("({}) % ({})", a, b),
                    ("pow", [a, b]) => format!("f64::powf({a}, {b})"),
                    ("deg", [x]) => format!("f64::to_degrees({x})"),
                    ("rad", [x]) => format!("f64::to_radians({x})"),
                    ("sign", [x]) => format!("lr::stdlib::math_sign({x})"),
                    ("clamp", [x, lo, hi]) => format!("lr::at(lr::stdlib::math_clamp({x}, {lo}, {hi}), {loc})?"),
                    ("lerp", [a, b, t]) => format!("lr::stdlib::math_lerp({a}, {b}, {t})"),
                    ("ldexp", [m, e]) => format!("lr::stdlib::math_ldexp({m}, {e})"),
                    ("frexp", [x]) => format!("lr::stdlib::math_frexp({x})"),
                    ("modf", [x]) => format!("lr::stdlib::math_modf({x})"),
                    ("random", []) => "lr::stdlib::math_random()".to_string(),
                    ("random", [hi]) => format!("lr::at(lr::stdlib::math_random_range(None, {hi}), {loc})?"),
                    ("random", [lo, hi]) => format!("lr::at(lr::stdlib::math_random_range(Some({lo}), {hi}), {loc})?"),
                    ("noise", [x]) => format!("lr::stdlib::math_noise({x}, 0.0, 0.0)"),
                    ("noise", [x, y]) => format!("lr::stdlib::math_noise({x}, {y}, 0.0)"),
                    ("noise", [x, y, z]) => format!("lr::stdlib::math_noise({x}, {y}, {z})"),
                    ("randomseed", [n]) => format!("lr::stdlib::math_randomseed({n})"),
                    // exp log10 sin cos tan asin acos atan sinh cosh tanh round
                    (f, [x]) => format!("f64::{f}({x})"),
                    _ => unreachable!("math.{name}: arity checked"),
                };
                (code, vec![(sty, false); crate::check::math_fn_results(name)])
            }
            MToInteger => {
                let x = self.arg_nn(&all[0], "bad argument #1 to 'tointeger'");
                (format!("lr::int::from_number({})", strip(x)), vec![(sty, true)])
            }
            MMin | MMax => {
                let xs: Vec<String> = all.iter().map(|a| self.arg_nn(a, "bad argument (number expected, got nil)")).map(strip).collect();
                let f = if b == MMin { "math_min" } else { "math_max" };
                (format!("lr::stdlib::{f}({}, &[{}])", xs[0], xs[1..].join(", ")), vec![(sty, false)])
            }
            TInsert => {
                let t = self.arg_ref(&all[0], "bad argument #1 to 'insert'");
                if all.len() == 3 {
                    let p = self.arg_nn(&all[1], "bad argument #2 to 'insert'");
                    let v = self.arg_to(&all[2], false);
                    (format!("lr::at({}.insert_at({}, {}), {loc})?", atom(t), strip(p), strip(v)), vec![])
                } else {
                    let v = self.arg_to(&all[1], false);
                    (format!("{}.push({})", atom(t), strip(v)), vec![])
                }
            }
            TRemove => {
                let t = self.arg_ref(&all[0], "bad argument #1 to 'remove'");
                if all.len() == 2 {
                    let p = self.arg_nn(&all[1], "bad argument #2 to 'remove'");
                    (format!("lr::at({}.remove_at({}), {loc})?", atom(t), strip(p)), vec![(sty, true)])
                } else {
                    (format!("{}.pop()", atom(t)), vec![(sty, true)])
                }
            }
            TConcat => {
                let t = self.arg_ref(&all[0], "bad argument #1 to 'concat'");
                let sep = match all.get(1) {
                    Some(s) => {
                        let c = self.arg_nn(s, "bad argument #2 to 'concat'");
                        format!("Some(&{})", atom(c))
                    }
                    None => "None".into(),
                };
                let i = match all.get(2) {
                    Some(x) => self.arg_to(x, true),
                    None => "None".into(),
                };
                let j = match all.get(3) {
                    Some(x) => self.arg_to(x, true),
                    None => "None".into(),
                };
                (format!("lr::at(lr::stdlib::table_concat(&{}, {sep}, {}, {}), {loc})?", atom(t), strip(i), strip(j)), vec![(sty, false)])
            }
            TCreate => {
                let n = self.arg_nn(&all[0], "bad argument #1 to 'create'");
                match all.get(1) {
                    Some(v) => {
                        let vc = self.arg_to(v, false);
                        (format!("lr::at(lr::Arr::filled({}, {}), {loc})?", strip(n), strip(vc)), vec![(sty, false)])
                    }
                    None => (format!("lr::at(lr::Arr::with_capacity({}), {loc})?", strip(n)), vec![(sty, false)]),
                }
            }
            TClone => {
                let t = self.arg_ref(&all[0], "bad argument #1 to 'clone'");
                (format!("{}.shallow_clone()", atom(t)), vec![(sty, false)])
            }
            StrFind | StrMatch => {
                let s = self.arg_nn(&all[0], "bad argument #1 (string expected)");
                let p = self.arg_nn(&all[1], "bad argument #2 (pattern string expected)");
                let init = match all.get(2) {
                    Some(x) => self.arg_to(x, true),
                    None => "None".into(),
                };
                let plain = match all.get(3) {
                    Some(x) => {
                        let v = self.arg_to(x, true);
                        format!("{}.unwrap_or(false)", atom(v))
                    }
                    None => "false".into(),
                };
                let outs: Vec<(TyId, bool)> = self.ck.info.builtin_outs.get(&e.id).cloned().unwrap_or_default().iter().map(|o| (o.ty, true)).collect();
                let m = self.fresh("m");
                let mut parts = Vec::new();
                if b == StrFind {
                    parts.push(format!("{m}.start"));
                    parts.push(format!("{m}.end"));
                }
                let first = parts.len();
                for (i, (t, _)) in outs[first..].iter().enumerate() {
                    // number-typed captures are position captures `()`
                    let acc = if matches!(self.node(*t), TyNode::Num) { "pos" } else { "cap" };
                    parts.push(format!("{m}.{acc}({i})"));
                }
                let val = if parts.len() == 1 { parts[0].clone() } else { format!("({})", parts.join(", ")) };
                // a pattern not known at compile time must not have captures
                let find = if self.ck.info.pattern_caps.contains_key(&e.id) {
                    format!("lr::stdlib::string_find(&{}, &{}, {}, {plain})", atom(s), atom(p), strip(init))
                } else {
                    let func = if b == StrFind { "find" } else { "match" };
                    let max_caps = match (self.ck.info.pattern_full.contains(&e.id), b == StrFind) {
                        (false, _) => "usize::MAX",
                        (true, true) => "0",
                        (true, false) => "1",
                    };
                    let match_value = b == StrMatch;
                    format!(
                        "lr::stdlib::string_find_dyn(&{}, &{}, {}, {plain}, {func:?}, {max_caps}, {match_value})",
                        atom(s),
                        atom(p),
                        strip(init)
                    )
                };
                (format!("{{ let {m} = lr::at({find}, {loc})?; {val} }}"), outs)
            }
            StrGsub => self.gsub_code(e, &all),
            SelectCount => {
                let (pre, src) = self.select_src(&all[1]);
                (rir::block(pre, rir::cast(rir::method(src, "len", vec![]), "f64")).full(), vec![(sty, false)])
            }
            Select => {
                // `select(i, ...)` adjusted to a fixed number of values
                let n = self.arg_nn(&all[0], "bad argument #1 to 'select' (number expected)");
                let nv = self.fresh("n");
                let mut pre = vec![rir::let_(nv.clone(), n)];
                let (p, src) = self.select_src(&all[1]);
                pre.extend(p);
                let outs: Vec<(TyId, bool)> = self.ck.info.builtin_outs.get(&e.id).cloned().unwrap_or_default().iter().map(|o| (o.ty, true)).collect();
                let st = self.fresh("s");
                let start = rir::atom_e(st.clone());
                let first = rir::at(rir::call("lr::va::select", vec![rir::method(src.clone(), "len", vec![]), rir::atom_e(nv)]), &loc);
                pre.push(rir::let_(st, first));
                let vals: Vec<RExpr> = (0..outs.len()).map(|k| va_get(&src, &start, k)).collect();
                let val = match vals.len() {
                    0 => rir::atom_e("()"),
                    1 => vals.into_iter().next().unwrap(),
                    _ => RExpr::Tuple(vals),
                };
                (rir::block(pre, val).full(), outs)
            }
            StrGmatch => unreachable!("string.gmatch is generated by gmatch_for"),
            TUnpack => {
                // the result vector (no fixed results); `multi_pack` binds it
                let t = self.arg_ref(&all[0], "bad argument #1 to 'unpack' (table expected, got nil)");
                let i = match all.get(1) {
                    Some(a) => self.arg_to(a, true),
                    None => rir::atom_e("None"),
                };
                let j = match all.get(2) {
                    Some(a) => self.arg_to(a, true),
                    None => rir::atom_e("None"),
                };
                (format!("lr::at(lr::va::unpack(&{}, {}, {}, {}), {loc})?", atom(t), strip(i), strip(j), all.len()), vec![])
            }
            TSort => {
                let t = self.arg_ref(&all[0], "bad argument #1 to 'sort'");
                let tt = self.arg_ety(&all[0]).ty;
                let el = match self.node(tt) {
                    TyNode::Table(tab) => self.ck.st.tab(tab).elem.map(|s| s.ty).unwrap_or(tt),
                    _ => tt,
                };
                let cmp = match all.get(1) {
                    Some(f) => {
                        let fc = self.arg_nn(f, "bad argument #2 to 'sort'");
                        let fv = self.fresh("cmp");
                        return (
                            format!("{{ let {fv} = {}; lr::at(lr::stdlib::table_sort(&{}, |a, b| {fv}.call((a.clone(), b.clone()))), {loc})? }}", strip(fc), atom(t)),
                            vec![],
                        );
                    }
                    None => match self.node(el) {
                        TyNode::Str => "|a, b| Ok(a.as_bytes() < b.as_bytes())",
                        _ => "|a, b| Ok(a < b)",
                    },
                };
                (format!("lr::at(lr::stdlib::table_sort(&{}, {cmp}), {loc})?", atom(t)), vec![])
            }
        }
    }

    // Closures and functions

    /// Function value for a function literal / non-static local function.
    /// Function value for a function literal / non-static local function.
    ///
    /// The closure becomes an environment struct holding its captures (traced by
    /// the collector) that implements `lr::Callable`. Inside the body, captured
    /// copyable values are bound by value, cells and handles by reference
    /// (`(*name)` where a value is needed), so a call does not touch reference
    /// counts. A recursive closure refers to itself through `__this`.
    fn closure(&mut self, f: &FuncBody, self_sym: Option<SymId>) -> RExpr {
        let ft_id = self.ck.info.funcs[&f.id];
        let ft = self.func_of(ft_id);
        let (args_ty, rty) = self.fn_args(&ft);
        let finfo = self.res.funcs[&f.id].clone();
        let env = self.fresh("Env");
        let mut fields = Vec::new();
        let mut inits = Vec::new();
        let mut binds = Vec::new();
        let mut refs = HashSet::new();
        for c in &finfo.captures {
            if self.is_ns_sym(*c) || self.ck.info.builtin_aliases.contains_key(c) {
                continue; // compile-time namespace or builtin alias: nothing to capture
            }
            let n = self.sym_name(*c);
            let cell = self.res.sym(*c).is_cell();
            let ty = self.capture_ty(*c);
            let slot = self.ck.info.sym_slot[c];
            let outer = self.sym_access(*c);
            if !cell && self.is_copy_ty(slot.ty) {
                inits.push((n.clone(), outer));
                binds.push(rir::let_(n.clone(), rir::field(rir::atom_e("self"), n.clone())));
            } else {
                inits.push((n.clone(), rir::method(outer, "clone", vec![])));
                binds.push(rir::let_(n.clone(), rir::borrow(rir::field(rir::atom_e("self"), n.clone()))));
                if !cell {
                    refs.insert(*c);
                }
            }
            fields.push((n, ty));
        }
        let (patterns, prologue) = self.param_patterns(f, &ft);
        let rets = self.ck.st.rets_known(ft.rets).cloned().unwrap_or_default();
        let tail = self.ck.st.rets_tail(ft.rets);
        let self_ref = finfo.self_referenced && self_sym.is_some();
        let mut pro = vec![rir::let_(tuple_ty(&patterns), rir::atom_e("__args"))];
        pro.extend(binds);
        if self_ref {
            let s = self_sym.unwrap();
            pro.push(rir::let_(self.sym_name(s), rir::method(rir::atom_e("__this"), "clone", vec![])));
        }
        pro.extend(prologue);
        self.ref_caps.push(refs);
        let body = self.func_body_ir(f, rets, tail);
        self.ref_caps.pop();
        RExpr::Env(Box::new(rir::EnvFn { env, fields, inits, args_ty, rty, prologue: pro, body }))
    }

    /// Rust type of a captured variable inside a closure environment.
    fn capture_ty(&mut self, s: SymId) -> String {
        let slot = self.ck.info.sym_slot[&s];
        let opt = self.sym_opt(s);
        let ty = self.opt_ty(slot.ty, opt);
        if self.res.sym(s).is_cell() {
            format!("lr::Cell<{ty}>")
        } else {
            ty
        }
    }

    /// Expression naming a variable's value in the current function (captures
    /// bound by reference are dereferenced).
    fn sym_access(&self, s: SymId) -> RExpr {
        let name = self.sym_name(s);
        if self.ref_caps.last().map(|r| r.contains(&s)).unwrap_or(false) {
            rir::deref(rir::atom_e(name))
        } else {
            rir::atom_e(name)
        }
    }

    /// Destructuring patterns for a closure's argument tuple, plus the prologue
    /// that moves captured-and-assigned parameters into cells.
    fn param_patterns(&mut self, f: &FuncBody, _ft: &FuncTy) -> (Vec<String>, Vec<RStmt>) {
        let mut ps = Vec::new();
        let mut pro = Vec::new();
        for p in &f.params {
            let s = self.res.decl(p.name.id);
            let sym = self.res.sym(s).clone();
            let name = self.sym_name(s);
            if sym.is_cell() {
                ps.push(name.clone());
                pro.push(rir::let_(name.clone(), rir::call("lr::Cell::new", vec![rir::atom_e(name)])));
            } else if sym.assigned {
                ps.push(format!("mut {name}"));
            } else {
                ps.push(name);
            }
        }
        if f.vararg.is_some() {
            ps.push(VA.into());
        }
        (ps, pro)
    }

    fn params(&mut self, f: &FuncBody, ft: &FuncTy) -> (Vec<String>, String) {
        let mut ps = Vec::new();
        let mut pro = String::new();
        for (i, p) in f.params.iter().enumerate() {
            let s = self.res.decl(p.name.id);
            let sym = self.res.sym(s).clone();
            let name = self.sym_name(s);
            let ty = self.slot_ty(ft.params[i]);
            if sym.is_cell() {
                ps.push(format!("{name}: {ty}"));
                let _ = write!(pro, "let {name} = lr::Cell::new({name}); ");
            } else if sym.assigned {
                ps.push(format!("mut {name}: {ty}"));
            } else {
                ps.push(format!("{name}: {ty}"));
            }
        }
        if let Some(v) = ft.vararg {
            ps.push(format!("{VA}: {}", self.va_ty(v)));
        }
        (ps, pro)
    }

    fn func_body(&mut self, f: &FuncBody, rets: Vec<Slot>, tail: Option<Slot>) -> String {
        self.func_body_ir(f, rets, tail).print()
    }

    fn func_body_ir(&mut self, f: &FuncBody, rets: Vec<Slot>, tail: Option<Slot>) -> rir::FnBody {
        self.fn_rets.push(FnRets::Func(rets.clone(), tail, f.id));
        let saved = std::mem::take(&mut self.loops);
        let stmts = self.block_stats(&f.body);
        self.loops = saved;
        self.fn_rets.pop();
        let tail = if self.ck.info.falls_through.contains(&f.id) {
            let mut v: Vec<RExpr> = rets.iter().map(|_| rir::atom_e("None")).collect();
            if tail.is_some() {
                v.push(rir::call("Vec::new", vec![]));
            }
            let val = match v.len() {
                0 => RExpr::Tuple(vec![]),
                1 => v[0].clone(),
                _ => RExpr::Tuple(v),
            };
            Some(rir::call("Ok", vec![val]))
        } else { None };
        rir::FnBody { stmts, tail }
    }

    fn static_fn(&mut self, s: SymId, f: &FuncBody) {
        let ft_id = self.ck.info.funcs[&f.id];
        let ft = self.func_of(ft_id);
        let (params, pro) = self.params(f, &ft);
        let rets = self.ck.st.rets_known(ft.rets).cloned().unwrap_or_default();
        let tail = self.ck.st.rets_tail(ft.rets);
        let rty = self.result_ty(&rets, tail);
        self.ref_caps.push(HashSet::new());
        let body = self.func_body(f, rets, tail);
        self.ref_caps.pop();
        let name = self.static_fn_name(s);
        let sym = self.res.sym(s);
        let doc = format!("/// `local function {}` ({})", sym.name, self.sm.loc(f.span));
        self.hoisted.push(format!("{doc}\nfn {name}({}) -> lr::LResult<{rty}> {{\n{pro}{body}}}\n", params.join(", ")));
    }

    // Statements

    fn block_stats(&mut self, b: &Block) -> Vec<RStmt> {
        let mut out = Vec::new();
        for s in &b.stats {
            self.stat(s, &mut out);
            // `error(...)` ends the block (it is emitted as a `return`); statements
            // after it are dead code
            if let StatKind::Call(e) = &s.kind {
                if is_error_call(e, self.res) {
                    break;
                }
            }
        }
        out
    }

    fn block(&mut self, b: &Block) -> Vec<RStmt> {
        self.block_stats(b)
    }

    /// Locals bound to `require("rust:...")` exist only at compile time.
    fn is_ns_sym(&self, s: SymId) -> bool {
        self.ck.info.sym_slot.get(&s).map(|sl| matches!(self.node(sl.ty), TyNode::Namespace(..))).unwrap_or(false)
    }

    fn declare_local(&mut self, s: SymId, value: impl Into<RExpr>, out: &mut Vec<RStmt>) {
        let value = value.into();
        if self.is_ns_sym(s) {
            return;
        }
        let sym = self.res.sym(s).clone();
        let name = self.sym_name(s);
        let slot = self.ck.info.sym_slot[&s];
        let opt = self.sym_opt(s);
        let ty = self.opt_ty(slot.ty, opt);
        out.push(if sym.is_cell() {
            RStmt::Let(name, Some(format!("lr::Cell<{ty}>")), rir::call("lr::Cell::new", vec![value]))
        } else if sym.assigned {
            RStmt::Let(format!("mut {name}"), Some(ty), value)
        } else {
            RStmt::Let(name, Some(ty), value)
        });
    }

    fn stat(&mut self, s: &Stat, out: &mut Vec<RStmt>) {
        match &s.kind {
            StatKind::Local(..) if self.ck.info.alias_decls.contains(&s.id) => {}
            StatKind::Local(names, exprs) => {
                let syms: Vec<SymId> = names.iter().map(|(n, _)| self.res.decl(n.id)).collect();
                let opts: Vec<bool> = syms.iter().map(|s| self.sym_opt(*s)).collect();
                let (pre, vals) = self.values(exprs, names.len(), s.span);
                emit(out, &pre);
                // All values are computed before any binding becomes visible.
                if names.len() > 1 && exprs.len() > 1 {
                    let mut tmps = Vec::new();
                    for (i, v) in vals.into_iter().enumerate() {
                        let t = self.fresh("l");
                        let c = self.coerce(v, opts[i], names[i].0.span, "attempt to use a nil value");
                        out.push(rir::let_(t.clone(), c));
                        tmps.push(rir::atom_e(t));
                    }
                    for (i, sym) in syms.iter().enumerate() {
                        self.declare_local(*sym, tmps[i].clone(), out);
                    }
                } else {
                    for (i, (sym, v)) in syms.iter().zip(vals).enumerate() {
                        let c = if exprs.is_empty() {
                            let slot = self.ck.info.sym_slot[sym];
                            let t = self.rust_ty(slot.ty);
                            rir::atom_e(format!("None::<{t}>"))
                        } else {
                            self.coerce(v, opts[i], names[i].0.span, "attempt to use a nil value")
                        };
                        self.declare_local(*sym, c, out);
                    }
                }
                // `<close>`: a scope guard closes the object on every exit path
                for ((n, _), sym) in names.iter().zip(&syms) {
                    if self.ck.info.local_attrs.get(&n.id) == Some(&crate::ast::LocalAttr::Close) {
                        let g = self.fresh("close");
                        let acc = self.sym_access(*sym);
                        let f = if self.sym_opt(*sym) { "opt" } else { "new" };
                        out.push(rir::let_(g, rir::call(format!("lr::handle::CloseOnExit::{f}"), vec![rir::borrow(acc)])));
                    }
                }
            }
            StatKind::LocalFunction(n, f) => {
                let sym = self.res.decl(n.id);
                if self.res.sym(sym).is_static {
                    self.static_fn(sym, f);
                    return;
                }
                let late = self.ck.late_init.contains(&sym);
                if late {
                    // declared first so the body can refer to the (reassignable) variable
                    let slot = self.ck.info.sym_slot[&sym];
                    let t = self.rust_ty(slot.ty);
                    self.declare_local(sym, format!("None::<{t}>"), out);
                    let c = self.closure(f, None);
                    let w = self.write_sym(sym, rir::some(RExpr::from(c)));
                    emit(out, &[w]);
                } else {
                    let c = self.closure(f, Some(sym));
                    self.declare_local(sym, c, out);
                }
            }
            StatKind::Function(target, f) => {
                let mut c = self.closure(f, None);
                if matches!(self.ck.info.access.get(&target.id), Some(Access::Runtime)) {
                    c = rir::call("lr::dynamic_fn::function", vec![c]);
                }
                self.assign(&[target.clone()], vec![Val { code: c.into(), opt: false }], Vec::new(), out);
            }
            StatKind::Assign(targets, exprs) => {
                // Targets' subexpressions, then values, then writes.
                let (tpre, places) = self.places(targets);
                let (pre, vals) = self.values(exprs, targets.len(), s.span);
                emit(out, &tpre);
                emit(out, &pre);
                let mut tmps = Vec::new();
                if targets.len() > 1 {
                    for v in vals {
                        let t = self.fresh("v");
                        emit(out, &[rir::let_(t.clone(), v.code)]);
                        tmps.push(Val { code: rir::atom_e(t), opt: v.opt });
                    }
                } else {
                    tmps = vals;
                }
                for ((p, v), t) in places.into_iter().zip(tmps).zip(targets.iter()) {
                    let w = self.write_place(&p, v, t.span);
                    emit(out, &w);
                }
            }
            StatKind::Compound(op, target, rhs) => {
                let (tpre, places) = self.places(std::slice::from_ref(target));
                emit(out, &tpre);
                let p = &places[0];
                let cur = self.read_place(p, target);
                let (cur, evaluated_rhs) = if matches!(p, Place::DynamicMap { .. }) {
                    // Reading an invalid dynamic key yields nil; Luau still
                    // evaluates the RHS before arithmetic rejects that nil.
                    let old = self.fresh("old");
                    emit(out, &[rir::let_(old.clone(), cur.code)]);
                    let right = self.expr(rhs);
                    let right_name = self.fresh("rhs");
                    emit(out, &[rir::let_(right_name.clone(), right.code)]);
                    let left = if cur.opt { rir::atom_e(old) } else { rir::some(rir::atom_e(old)) };
                    let right = if right.opt { rir::atom_e(right_name) } else { rir::some(rir::atom_e(right_name)) };
                    let checked = if *op == BinOp::Concat {
                        rir::call("lr::traversal::concatenation_operands", vec![left, right])
                    } else {
                        let operation = match op {
                            BinOp::Add => "lr::dynamic::Arith::Add",
                            BinOp::Sub => "lr::dynamic::Arith::Sub",
                            BinOp::Mul => "lr::dynamic::Arith::Mul",
                            BinOp::Div => "lr::dynamic::Arith::Div",
                            BinOp::IDiv => "lr::dynamic::Arith::IDiv",
                            BinOp::Mod => "lr::dynamic::Arith::Mod",
                            BinOp::Pow => "lr::dynamic::Arith::Pow",
                            _ => unreachable!(),
                        };
                        rir::call("lr::traversal::arithmetic_operands", vec![rir::atom_e(operation), left, right])
                    };
                    let operands = self.fresh("operands");
                    emit(out, &[rir::let_(operands.clone(), rir::at(checked, &self.loc(target.span)))]);
                    (Val { code: rir::field(rir::atom_e(operands.clone()), "0"), opt: false }, Some(rir::field(rir::atom_e(operands), "1")))
                } else { (cur, None) };
                let mut cur = self.coerce(cur, false, target.span, "attempt to perform arithmetic on a nil value");
                if self.promoted_lookup(target.id).is_some() {
                    let saved = self.fresh("old");
                    emit(out, &[rir::let_(saved.clone(), cur)]);
                    cur = rir::atom_e(saved);
                }
                let r = evaluated_rhs.unwrap_or_else(|| self.expr_nn(rhs, "attempt to perform arithmetic on a nil value"));
                let v = match op {
                    _ if self.is_int_expr(target) => self.int_arith(*op, cur, r, target.span),
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => rir::bin(rop(*op), cur, r),
                    BinOp::IDiv => rir::call("lr::stdlib::floor_div", vec![cur, r]),
                    BinOp::Mod => rir::call("lr::stdlib::modulo", vec![cur, r]),
                    BinOp::Pow => rir::call("f64::powf", vec![cur, r]),
                    BinOp::Concat => concat_call(vec![cur, r]),
                    _ => unreachable!(),
                };
                // the new value is computed (reading the target once) before the write
                let tv = self.fresh("v");
                emit(out, &[rir::let_(tv.clone(), v)]);
                let w = self.write_place(p, Val { code: rir::atom_e(tv), opt: false }, target.span);
                emit(out, &w);
            }
            StatKind::Call(e) => {
                if is_error_call(e, self.res) {
                    let ExprKind::Call(_, args) = &e.kind else { unreachable!() };
                    let v = self.expr(&args[0]);
                    let msg = rir::call("lr::show::tostring", vec![rir::borrow(v.code)]);
                    // error(msg, level): see `Error` in `builtin_args`
                    let raise = match self.ck.info.dynamic.error_levels.get(&e.id).copied() {
                        Some(crate::check_dynamic::ErrorLevel::Zero) => rir::call("lr::error::raise_unlocated", vec![msg]),
                        Some(crate::check_dynamic::ErrorLevel::Two(sp)) => rir::call("lr::error::raise", vec![msg, rir::atom_e(self.loc(sp))]),
                        _ => rir::call("lr::error::raise", vec![msg, rir::atom_e(self.loc(e.span))]),
                    };
                    out.push(RStmt::Return(raise));
                    return;
                }
                // a block-like call expression is printed as `let _ = { .. };`
                // (its value is not `()`)
                let (pre, _) = self.multi(e, Some(0));
                emit(out, &pre);
            }
            StatKind::Do(b) => {
                let inner = self.block(b);
                out.push(RStmt::Block(inner));
            }
            StatKind::While(c, b) => {
                let id = self.loop_enter(b);
                let cond = if matches!(c.kind, ExprKind::Bool(true)) { None } else { Some(self.cond(c)) };
                let body = self.block(b);
                let l = self.loops.last().unwrap();
                let label = l.break_label.then(|| format!("'l{id}"));
                let body = if l.labeled { vec![RStmt::Labeled(format!("'c{id}"), body)] } else { body };
                out.push(RStmt::Loop { label, cond, body });
                self.loops.pop();
            }
            StatKind::Repeat(b, c) => {
                let id = self.loop_enter(b);
                let labeled = self.loops.last().unwrap().labeled;
                // `until false` never exits: no `break` at all, so the Rust loop has
                // type `!` as the checker assumes
                let exit = |cc: &RExpr| if is_false(cc) { vec![] } else { vec![RStmt::If(vec![(cc.clone(), vec![RStmt::Break(None)])], None)] };
                if labeled {
                    // `continue` evaluates the condition within the body's scope so its locals
                    // remain visible to `until`.
                    let cc = self.cond(c);
                    let l = self.loops.last_mut().unwrap();
                    l.until = Some(cc.clone());
                    l.break_label = true;
                    let mut body = self.block(b);
                    body.extend(exit(&cc));
                    out.push(RStmt::Loop { label: Some(format!("'l{id}")), cond: None, body });
                } else {
                    let mut body = self.block(b);
                    let cc = self.cond(c);
                    body.extend(exit(&cc));
                    out.push(RStmt::Loop { label: None, cond: None, body });
                }
                self.loops.pop();
            }
            StatKind::If(arms, els) => {
                let mut rarms = Vec::new();
                for (c, b) in arms {
                    let cc = self.cond(c);
                    let body = self.block(b);
                    rarms.push((cc, body));
                }
                let els = els.as_ref().map(|b| self.block(b));
                out.push(RStmt::If(rarms, els));
            }
            StatKind::NumFor(v, a, b, c, body) => {
                out.push(self.num_for(s, v, a, b, c.as_ref(), body));
            }
            StatKind::GenFor(names, exprs, body) => {
                if self.ck.info.iteration.contains_key(&s.id) && !matches!(self.ck.info.fors.get(&s.id), Some(ForKind::Native(..))) {
                    out.push(self.general_for_code(s, names, exprs, body));
                } else {
                    self.gen_for(s, names, exprs, body, out);
                }
            }
            StatKind::Return(exprs) => self.ret(exprs, s.span, out),
            StatKind::Break => {
                let l = self.loops.last().unwrap();
                out.push(RStmt::Break(l.labeled.then(|| format!("'l{}", l.id))));
            }
            StatKind::Continue => {
                let l = self.loops.last().unwrap();
                let lbl = format!("'l{}", l.id);
                match &l.until {
                    Some(cc) if is_false(cc) => out.push(RStmt::Continue(Some(lbl))),
                    Some(cc) => {
                        out.push(RStmt::If(vec![(cc.clone(), vec![RStmt::Break(Some(lbl.clone()))])], None));
                        out.push(RStmt::Continue(Some(lbl)));
                    }
                    None => out.push(RStmt::Break(Some(format!("'c{}", l.id)))),
                }
            }
            StatKind::TypeAlias(..) => {}
        }
    }

    fn loop_enter(&mut self, b: &Block) -> u32 {
        self.tmp += 1;
        let labeled = has_continue(b);
        let break_label = labeled && has_break(b);
        self.loops.push(LoopCtx { id: self.tmp, labeled, break_label, until: None });
        self.tmp
    }

    /// Values for an assignment/declaration list, adjusted to `n`.
    fn values(&mut self, exprs: &[Expr], n: usize, _span: Span) -> (Vec<RStmt>, Vec<Val>) {
        let mut vals = Vec::new();
        let mut pre = Vec::new();
        for (i, e) in exprs.iter().enumerate() {
            if i + 1 == exprs.len() && matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..)) {
                let want = n.saturating_sub(vals.len());
                let (p, vs) = self.multi(e, Some(want));
                if !p.is_empty() {
                    let mut bound = Vec::new();
                    for v in vals.drain(..) {
                        let v: Val = v;
                        let t = self.fresh("x");
                        pre.push(rir::let_(t.clone(), v.code));
                        bound.push(Val { code: rir::atom_e(t), opt: v.opt });
                    }
                    vals = bound;
                    pre.extend(p);
                }
                vals.extend(vs);
            } else if i + 1 == exprs.len() && matches!(e.kind, ExprKind::Vararg) {
                // `...` adjusted to the remaining values
                for k in 0..n.saturating_sub(vals.len()) {
                    vals.push(Val { code: va_get(&rir::atom_e(VA), &rir::atom_e("0"), k), opt: true });
                }
            } else if i >= n {
                // extra values: evaluated, discarded
                let v = self.expr(e);
                pre.push(rir::let_("_", v.code));
            } else {
                vals.push(self.expr(e));
            }
        }
        while vals.len() < n {
            vals.push(Val { code: rir::atom_e("None"), opt: true });
        }
        (pre, vals)
    }

    fn places(&mut self, targets: &[Expr]) -> (Vec<RStmt>, Vec<Place>) {
        let mut pre = Vec::new();
        let mut ps = Vec::new();
        for t in targets {
            match &t.kind {
                ExprKind::Name(n) => match self.res.res(n.id) {
                    Some(Res::Local(s)) => ps.push(Place::Local(s)),
                    _ => ps.push(Place::Local(0)),
                },
                ExprKind::Field(obj, name) => {
                    let o = self.expr_nn(obj, "attempt to index a nil value");
                    let ov = self.fresh("o");
                    pre.push(rir::let_(ov.clone(), o));
                    match self.ck.info.access.get(&t.id).cloned() {
                        Some(Access::Runtime) => {
                            let key = self.str_lit(name.text.as_bytes());
                            ps.push(Place::Runtime { obj: ov, key: rir::call("lr::dynamic::to_value", vec![key]) });
                        }
                        Some(Access::Field(f)) => {
                            let ot = self.ck.info.expr[&obj.id].ty;
                            let TyNode::Table(tab) = self.node(ot) else { unreachable!() };
                            let root = self.ck.st.tab_root(tab);
                            let store_opt = self.field_store_opt(root, &f);
                            ps.push(Place::Field { obj: ov, name: f, store_opt });
                        }
                        Some(Access::Map) => {
                            let tab = match self.node(self.ck.info.expr[&obj.id].ty) { TyNode::Table(tab) => tab, _ => unreachable!() };
                            if self.dynamic_map(tab) {
                                let key = self.str_lit(name.text.as_bytes());
                                let key = rir::call("lr::dynamic::to_value", vec![key]);
                                let saved = self.fresh("key");
                                pre.push(rir::let_(saved.clone(), key));
                                ps.push(Place::DynamicMap { obj: ov, key: rir::atom_e(saved), key_span: t.span });
                                continue;
                            }
                            let k = self.named_map_key(obj, &name.text);
                            ps.push(Place::Map { obj: ov, key: k });
                        }
                        Some(Access::NativeField(get, set)) => {
                            ps.push(Place::NativeField { obj: ov, get, set });
                        }
                        _ => ps.push(Place::Local(0)),
                    }
                }
                ExprKind::Index(obj, key) => {
                    let o = self.expr_nn(obj, "attempt to index a nil value");
                    let ov = self.fresh("o");
                    pre.push(rir::let_(ov.clone(), o));
                    match self.ck.info.access.get(&t.id).cloned() {
                        Some(Access::Runtime) => {
                            let value = self.expr(key);
                            let ty = self.ck.info.expr[&key.id].ty;
                            let value = if self.is_any_ty(ty) || self.ck.info.dynamic.boxed.contains(&key.id) { value.code } else { rir::call("lr::dynamic::to_value", vec![value.code]) };
                            let name = self.fresh("key");
                            pre.push(rir::let_(name.clone(), value));
                            ps.push(Place::Runtime { obj: ov, key: rir::atom_e(name) });
                        }
                        Some(Access::Array) => {
                            let k = self.expr_nn(key, "table index is nil");
                            let kv = self.fresh("k");
                            pre.push(rir::let_(kv.clone(), k));
                            ps.push(Place::Array { obj: ov, key: kv });
                        }
                        Some(Access::Map) => {
                            let tab = match self.node(self.ck.info.expr[&obj.id].ty) { TyNode::Table(tab) => tab, _ => unreachable!() };
                            if self.dynamic_map(tab) {
                                let value = self.raw_map_key(key);
                                let name = self.fresh("key");
                                pre.push(rir::let_(name.clone(), value));
                                ps.push(Place::DynamicMap { obj: ov, key: rir::atom_e(name), key_span: key.span });
                                continue;
                            }
                            let k = self.map_key_for(key, tab);
                            let kv = self.fresh("k");
                            pre.push(rir::let_(kv.clone(), k));
                            ps.push(Place::Map { obj: ov, key: rir::atom_e(kv) });
                        }
                        Some(Access::Field(f)) => {
                            let ot = self.ck.info.expr[&obj.id].ty;
                            let TyNode::Table(tab) = self.node(ot) else { unreachable!() };
                            let root = self.ck.st.tab_root(tab);
                            let store_opt = self.field_store_opt(root, &f);
                            ps.push(Place::Field { obj: ov, name: f, store_opt });
                        }
                        _ => ps.push(Place::Local(0)),
                    }
                }
                _ => ps.push(Place::Local(0)),
            }
        }
        (pre, ps)
    }

    fn read_place(&mut self, p: &Place, target: &Expr) -> Val {
        match p {
            Place::Runtime { obj, key } => Val { code: rir::at(rir::method(rir::atom_e(obj.clone()), "get", vec![rir::borrow(key.clone())]), &self.loc(target.span)), opt: false },
            Place::Local(s) => {
                let code = self.read_sym(*s);
                let opt = self.sym_opt(*s);
                match self.ck.info.narrowed.get(&target.id) {
                    Some(Narrow::NonNil) if opt => Val { code: rir::call("lr::narrowed", vec![code]), opt: false },
                    _ => {
                        // a late-initialized local is read with a presence check
                        Val { code, opt }
                    }
                }
            }
            Place::Field { obj, name, store_opt } => {
                if let Some(plan) = self.promoted_lookup(target.id) {
                    return self.lookup_read(plan, rir::borrow(rir::atom_e(obj.clone())), name);
                }
                Val { code: Self::record_read(rir::atom_e(obj.clone()), name), opt: *store_opt }
            }
            Place::Array { obj, key } => Val { code: rir::method(rir::atom_e(obj.clone()), "get", vec![rir::atom_e(key.clone())]), opt: true },
            Place::Map { obj, key } => Val { code: rir::method(rir::atom_e(obj.clone()), "get", vec![rir::borrow(key.clone())]), opt: true },
            Place::DynamicMap { obj, key, .. } => Val { code: self.dynamic_map_read(rir::method(key.clone(), "clone", vec![]), obj), opt: true },
            Place::NativeField { obj, get, .. } => {
                let getter = self.native_wrapper(*get);
                let ty = self.ck.info.expr[&target.id];
                Val { code: rir::try_(rir::call(getter, vec![rir::borrow(rir::atom_e(obj.clone()))])), opt: self.ety_opt(ty) }
            }
        }
    }

    fn write_sym(&mut self, s: SymId, value: impl Into<RExpr>) -> RStmt {
        let value = value.into();
        let sym = self.res.sym(s).clone();
        let name = rir::atom_e(self.sym_name(s));
        if sym.is_cell() {
            RStmt::Semi(rir::method(name, "set", vec![value]))
        } else {
            RStmt::Assign(name, value)
        }
    }

    fn write_place(&mut self, p: &Place, v: Val, span: Span) -> Vec<RStmt> {
        match p {
            Place::Runtime { obj, key } => {
                let value = rir::call("lr::dynamic::to_value", vec![v.code]);
                vec![RStmt::Semi(rir::at(rir::method(rir::atom_e(obj.clone()), "set", vec![key.clone(), value]), &self.loc(span)))]
            }
            Place::Local(s) => {
                let opt = self.sym_opt(*s);
                let c = self.coerce(v, opt, span, "attempt to use a nil value");
                vec![self.write_sym(*s, c)]
            }
            Place::Field { obj, name, store_opt } => {
                let c = self.coerce(v, *store_opt, span, "attempt to use a nil value");
                let t = self.fresh("v");
                let slot = rir::field(rir::method(rir::atom_e(obj.clone()), "borrow_mut", vec![]), rust_ident(name));
                vec![
                    rir::let_(t.clone(), c),
                    rir::let_(t.clone(), rir::call("std::mem::replace", vec![rir::unary("&mut ", slot), rir::atom_e(t.clone())])),
                    RStmt::Semi(rir::call("lr::value::release", vec![rir::atom_e(t)])),
                ]
            }
            Place::Array { obj, key } => {
                let loc = self.loc(span);
                let f = if v.opt { "set_opt" } else { "set" };
                vec![RStmt::Semi(rir::at(rir::method(rir::atom_e(obj.clone()), f, vec![rir::atom_e(key.clone()), v.code]), &loc))]
            }
            Place::Map { obj, key } => {
                let f = if v.opt { "set_opt" } else { "set" };
                vec![RStmt::Semi(rir::method(rir::atom_e(obj.clone()), f, vec![key.clone(), v.code]))]
            }
            Place::DynamicMap { obj, key, key_span } => {
                let f = if v.opt { "set_opt" } else { "set" };
                let value_name = self.fresh("value");
                let checked = rir::at(rir::call("lr::dynamic::Key::new", vec![key.clone()]), &self.loc(*key_span));
                vec![
                    rir::let_(value_name.clone(), v.code),
                    RStmt::Semi(rir::method(rir::atom_e(obj.clone()), f, vec![checked, rir::atom_e(value_name)])),
                ]
            }
            Place::NativeField { obj, set, .. } => {
                let setter = set.map(|s| self.native_wrapper(s)).unwrap_or_default();
                vec![RStmt::Semi(rir::try_(rir::call(setter, vec![rir::borrow(rir::atom_e(obj.clone())), v.code])))]
            }
        }
    }

    fn assign(&mut self, targets: &[Expr], vals: Vec<Val>, pre: Vec<RStmt>, out: &mut Vec<RStmt>) {
        let (tpre, places) = self.places(targets);
        emit(out, &tpre);
        emit(out, &pre);
        for ((p, v), t) in places.into_iter().zip(vals).zip(targets) {
            let w = self.write_place(&p, v, t.span);
            emit(out, &w);
        }
    }

    fn ret(&mut self, exprs: &[Expr], span: Span, out: &mut Vec<RStmt>) {
        let ctx = self.fn_rets.last().cloned().unwrap_or(FnRets::Module);
        match ctx {
            FnRets::Module => {
                let mi = self.cur_module;
                let v = match (exprs.first(), self.ck.info.module_value[mi]) {
                    (Some(e), Some(mv)) => {
                        let opt = self.ety_opt(mv);
                        self.expr_to(e, opt)
                    }
                    _ => rir::atom_e("()"),
                };
                emit(out, &[RStmt::Return(rir::call("Ok", vec![v]))]);
            }
            FnRets::Func(rets, tail, fid) => {
                if exprs.len() == 1 && self.ck.is_self_call_of(&exprs[0], fid) && self.res.funcs[&fid].local_func_sym.is_some() {
                    // tail call to itself: same result tuple
                    if let Some(CallKind::Static(_)) | Some(CallKind::Value) = self.ck.info.calls.get(&exprs[0].id) {
                        if let (RExpr::Try(call), _) = self.call_raw(&exprs[0]) {
                            emit(out, &[RStmt::Return(*call)]);
                            return;
                        }
                    }
                }
                if tail.is_some() {
                    return self.ret_tail(exprs, &rets, span, out);
                }
                let opts: Vec<bool> = rets.iter().map(|s| self.is_null(s.null)).collect();
                let (pre, vals) = self.values(exprs, rets.len(), span);
                emit(out, &pre);
                let mut cs: Vec<RExpr> =
                    vals.into_iter().enumerate().map(|(i, v)| self.coerce(v, opts[i], span, "attempt to return a nil value")).collect();
                let val = match cs.len() {
                    0 => rir::atom_e("()"),
                    1 => cs.remove(0),
                    _ => RExpr::Tuple(cs),
                };
                emit(out, &[RStmt::Return(rir::call("Ok", vec![val]))]);
            }
        }
    }
    /// `return` in a function with a result tail: the fixed results, then the
    /// vector of the remaining values (ending in a pack's values).
    fn ret_tail(&mut self, exprs: &[Expr], rets: &[Slot], span: Span, out: &mut Vec<RStmt>) {
        let mut pre = Vec::new();
        let mut vals: Vec<(Val, Span)> = Vec::new();
        let mut rest = None;
        for (i, e) in exprs.iter().enumerate() {
            let last = i + 1 == exprs.len();
            if last && (self.is_pack(e) || matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..))) {
                // earlier values are evaluated first
                let (p, pvals, r) = if self.is_pack(e) {
                    let (p, pv, src, start) = self.pack_src(e);
                    (p, pv, Some((src, start)))
                } else {
                    let (p, pv) = self.multi(e, None);
                    (p, pv, None)
                };
                if !p.is_empty() {
                    for (v, _) in vals.iter_mut() {
                        let t = self.fresh("x");
                        let c = std::mem::replace(&mut v.code, rir::atom_e(t.clone()));
                        pre.push(rir::let_(t, c));
                    }
                    pre.extend(p);
                }
                vals.extend(pvals.into_iter().map(|v| (v, e.span)));
                rest = r;
            } else {
                let v = self.expr(e);
                vals.push((v, e.span));
            }
        }
        emit(out, &pre);
        let k = rets.len();
        let mut cs = Vec::new();
        let mut consumed = 0;
        let mut it = vals.into_iter();
        for s in rets {
            let v = match (it.next(), &rest) {
                (Some((v, _)), _) => v,
                (None, Some((src, start))) => {
                    consumed += 1;
                    Val { code: va_get(src, start, consumed - 1), opt: true }
                }
                (None, None) => Val { code: rir::atom_e("None"), opt: true },
            };
            let opt = self.is_null(s.null);
            cs.push(self.coerce(v, opt, span, "attempt to return a nil value"));
        }
        let _ = k;
        let items: Vec<RExpr> = it.map(|(v, sp)| self.coerce(v, true, sp, "")).collect();
        let fixed = RExpr::Macro("vec".into(), items);
        cs.push(match rest {
            Some((src, start)) => rir::call("lr::va::with_rest", vec![fixed, rir::borrow(src), va_index(&start, consumed)]),
            None => fixed,
        });
        let val = if cs.len() == 1 { cs.remove(0) } else { RExpr::Tuple(cs) };
        emit(out, &[RStmt::Return(rir::call("Ok", vec![val]))]);
    }

    #[allow(clippy::too_many_arguments)]
    fn num_for(&mut self, _s: &Stat, v: &Name, a: &Expr, b: &Expr, c: Option<&Expr>, body: &Block) -> RStmt {
        let start = self.expr_nn(a, "'for' initial value must be a number");
        let limit = self.expr_nn(b, "'for' limit must be a number");
        let (step, step_lit) = match c {
            Some(c) => match &c.kind {
                ExprKind::Number(n) => (rir::token(num_lit(*n)), Some(*n)),
                ExprKind::Unary(UnOp::Neg, x) if matches!(x.kind, ExprKind::Number(_)) => {
                    let ExprKind::Number(n) = x.kind else { unreachable!() };
                    (rir::token(num_lit(-n)), Some(-n))
                }
                _ => (self.expr_nn(c, "'for' step must be a number"), None),
            },
            None => (rir::atom_e("1.0"), Some(1.0)),
        };
        let id = self.loop_enter(body);
        let labeled = self.loops.last().unwrap().labeled;
        let sym = self.res.decl(v.id);
        let inner = self.block(body);
        let (s, e, st, i) = (format!("__s{id}"), format!("__e{id}"), format!("__st{id}"), format!("__i{id}"));
        let mut out = vec![RStmt::Let(s.clone(), Some("f64".into()), start), RStmt::Let(e.clone(), Some("f64".into()), limit)];
        // Luau 0.743's test: `step > 0 ? i <= limit : i >= limit`. A zero (or NaN)
        // step takes the second form: no iterations when start < limit, otherwise
        // The loop runs until `break`.
        let cond = match step_lit {
            Some(x) if x > 0.0 => rir::bin(ROp::Le, rir::atom_e(i.clone()), rir::atom_e(e.clone())),
            Some(_) => rir::bin(ROp::Ge, rir::atom_e(i.clone()), rir::atom_e(e.clone())),
            None => rir::if_(rir::bin(ROp::Gt, rir::atom_e(st.clone()), rir::atom_e("0.0")), rir::bin(ROp::Le, rir::atom_e(i.clone()), rir::atom_e(e.clone())), rir::bin(ROp::Ge, rir::atom_e(i.clone()), rir::atom_e(e))),
        };
        out.push(RStmt::Let(st.clone(), Some("f64".into()), step));
        out.push(rir::let_(format!("mut {i}"), rir::atom_e(s)));
        let mut loop_body = self.loop_var_ir(sym, rir::atom_e(i.clone()));
        if labeled { loop_body.push(RStmt::Labeled(format!("'c{id}"), inner)); } else { loop_body.extend(inner); }
        loop_body.push(RStmt::OpAssign(rir::atom_e(i), "+=", rir::atom_e(st)));
        out.push(RStmt::Loop { label: self.loops.last().filter(|l| l.break_label).map(|_| format!("'l{id}")), cond: Some(cond), body: loop_body });
        self.loops.pop();
        RStmt::Block(out)
    }

    fn loop_var_ir(&mut self, sym: SymId, value: RExpr) -> Vec<RStmt> {
        let mut s = Vec::new();
        let v = if self.sym_opt(sym) { rir::some(value) } else { value };
        self.declare_local(sym, v, &mut s);
        s
    }

    fn gen_for(&mut self, s: &Stat, names: &[Name], exprs: &[Expr], body: &Block, out: &mut Vec<RStmt>) {
        let kind = self.ck.info.fors.get(&s.id).copied().unwrap_or(ForKind::Ipairs);
        if let ForKind::Native(into, next) = kind {
            return self.native_for(names, &exprs[0], into, next, body, out);
        }
        if kind == ForKind::Gmatch {
            return self.gmatch_for(s, names, &exprs[0], body, out);
        }
        let ExprKind::Call(_, args) = &exprs[0].kind else { return };
        let t = self.expr_nn(&args[0], "cannot iterate over nil");
        let id = self.loop_enter(body);
        let labeled = self.loops.last().unwrap().labeled;
        let ksym = self.res.decl(names[0].id);
        let vsym = names.get(1).map(|n| self.res.decl(n.id));
        let inner = self.block(body);
        let tv = format!("__t{id}");
        let label = self.loops.last().filter(|l| l.break_label).map(|_| format!("'l{id}"));
        let body_code = if labeled { vec![RStmt::Labeled(format!("'c{id}"), inner)] } else { inner };
        let mut block = vec![rir::let_(tv.clone(), t)];
        match kind {
            ForKind::Ipairs | ForKind::PairsArray => {
                let n = format!("__n{id}");
                let x = format!("__v{id}");
                block.push(RStmt::Let(format!("mut {n}"), Some("usize".into()), rir::atom_e("0")));
                let kdecl = self.loop_var_ir(ksym, rir::cast(rir::atom_e(n.clone()), "f64"));
                let vdecl = match vsym {
                    Some(v) => self.loop_var_ir(v, rir::atom_e(x.clone())),
                    None => vec![],
                };
                let xname = if vsym.is_some() { x.clone() } else { "_".into() };
                let mut body = vec![RStmt::OpAssign(rir::atom_e(n.clone()), "+=", rir::atom_e("1"))];
                body.extend(kdecl);
                body.extend(vdecl);
                body.extend(body_code);
                block.push(RStmt::Loop { label, cond: Some(rir::let_cond(format!("Some({xname})"), rir::method(rir::atom_e(tv), "get_at", vec![rir::atom_e(n)]))), body });
            }
            ForKind::PairsMap => {
                let k = format!("__k{id}");
                let x = format!("__v{id}");
                let kt = self.ck.info.sym_slot[&ksym].ty;
                let kexpr = match self.node(kt) {
                    TyNode::Num => rir::method(rir::atom_e(k.clone()), "get", vec![]),
                    TyNode::Bool => rir::atom_e(k.clone()),
                    TyNode::Any => rir::method(rir::atom_e(k.clone()), "value", vec![]),
                    _ => rir::method(rir::atom_e(k.clone()), "clone", vec![]),
                };
                let kdecl = self.loop_var_ir(ksym, kexpr);
                let vdecl = match vsym {
                    Some(v) => self.loop_var_ir(v, rir::atom_e(x.clone())),
                    None => vec![],
                };
                let xname = if vsym.is_some() { x.clone() } else { "_".into() };
                let mut body = vec![RStmt::LetElse(format!("Some({xname})"), rir::method(rir::atom_e(tv.clone()), "get", vec![rir::borrow(rir::atom_e(k.clone()))]), rir::atom_e("continue"))];
                body.extend(kdecl);
                body.extend(vdecl);
                body.extend(body_code);
                block.push(RStmt::ForIn { label, pat: k, iter: rir::method(rir::atom_e(tv), "keys", vec![]), body });
            }
            ForKind::Native(..) | ForKind::Gmatch | ForKind::Function | ForKind::Runtime => unreachable!("handled before the match"),
        }
        out.push(RStmt::Block(block));
        self.loops.pop();
    }

    /// `for a, b in iter do`: calls the iterator's `next` wrapper per iteration. The
    /// iterator handle is a block local, so it is released on exhaustion, `break`,
    /// `return` and errors alike.
    #[allow(clippy::too_many_arguments)]
    fn native_for(&mut self, names: &[Name], e: &Expr, into: Option<usize>, next: usize, body: &Block, out: &mut Vec<RStmt>) {
        let t = self.expr_nn(e, "cannot iterate over nil");
        let id = self.loop_enter(body);
        let labeled = self.loops.last().unwrap().labeled;
        let syms: Vec<SymId> = names.iter().map(|n| self.res.decl(n.id)).collect();
        let inner = self.block(body);
        let tv = format!("__t{id}");
        let label = self.loops.last().filter(|l| l.break_label).map(|_| format!("'l{id}"));
        let body_code = if labeled { vec![RStmt::Labeled(format!("'c{id}"), inner)] } else { inner };
        let loc = self.loc(e.span);
        let wnext = self.native_wrapper(next);
        let mut block = vec![rir::let_(tv.clone(), t)];
        if let Some(i) = into {
            let wi = self.native_wrapper(i);
            block.push(rir::let_(tv.clone(), rir::at(rir::call(wi, vec![rir::borrow(rir::atom_e(tv.clone()))]), &loc)));
        }
        let x = format!("__v{id}");
        let mut decls = Vec::new();
        if syms.len() == 1 {
            decls = self.loop_var_ir(syms[0], rir::atom_e(x.clone()));
        } else {
            let parts: Vec<String> = (0..syms.len()).map(|i| format!("{x}_{i}")).collect();
            decls.push(rir::let_(tuple_ty(&parts), rir::atom_e(x.clone())));
            for (i, s) in syms.iter().enumerate() {
                decls.extend(self.loop_var_ir(*s, rir::atom_e(parts[i].clone())));
            }
        }
        decls.extend(body_code);
        block.push(RStmt::Loop { label, cond: Some(rir::let_cond(format!("Some({x})"), rir::at(rir::call(wnext, vec![rir::borrow(rir::atom_e(tv))]), &loc))), body: decls });
        out.push(RStmt::Block(block));
        self.loops.pop();
    }

    /// `string.gsub(s, p, repl, n)`: the operands are evaluated in order, then the
    /// runtime scans once for the replacement kind the checker settled on.
    fn gsub_code(&mut self, e: &Expr, all: &[Arg]) -> (String, Vec<(TyId, bool)>) {
        let loc = self.loc(e.span);
        let outs: Vec<(TyId, bool)> = self.ck.info.builtin_outs[&e.id].iter().map(|o| (o.ty, false)).collect();
        let mode = self.ck.info.gsub_modes[&e.id].clone();
        let (sv, pv, rv, nv) = (self.fresh("s"), self.fresh("p"), self.fresh("r"), self.fresh("n"));
        let s = self.arg_nn(&all[0], "bad argument #1 to 'gsub'");
        let p = self.arg_nn(&all[1], "bad argument #2 to 'gsub'");
        let (r, call) = match mode {
            GsubMode::Template => {
                let r = self.arg_nn(&all[2], "bad argument #3 to 'gsub'");
                (r, format!("lr::subst::gsub_template(&{sv}, &{pv}, &{rv}, {nv})"))
            }
            GsubMode::Table => {
                let r = self.arg_ref(&all[2], "bad argument #3 to 'gsub'");
                (r, format!("lr::subst::gsub_table(&{sv}, &{pv}, &{rv}, {nv})"))
            }
            GsubMode::Func(_) => {
                let r = self.arg_nn(&all[2], "bad argument #3 to 'gsub'");
                let kinds = match self.ck.info.pattern_caps.get(&e.id) {
                    Some(c) if !c.is_empty() => c.clone(),
                    _ => vec![false],
                };
                let args: Vec<String> = kinds.iter().enumerate().map(|(i, &pos)| format!("__m.{}({i})", if pos { "pos_arg" } else { "str_arg" })).collect();
                (r, format!("lr::subst::gsub_fn(&{sv}, &{pv}, {nv}, |__m| {rv}.call({}))", tuple_ty(&args)))
            }
        };
        let n = match all.get(3) {
            Some(x) => self.arg_to(x, true),
            None => "None".into(),
        };
        (
            format!("{{ let {sv} = {}; let {pv} = {}; let {rv} = {}; let {nv} = {}; lr::at({call}, {loc})? }}", strip(s), strip(p), strip(r), strip(n)),
            outs,
        )
    }

    /// `for a, b in string.gmatch(s, p) do`: one `Gmatch` state per loop, advanced by
    /// each iteration; the loop variables are the match's captures.
    fn gmatch_for(&mut self, s: &Stat, names: &[Name], e: &Expr, body: &Block, out: &mut Vec<RStmt>) {
        let (subject, pat): (&Expr, &Expr) = match &e.kind {
            ExprKind::Call(_, args) => (&args[0], &args[1]),
            ExprKind::Method(o, _, args) => (&**o, &args[0]),
            _ => unreachable!("checked by gmatch_for"),
        };
        let subj = self.expr_nn(subject, "bad argument #1 to 'gmatch'");
        let pattern = self.expr_nn(pat, "bad argument #2 to 'gmatch'");
        let kinds = self.ck.info.gmatch_caps[&s.id].clone();
        let id = self.loop_enter(body);
        let labeled = self.loops.last().unwrap().labeled;
        let syms: Vec<SymId> = names.iter().map(|n| self.res.decl(n.id)).collect();
        let inner = self.block(body);
        let label = self.loops.last().filter(|l| l.break_label).map(|_| format!("'l{id}"));
        let body_code = if labeled { vec![RStmt::Labeled(format!("'c{id}"), inner)] } else { inner };
        let loc = self.loc(e.span);
        let m = format!("__m{id}");
        let mut decls = Vec::new();
        for (i, (sym, &pos)) in syms.iter().zip(&kinds).enumerate() {
            let value = rir::method(rir::atom_e(m.clone()), if pos { "position" } else { "text" }, vec![rir::atom_e(i.to_string())]);
            decls.extend(self.loop_var_ir(*sym, value));
        }
        decls.extend(body_code);
        let block = vec![rir::let_(format!("__g{id}_s"), subj), rir::let_(format!("__g{id}_p"), pattern), rir::let_(format!("mut __g{id}"), rir::call("lr::subst::Gmatch::new", vec![rir::borrow(rir::atom_e(format!("__g{id}_s"))), rir::borrow(rir::atom_e(format!("__g{id}_p")))])), RStmt::Loop { label, cond: Some(rir::let_cond(format!("Some({m})"), rir::at(rir::method(rir::atom_e(format!("__g{id}")), "next", vec![]), &loc))), body: decls }];
        out.push(RStmt::Block(block));
        self.loops.pop();
    }

    // Modules

    fn module_file(&mut self, mi: usize) -> String {
        self.cur_module = mi;
        self.strs.clear();
        self.str_index.clear();
        self.hoisted.clear();
        self.static_values.clear();
        self.module_releases.clear();
        let u = &self.units[mi];
        self.fn_rets.clear();
        self.fn_rets.push(FnRets::Module);
        let mut body = block_text(&self.block_stats(&u.module.body));
        self.fn_rets.pop();
        let returns = matches!(u.module.body.stats.last().map(|s| &s.kind), Some(StatKind::Return(_)));
        if !returns && !block_exits(&u.module.body, self.res) {
            body.push_str("Ok(())\n");
        }
        let vt = match self.ck.info.module_value[mi] {
            Some(v) => {
                let opt = self.ety_opt(v);
                self.opt_ty(v.ty, opt)
            }
            None => "()".into(),
        };
        let file = &self.sm.files[u.module.file as usize];
        let mut s = String::new();
        let _ = writeln!(s, "//! Generated by luarc from `{}`. Do not edit.\n", file.display);
        let _ = writeln!(s, "#[allow(unused_imports)]\nuse crate::lr;\n#[allow(unused_imports)]\nuse crate::records::*;\n");
        if !self.strs.is_empty() {
            let lits: Vec<String> = self.strs.iter().map(|b| format!("    lr::LStr::from_bytes({}),", rust_bytes_lit(b))).collect();
            let _ = writeln!(
                s,
                "thread_local! {{\n    /// String literals of this module (created once).\n    static STRINGS: Vec<lr::LStr> = vec![\n{}\n    ];\n}}\n\n/// String literal `i` of this module.\nfn __str(i: usize) -> lr::LStr {{\n    STRINGS.with(|s| s[i].clone())\n}}\n",
                lits.join("\n")
            );
        }
        for v in self.static_values.values() {
            s.push_str(v);
            s.push('\n');
        }
        for h in &self.hoisted {
            s.push_str(h);
            s.push('\n');
        }
        self.module_releases.push("MODULE_VALUE.with(|m| m.borrow_mut().take());".into());
        let releases = std::mem::take(&mut self.module_releases).join("\n    ");
        let _ = writeln!(
            s,
            "thread_local! {{\n    static MODULE_VALUE: std::cell::RefCell<Option<{vt}>> = const {{ std::cell::RefCell::new(None) }};\n}}\n"
        );
        let _ = writeln!(
            s,
            "/// Returns the module value, running the module body on first use.\npub fn require() -> lr::LResult<{vt}> {{\n    if let Some(v) = MODULE_VALUE.with(|m| m.borrow().clone()) {{\n        return Ok(v);\n    }}\n    let v = init()?;\n    MODULE_VALUE.with(|m| *m.borrow_mut() = Some(v.clone()));\n    lr::shutdown::at_exit(release);\n    Ok(v)\n}}\n\n/// Drops this module's values at program shutdown (modules are released in\n/// reverse initialization order, before the final collection).\nfn release() {{\n    {releases}\n}}\n"
        );
        let _ = writeln!(s, "fn init() -> lr::LResult<{vt}> {{\n{body}}}");
        s
    }

    pub fn generate(mut self, entry: usize) -> Output {
        let mut files = Vec::new();
        let mut mods = Vec::new();
        for mi in 0..self.units.len() {
            let code = self.module_file(mi);
            let ident = self.units[mi].ident.clone();
            files.push((format!("src/{ident}.rs"), code));
            mods.push(ident);
        }
        let (natives, wrapper_lines) = self.natives_file();
        files.push(("src/natives.rs".into(), natives));
        let records = self.record_defs();
        let mut rec = String::from("//! Record structs (one per structural record type). Generated by luarc.\n\n#[allow(unused_imports)]\nuse crate::lr;\n\n");
        rec.push_str(&records);
        files.push(("src/records.rs".into(), rec));
        let mut main = String::new();
        let _ = writeln!(main, "//! Generated by luarc. Entry module: `{}`.", self.sm.files[self.units[entry].module.file as usize].display);
        let _ = writeln!(main, "// Source identifiers keep their spelling and source-level dead stores are kept as written.");
        let _ = writeln!(main, "#![allow(non_snake_case, unused_assignments)]\n");
        let _ = writeln!(main, "use luarc_runtime as lr;\n");
        let _ = writeln!(main, "mod natives;\nmod records;");
        for m in &mods {
            let _ = writeln!(main, "mod {m};");
        }
        let host = if self.ck.info.calls.values().any(|c| matches!(c, CallKind::Coroutine(_))) { "run_main_coroutine" } else { "run_main" };
        let callback = rir::closure("", rir::block(vec![RStmt::Semi(rir::try_(rir::call(format!("{}::require", self.units[entry].ident), vec![])))], rir::call("Ok", vec![RExpr::Tuple(vec![])])));
        let host = RStmt::Function { name: "main".into(), body: vec![RStmt::Semi(rir::call(format!("lr::{host}"), vec![callback]))] };
        let _ = writeln!(main, "\n{}", host.print());
        files.push(("src/main.rs".into(), main));
        Output { files, wrapper_lines }
    }
}

/// Appends statements.
fn emit(out: &mut Vec<RStmt>, stmts: &[RStmt]) {
    out.extend_from_slice(stmts);
}

/// Statements as lines of text (function and loop bodies still assembled as strings).
fn block_text(stmts: &[RStmt]) -> String {
    let mut out = String::new();
    for s in stmts {
        out.push_str(&s.print());
        out.push('\n');
    }
    out
}

/// Name of a variadic function's `...` parameter (a nested function cannot use
/// its parent's `...`, so the name never needs to be unique).
const VA: &str = "__va";

/// Index `start + k` into `...`.
fn va_index(start: &RExpr, k: usize) -> RExpr {
    match start {
        RExpr::Atom(a) if a == "0" => rir::atom_e(k.to_string()),
        _ if k == 0 => start.clone(),
        _ => rir::bin(ROp::Add, start.clone(), rir::atom_e(k.to_string())),
    }
}

/// Value `start + k` of a pack vector (nil past the end).
fn va_get(src: &RExpr, start: &RExpr, k: usize) -> RExpr {
    rir::call("lr::va::get", vec![rir::borrow(src.clone()), va_index(start, k)])
}

/// The literal `false` (a condition that never holds).
fn is_false(e: &RExpr) -> bool {
    matches!(e, RExpr::Atom(a) if a == "false")
}

/// Statements as text, for code still assembled as strings.
fn stmts_text(stmts: &[RStmt]) -> String {
    stmts.iter().map(|s| s.print() + " ").collect()
}

/// `continue` targeting this loop (not nested loops or functions).
pub fn has_continue(b: &Block) -> bool {
    b.stats.iter().any(|s| match &s.kind {
        StatKind::Continue => true,
        StatKind::Do(x) => has_continue(x),
        StatKind::If(arms, els) => arms.iter().any(|(_, x)| has_continue(x)) || els.as_ref().map(has_continue).unwrap_or(false),
        _ => false,
    })
}

pub fn param_is_self(k: SymKind) -> bool {
    k == SymKind::Param
}

/// The Rust operator of an arithmetic or comparison source operator.
fn rop(op: BinOp) -> ROp {
    match op {
        BinOp::Add => ROp::Add,
        BinOp::Sub => ROp::Sub,
        BinOp::Mul => ROp::Mul,
        BinOp::Div => ROp::Div,
        BinOp::Lt => ROp::Lt,
        BinOp::Le => ROp::Le,
        BinOp::Gt => ROp::Gt,
        BinOp::Ge => ROp::Ge,
        BinOp::Eq => ROp::Eq,
        BinOp::Ne => ROp::Ne,
        _ => unreachable!("not a Rust operator: {op:?}"),
    }
}

/// `lr::stdlib::concat(&[&a as &dyn ConcatPart, &b, ...])`.
fn concat_call(parts: Vec<RExpr>) -> RExpr {
    let mut ps: Vec<RExpr> = parts.into_iter().map(rir::borrow).collect();
    ps[0] = rir::cast(ps[0].clone(), "&dyn lr::stdlib::ConcatPart");
    rir::call("lr::stdlib::concat", vec![rir::borrow(RExpr::Array(ps))])
}

/// Rust tuple type (or expression) for a list of elements: `()`, `(a,)`, `(a, b)`.
pub fn tuple_ty(items: &[String]) -> String {
    match items.len() {
        0 => "()".into(),
        1 => format!("({},)", items[0]),
        _ => format!("({})", items.join(", ")),
    }
}

impl<'a> Gen<'a> {
    /// Whether an expression has the exact `integer` type.
    pub(crate) fn is_int_expr(&self, e: &Expr) -> bool {
        match self.ck.info.expr.get(&e.id) {
            Some(t) => self.ty_is_int(t.ty),
            None => false,
        }
    }

    fn ty_is_int(&self, t: TyId) -> bool {
        match self.node(t) {
            TyNode::Int => true,
            TyNode::NPrim(p) => crate::check::is_int_prim(&p),
            _ => false,
        }
    }

    /// Checked integer arithmetic (`/` and `^` are float operations, as in Lua).
    pub(crate) fn int_arith(&mut self, op: BinOp, x: RExpr, y: RExpr, span: crate::diag::Span) -> RExpr {
        let loc = self.loc(span);
        let float = |v: RExpr| rir::at(rir::call("lr::int::float_operand", vec![v]), &loc);
        match op {
            BinOp::Div => rir::bin(ROp::Div, float(x), float(y)),
            BinOp::Pow => rir::call("f64::powf", vec![float(x), float(y)]),
            _ => {
                let f = match op {
                    BinOp::Add => "add",
                    BinOp::Sub => "sub",
                    BinOp::Mul => "mul",
                    BinOp::IDiv => "idiv",
                    _ => "modulo",
                };
                rir::at(rir::call(format!("lr::int::{f}"), vec![x, y]), &loc)
            }
        }
    }
}
impl<'a> Gen<'a> {
    /// A builtin used as a function value: a capture-free closure with the
    /// signature the checker fixed from its uses.
    pub(crate) fn builtin_value_code(&mut self, e: &Expr) -> String {
        use crate::resolve::Builtin as B;
        let (b, field) = self.ck.info.builtin_values[&e.id].clone();
        let t = self.ck.info.expr[&e.id].ty;
        let f = self.func_of(t);
        let (args_ty, rty) = self.fn_args(&f);
        let n = f.params.len();
        let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let opt: Vec<bool> = f.params.iter().map(|p| self.is_null(p.null)).collect();
        let loc = self.loc(e.span);
        let body = match (b, field.as_deref()) {
            (B::Print, None) => {
                let items: Vec<String> = names.iter().map(|a| format!("&{a} as &dyn lr::LuaDisplay")).collect();
                format!("lr::stdlib::print(&[{}]); Ok(())", items.join(", "))
            }
            (B::ToString, None) => "Ok(lr::show::tostring(&a0))".to_string(),
            (B::Type, None) => "Ok(lr::LStr::from(lr::LuaType::lua_type(&a0)))".to_string(),
            (B::Error, None) => format!("lr::error::raise::<()>(lr::show::tostring(&a0), {loc})"),
            (B::ToNumber, None) => "Ok(lr::stdlib::tonumber(&a0))".to_string(),
            (B::StringLib, Some("upper")) => "Ok(lr::stdlib::string_upper(&a0))".to_string(),
            (B::StringLib, Some("lower")) => "Ok(lr::stdlib::string_lower(&a0))".to_string(),
            (B::StringLib, Some("len")) => "Ok(a0.len())".to_string(),
            (B::Math, Some(m @ ("floor" | "ceil" | "abs" | "sqrt"))) => format!("Ok(f64::{m}(a0))"),
            (B::Math, Some(m @ ("min" | "max"))) => format!("Ok(lr::stdlib::math_{m}(a0, &[{}]))", names[1..].join(", ")),
            (B::Table, Some("insert")) => "a0.push(a1); Ok(())".to_string(),
            _ => "unreachable!(\"luarc: unsupported builtin value\")".to_string(),
        };
        // optional parameters of a value-shaped builtin are displayed as nil
        let _ = opt;
        let env = self.fresh("BEnv");
        format!(
            "{{ #[derive(lr::Trace)] #[dumpster(crate = lr::gc::dumpster)] struct {env}; impl lr::Callable<{args_ty}, {rty}> for {env} {{ fn call(&self, _this: &lr::LFn<{args_ty}, {rty}>, __args: {args_ty}) -> lr::LResult<{rty}> {{ let {} = __args; {body} }} }} lr::LFn::new({env}) }}",
            tuple_ty(&names)
        )
    }
}

impl<'a> Gen<'a> {
    /// `task.spawn(function() ... end)` and the other task functions.
    fn task_call_code(&mut self, e: &Expr, name: &str, args: &[Expr]) -> (String, Vec<(TyId, bool)>) {
        let sty = self.ck.info.expr[&e.id].ty;
        let loc = self.loc(e.span);
        match name {
            "spawn" => {
                let ExprKind::Function(f) = &args[0].kind else { unreachable!() };
                (self.task_spawn_code(f), vec![(sty, false)])
            }
            "wake_through" => {
                let x = self.expr_nn(&args[0], "bad argument to task.wake_through (got nil)");
                let ty = self.ck.info.task_wakers[&e.id];
                let (m, a) = self.ck.adapters.task_waker(ty).map(|(m, a)| (m.to_string(), a.to_string())).unwrap_or_default();
                (
                    format!("{{ let __wk = (*{}.get()?).clone(); lr::task::set_wake_hook(Some(std::sync::Arc::new(move || {{ let _ = __wk.{m}({a}); }}))); }}", atom(x)),
                    vec![],
                )
            }
            "cancel" | "is_pending" => {
                let t = self.expr_nn(&args[0], "bad argument to task function (task expected, got nil)");
                (format!("lr::task::{name}({})", strip(t)), vec![(sty, false)])
            }
            "run_ready" => (format!("(lr::at(lr::task::run_ready(), {loc})? as f64)"), vec![(sty, false)]),
            "wait_idle" => (format!("{{ lr::at(lr::task::wait_idle(), {loc})?; 0.0 }}"), vec![(sty, false)]),
            "polls" => ("(lr::task::polls() as f64)".to_string(), vec![(sty, false)]),
            _ => ("(lr::task::pending() as f64)".to_string(), vec![(sty, false)]),
        }
    }

    /// A task function lowered to a Rust future: captures are moved into the
    /// `async` block (copyable values by value, shared objects by a clone of
    /// their handle), the body is the ordinary function body; `await` is
    /// `.await` on the native future.
    fn task_spawn_code(&mut self, f: &FuncBody) -> String {
        let finfo = self.res.funcs[&f.id].clone();
        let mut pre = Vec::new();
        let mut binds = Vec::new();
        let mut refs = HashSet::new();
        for c in &finfo.captures {
            if self.is_ns_sym(*c) {
                continue;
            }
            let n = self.sym_name(*c);
            let cell = self.res.sym(*c).is_cell();
            let slot = self.ck.info.sym_slot[c];
            let outer = self.sym_access(*c);
            if !cell && self.is_copy_ty(slot.ty) {
                pre.push(rir::let_(format!("__cap_{n}"), outer));
                binds.push(rir::let_(n.clone(), rir::atom_e(format!("__cap_{n}"))));
            } else {
                pre.push(rir::let_(format!("__cap_{n}"), rir::method(outer, "clone", vec![])));
                binds.push(rir::let_(n.clone(), rir::borrow(rir::atom_e(format!("__cap_{n}")))));
                if !cell {
                    refs.insert(*c);
                }
            }
        }
        self.ref_caps.push(refs);
        let body = self.func_body_ir(f, vec![], None);
        self.ref_caps.pop();
        RExpr::Spawn(Box::new(rir::SpawnFn { captures: pre, binds, body })).full()
    }
}


