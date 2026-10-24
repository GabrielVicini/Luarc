//! Type inference and checking.
//!
//! Constraint generation walks every module once. Structural constraints are solved
//! eagerly by unification; operations whose operand types are not yet known
//! (method calls on parameters, indexing of tables whose kind is still open, ...)
//! are queued and retried until no progress is made. Nullability is solved last.
//! The result (`Info`) records every decision the lowering stage needs.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::fmtspec::{Conv, Directive, FmtPiece};
use crate::ast::*;
use crate::diag::{Diagnostic, SourceMap, Span};
use crate::check_native::NativeInst;
use crate::native::types::TypeFacts;
use crate::native::world::{ItemRef, World};
use crate::resolve::{assigned_in_block, Builtin, Res, Resolution, SymId};
use crate::types::*;

// Results consumed by lowering

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinFn {
    Print,
    ToString,
    ToNumber,
    Type,
    Assert,
    Error,
    Pcall,
    Xpcall,
    Bit32(&'static str),
    StrLen,
    StrSplit,
    StrSub,
    StrUpper,
    StrReverse,
    StrLower,
    StrFormat,
    StrRep,
    StrByte,
    StrChar,
    StrFind,
    StrMatch,
    StrGsub,
    /// Only valid as the iterator of a `for ... in` loop.
    StrGmatch,
    TInsert,
    TFreeze,
    TIsFrozen,
    TMove,
    TRemove,
    TConcat,
    TCreate,
    TClone,
    TClear,
    Next,
    TSort,
    MFloor,
    MToInteger,
    MCeil,
    MSqrt,
    MAbs,
    MMin,
    MMax,
    /// `select("#", ...)`.
    SelectCount,
    /// `select(i, ...)`: the values of `...` from index `i`.
    Select,
    /// `table.unpack(t, i, j)`: a run-time number of results.
    TUnpack,
    TPack,
    /// Fixed-value select and protected calls retain their exact run-time count.
    SelectFixedCount,
    SelectFixed,
    PcallPack,
    /// Other `math` functions: (name, min args, max args), numbers in,
    /// `math_fn_results` numbers out.
    MFn(&'static str, usize, usize),
    CollectGarbage,
}

/// `math` functions of Luau 0.743 lowered to `MFn`.
pub const MATH_FNS: &[(&str, usize, usize)] = &[
    ("exp", 1, 1),
    ("log", 1, 2),
    ("log10", 1, 1),
    ("sin", 1, 1),
    ("cos", 1, 1),
    ("tan", 1, 1),
    ("asin", 1, 1),
    ("acos", 1, 1),
    ("atan", 1, 1),
    ("atan2", 2, 2),
    ("sinh", 1, 1),
    ("cosh", 1, 1),
    ("tanh", 1, 1),
    ("deg", 1, 1),
    ("rad", 1, 1),
    ("sign", 1, 1),
    ("round", 1, 1),
    ("fmod", 2, 2),
    ("pow", 2, 2),
    ("clamp", 3, 3),
    ("lerp", 3, 3),
    ("ldexp", 2, 2),
    ("frexp", 1, 1),
    ("modf", 1, 1),
    ("random", 0, 2),
    ("randomseed", 1, 1),
    ("noise", 1, 3),
];

/// Whether the last of `args` is a call that expanded to `n_vals - (len - 1)` ≠ 1
/// values.
fn multi_tail(args: &[Expr], n_vals: usize) -> bool {
    matches!(args.last().map(|a| &a.kind), Some(ExprKind::Call(..) | ExprKind::Method(..))) && n_vals != args.len()
}

/// Number of results of an `MFn` math function (the others return one number).
pub fn math_fn_results(name: &str) -> usize {
    match name {
        "frexp" | "modf" => 2,
        "randomseed" => 0,
        _ => 1,
    }
}

#[derive(Clone, Debug)]
pub enum CallKind {
    /// Direct call of a static (non-capturing) local function.
    Static(SymId),
    /// Call through a function value.
    Value,
    /// `obj:m(args)` on a record field holding a function (obj passed as self).
    RecordMethod(String),
    /// Dormant static record attachment (source builtin enabling follows in 1d).
    RecordParent,
    Builtin(BuiltinFn),
    Native(usize),
    Require(usize),
    RequireRust,
    /// `task.spawn` / `task.cancel` / ...
    Task(String),
    /// Source coroutine library operations (all yielding happens in the runtime).
    Coroutine(String),
    /// `await(f)`.
    Await,
}

#[derive(Clone, Debug)]
pub enum Access {
    Runtime,
    Array,
    Map,
    Field(String),
    /// Public field of a native handle (field-get instance; field-set instance for writes).
    NativeField(usize, Option<usize>),
    /// Enum unit variant constant (native instance index).
    NativeConst(usize),
    Namespace,
    MathPi,
    MathHuge,
    Arg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Narrow {
    NonNil,
    PcallOk,
    PcallErr,
    /// An `any` local known to hold this kind of value (`type(x) == "number"`).
    Is(crate::check_dynamic::Tag),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogicKind {
    /// Left operand is boolean (possibly nil).
    BoolLeft,
    /// Left operand is `FalseOr<T>`.
    FalseOrLeft,
    /// Left operand is a value that is falsey only when nil.
    ValueLeft,
    /// The left operand decides statically (`true or x`, `false and x`, `0 or x`):
    /// the result is the left operand, the right one never runs.
    LeftOnly,
    /// The left operand decides statically the other way (`true and x`, `"" and x`,
    /// `false or x`): the result is the right operand.
    RightOnly,
    /// An operand is `any`: the result is `any`, truthiness is the run-time tag.
    AnyLeft,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForKind {
    Function,
    Runtime,
    Ipairs,
    PairsArray,
    PairsMap,
    /// `string.gmatch(s, p)`; the pattern's captures are in `Info::gmatch_caps`.
    Gmatch,
    /// Native iterator: optional `IntoIterator::into_iter` instance, then the
    /// `Iterator::next` instance called once per iteration.
    Native(Option<usize>, usize),
}

/// The replacement argument of `string.gsub`.
#[derive(Clone, Debug)]
pub enum GsubMode {
    /// a string with `%0`..`%9`
    Template,
    /// a `{[string]: string}` table
    Table,
    /// a function of the captures; its result slot decides whether it may return nil
    Func(Slot),
}

#[derive(Default)]
pub struct Info {
    pub xpcall_boxes: Vec<(TyId, Span)>,
    pub runtime_tables: crate::check_runtime_table::RuntimeInfo,
    /// Functions whose arguments cross an erased runtime boundary.
    pub runtime_functions: HashSet<NodeId>,
    pub expr: HashMap<NodeId, ETy>,
    pub sym_slot: HashMap<SymId, Slot>,
    pub narrowed: HashMap<NodeId, Narrow>,
    pub calls: HashMap<NodeId, CallKind>,
    pub access: HashMap<NodeId, Access>,
    pub logic: HashMap<NodeId, LogicKind>,
    pub fors: HashMap<NodeId, ForKind>,
    pub iteration: HashMap<NodeId, crate::check_iteration::Iteration>,
    pub table_layouts: HashMap<NodeId, (usize, usize)>,
    pub unproven_table_layouts: Vec<(NodeId, Span)>,
    pub next_tables: Vec<TyId>,
    pub constant_strings: HashMap<NodeId, Vec<u8>>,
    pub rooted_constant_string_files: HashSet<u32>,
    pub next_key_sources: HashMap<SymId, Vec<crate::check_next_identity::KeySource>>,
    pub next_key_checks: Vec<(Expr, Expr)>,
    pub array_loop_tables: HashMap<NodeId, ETy>,
    pub funcs: HashMap<NodeId, TyId>,
    pub coroutines: crate::check_coroutine::CoroutineInfo,
    pub falls_through: HashSet<NodeId>,
    pub natives: Vec<NativeInst>,
    pub formats: HashMap<NodeId, Vec<FmtPiece>>,
    pub field_refs: Vec<(TabId, String)>,
    /// Final own/fallback candidates for reads in the record-parent checker path.
    pub record_lookups: HashMap<NodeId, crate::check_metatable::RecordLookup>,
    pub record_methods: HashMap<NodeId, ETy>,
    pub record_attachments: HashMap<NodeId, (ETy, ETy)>,
    pub record_keys: HashMap<NodeId, String>,
    pub soft_deferred: Vec<Option<Soft>>,
    /// Module index → module return value type (None: returns nothing).
    pub module_value: Vec<Option<ETy>>,
    /// `#e` nodes whose operand is a string (otherwise an array).
    pub len_str: HashSet<NodeId>,
    /// Native instances that are adapter-provided `close()` methods.
    pub closes: HashSet<usize>,
    /// `string.find` / `string.match` call nodes → number of captures of the
    /// literal pattern (results are typed per capture).
    pub pattern_caps: HashMap<NodeId, Vec<bool>>,
    /// `find`/`match` calls with a pattern not known at compile time whose call site
    /// observes more results than a pattern without captures gives.
    pub pattern_full: HashSet<NodeId>,
    /// Result types of builtins with several results (by call node).
    pub builtin_outs: HashMap<NodeId, Vec<ETy>>,
    /// How each `string.gsub` call produces its replacements.
    pub gsub_modes: HashMap<NodeId, GsubMode>,
    /// Replacement strings of `string.gsub` calls known at compile time.
    pub gsub_templates: HashMap<NodeId, Vec<u8>>,
    /// Captures of a `string.gmatch` loop's pattern (`true`: position capture), by loop.
    pub gmatch_caps: HashMap<NodeId, Vec<bool>>,
    /// Builtin call nodes (function or method form) whose last argument is a call
    /// that gives zero or several values → the values it expands to.
    pub multi_tail: HashMap<NodeId, Vec<ETy>>,
    /// Calls used for all their values whose callee returns a run-time number of
    /// values: the element of the values after the fixed results.
    pub pack_calls: HashMap<NodeId, ETy>,
    pub packs: crate::check_packs::PackInfo,
    /// `<const>` / `<close>` attributes of local declarations (name node ids).
    pub local_attrs: HashMap<NodeId, crate::ast::LocalAttr>,
    /// Locals bound once to a builtin (`local log = print`): calls through them are builtin calls.
    pub builtin_aliases: HashMap<SymId, crate::check_builtin::BuiltinRef>,
    /// Locals initialized with a string literal and never reassigned → that string.
    pub const_strs: HashMap<SymId, Vec<u8>>,
    /// `local` statements declaring such aliases (no code is generated for them).
    pub alias_decls: HashSet<NodeId>,
    /// Builtins used as function values (expression node → builtin).
    pub builtin_values: HashMap<NodeId, crate::check_builtin::BuiltinRef>,
    /// `pcall` call node → number of results of the called function.
    pub pcall_rets: HashMap<NodeId, usize>,
    /// `await(x)` nodes on native values implementing Future → instance.
    pub await_native: HashMap<NodeId, usize>,
    /// `task.wake_through(x)` nodes → native type with a waker adapter.
    pub task_wakers: HashMap<NodeId, crate::native::world::ItemRef>,
    /// Native record tables → concrete rustdoc type arguments (by parameter name).
    pub record_rd_args: HashMap<TabId, HashMap<String, (usize, rustdoc_types::Type)>>,
    /// (native instance, parameter) → traits implemented by the source table passed there.
    pub trait_impls: HashMap<(usize, usize), Vec<crate::check_trait::TraitImpl>>,
    /// `pcall` call node → whether each result after the first is never nil on success.
    pub pcall_nonnull: HashMap<NodeId, Vec<bool>>,
    /// Boxing, casts and dynamic operations of the type `any`.
    pub dynamic: crate::check_dynamic::DynInfo,
}

#[derive(Clone)]
pub struct ModuleUnit {
    pub module: Module,
    pub pseudo_func: NodeId,
    /// Rust-safe module identifier.
    pub ident: String,
    /// `require("./x")` call node → module index.
    pub requires: HashMap<NodeId, usize>,
    /// `require("rust:x")` call node → crate index.
    pub rust_requires: HashMap<NodeId, usize>,
}

// Deferred operations

#[derive(Clone, Debug)]
pub(crate) enum Op {
    /// A value whose producer must settle before conversion to dynamic `any`.
    FlowAny { node: NodeId, value: ETy, dst: Slot, span: Span },
    RecordParent { node: NodeId, child: ETy, class: SymId, span: Span },
    RecordMetatable { node: NodeId, child: ETy, metatable: ETy, span: Span },
    /// `pack`: the elements of a trailing `...` argument.
    Call { callee: ETy, args: Vec<ETy>, nodes: Vec<NodeId>, spans: Vec<Span>, results: Vec<ETy>, span: Span, pack: Option<ETy> },
    Field { node: NodeId, obj: ETy, name: String, result: ETy, write: Option<ETy>, span: Span },
    Index { node: NodeId, obj: ETy, key: ETy, key_lit: Option<String>, result: ETy, write: Option<ETy>, span: Span },
    Method { node: NodeId, obj: ETy, name: String, args: Vec<ETy>, spans: Vec<Span>, results: Vec<ETy>, span: Span },
    Logic { node: NodeId, and: bool, a: ETy, b: ETy, result: ETy, span: Span, site: crate::check_dynamic::LogicSite },
    Len { node: NodeId, e: ETy, span: Span },
    NumOrStr { e: ETy, default_str: bool, span: Span, what: &'static str },
    Test { ty: TyId, null: NullId },
    Pairs { node: NodeId, t: ETy, k: Slot, v: Slot, span: Span },
    NativeFor { node: NodeId, t: ETy, vars: Vec<Slot>, span: Span },
    /// Arithmetic (`op` None: unary minus): integer × integer or number × number.
    Arith { op: Option<BinOp>, x: ETy, y: ETy, r: TyId, span: Span },
    /// Native i64/u64 parameter: accepts `integer` or (checked) `number`.
    IntParam { ty: TyId },
    /// A builtin used as a function value; its signature comes from its uses.
    BuiltinValue { r: crate::check_builtin::BuiltinRef, ty: TyId, span: Span },
    /// A table passed to a trait-bounded native generic parameter.
    TraitImpl { inst: usize, param: usize, arg: ETy, span: Span },
    /// `pcall(f)` where the results of `f` are not known yet (`fn` is a parameter whose
    /// type comes from the call site): binds the pcall results once they are.
    PcallRets { node: NodeId, rets: RetsId, inner: Slot, extras: Vec<ETy>, span: Span },
    Next { table: ETy, key: Option<ETy>, results: Vec<ETy>, span: Span },
    Clear { table: ETy, span: Span },
}

pub(crate) struct FnCtx {
    id: NodeId,
    /// A task function (`task.spawn(function() ... end)`): `await` is allowed.
    pub(crate) task: bool,
    annotated: bool,
    /// (values, span, self tail call, trailing pack element)
    returns: Vec<(Vec<ETy>, Span, bool, Option<ETy>)>,
    /// Element slot of the function's `...`.
    vararg: Option<Slot>,
    /// Set for a copy made for one call site (`specialize.rs`).
    pub(crate) call_site: Option<Span>,
    /// Expression ids of each `return` (parallel to `returns`), to box values returned as `any`.
    ret_nodes: Vec<Vec<NodeId>>,
}

pub struct Checker<'a> {
    pub res: &'a Resolution,
    pub sm: &'a SourceMap,
    pub world: &'a World,
    pub facts: TypeFacts,
    pub st: Store,
    pub info: Info,
    pub errors: Vec<Diagnostic>,
    /// Locals declared without a value (or reassigned local functions): stored as
    /// optional, read with a runtime presence check ("soft"), like Lua's nil.
    pub late_init: HashSet<SymId>,
    pending: Vec<Op>,
    requirements: Vec<(ETy, Span, String)>,
    pub(crate) fns: Vec<FnCtx>,
    narrow: Vec<HashMap<SymId, Narrow>>,
    pcall_pairs: HashMap<SymId, SymId>,
    /// `local ok, v, w = pcall(...)`: results after the second, non-nil when `ok`.
    pcall_extras: HashMap<SymId, Vec<SymId>>,
    /// Result slots assumed non-nil for narrowing (verified once nullness is final).
    pcall_checks: Vec<(Span, Vec<(Slot, bool)>)>,
    /// `and`/`or` nodes decided as `ValueLeft`: (node, left type, is `and`, result type, span),
    /// re-validated against the final types in `finish`.
    logic_checks: Vec<(NodeId, TyId, bool, TyId, Span)>,
    /// Calls whose result count was taken before the callee was known (`want` unset):
    /// callee or receiver, method name, assumed count, span. Re-checked in `finish`
    /// so a wrong guess is a diagnostic, never silently dropped results.
    arity_guesses: Vec<(ETy, Option<String>, usize, Span)>,
    /// The next `exprs_all` may end in a call returning a run-time number of
    /// values (argument lists, `print`, table constructors, `return`).
    pub(crate) allow_pack: bool,
    /// The tail call of a `print` argument list: codegen prints its final result
    /// count, so a guessed count there is harmless.
    arity_exempt: Option<NodeId>,
    aliases: HashMap<(u32, String), (TypeExpr, Option<Slot>)>,
    rust_imports: HashMap<(u32, String), ItemRef>,
    pub(crate) native_records: HashMap<(ItemRef, Vec<TyId>), TabId>,
    /// Associated item or variant → (owning type, (impl, trait)) for namespace calls.
    pub(crate) ns_owner: HashMap<ItemRef, (ItemRef, Option<(ItemRef, Option<ItemRef>)>)>,
    /// Concrete type arguments of an alias an associated item was reached through.
    pub(crate) ns_rd_args: HashMap<ItemRef, HashMap<String, (usize, rustdoc_types::Type)>>,
    pub(crate) pending_alias_args: Option<HashMap<String, (usize, rustdoc_types::Type)>>,
    pub adapters: &'a crate::native::adapters::AdapterSet,
    pub(crate) cur_file: u32,
    units: Vec<(HashMap<NodeId, usize>, HashMap<NodeId, usize>)>,
    pub(crate) defaults_round: bool,
    /// Call node of the builtin whose signature is being checked.
    pub(crate) cur_call: NodeId,
    /// Defaults round for literals (applied after every other default).
    pub(crate) literal_defaults: bool,
    /// The next checked function body is a task function.
    pub(crate) next_fn_is_task: bool,
    pub(crate) metatables: crate::check_metatable::MetaState,
    pub(crate) dynamic: crate::check_dynamic::DynState,
    /// Results the current `pcall` call site takes (`None`: all).
    pub(crate) pcall_want: Option<usize>,
    pub(crate) exact_pcall: bool,
}

const PACK_CALL_MSG: &str = "this call returns a variable number of values (`...`): it can end the arguments of a function call or print, end a table constructor or a return, or be assigned to a fixed number of variables";

const PACK_MSG: &str = "'...' cannot be used here: its number of values is only known at run time (it can end the arguments of a function call or print, end a table constructor or a return, or be assigned to a fixed number of variables)";

pub fn is_lib(e: &Expr, res: &Resolution) -> Option<Builtin> {
    if let ExprKind::Name(n) = &e.kind {
        if let Some(Res::Builtin(b)) = res.res(n.id) {
            return Some(b);
        }
    }
    None
}

impl<'a> Checker<'a> {
    pub fn new(res: &'a Resolution, sm: &'a SourceMap, world: &'a World, adapters: &'a crate::native::adapters::AdapterSet) -> Self {
        Checker {
            res,
            sm,
            world,
            facts: TypeFacts::default(),
            st: Store::new(),
            info: Info::default(),
            errors: Vec::new(),
            late_init: HashSet::new(),
            pending: Vec::new(),
            requirements: Vec::new(),
            fns: Vec::new(),
            narrow: Vec::new(),
            pcall_pairs: HashMap::new(),
            pcall_extras: HashMap::new(),
            pcall_checks: Vec::new(),
            logic_checks: Vec::new(),
            arity_guesses: Vec::new(),
            allow_pack: false,
            arity_exempt: None,
            aliases: HashMap::new(),
            rust_imports: HashMap::new(),
            native_records: HashMap::new(),
            ns_owner: HashMap::new(),
            ns_rd_args: HashMap::new(),
            pending_alias_args: None,
            adapters,
            cur_file: 0,
            units: Vec::new(),
            defaults_round: false,
            cur_call: 0,
            literal_defaults: false,
            next_fn_is_task: false,
            metatables: Default::default(),
            dynamic: Default::default(),
            pcall_want: None,
            exact_pcall: false,
        }
    }

    pub(crate) fn error(&mut self, span: Span, msg: impl Into<String>) {
        // messages say "a <type> value"; the dynamic type reads "an 'any' value"
        let msg: String = msg.into().replace(" a any value", " an 'any' value");
        self.errors.push(Diagnostic::new(span, msg));
    }

    // Small constructors

    pub(crate) fn prim(&mut self, n: TyNode) -> TyId {
        self.st.ty(n)
    }
    pub(crate) fn val(&mut self, ty: TyId) -> ETy {
        ETy { ty, null: self.st.null_false, soft: Soft::No }
    }
    pub(crate) fn num(&mut self) -> ETy {
        let t = self.prim(TyNode::Num);
        self.val(t)
    }
    pub(crate) fn str_(&mut self) -> ETy {
        let t = self.prim(TyNode::Str);
        self.val(t)
    }
    pub(crate) fn bool_(&mut self) -> ETy {
        let t = self.prim(TyNode::Bool);
        self.val(t)
    }
    pub(crate) fn nil(&mut self) -> ETy {
        let t = self.st.var();
        ETy { ty: t, null: self.st.null_true, soft: Soft::No }
    }
    pub(crate) fn of_slot(&self, s: Slot) -> ETy {
        ETy { ty: s.ty, null: s.null, soft: Soft::No }
    }
    pub(crate) fn fresh_result(&mut self) -> ETy {
        let ty = self.st.var();
        let null = self.st.new_null();
        ETy { ty, null, soft: Soft::No }
    }
    pub(crate) fn deferred_result(&mut self) -> ETy {
        let mut r = self.fresh_result();
        self.info.soft_deferred.push(None);
        r.soft = Soft::Deferred((self.info.soft_deferred.len() - 1) as u32);
        r
    }
    pub(crate) fn set_soft(&mut self, r: &ETy, s: Soft) {
        if let Soft::Deferred(d) = r.soft {
            self.info.soft_deferred[d as usize] = Some(s);
        }
    }

    // Type display

    pub fn show(&self, t: TyId) -> String {
        self.show_depth(t, 0)
    }
    pub(crate) fn show_depth(&self, t: TyId, d: u32) -> String {
        if d > 4 {
            return "...".into();
        }
        match self.st.node(t) {
            TyNode::Var => "unknown".into(),
            TyNode::Link(_) => unreachable!(),
            TyNode::Num => "number".into(),
            TyNode::NumVar => "number".into(),
            TyNode::Int => "integer".into(),
            TyNode::Str => "string".into(),
            TyNode::Bool => "boolean".into(),
            TyNode::Future(_) => "future".into(),
            TyNode::Task => "task".into(),
            TyNode::Any => "any".into(),
            TyNode::Nil => "nil".into(),
            TyNode::Native(n) => {
                let base = n.key.rsplit("::").next().unwrap_or(&n.key).to_string();
                if n.args.is_empty() {
                    base
                } else {
                    let a: Vec<String> = n.args.iter().map(|t| self.show_depth(*t, d + 1)).collect();
                    format!("{base}<{}>", a.join(", "))
                }
            }
            TyNode::NPrim(p) => p.to_string(),
            TyNode::Namespace(r) => {
                let w = self.world;
                let path = w.def_path(*r);
                format!("{} {}", if w.item(*r).map(|i| matches!(i.inner, rustdoc_types::ItemEnum::Module(_))).unwrap_or(false) { "module" } else { "namespace" }, path.join("."))
            }
            TyNode::FalseOr(x) => format!("false | {}", self.show_depth(*x, d + 1)),
            TyNode::Pcall(s) => format!("{} | string", self.show_depth(s.ty, d + 1)),
            TyNode::Func(f) => {
                let mut ps: Vec<String> = f.params.iter().map(|p| self.show_slot(*p, d + 1)).collect();
                if let Some(v) = f.vararg {
                    ps.push(format!("...{}", self.show_slot(v, d + 1)));
                }
                let rs = match self.st.rets_known(f.rets) {
                    Some(r) => {
                        let mut v: Vec<String> = r.iter().map(|p| self.show_slot(*p, d + 1)).collect();
                        if let Some(t) = self.st.rets_tail(f.rets) {
                            v.push(format!("...{}", self.show_slot(t, d + 1)));
                        }
                        if v.len() == 1 && self.st.rets_tail(f.rets).is_none() {
                            v[0].clone()
                        } else {
                            format!("({})", v.join(", "))
                        }
                    }
                    None => "...".into(),
                };
                format!("({}) -> {}", ps.join(", "), rs)
            }
            TyNode::Table(tb) => {
                let tn = self.st.tab(*tb);
                match tn.kind {
                    TKind::Unknown => "{}".into(),
                    TKind::Array => format!("{{{}}}", tn.elem.map(|s| self.show_depth(s.ty, d + 1)).unwrap_or_default()),
                    TKind::Map => format!(
                        "{{[{}]: {}}}",
                        tn.key.map(|s| self.show_depth(s.ty, d + 1)).unwrap_or_default(),
                        tn.val.map(|s| self.show_depth(s.ty, d + 1)).unwrap_or_default()
                    ),
                    TKind::Record => {
                        if let Some(h) = &tn.hint {
                            return h.clone();
                        }
                        let fs: Vec<String> =
                            tn.fields.iter().map(|(k, s)| format!("{k}: {}", self.show_slot(*s, d + 1))).collect();
                        format!("{{{}}}", fs.join(", "))
                    }
                }
            }
        }
    }
    pub(crate) fn show_slot(&self, s: Slot, d: u32) -> String {
        let base = self.show_depth(s.ty, d);
        let n = self.st.null_root(s.null) as usize;
        if self.st.nulls[n].forced.is_some() {
            format!("{base}?")
        } else {
            base
        }
    }

    // Unification

    pub(crate) fn mismatch(&mut self, span: Span, a: TyId, b: TyId) {
        let (sa, sb) = (self.show(a), self.show(b));
        self.error(span, format!("type mismatch: expected {sb}, found {sa}"));
    }

    pub fn unify(&mut self, a: TyId, b: TyId, span: Span) -> bool {
        let (ra, rb) = (self.st.root(a), self.st.root(b));
        if ra == rb {
            return true;
        }
        let (na, nb) = (self.st.tys[ra as usize].clone(), self.st.tys[rb as usize].clone());
        if self.metatables.general && !matches!((&na, &nb), (TyNode::Table(_), TyNode::Table(_))) {
            if let Some(message) = self.general_record_type_error(ra, rb) {
                self.error(span, message);
                return false;
            }
        }
        match (&na, &nb) {
            (TyNode::Var, _) => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            (_, TyNode::Var) => {
                self.st.tys[rb as usize] = TyNode::Link(ra);
                true
            }
            // an integral literal takes the numeric type it meets
            (TyNode::NumVar, TyNode::NumVar | TyNode::Num | TyNode::Int) => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            (TyNode::Num | TyNode::Int, TyNode::NumVar) => {
                self.st.tys[rb as usize] = TyNode::Link(ra);
                true
            }
            (TyNode::NumVar, TyNode::NPrim(p)) if !matches!(p.as_ref(), "bool" | "char" | "str") => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            (TyNode::NPrim(p), TyNode::NumVar) if !matches!(p.as_ref(), "bool" | "char" | "str") => {
                self.st.tys[rb as usize] = TyNode::Link(ra);
                true
            }
            (TyNode::Num, TyNode::Num) | (TyNode::Int, TyNode::Int) | (TyNode::Str, TyNode::Str) | (TyNode::Bool, TyNode::Bool) | (TyNode::Nil, TyNode::Nil) => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            (TyNode::Native(x), TyNode::Native(y)) if x.key == y.key && x.args.len() == y.args.len() => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                let mut ok = true;
                for (p, q) in x.args.iter().zip(y.args.iter()) {
                    ok &= self.unify(*p, *q, span);
                }
                ok
            }
            (TyNode::NPrim(x), TyNode::NPrim(y)) if x == y => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            // a pinned native primitive is more specific than its value type
            (TyNode::NPrim(p), TyNode::Num | TyNode::Int | TyNode::Str | TyNode::Bool) if nprim_matches(p, &nb) => {
                self.st.tys[rb as usize] = TyNode::Link(ra);
                true
            }
            (TyNode::Num | TyNode::Int | TyNode::Str | TyNode::Bool, TyNode::NPrim(p)) if nprim_matches(p, &na) => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            (TyNode::Namespace(r1), TyNode::Namespace(r2)) if r1 == r2 => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            (TyNode::Task, TyNode::Task) | (TyNode::Any, TyNode::Any) => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                true
            }
            (TyNode::Future(x), TyNode::Future(y)) if x.len() == y.len() => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                let mut ok = true;
                for (p, q) in x.iter().zip(y.iter()) {
                    ok &= self.unify_slot(*p, *q, span);
                }
                ok
            }
            (TyNode::FalseOr(x), TyNode::FalseOr(y)) => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                self.unify(*x, *y, span)
            }
            (TyNode::Pcall(x), TyNode::Pcall(y)) => {
                self.st.tys[ra as usize] = TyNode::Link(rb);
                self.unify_slot(*x, *y, span)
            }
            (TyNode::Table(x), TyNode::Table(y)) => {
                if self.metatables.enabled && !self.preflight_record_merge(*x, *y, span) {
                    return false;
                }
                self.st.tys[ra as usize] = TyNode::Link(rb);
                self.unify_tabs(*x, *y, span)
            }
            (TyNode::Func(f), TyNode::Func(g)) => {
                if f.params.len() != g.params.len() || f.vararg.is_some() != g.vararg.is_some() {
                    let (sa, sb) = (self.show(ra), self.show(rb));
                    self.error(span, format!("function type mismatch: expected {sb}, found {sa} (parameter counts differ)"));
                    return false;
                }
                self.st.tys[ra as usize] = TyNode::Link(rb);
                let mut ok = true;
                for (p, q) in f.params.iter().zip(g.params.iter()) {
                    ok &= self.unify_slot(*p, *q, span);
                }
                if let (Some(p), Some(q)) = (f.vararg, g.vararg) {
                    ok &= self.unify_slot(p, q, span);
                }
                ok & self.unify_rets(f.rets, g.rets, span)
            }
            _ => {
                self.mismatch(span, a, b);
                false
            }
        }
    }

    pub fn unify_slot(&mut self, a: Slot, b: Slot, span: Span) -> bool {
        let ok = self.unify(a.ty, b.ty, span);
        if let Err((sp, msg)) = self.st.equate(a.null, b.null) {
            let sp = if sp == Span::default() { span } else { sp };
            self.error(sp, msg);
            return false;
        }
        ok
    }

    pub(crate) fn unify_rets(&mut self, a: RetsId, b: RetsId, span: Span) -> bool {
        let (ra, rb) = (self.st.rets_root(a), self.st.rets_root(b));
        if ra == rb {
            return true;
        }
        let (na, nb) = (self.st.rets[ra as usize].clone(), self.st.rets[rb as usize].clone());
        match (na, nb) {
            (RetsNode::Unknown, _) => {
                self.st.rets[ra as usize] = RetsNode::Link(rb);
                true
            }
            (_, RetsNode::Unknown) => {
                self.st.rets[rb as usize] = RetsNode::Link(ra);
                true
            }
            (RetsNode::Known(x), RetsNode::Known(y)) => {
                let (tx, ty) = (self.st.rets_tail.get(&ra).copied(), self.st.rets_tail.get(&rb).copied());
                if tx.is_some() != ty.is_some() {
                    self.error(span, "function type mismatch: one returns a variable number of values (`...`), the other a fixed number");
                    return false;
                }
                if x.len() != y.len() {
                    self.error(
                        span,
                        format!("function type mismatch: one returns {} value(s), the other {}", x.len(), y.len()),
                    );
                    return false;
                }
                self.st.rets[ra as usize] = RetsNode::Link(rb);
                let mut ok = true;
                for (p, q) in x.iter().zip(y.iter()) {
                    ok &= self.unify_slot(*p, *q, span);
                }
                if let (Some(p), Some(q)) = (tx, ty) {
                    ok &= self.unify_slot(p, q, span);
                }
                ok
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn unify_tabs(&mut self, x: TabId, y: TabId, span: Span) -> bool {
        let (rx, ry) = (self.st.tab_root(x), self.st.tab_root(y));
        if rx == ry {
            return true;
        }
        if self.st.tab(rx).runtime || self.st.tab(ry).runtime {
            return self.unify_runtime_tables(rx, ry, span);
        }
        let (left, right) = (self.st.tab(rx), self.st.tab(ry));
        let dense_left = !left.sparse && left.kind == TKind::Array && !left.ctors.is_empty();
        let dense_right = !right.sparse && right.kind == TKind::Array && !right.ctors.is_empty();
        if (left.sparse && dense_right) || (right.sparse && dense_left) {
            self.error(span, "nil-preserving and dense arrays cannot share one static type");
            return false;
        }
        if left.sparse && right.sparse && left.packed != right.packed {
            self.error(span, "table.pack results and nil-preserving constructors cannot share one static type");
            return false;
        }
        if self.metatables.enabled && !self.preflight_record_merge(rx, ry, span) {
            return false;
        }
        let tx = self.st.tabs[rx as usize].clone();
        self.st.tab_mut(ry).sparse |= tx.sparse;
        self.st.tab_mut(ry).packed |= tx.packed;
        let parents = (tx.parent, self.st.tab(ry).parent);
        let metatables = (tx.metatable, self.st.tab(ry).metatable);
        self.st.tabs[rx as usize].link = Some(ry);
        self.st.tab_mut(ry).parent = parents.1.or(parents.0);
        self.st.tab_mut(ry).metatable = metatables.1.or(metatables.0);
        if let (Some(a), Some(b)) = metatables {
            if !self.unify_tabs(a, b, span) { return false; }
        }
        if let (Some(a), Some(b)) = parents {
            if !self.unify_tabs(a, b, span) {
                return false;
            }
        }
        if let Some(m) = self.info.record_rd_args.get(&rx).cloned() {
            self.info.record_rd_args.entry(ry).or_insert(m);
        }
        let mut ok = true;
        let ky = self.st.tab(ry).kind;
        let kind = match (tx.kind, ky) {
            (TKind::Unknown, k) | (k, TKind::Unknown) => k,
            (a, b) if a == b => a,
            (a, b) => {
                self.error(
                    span,
                    format!("table is used as {} here but as {} elsewhere (mixed tables are unsupported)", kname(b), kname(a)),
                );
                return false;
            }
        };
        self.st.tab_mut(ry).kind = kind;
        for (sel, get) in [(0, tx.elem), (1, tx.key), (2, tx.val)] {
            if let Some(s) = get {
                let other = match sel {
                    0 => self.st.tab(ry).elem,
                    1 => self.st.tab(ry).key,
                    _ => self.st.tab(ry).val,
                };
                match other {
                    Some(o) => ok &= self.unify_slot(s, o, span),
                    None => {
                        let t = self.st.tab_mut(ry);
                        match sel {
                            0 => t.elem = Some(s),
                            1 => t.key = Some(s),
                            _ => t.val = Some(s),
                        }
                    }
                }
            }
        }
        let y_closed = self.st.tab(ry).closed;
        let y_fields: BTreeSet<String> = self.st.tab(ry).fields.keys().cloned().collect();
        if tx.closed {
            for f in &y_fields {
                if !tx.fields.contains_key(f) {
                    ok = false;
                    self.error(span, format!("field '{f}' is not part of the record type {}", type_hint(&tx)));
                }
            }
        }
        for (name, s) in &tx.fields {
            let existing = self.st.tab(ry).fields.get(name).copied();
            match existing {
                Some(o) => ok &= self.unify_slot(*s, o, span),
                None => {
                    if y_closed {
                        ok = false;
                        let h = type_hint(self.st.tab(ry));
                        self.error(span, format!("field '{name}' is not part of the record type {h}"));
                    } else {
                        self.st.tab_mut(ry).fields.insert(name.clone(), *s);
                    }
                }
            }
        }
        let t = self.st.tab_mut(ry);
        t.closed |= tx.closed;
        t.ctors.extend(tx.ctors);
        if t.native.is_none() {
            t.native = tx.native;
        }
        if t.hint.is_none() {
            t.hint = tx.hint;
        }
        ok
    }

    /// A value flows into a storage slot.
    pub(crate) fn flow(&mut self, v: ETy, dst: Slot, span: Span) -> bool {
        let ok = self.unify(v.ty, dst.ty, span);
        self.st.edge(v.null, dst.null, span);
        ok
    }

    /// The value must not be nil here (hard-nil values are compile errors, soft
    /// table reads get a runtime check).
    pub(crate) fn need(&mut self, v: ETy, span: Span, what: &str) {
        self.requirements.push((v, span, what.to_string()));
    }

    pub(crate) fn table_ty(&mut self, tab: TabId) -> TyId {
        self.st.ty(TyNode::Table(tab))
    }

    pub(crate) fn ensure_kind(&mut self, tab: TabId, k: TKind, span: Span) -> bool {
        let cur = self.st.tab(tab).kind;
        if cur == k {
            return true;
        }
        if cur == TKind::Unknown {
            self.st.tab_mut(tab).kind = k;
            return true;
        }
        self.error(span, format!("table is used as {} here but as {} elsewhere (mixed tables are unsupported)", kname(k), kname(cur)));
        false
    }

    pub(crate) fn elem_slot(&mut self, tab: TabId) -> Slot {
        if let Some(s) = self.st.tab(tab).elem {
            return s;
        }
        let v = self.st.var();
        let sp = self.st.tab(tab).span;
        let s = self.st.fixed_slot(v, sp, "arrays cannot contain nil (holes are unsupported)");
        self.st.tab_mut(tab).elem = Some(s);
        s
    }
    pub(crate) fn key_slot(&mut self, tab: TabId) -> Slot {
        if let Some(s) = self.st.tab(tab).key {
            return s;
        }
        let v = self.st.var();
        let sp = self.st.tab(tab).span;
        let s = self.st.fixed_slot(v, sp, "map keys cannot be nil");
        self.st.tab_mut(tab).key = Some(s);
        s
    }
    pub(crate) fn val_slot(&mut self, tab: TabId) -> Slot {
        if let Some(s) = self.st.tab(tab).val {
            return s;
        }
        let v = self.st.var();
        let sp = self.st.tab(tab).span;
        let s = self.st.fixed_slot(v, sp, "map values cannot be nil (assigning nil deletes the key)");
        self.st.tab_mut(tab).val = Some(s);
        s
    }

    pub(crate) fn field_slot(&mut self, tab: TabId, name: &str, span: Span) -> Option<Slot> {
        if let Some(s) = self.st.tab(tab).fields.get(name) {
            return Some(*s);
        }
        if self.st.tab(tab).closed {
            let h = type_hint(self.st.tab(tab));
            self.error(span, format!("field '{name}' does not exist on record type {h}"));
            return None;
        }
        let v = self.st.var();
        let s = self.st.slot(v);
        self.st.tab_mut(tab).fields.insert(name.to_string(), s);
        Some(s)
    }

    pub(crate) fn field_read(&mut self, tab: TabId, name: &str, span: Span) -> ETy {
        match self.field_slot(tab, name, span) {
            Some(s) => {
                self.info.field_refs.push((tab, name.to_string()));
                ETy { ty: s.ty, null: s.null, soft: Soft::Field((self.info.field_refs.len() - 1) as u32) }
            }
            None => self.fresh_result(),
        }
    }

    // Annotations

    pub fn type_slot(&mut self, te: &TypeExpr) -> Slot {
        match te {
            TypeExpr::Optional(inner) => {
                let t = self.type_ty(inner);
                // `any` already holds nil: no separate optional wrapper
                if matches!(self.st.node(t), TyNode::Any) {
                    return self.st.slot(t);
                }
                self.st.optional_slot(t, te.span())
            }
            TypeExpr::Nil(sp) => {
                let t = self.st.ty(TyNode::Nil);
                self.st.optional_slot(t, *sp)
            }
            _ => {
                let t = self.type_ty(te);
                if matches!(self.st.node(t), TyNode::Any) {
                    return self.st.slot(t);
                }
                self.st.fixed_slot(t, te.span(), "the annotated type is not optional")
            }
        }
    }

    pub(crate) fn type_ty(&mut self, te: &TypeExpr) -> TyId {
        match te {
            TypeExpr::Named(path, sp) => self.named_type(path, *sp),
            TypeExpr::Nil(_) => self.st.ty(TyNode::Nil),
            TypeExpr::Optional(inner) => {
                self.error(inner.span(), "optional type is not allowed in this position");
                self.st.var()
            }
            TypeExpr::Array(e, sp) => {
                let tab = self.st.new_tab(TKind::Array, *sp);
                let el = self.type_ty_nonopt(e, "arrays cannot contain nil");
                let s = self.st.fixed_slot(el, *sp, "arrays cannot contain nil (holes are unsupported)");
                self.st.tab_mut(tab).elem = Some(s);
                self.table_ty(tab)
            }
            TypeExpr::Map(k, v, sp) => {
                let tab = self.st.new_tab(TKind::Map, *sp);
                let kt = self.type_ty_nonopt(k, "map keys cannot be nil");
                let vt = self.type_ty_nonopt(v, "map values cannot be nil");
                let ks = self.st.fixed_slot(kt, *sp, "map keys cannot be nil");
                let vs = self.st.fixed_slot(vt, *sp, "map values cannot be nil");
                let t = self.st.tab_mut(tab);
                t.key = Some(ks);
                t.val = Some(vs);
                self.table_ty(tab)
            }
            TypeExpr::Record(fields, sp) => {
                let tab = self.st.new_tab(if fields.is_empty() { TKind::Unknown } else { TKind::Record }, *sp);
                for (n, t) in fields {
                    let s = self.type_slot(t);
                    self.st.tab_mut(tab).fields.insert(n.text.clone(), s);
                }
                self.st.tab_mut(tab).closed = !fields.is_empty();
                self.table_ty(tab)
            }
            TypeExpr::Func(ps, rs, _) => {
                let (params, vararg) = self.type_list(ps);
                let r = self.type_rets(rs);
                self.st.ty(TyNode::Func(Rc::new(FuncTy { params, rets: r, vararg })))
            }
            TypeExpr::Variadic(_, sp) => {
                self.error(*sp, "`...T` can only end a parameter or result type list");
                self.st.var()
            }
            TypeExpr::Applied(name, args, sp) => self.applied_type(name, args, *sp),
            TypeExpr::Union(members, sp) => self.union_type(members, *sp),
            TypeExpr::Unsupported(what, sp) => {
                self.error(*sp, format!("{what} are not supported in this version"));
                self.st.var()
            }
        }
    }

    /// Slots of a type list whose last element may be `...T` (returned apart).
    pub(crate) fn type_list(&mut self, ts: &[TypeExpr]) -> (Vec<Slot>, Option<Slot>) {
        let (fixed, tail) = match ts.last() {
            Some(TypeExpr::Variadic(t, _)) => (&ts[..ts.len() - 1], Some(&**t)),
            _ => (ts, None),
        };
        let slots = fixed.iter().map(|t| self.type_slot(t)).collect();
        (slots, tail.map(|t| self.type_slot(t)))
    }

    /// Result node of an annotated result list (`(T, ...U)` has a tail).
    pub(crate) fn type_rets(&mut self, rs: &[TypeExpr]) -> RetsId {
        let (fixed, tail) = self.type_list(rs);
        let r = self.st.new_rets(RetsNode::Known(fixed));
        if let Some(t) = tail {
            self.st.rets_tail.insert(r, t);
        }
        r
    }

    pub(crate) fn type_ty_nonopt(&mut self, te: &TypeExpr, what: &str) -> TyId {
        match te {
            TypeExpr::Optional(i) => {
                self.error(te.span(), format!("{what} (optional element types are unsupported)"));
                self.type_ty(i)
            }
            _ => self.type_ty(te),
        }
    }

    pub(crate) fn named_type(&mut self, path: &[String], sp: Span) -> TyId {
        if path.len() == 1 {
            match path[0].as_str() {
                "number" => return self.st.ty(TyNode::Num),
                "integer" => return self.st.ty(TyNode::Int),
                "string" => return self.st.ty(TyNode::Str),
                "boolean" => return self.st.ty(TyNode::Bool),
                // the dynamic type
                "any" => return self.st.ty(TyNode::Any),
                "unknown" => {
                    self.error(sp, "'unknown' is not supported: values need one static type (use 'any' for a dynamic value)");
                    return self.st.var();
                }
                _ => {}
            }
            if let Some(t) = self.tparam(&path[0]) {
                return t;
            }
            let key = (self.cur_file, path[0].clone());
            if self.dynamic.generic_aliases.contains_key(&key) {
                self.error(sp, format!("generic type '{}' needs type arguments", path[0]));
                return self.st.var();
            }
            if let Some((te, cached)) = self.aliases.get(&key).cloned() {
                if let Some(s) = cached {
                    return s.ty;
                }
                // Placeholder breaks recursion: recursive aliases resolve to themselves.
                let v = self.st.var();
                let placeholder = self.st.slot(v);
                self.aliases.get_mut(&key).unwrap().1 = Some(placeholder);
                // an alias body does not see the type parameters of the code that uses it
                let outer = std::mem::take(&mut self.dynamic.tparams);
                let t = self.type_ty(&te);
                self.dynamic.tparams = outer;
                if let TyNode::Table(tb) = self.st.node(t).clone() {
                    self.st.tab_mut(tb).hint = Some(path[0].clone());
                }
                self.unify(v, t, sp);
                return t;
            }
            self.error(sp, format!("unknown type '{}'", path[0]));
            return self.st.var();
        }
        // `alias.Type.Path` where alias = require("rust:crate")
        let key = (self.cur_file, path[0].clone());
        match self.rust_imports.get(&key).copied() {
            Some(root) => match self.native_type_annotation(root, &path[1..], sp) {
                Some(t) => t,
                None => {
                    let c = self.world.info(root.krate).package.clone();
                    self.error(sp, format!("crate '{c}' has no importable type '{}'", path[1..].join(".")));
                    self.st.var()
                }
            },
            None => {
                self.error(sp, format!("unknown type '{}' ('{}' is not a Rust import of this module)", path.join("."), path[0]));
                self.st.var()
            }
        }
    }

    // Program entry

    /// Checks all modules (dependencies first). `order` lists module indexes.
    pub fn check_program(&mut self, units: &[ModuleUnit], order: &[usize]) {
        self.info.module_value = vec![None; units.len()];
        self.units = units.iter().map(|u| (u.requires.clone(), u.rust_requires.clone())).collect();
        for u in units {
            self.find_builtin_aliases(&u.module.body);
        }

        self.prepare_coroutines(units);

        for unit in units {
            if matches!(unit.module.options.oracle_optimization, Some(1 | 2)) {
                self.info.rooted_constant_string_files.insert(unit.module.file);
            }
            let layout = crate::check_layout::analyze(&unit.module.body, self.res, unit.module.options);
            self.info.table_layouts.extend(layout.layouts);
            self.info.constant_strings.extend(layout.strings);
            self.info.unproven_table_layouts.extend(layout.unproven);
            self.info.next_key_sources.extend(crate::check_next_identity::sources(&unit.module.body, self.res));
        }

        self.prepare_source_metatables(units);
        self.prepare_runtime_tables(units);
        for u in units {
            self.info.local_attrs.extend(u.module.attrs.iter().map(|(k, v)| (*k, *v)));
        }
        for &mi in order {
            self.check_module(&units[mi], mi);
        }
        self.solve_pending();
        self.check_close_locals();
        self.finish();
        self.check_coroutine_boundaries();
    }

    /// `<close>` variables hold native objects (or nil); `<const>` variables are
    /// never assigned after their declaration.
    fn check_close_locals(&mut self) {
        let attrs: Vec<(NodeId, crate::ast::LocalAttr)> = self.info.local_attrs.iter().map(|(k, v)| (*k, *v)).collect();
        for (name, attr) in attrs {
            let sym = self.res.decl(name);
            let span = self.res.sym(sym).span;
            if self.res.sym(sym).assigned {
                let what = if attr == crate::ast::LocalAttr::Close { "close" } else { "const" };
                self.error(span, format!("attempt to assign to a <{what}> variable"));
            }
            if attr == crate::ast::LocalAttr::Close {
                let Some(slot) = self.info.sym_slot.get(&sym).copied() else { continue };
                if !matches!(self.st.node(slot.ty), TyNode::Native(_)) {
                    let s = self.show(slot.ty);
                    self.error(span, format!("a <close> variable must hold a native object (it is released when the scope exits), not a {s} value"));
                }
            }
        }
    }

    pub(crate) fn check_module(&mut self, u: &ModuleUnit, mi: usize) {
        self.cur_file = u.module.file;
        // Type aliases and Rust imports are module-scoped and order-independent.
        for st in &u.module.body.stats {
            match &st.kind {
                StatKind::TypeAlias(n, params, te) => {
                    let key = (self.cur_file, n.text.clone());
                    let twice = if params.is_empty() {
                        self.aliases.insert(key.clone(), (te.clone(), None)).is_some() || self.dynamic.generic_aliases.contains_key(&key)
                    } else {
                        let names: Vec<String> = params.iter().map(|p| p.text.clone()).collect();
                        self.dynamic.generic_aliases.insert(key.clone(), (names, te.clone())).is_some() || self.aliases.contains_key(&key)
                    };
                    if twice {
                        self.error(n.span, format!("type '{}' is defined twice", n.text));
                    }
                }
                StatKind::Local(names, exprs) => {
                    for (i, e) in exprs.iter().enumerate() {
                        if let Some(&c) = u.rust_requires.get(&e.id) {
                            if let Some((n, _)) = names.get(i) {
                                self.rust_imports.insert((self.cur_file, n.text.clone()), self.world.root(c));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        self.fns.push(FnCtx { id: u.pseudo_func, task: false, annotated: false, returns: Vec::new(), vararg: None, call_site: None, ret_nodes: Vec::new() });
        self.block(&u.module.body);
        let ctx = self.fns.pop().unwrap();
        let mut value: Option<ETy> = None;
        for (vals, span, _, pack) in &ctx.returns {
            if vals.len() > 1 || pack.is_some() {
                self.error(*span, "a module must return at most one value");
            }
            if let Some(v) = vals.first() {
                match value {
                    None => value = Some(*v),
                    Some(prev) => {
                        self.unify(v.ty, prev.ty, *span);
                    }
                }
            }
        }
        self.info.module_value[mi] = value;
    }

    // Statements

    pub(crate) fn push_frame(&mut self) {
        self.narrow.push(HashMap::new());
    }
    pub(crate) fn pop_frame(&mut self) {
        self.narrow.pop();
    }
    pub(crate) fn kill(&mut self, s: SymId) {
        for f in self.narrow.iter_mut() {
            f.remove(&s);
        }
    }
    pub(crate) fn add_facts(&mut self, facts: &[(SymId, Narrow)]) {
        let top = self.narrow.last_mut().unwrap();
        for (s, n) in facts {
            top.insert(*s, *n);
        }
    }
    pub(crate) fn lookup_narrow(&self, s: SymId) -> Option<Narrow> {
        let sym = self.res.sym(s);
        if sym.assigned_in_closure {
            return None;
        }
        if sym.assigned && sym.func != self.fns.last().unwrap().id {
            return None;
        }
        self.narrow.iter().rev().find_map(|f| f.get(&s).copied())
    }

    pub(crate) fn block(&mut self, b: &Block) {
        self.push_frame();
        for s in &b.stats {
            self.stat(s);
        }
        self.pop_frame();
    }

    pub(crate) fn sym_slot(&mut self, s: SymId) -> Slot {
        if let Some(sl) = self.info.sym_slot.get(&s) {
            return *sl;
        }
        let v = self.st.var();
        let sl = self.st.slot(v);
        self.info.sym_slot.insert(s, sl);
        sl
    }

    pub(crate) fn declare(&mut self, n: &Name, ann: Option<&TypeExpr>) -> Slot {
        let sym = self.res.decl(n.id);
        let slot = match ann {
            Some(t) => self.type_slot(t),
            None => {
                let v = self.st.var();
                self.st.slot(v)
            }
        };
        self.info.sym_slot.insert(sym, slot);
        self.kill(sym);
        slot
    }

    pub(crate) fn stat(&mut self, s: &Stat) {
        match &s.kind {
            StatKind::Local(..) if self.info.alias_decls.contains(&s.id) => {}
            StatKind::Local(names, exprs) => {
                // a table constructor initializing an annotated local boxes its `any` items
                for (i, (_, ann)) in names.iter().enumerate() {
                    if let (Some(ann), Some(x)) = (ann, exprs.get(i)) {
                        if matches!(x.kind, ExprKind::Table(_)) {
                            self.dynamic.table_ann.insert(x.id, ann.clone());
                        }
                    }
                }
                let vals = self.exprs_all(exprs, Some(names.len()));
                let is_pcall = exprs.len() == 1
                    && matches!(self.info.calls.get(&exprs[0].id), Some(CallKind::Builtin(BuiltinFn::Pcall)));
                for (i, (n, ann)) in names.iter().enumerate() {
                    let slot = self.declare(n, ann.as_ref());
                    match vals.get(i) {
                        Some(v) => {
                            // a value flowing into an `any` local is boxed
                            self.flow_node(exprs.get(i).map(|x| x.id), *v, slot, n.span);
                        }
                        None if exprs.is_empty() => {
                            self.late_init.insert(self.res.decl(n.id));
                        }
                        None => self.st.force(slot.null, n.span),
                    }
                }
                if is_pcall && names.len() >= 2 {
                    let (a, b) = (self.res.decl(names[0].0.id), self.res.decl(names[1].0.id));
                    if !self.res.sym(a).assigned && !self.res.sym(b).assigned {
                        self.pcall_pairs.insert(a, b);
                        // results the function never returns as nil are present when ok
                        let nonnull = self.info.pcall_nonnull.get(&exprs[0].id).cloned().unwrap_or_default();
                        let extras: Vec<SymId> = names
                            .iter()
                            .skip(2)
                            .enumerate()
                            .filter(|(i, _)| nonnull.get(*i).copied().unwrap_or(false))
                            .map(|(_, (n, _))| self.res.decl(n.id))
                            .filter(|s| !self.res.sym(*s).assigned)
                            .collect();
                        self.pcall_extras.insert(a, extras);
                    }
                }
            }
            StatKind::LocalFunction(n, f) => {
                let sym = self.res.decl(n.id);
                let ft = self.func_ty_skeleton(f);
                let slot = self.st.fixed_slot(ft, n.span, "functions are never nil");
                self.info.sym_slot.insert(sym, slot);
                if self.res.sym(sym).assigned && self.res.sym(sym).captured {
                    self.late_init.insert(sym);
                }
                self.check_func_body(f, ft);
            }
            StatKind::Function(target, f) => {
                // Ordinary records infer self from storage; classes infer it from calls.
                let is_method = f.params.first().map(|p| p.name.text == "self" && p.name.span == f.span).unwrap_or(false);
                let self_ty = match (&target.kind, is_method) {
                    (ExprKind::Field(obj, _), true) => {
                        let ty = self.expr(obj).ty;
                        // Luau 0.743: a class stores a method; its caller supplies the receiver.
                        if self.metatables.general || self.is_record_class(ty) { None } else { Some(ty) }
                    }
                    _ => None,
                };
                let ft = self.func_ty_skeleton(f);
                if let Some(st) = self_ty {
                    if let TyNode::Func(fty) = self.st.node(ft).clone() {
                        self.unify(fty.params[0].ty, st, f.span);
                    }
                }
                if self.metatables.general && is_method {
                    if let (ExprKind::Field(obj, _), TyNode::Func(function)) = (&target.kind, self.st.node(ft)) {
                        if let Some(owner) = self.info.expr.get(&obj.id) {
                            self.metatables.receivers.push((owner.ty, function.params[0].ty, f.span));
                        }
                    }
                }
                let v = self.val(ft);
                self.assign_to(target, v, target.span);
                self.check_func_body(f, ft);
            }
            StatKind::Assign(targets, exprs) => {
                let vals = self.exprs_all(exprs, Some(targets.len()));
                for (i, t) in targets.iter().enumerate() {
                    let v = match vals.get(i) {
                        Some(v) => *v,
                        None => self.nil(),
                    };
                    self.assign_to_node(t, v, t.span, exprs.get(i).filter(|_| vals.get(i).is_some()).map(|x| x.id));
                }
            }
            StatKind::Compound(op, target, rhs) => {
                let cur = self.expr(target);
                let r = self.expr(rhs);
                if self.is_any(cur.ty) || self.is_any(r.ty) {
                    self.error(s.span, format!("'{}=' on an 'any' value is not supported; write `x = x {} y` instead", op.symbol(), op.symbol()));
                    return;
                }
                let res = self.binary_value(*op, cur, r, s.span);
                self.assign_to(target, res, target.span);
            }
            StatKind::Call(e) => {
                self.expr_multi(e, Some(0));
            }
            StatKind::Do(b) => self.block(b),
            StatKind::While(c, b) => {
                self.kill_assigned(b);
                let ce = self.expr(c);
                self.test_value(c, ce);
                let (then_f, _) = self.cond_facts(c);
                self.push_frame();
                self.add_facts(&then_f);
                self.block(b);
                self.pop_frame();
            }
            StatKind::Repeat(b, c) => {
                self.kill_assigned(b);
                self.push_frame();
                for st in &b.stats {
                    self.stat(st);
                }
                let ce = self.expr(c);
                self.test_value(c, ce);
                self.pop_frame();
            }
            StatKind::If(arms, els) => {
                let mut else_facts_acc: Vec<(SymId, Narrow)> = Vec::new();
                let mut all_exit = true;
                self.push_frame();
                for (c, b) in arms {
                    let ce = self.expr(c);
                    self.test_value(c, ce);
                    let (t, f) = self.cond_facts(c);
                    self.push_frame();
                    self.add_facts(&t);
                    self.block(b);
                    self.pop_frame();
                    all_exit &= block_exits(b, self.res);
                    // later arms run only when this condition was false
                    self.add_facts(&f);
                    else_facts_acc.extend(f);
                }
                if let Some(b) = els {
                    self.block(b);
                }
                self.pop_frame();
                // `if not x then return end`: the rest of the block knows the else facts.
                if els.is_none() && all_exit {
                    let still: Vec<(SymId, Narrow)> = else_facts_acc;
                    self.add_facts(&still);
                }
            }
            StatKind::NumFor(v, a, b, c, body) => {
                for e in [Some(a), Some(b), c.as_ref()].into_iter().flatten() {
                    let x = self.expr(e);
                    let n = self.prim(TyNode::Num);
                    self.unify(x.ty, n, e.span);
                    self.need(x, e.span, "'for' bounds must be numbers");
                }
                self.kill_assigned(body);
                self.push_frame();
                let slot = self.declare(v, None);
                let n = self.prim(TyNode::Num);
                self.unify(slot.ty, n, v.span);
                self.block(body);
                self.pop_frame();
            }
            StatKind::GenFor(names, exprs, body) => {
                self.gen_for(s, names, exprs, body);
            }
            StatKind::Return(exprs) => {
                let self_tail = exprs.len() == 1 && self.is_self_call(&exprs[0]);
                let (vals, pack) = if self_tail {
                    // Self tail call: its results are exactly this function's results.
                    self.expr_multi(&exprs[0], Some(0));
                    (Vec::new(), None)
                } else if let Some(last) = exprs.last().filter(|l| self.is_pack(l)) {
                    // `return a, ...`: a run-time number of values
                    let vals: Vec<ETy> = exprs[..exprs.len() - 1].iter().map(|x| self.expr(x)).collect();
                    (vals, Some(self.pack_value(last)))
                } else {
                    self.allow_pack = true;
                    let vals = self.exprs_all(exprs, None);
                    let pack = exprs.last().and_then(|l| self.info.pack_calls.get(&l.id).copied());
                    (vals, pack)
                };
                let ctx = self.fns.last_mut().unwrap();
                ctx.returns.push((vals, s.span, self_tail, pack));
                ctx.ret_nodes.push(exprs.iter().map(|x| x.id).collect());
            }
            StatKind::Break | StatKind::Continue | StatKind::TypeAlias(..) => {}
        }
    }

    pub fn is_self_call_of(&self, e: &Expr, func: NodeId) -> bool {
        if let ExprKind::Call(f, _) = &e.kind {
            if let ExprKind::Name(n) = &f.kind {
                if let Some(Res::Local(s)) = self.res.res(n.id) {
                    if let Some(body) = self.res.sym(s).func_body {
                        return body == func && !self.res.sym(s).assigned;
                    }
                }
            }
        }
        false
    }

    pub(crate) fn is_self_call(&self, e: &Expr) -> bool {
        let ctx = self.fns.last().unwrap();
        !ctx.annotated && self.is_self_call_of(e, ctx.id)
    }

    pub(crate) fn kill_assigned(&mut self, b: &Block) {
        let mut set = BTreeSet::new();
        assigned_in_block(self.res, b, &mut set);
        for s in set {
            self.kill(s);
        }
    }

    pub(crate) fn assign_to(&mut self, t: &Expr, v: ETy, span: Span) {
        self.assign_to_node(t, v, span, None)
    }

    /// `node`: the expression the value comes from (boxed when the target is `any`).
    pub(crate) fn assign_to_node(&mut self, t: &Expr, v: ETy, span: Span, node: Option<NodeId>) {
        match &t.kind {
            ExprKind::Name(n) => {
                if let Some(Res::Local(sym)) = self.res.res(n.id) {
                    let slot = self.sym_slot(sym);
                    let e = self.of_slot(slot);
                    self.info.expr.insert(t.id, e);
                    self.flow_node(node, v, slot, span);
                    self.kill(sym);
                }
            }
            ExprKind::Field(obj, name) => {
                let o = self.expr(obj);
                self.need(o, obj.span, "attempt to index a nil value");
                let r = self.fresh_result();
                self.info.expr.insert(t.id, r);
                if let Some(n) = node {
                    self.dynamic.write_nodes.insert(t.id, n);
                }
                self.do_field(t.id, o, name.text.clone(), r, Some(v), name.span);
            }
            ExprKind::Index(obj, key) => {
                let o = self.expr(obj);
                self.need(o, obj.span, "attempt to index a nil value");
                let k = self.expr(key);
                self.need(k, key.span, "table index is nil");
                let lit = if self.metatables.general { literal_record_key(key) } else { match &key.kind {
                    ExprKind::Str(s) => String::from_utf8(s.clone()).ok(),
                    _ => None,
                } };
                let r = self.fresh_result();
                self.info.expr.insert(t.id, r);
                if let Some(n) = node {
                    self.dynamic.write_nodes.insert(t.id, n);
                }
                self.do_index(t.id, o, k, lit, r, Some(v), t.span);
            }
            _ => self.error(span, "cannot assign to this expression"),
        }
    }

    pub(crate) fn gen_for(&mut self, s: &Stat, names: &[Name], exprs: &[Expr], body: &Block) {
        let (kind, arg) = match exprs {
            [e] => match &e.kind {
                ExprKind::Call(f, args) if args.len() == 1 => match is_lib(f, self.res) {
                    Some(Builtin::Ipairs) => (Some(true), &args[0]),
                    Some(Builtin::Pairs) => (Some(false), &args[0]),
                    _ => (None, e),
                },
                _ => (None, e),
            },
            _ => (None, &exprs[0]),
        };
        let Some(is_ipairs) = kind else {
            if let [e] = exprs {
                if let Some(operands) = self.gmatch_operands(e) {
                    return self.gmatch_for(s, names, &operands, body, e.span);
                }
            }
            return self.general_for(s, names, exprs, body);
        };
        if names.len() > 2 {
            self.error(names[2].span, "pairs/ipairs loops bind at most two variables");
        }
        let t = self.expr(arg);
        self.info.array_loop_tables.insert(s.id, t);
        self.need(t, arg.span, "cannot iterate over nil");
        self.info.packs.restricted.push((t.ty, arg.span, "iteration over a nil-preserving array is not supported"));
        self.kill_assigned(body);
        self.push_frame();
        let k = self.declare(&names[0], None);
        let v = match names.get(1) {
            Some(n) => self.declare(n, None),
            None => {
                let ty = self.st.var();
                self.st.slot(ty)
            }
        };
        if is_ipairs {
            if matches!(self.st.node(t.ty), TyNode::Table(tab) if self.st.tab(*tab).runtime) {
                self.runtime_pairs(s.id, t, k, v, crate::check_iteration::IterationMode::Ipairs, s.span);
                self.block(body);
                self.pop_frame();
                return;
            }
            let tab = self.new_table_var(arg.span);
            self.unify(t.ty, tab.0, arg.span);
            self.ensure_kind(tab.1, TKind::Array, arg.span);
            let n = self.prim(TyNode::Num);
            self.unify(k.ty, n, names[0].span);
            let el = self.elem_slot(tab.1);
            self.unify(v.ty, el.ty, s.span);
            self.info.fors.insert(s.id, ForKind::Ipairs);
        } else {
            self.try_or_defer(Op::Pairs { node: s.id, t, k, v, span: arg.span });
        }
        self.block(body);
        self.pop_frame();
    }

    /// The subject and pattern of `string.gmatch(s, p)` / `s:gmatch(p)`.
    fn gmatch_operands<'e>(&self, e: &'e Expr) -> Option<Vec<&'e Expr>> {
        match &e.kind {
            ExprKind::Call(f, args) => match &f.kind {
                ExprKind::Field(lib, name) if name.text == "gmatch" && is_lib(lib, self.res) == Some(Builtin::StringLib) => Some(args.iter().collect()),
                _ => None,
            },
            ExprKind::Method(o, name, args) if name.text == "gmatch" => Some(std::iter::once(&**o).chain(args.iter()).collect()),
            _ => None,
        }
    }

    pub(crate) fn new_table_var(&mut self, span: Span) -> (TyId, TabId) {
        let tab = self.st.new_tab(TKind::Unknown, span);
        (self.table_ty(tab), tab)
    }

    // Functions

    pub(crate) fn func_ty_skeleton(&mut self, f: &FuncBody) -> TyId {
        // `function f<T>`: T is a fresh inference variable per checked copy
        let generic = self.push_generics(f);
        let params: Vec<Slot> = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let sym = self.res.decl(p.name.id);
                let slot = if let Some(slot) = self.runtime_parameter(f, i) { slot } else { match &p.ty {
                    Some(t) => self.type_slot(t),
                    None if i == 0 && p.name.text == "self" && p.name.span == f.span => {
                        let v = self.st.var();
                        self.st.fixed_slot(v, p.name.span, "'self' is never nil")
                    }
                    None if self.info.runtime_functions.contains(&f.id) => {
                        let v = self.st.ty(TyNode::Any);
                        self.st.slot(v)
                    }
                    None => {
                        let v = self.st.var();
                        self.st.slot(v)
                    }
                } };
                self.info.sym_slot.insert(sym, slot);
                slot
            })
            .collect();
        let rets = match &f.rets {
            Some(rs) => self.type_rets(rs),
            None => self.st.new_rets(RetsNode::Unknown),
        };
        let vararg = f.vararg.as_ref().map(|(_, t)| match t {
            Some(t) => self.type_slot(t),
            None if self.info.runtime_functions.contains(&f.id) => {
                let any = self.st.ty(TyNode::Any);
                self.st.slot(any)
            }
            None => {
                let v = self.st.var();
                self.st.slot(v)
            }
        });
        let ty = self.st.ty(TyNode::Func(Rc::new(FuncTy { params, rets, vararg })));
        self.info.funcs.insert(f.id, ty);
        if generic {
            self.dynamic.tparams.pop();
        }
        ty
    }

    pub(crate) fn check_func_body(&mut self, f: &FuncBody, ft: TyId) {
        let generic = self.enter_generics(f);
        self.check_func_body_inner(f, ft);
        if generic {
            self.dynamic.tparams.pop();
        }
    }

    fn check_func_body_inner(&mut self, f: &FuncBody, ft: TyId) {
        let TyNode::Func(fty) = self.st.node(ft).clone() else { unreachable!() };
        let task = std::mem::take(&mut self.next_fn_is_task);
        self.fns.push(FnCtx { id: f.id, task, annotated: f.rets.is_some(), returns: Vec::new(), vararg: fty.vararg, call_site: f.call_site, ret_nodes: Vec::new() });
        self.push_frame();
        for st in &f.body.stats {
            self.stat(st);
        }
        self.pop_frame();
        let ctx = self.fns.pop().unwrap();
        let falls = !block_exits(&f.body, self.res);
        if falls {
            self.info.falls_through.insert(f.id);
        }
        // Result arity: annotated, fixed earlier by unification, or the max count.
        // A function with a pack return (`return ...`) has the smallest fixed
        // count of its returns, then a tail of run-time-counted values.
        let has_pack = ctx.returns.iter().any(|r| !r.2 && r.3.is_some());
        let known = self.st.rets_known(fty.rets).cloned();
        let (slots, tail) = match known {
            Some(k) => {
                let tail = self.st.rets_tail(fty.rets);
                if tail.is_none() {
                    for (_, span, _, pack) in &ctx.returns {
                        if pack.is_some() {
                            self.error(*span, "this returns a variable number of values (`...`), but the function's result type has a fixed number (annotate it as `(..., ...T)`)");
                        }
                    }
                }
                (k, tail)
            }
            None => {
                let counts = ctx.returns.iter().filter(|r| !r.2).map(|r| r.0.len());
                let n = if has_pack { counts.min().unwrap_or(0) } else { counts.max().unwrap_or(0) };
                let v: Vec<Slot> = (0..n)
                    .map(|_| {
                        let t = self.st.var();
                        self.st.slot(t)
                    })
                    .collect();
                let r = self.st.rets_root(fty.rets);
                self.st.rets[r as usize] = RetsNode::Known(v.clone());
                let tail = has_pack.then(|| {
                    let t = self.st.var();
                    let s = self.st.slot(t);
                    self.st.rets_tail.insert(r, s);
                    s
                });
                (v, tail)
            }
        };
        for (ri, (vals, span, self_tail, pack)) in ctx.returns.iter().enumerate() {
            if *self_tail {
                continue;
            }
            if vals.len() > slots.len() && tail.is_none() {
                self.error(*span, format!("function returns {} values but its type allows {}", vals.len(), slots.len()));
            }
            // a pack against a fixed result type was reported above
            if pack.is_some() && tail.is_none() {
                continue;
            }
            for (i, sl) in slots.iter().enumerate() {
                match (vals.get(i), pack) {
                    (Some(v), _) => {
                        let node = ctx.ret_nodes.get(ri).and_then(|n| n.get(i)).copied();
                        self.flow_node(node, *v, *sl, *span);
                    }
                    // a fixed result taken from the pack: nil when it runs out
                    (None, Some(p)) => {
                        let p = ETy { null: self.st.null_true, ..*p };
                        self.flow(p, *sl, *span);
                    }
                    (None, None) => self.st.force(sl.null, *span),
                }
            }
            if let Some(t) = tail {
                for v in vals.iter().skip(slots.len()) {
                    self.flow(*v, t, *span);
                }
                if let Some(p) = pack {
                    self.flow(*p, t, *span);
                }
            }
        }
        if falls {
            for sl in &slots {
                self.st.force(sl.null, f.span);
            }
        }
    }

    // Expressions

    pub(crate) fn record(&mut self, e: &Expr, t: ETy) -> ETy {
        self.info.expr.insert(e.id, t);
        t
    }

    /// Single-value expression.
    pub fn expr(&mut self, e: &Expr) -> ETy {
        match &e.kind {
            ExprKind::Call(..) | ExprKind::Method(..) => {
                let v = self.expr_multi(e, Some(1));
                let t = v[0];
                self.record(e, t)
            }
            _ => {
                let t = self.expr_inner(e);
                self.record(e, t)
            }
        }
    }

    /// Expression list with Lua adjustment: every expression but the last yields one
    /// value; a trailing call expands to all its results (or the remaining `want`).
    pub(crate) fn exprs_all(&mut self, es: &[Expr], want: Option<usize>) -> Vec<ETy> {
        let allow_pack = std::mem::take(&mut self.allow_pack);
        let mut out = Vec::new();
        for (i, e) in es.iter().enumerate() {
            let last = i + 1 == es.len();
            if last && matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..)) {
                let rest = want.map(|w| w.saturating_sub(out.len()));
                let v = self.expr_multi(e, rest);
                out.extend(v);
                // a call returning a run-time number of values
                if want.is_none() && !allow_pack && self.info.pack_calls.contains_key(&e.id) {
                    self.error(e.span, PACK_CALL_MSG);
                }
            } else if last && matches!(e.kind, ExprKind::Vararg) {
                // `...` adjusted to the values still wanted (nil when it runs out)
                let el = self.va_elem();
                self.record(e, el);
                match want {
                    Some(w) => out.extend(std::iter::repeat(el).take(w.saturating_sub(out.len()))),
                    None => {
                        self.error(e.span, PACK_MSG);
                        let v = self.va_pack();
                        out.push(v);
                    }
                }
            } else {
                out.push(self.expr(e));
            }
        }
        out
    }

    /// Call with `want` results (`None`: all results; arity must be known).
    pub(crate) fn expr_multi(&mut self, e: &Expr, want: Option<usize>) -> Vec<ETy> {
        let r = match &e.kind {
            ExprKind::Call(f, args) => self.call(e, f, args, want),
            ExprKind::Method(o, name, args) => self.method_call(e, o, name, args, want),
            _ => vec![self.expr(e)],
        };
        let first = match r.first() {
            Some(f) => *f,
            None => self.nil(),
        };
        self.info.expr.insert(e.id, first);
        r
    }

    pub(crate) fn expr_inner(&mut self, e: &Expr) -> ETy {
        match &e.kind {
            ExprKind::Nil => self.nil(),
            ExprKind::Bool(_) => self.bool_(),
            ExprKind::Number(n) if n.fract() == 0.0 && n.abs() <= 9007199254740992.0 => {
                // an integral literal is a number unless the program uses it as an integer
                let v = self.st.ty(TyNode::NumVar);
                self.val(v)
            }
            ExprKind::Number(_) => self.num(),
            ExprKind::Int(_) => {
                let t = self.prim(TyNode::Int);
                self.val(t)
            }
            ExprKind::Str(_) => self.str_(),
            ExprKind::Vararg => self.va_elem(),
            ExprKind::Interp(parts) => {
                for p in parts {
                    if let InterpPart::Expr(x) = p {
                        self.expr(x);
                    }
                }
                self.str_()
            }
            ExprKind::Name(n) => self.name(e, n),
            ExprKind::Paren(x) => self.expr(x),
            ExprKind::Cast(x, te) => self.cast_expr(e, x, te),
            ExprKind::Function(f) => {
                let ft = self.func_ty_skeleton(f);
                self.check_func_body(f, ft);
                self.val(ft)
            }
            ExprKind::Table(items) => self.table(e, items),
            ExprKind::Field(obj, name) => {
                if let Some(b) = is_lib(obj, self.res) {
                    return self.lib_value(e, b, &name.text, name.span);
                }
                let o = self.expr(obj);
                self.need(o, obj.span, "attempt to index a nil value");
                let r = self.deferred_result();
                self.do_field(e.id, o, name.text.clone(), r, None, name.span);
                r
            }
            ExprKind::Index(obj, key) => {
                let o = self.expr(obj);
                self.need(o, obj.span, "attempt to index a nil value");
                let k = self.expr(key);
                self.need(k, key.span, "table index is nil");
                let lit = if self.metatables.general { literal_record_key(key) } else { match &key.kind {
                    ExprKind::Str(s) => String::from_utf8(s.clone()).ok(),
                    _ => None,
                } };
                let r = self.deferred_result();
                self.do_index(e.id, o, k, lit, r, None, e.span);
                r
            }
            ExprKind::Binary(op, a, b) => self.binary(e, *op, a, b),
            ExprKind::Unary(op, a) => {
                let x = self.expr(a);
                match op {
                    UnOp::Neg if self.is_any(x.ty) || self.runtime_type(x.ty) => {
                        // unary minus on an `any` value is decided at run time
                        self.info.dynamic.dyn_neg.insert(e.id);
                        if self.runtime_type(x.ty) { self.runtime_box(a, x); }
                        self.any_val()
                    }
                    UnOp::Neg => {
                        self.need(x, a.span, "attempt to perform arithmetic on a nil value");
                        let r = self.st.var();
                        self.try_or_defer(Op::Arith { op: None, x, y: x, r, span: a.span });
                        self.val(r)
                    }
                    UnOp::Not => {
                        self.test_value(a, x);
                        self.bool_()
                    }
                    UnOp::Len => {
                        self.need(x, a.span, "attempt to get length of a nil value");
                        self.try_or_defer(Op::Len { node: e.id, e: x, span: a.span });
                        self.num()
                    }
                }
            }
            ExprKind::IfElse(c, a, b) => {
                let ce = self.expr(c);
                self.test_value(c, ce);
                let (t, f) = self.cond_facts(c);
                self.push_frame();
                self.add_facts(&t);
                let x = self.expr(a);
                self.pop_frame();
                self.push_frame();
                self.add_facts(&f);
                let y = self.expr(b);
                self.pop_frame();
                self.unify(x.ty, y.ty, b.span);
                let r = self.fresh_result();
                self.unify(r.ty, x.ty, e.span);
                self.st.edge(x.null, r.null, e.span);
                self.st.edge(y.null, r.null, e.span);
                // soft branches become optional values
                if x.soft != Soft::No {
                    self.st.force(r.null, a.span);
                }
                if y.soft != Soft::No {
                    self.st.force(r.null, b.span);
                }
                r
            }
            ExprKind::Call(..) | ExprKind::Method(..) => unreachable!(),
        }
    }

    pub(crate) fn name(&mut self, e: &Expr, n: &Name) -> ETy {
        match self.res.res(n.id) {
            Some(Res::Local(sym)) if self.info.builtin_aliases.contains_key(&sym) => {
                let r = self.info.builtin_aliases[&sym].clone();
                self.builtin_value(e, r, n.span)
            }
            Some(Res::Local(sym)) => {
                let slot = self.sym_slot(sym);
                match self.lookup_narrow(sym) {
                    Some(Narrow::NonNil) => {
                        self.info.narrowed.insert(e.id, Narrow::NonNil);
                        self.val(slot.ty)
                    }
                    Some(Narrow::Is(tag)) if self.is_any(slot.ty) => {
                        self.info.dynamic.unboxed.insert(e.id, tag);
                        self.narrowed_any(tag)
                    }
                    Some(Narrow::Is(_)) => self.of_slot(slot),
                    Some(k @ (Narrow::PcallOk | Narrow::PcallErr)) => {
                        if let TyNode::Pcall(inner) = self.st.node(slot.ty).clone() {
                            self.info.narrowed.insert(e.id, k);
                            if k == Narrow::PcallOk {
                                self.of_slot(inner)
                            } else {
                                self.str_()
                            }
                        } else {
                            self.of_slot(slot)
                        }
                    }
                    None => {
                        let mut v = self.of_slot(slot);
                        if self.late_init.contains(&sym) {
                            v.soft = Soft::Yes;
                        }
                        v
                    }
                }
            }
            Some(Res::Builtin(Builtin::Arg)) => {
                let tab = self.st.new_tab(TKind::Array, n.span);
                let s = self.prim(TyNode::Str);
                let sl = self.st.fixed_slot(s, n.span, "arrays cannot contain nil");
                self.st.tab_mut(tab).elem = Some(sl);
                self.info.access.insert(e.id, Access::Arg);
                let t = self.table_ty(tab);
                self.val(t)
            }
            Some(Res::Builtin(b)) => match self.builtin_ref(e) {
                Some(r) => self.builtin_value(e, r, n.span),
                None => {
                    self.error(n.span, format!("library '{}' cannot be used as a value (use its functions, e.g. {}.insert)", n.text, n.text));
                    let _ = b;
                    self.fresh_result()
                }
            },
            None => self.fresh_result(),
        }
    }

    pub(crate) fn table(&mut self, e: &Expr, items: &[TableItem]) -> ETy {
        if self.call_array_candidate(items) {
            return self.call_array(e, items);
        }
        if self.info.runtime_tables.constructors.contains(&e.id) {
            return self.runtime_constructor(e, items);
        }
        let (ty, tab) = self.new_table_var(e.span);
        let has_pos = items.iter().any(|i| matches!(i, TableItem::Pos(_)));
        let has_named = items.iter().any(|i| matches!(i, TableItem::Named(..)));
        let has_keyed = items.iter().any(|i| matches!(i, TableItem::Keyed(..)));
        // Preserve map inference outside reserved record metadata literals.
        let record_keys = self.metatables.general && !has_pos && items.iter().any(|i| {
            matches!(i, TableItem::Keyed(k, _) if literal_record_key(k).as_deref() == Some("__index"))
        }) && items.iter().all(|i| match i {
            TableItem::Named(..) => true,
            TableItem::Keyed(k, _) => literal_record_key(k).is_some(),
            _ => false,
        });
        let has_keyed = has_keyed && !record_keys;
        if [has_pos, has_named, has_keyed].iter().filter(|x| **x).count() > 1 {
            self.error(e.span, "mixed table constructors (array items with named or keyed fields) are unsupported");
            for it in items {
                match it {
                    TableItem::Pos(x) | TableItem::Named(_, x) => {
                        self.expr(x);
                    }
                    TableItem::Keyed(k, x) => {
                        self.expr(k);
                        self.expr(x);
                    }
                }
            }
            return self.fresh_result();
        }
        let mut ctor = Vec::new();
        let mut constructor_keys = Vec::new();
        // items of a `{any}` array / an `any` field of the annotated local are boxed
        let ex = self.table_expectation(e.id);
        for (i, it) in items.iter().enumerate() {
            match it {
                TableItem::Pos(x) => {
                    self.ensure_kind(tab, TKind::Array, e.span);
                    let el = self.elem_slot(tab);
                    if ex.elem_any {
                        let any = self.st.ty(TyNode::Any);
                        self.unify(el.ty, any, x.span);
                    }
                    let vals = if i + 1 == items.len() && self.is_pack(x) {
                        vec![self.pack_value(x)]
                    } else if i + 1 == items.len() {
                        self.allow_pack = true;
                        let mut v = self.exprs_all(std::slice::from_ref(x), None);
                        if let Some(t) = self.info.pack_calls.get(&x.id).copied() {
                            v.push(t);
                        }
                        v
                    } else {
                        vec![self.expr(x)]
                    };
                    for (k, v) in vals.into_iter().enumerate() {
                        self.flow_node(Some(x.id).filter(|_| k == 0), v, el, x.span);
                    }
                }
                TableItem::Named(n, x) => {
                    self.ensure_kind(tab, TKind::Record, e.span);
                    let v = self.expr(x);
                    if ctor.contains(&n.text) {
                        self.error(n.span, format!("duplicate field '{}' in table constructor", n.text));
                    }
                    ctor.push(n.text.clone());
                    if let Some(sl) = self.field_slot(tab, &n.text, n.span) {
                        if ex.any_fields.contains(&n.text) {
                            let any = self.st.ty(TyNode::Any);
                            self.unify(sl.ty, any, x.span);
                        }
                        self.flow_node(Some(x.id), v, sl, x.span);
                    }
                }
                TableItem::Keyed(k, x) if record_keys => {
                    self.ensure_kind(tab, TKind::Record, e.span);
                    self.expr(k);
                    let v = self.expr(x);
                    if let Some(name) = literal_record_key(k) {
                        if ctor.contains(&name) { self.error(k.span, format!("duplicate field '{name}' in table constructor")); }
                        ctor.push(name.clone());
                        self.info.record_keys.insert(k.id, name.clone());
                        if let Some(slot) = self.field_slot(tab, &name, k.span) { self.flow(v, slot, x.span); }
                    }
                }
                TableItem::Keyed(k, x) => {
                    self.ensure_kind(tab, TKind::Map, e.span);
                    let kv = self.expr(k);
                    constructor_keys.push((kv.ty, k.span));
                    self.need(kv, k.span, "table index is nil");
                    let v = self.expr(x);
                    if self.metatables.general && literal_record_key(k).as_deref() == Some("__index") {
                        self.metatables.index_writes.push((v, k.span));
                    }
                    let ks = self.constructor_map_key(tab, kv, ex.key_any, k.span);
                    let vs = self.val_slot(tab);
                    if ex.val_any {
                        let any = self.st.ty(TyNode::Any);
                        self.unify(vs.ty, any, x.span);
                    }
                    if !self.is_any(ks.ty) { self.flow(kv, ks, k.span); }
                    self.flow_node(Some(x.id), v, vs, x.span);
                }
            }
        }
        if self.st.tab(tab).key.is_some_and(|key| self.is_any(key.ty)) {
            for (key, span) in constructor_keys { self.boxable(key, span); }
        }
        self.st.tab_mut(tab).ctors.push(ctor);
        self.val(ty)
    }

    pub(crate) fn lib_value(&mut self, e: &Expr, b: Builtin, name: &str, span: Span) -> ETy {
        match (b, name) {
            (Builtin::Math, "pi") => {
                self.info.access.insert(e.id, Access::MathPi);
                self.num()
            }
            (Builtin::Math, "huge") => {
                self.info.access.insert(e.id, Access::MathHuge);
                self.num()
            }
            _ => self.builtin_value(e, (b, Some(name.to_string())), span),
        }
    }

    // Operators

    pub(crate) fn binary(&mut self, e: &Expr, op: BinOp, a: &Expr, b: &Expr) -> ETy {
        match op {
            BinOp::And | BinOp::Or => {
                let x = self.expr(a);
                self.test_value(a, x);
                let (t, f) = self.cond_facts(a);
                self.push_frame();
                self.add_facts(if op == BinOp::And { &t } else { &f });
                let y = self.expr(b);
                self.pop_frame();
                let site = self.logic_site(a, b, x);
                let r = self.fresh_result();
                self.try_or_defer(Op::Logic { node: e.id, and: op == BinOp::And, a: x, b: y, result: r, span: e.span, site });
                r
            }
            BinOp::Eq | BinOp::Ne => {
                let x = self.expr(a);
                let y = self.expr(b);
                if let Some(r) = self.dyn_binary(e, op, a, b, x, y) {
                    return r;
                }
                let a_nil = matches!(a.kind, ExprKind::Nil);
                let b_nil = matches!(b.kind, ExprKind::Nil);
                if b_nil {
                    self.test_nil(a);
                } else if a_nil {
                    self.test_nil(b);
                } else {
                    self.unify(x.ty, y.ty, e.span);
                }
                self.bool_()
            }
            _ => {
                let x = self.expr(a);
                let y = self.expr(b);
                if let Some(r) = self.dyn_binary(e, op, a, b, x, y) {
                    return r;
                }
                self.binary_value(op, x, y, e.span)
            }
        }
    }

    pub(crate) fn binary_value(&mut self, op: BinOp, x: ETy, y: ETy, span: Span) -> ETy {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::IDiv | BinOp::Mod | BinOp::Pow => {
                self.need(x, span, "attempt to perform arithmetic on a nil value");
                self.need(y, span, "attempt to perform arithmetic on a nil value");
                let r = self.st.var();
                self.try_or_defer(Op::Arith { op: Some(op), x, y, r, span });
                self.val(r)
            }
            BinOp::Concat => {
                self.need(x, span, "attempt to concatenate a nil value");
                self.need(y, span, "attempt to concatenate a nil value");
                self.try_or_defer(Op::NumOrStr { e: x, default_str: true, span, what: "concatenate" });
                self.try_or_defer(Op::NumOrStr { e: y, default_str: true, span, what: "concatenate" });
                self.str_()
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.unify(x.ty, y.ty, span);
                self.need(x, span, "attempt to compare a nil value");
                self.need(y, span, "attempt to compare a nil value");
                self.try_or_defer(Op::NumOrStr { e: x, default_str: false, span, what: "compare" });
                self.bool_()
            }
            _ => unreachable!(),
        }
    }

    /// The program tests a value for truthiness: a non-boolean local/field becomes optional.
    pub(crate) fn test_value(&mut self, e: &Expr, v: ETy) {
        if let Some(null) = self.test_target(e) {
            self.try_or_defer(Op::Test { ty: v.ty, null });
        }
    }

    pub(crate) fn test_nil(&mut self, e: &Expr) {
        // an `any` value holds nil itself
        if self.info.expr.get(&e.id).is_some_and(|t| self.is_any(t.ty)) {
            return;
        }
        if let Some(null) = self.test_target(e) {
            self.st.force(null, e.span);
        }
    }

    pub(crate) fn test_target(&mut self, e: &Expr) -> Option<NullId> {
        match &e.kind {
            ExprKind::Name(n) => match self.res.res(n.id) {
                Some(Res::Local(s)) => Some(self.sym_slot(s).null),
                _ => None,
            },
            ExprKind::Field(..) => {
                let t = self.info.expr.get(&e.id)?;
                let mut soft = t.soft;
                if let Soft::Deferred(d) = soft {
                    soft = self.info.soft_deferred[d as usize].unwrap_or(Soft::No);
                }
                match soft {
                    Soft::Field(fid) => {
                        let (tab, name) = self.info.field_refs[fid as usize].clone();
                        self.st.tab(tab).fields.get(&name).map(|s| s.null)
                    }
                    _ => None,
                }
            }
            ExprKind::Paren(x) => self.test_target(x),
            _ => None,
        }
    }

    /// Facts true when `e` is truthy / falsy.
    pub(crate) fn cond_facts(&self, e: &Expr) -> (Vec<(SymId, Narrow)>, Vec<(SymId, Narrow)>) {
        let local = |x: &Expr| -> Option<SymId> {
            if let ExprKind::Name(n) = &x.kind {
                if let Some(Res::Local(s)) = self.res.res(n.id) {
                    return Some(s);
                }
            }
            None
        };
        match &e.kind {
            ExprKind::Name(_) => match local(e) {
                Some(s) => {
                    if let Some(&partner) = self.pcall_pairs.get(&s) {
                        let mut t = vec![(partner, Narrow::PcallOk)];
                        for x in self.pcall_extras.get(&s).cloned().unwrap_or_default() {
                            t.push((x, Narrow::NonNil));
                        }
                        (t, vec![(partner, Narrow::PcallErr)])
                    } else {
                        (vec![(s, Narrow::NonNil)], vec![])
                    }
                }
                None => (vec![], vec![]),
            },
            ExprKind::Paren(x) => self.cond_facts(x),
            ExprKind::Unary(UnOp::Not, x) => {
                let (t, f) = self.cond_facts(x);
                (f, t)
            }
            // `type(x) == "number"`: `x` is a number in the branch that proves it
            ExprKind::Binary(op @ (BinOp::Eq | BinOp::Ne), a, b) if self.type_test(a, b).is_some() => {
                let (s, tag) = self.type_test(a, b).unwrap_or_else(|| unreachable!());
                let fact = vec![(s, Narrow::Is(tag))];
                if *op == BinOp::Eq {
                    (fact, vec![])
                } else {
                    (vec![], fact)
                }
            }
            ExprKind::Binary(op @ (BinOp::Eq | BinOp::Ne), a, b) => {
                let target = if matches!(b.kind, ExprKind::Nil) {
                    local(a)
                } else if matches!(a.kind, ExprKind::Nil) {
                    local(b)
                } else {
                    None
                };
                match target {
                    Some(s) => {
                        let fact = vec![(s, Narrow::NonNil)];
                        if *op == BinOp::Ne {
                            (fact, vec![])
                        } else {
                            (vec![], fact)
                        }
                    }
                    None => (vec![], vec![]),
                }
            }
            ExprKind::Binary(BinOp::And, a, b) => {
                let (mut t, _) = self.cond_facts(a);
                t.extend(self.cond_facts(b).0);
                (t, vec![])
            }
            ExprKind::Binary(BinOp::Or, a, b) => {
                let (_, mut f) = self.cond_facts(a);
                f.extend(self.cond_facts(b).1);
                (vec![], f)
            }
            _ => (vec![], vec![]),
        }
    }

    // Deferred operation machinery

    pub(crate) fn try_or_defer(&mut self, op: Op) {
        if !self.attempt(&op) {
            self.pending.push(op);
        }
    }

    pub(crate) fn solve_pending(&mut self) {
        let mut rounds = 0;
        loop {
            // Normal passes until nothing changes.
            loop {
                let ops = std::mem::take(&mut self.pending);
                let mut any = false;
                for op in ops {
                    if self.attempt(&op) {
                        any = true;
                    } else {
                        self.pending.push(op);
                    }
                }
                any |= self.solve_record_reads();
                if !any && self.metatables.general {
                    any |= self.finish_general_record_receivers();
                }
                if !any {
                    break;
                }
            }
            if self.pending.is_empty() || rounds > 10_000 {
                break;
            }
            // Apply one default (comparison operands become numbers, concatenation
            // operands strings, unknown function values take the shape of their call,
            // unknown tables iterated with pairs become maps), then resume solving.
            rounds += 1;
            let ops = std::mem::take(&mut self.pending);
            let mut any = false;
            for op in ops {
                if !any {
                    self.defaults_round = true;
                    let ok = self.attempt(&op);
                    self.defaults_round = false;
                    if ok {
                        any = true;
                        continue;
                    }
                }
                self.pending.push(op);
            }
            if !any {
                // lowest priority: integral literals and arithmetic on them become numbers
                let ops = std::mem::take(&mut self.pending);
                self.defaults_round = true;
                self.literal_defaults = true;
                for op in ops {
                    if matches!(op, Op::Arith { .. }) && self.attempt(&op) {
                        any = true;
                        continue;
                    }
                    self.pending.push(op);
                }
                self.defaults_round = false;
                self.literal_defaults = false;
            }
            if !any {
                break;
            }
        }
        for op in std::mem::take(&mut self.pending) {
            let (span, what) = match &op {
                Op::FlowAny { span, .. } => (*span, "the value converted to any"),
                Op::RecordParent { span, .. } | Op::RecordMetatable { span, .. } => (*span, "the record types passed to setmetatable"),
                Op::Call { span, .. } => (*span, "the called value's type"),
                Op::Field { span, .. } | Op::Index { span, .. } => (*span, "the indexed value's type"),
                Op::Method { span, .. } => (*span, "the receiver's type"),
                Op::Logic { span, .. } => (*span, "the operand types"),
                Op::Len { span, .. } => (*span, "the operand type of '#'"),
                Op::NumOrStr { span, .. } => (*span, "the operand type"),
                Op::Pairs { span, .. } => (*span, "the iterated table's type"),
                Op::NativeFor { span, .. } => (*span, "the iterated value's type"),
                Op::Next { span, .. } => (*span, "the table passed to next"),
                Op::Clear { span, .. } => (*span, "the table passed to table.clear"),
                Op::Arith { span, .. } => (*span, "the operand types"),
                Op::IntParam { .. } => continue,
                Op::TraitImpl { span, .. } => (*span, "the type of the value passed as a trait implementation"),
                Op::PcallRets { span, .. } => {
                    self.error(*span, "cannot determine the results of this function; annotate its return type");
                    continue;
                }
                Op::BuiltinValue { span, r, .. } => {
                    let n = match &r.1 {
                        Some(f) => f.clone(),
                        None => format!("{:?}", r.0).to_lowercase(),
                    };
                    self.error(*span, format!("cannot infer the signature of builtin '{n}' used as a value; annotate it (e.g. `local f: (string) -> () = print`)"));
                    continue;
                }
                Op::Test { .. } => continue,
            };
            self.error(span, format!("cannot infer {what} here; add a type annotation"));
        }
        self.finish_record_reads();
    }

    pub(crate) fn attempt(&mut self, op: &Op) -> bool {
        match op.clone() {
            Op::FlowAny { node, value, dst, span } => self.attempt_any_flow(node, value, dst, span),
            Op::Next { table, key, results, span } => self.attempt_next(table, key, &results, span),
            Op::Clear { table, span } => self.attempt_clear(table, span),
            Op::RecordParent { node, child, class, span } => self.attempt_record_parent(node, child, class, span),
            Op::RecordMetatable { node, child, metatable, span } => self.attempt_record_metatable(node, child, metatable, span),
            Op::Test { ty, null } => match self.st.node(ty) {
                TyNode::Var => {
                    if self.defaults_round {
                        self.st.force(null, Span::default());
                        true
                    } else {
                        false
                    }
                }
                // an `any` value holds nil itself
                TyNode::Bool | TyNode::FalseOr(_) | TyNode::Any => true,
                _ => {
                    self.st.force(null, Span::default());
                    true
                }
            },
            Op::NumOrStr { e, default_str, span, what } => match self.st.node(e.ty).clone() {
                TyNode::Num | TyNode::Int | TyNode::NumVar | TyNode::NPrim(_) | TyNode::Str => true,
                TyNode::Var => {
                    if self.defaults_round {
                        let t = if default_str { self.prim(TyNode::Str) } else { self.prim(TyNode::Num) };
                        self.unify(e.ty, t, span);
                        true
                    } else {
                        false
                    }
                }
                _ => {
                    let s = self.show(e.ty);
                    self.error(span, format!("attempt to {what} a {s} value (numbers or strings expected)"));
                    true
                }
            },
            Op::Len { node, e, span } => match self.st.node(e.ty).clone() {
                TyNode::Str => {
                    self.info.len_str.insert(node);
                    true
                }
                TyNode::Table(t) => {
                    if self.st.tab(t).runtime {
                        self.info.runtime_tables.lengths.insert(node);
                        self.check_runtime_length(e, span, true);
                        return true;
                    }
                    self.info.packs.restricted.push((e.ty, span, "'#' on a nil-preserving array is not supported; use table.pack's n field"));
                    if self.st.tab(t).sparse {
                        self.error(span, "'#' on a nil-preserving array is not supported; use table.pack's n field");
                        return true;
                    }
                    if self.st.tab(t).kind == TKind::Unknown && !self.defaults_round {
                        return false;
                    }
                    if self.st.tab(t).kind == TKind::Map {
                        self.error(span, "'#' on a map is unsupported (it is only defined for arrays and strings)");
                        return true;
                    }
                    self.ensure_kind(t, TKind::Array, span);
                    true
                }
                TyNode::Var => false,
                _ => {
                    let s = self.show(e.ty);
                    self.error(span, format!("attempt to get length of a {s} value"));
                    true
                }
            },
            Op::Pairs { node, t, k, v, span } => match self.st.node(t.ty).clone() {
                TyNode::Table(tab) if self.st.tab(tab).runtime => {
                    self.runtime_pairs(node, t, k, v, crate::check_iteration::IterationMode::Pairs, span);
                    true
                }
                TyNode::Table(tab) => {
                    let kind = self.st.tab(tab).kind;
                    match kind {
                        TKind::Array => {
                            let n = self.prim(TyNode::Num);
                            self.unify(k.ty, n, span);
                            let el = self.elem_slot(tab);
                            self.unify(v.ty, el.ty, span);
                            self.info.fors.insert(node, ForKind::PairsArray);
                            true
                        }
                        TKind::Map => {
                            let ks = self.key_slot(tab);
                            let vs = self.val_slot(tab);
                            self.unify(k.ty, ks.ty, span);
                            self.unify(v.ty, vs.ty, span);
                            self.info.fors.insert(node, ForKind::PairsMap);
                            true
                        }
                        TKind::Record => {
                            self.error(span, "pairs() over a record is unsupported (record fields have different types)");
                            true
                        }
                        TKind::Unknown => {
                            if self.defaults_round {
                                self.ensure_kind(tab, TKind::Map, span);
                                self.attempt(op)
                            } else {
                                false
                            }
                        }
                    }
                }
                TyNode::Var => false,
                _ => {
                    let s = self.show(t.ty);
                    self.error(span, format!("pairs() expects a table, got {s}"));
                    true
                }
            },
            Op::IntParam { ty } => match self.st.node(ty) {
                TyNode::Var => {
                    if self.defaults_round {
                        let n = self.prim(TyNode::Int);
                        self.unify(ty, n, Span::default());
                        true
                    } else {
                        false
                    }
                }
                TyNode::Int | TyNode::Num | TyNode::NumVar | TyNode::NPrim(_) => true,
                _ => {
                    let s = self.show(ty);
                    self.error(Span::default(), format!("a native integer parameter received a {s} value"));
                    true
                }
            },
            Op::Arith { op, x, y, r, span } => self.attempt_arith(op, x, y, r, span),
            Op::BuiltinValue { r, ty, span } => self.attempt_builtin_value(&r, ty, span),
            Op::TraitImpl { inst, param, arg, span } => self.attempt_trait_impl(inst, param, arg, span),
            Op::PcallRets { node, rets, inner, extras, span } => self.attempt_pcall_rets(node, rets, inner, &extras, span),
            Op::NativeFor { node, t, vars, span } => match self.st.node(t.ty).clone() {
                TyNode::Table(_) | TyNode::Func(_) => self.attempt_general_for(node, t, &vars, span),
                TyNode::Native(nt) => {
                    if self.info.iteration.get(&node).is_some_and(|i| i.source_count > 1) {
                        self.error(span, "native iteration takes one iterator expression");
                        return true;
                    }
                    self.native_iter(node, &nt, t.ty, &vars, span);
                    true
                }
                TyNode::Var => false,
                _ => {
                    let s = self.show(t.ty);
                    self.error(span, format!("cannot iterate over a {s} value (use ipairs/pairs for tables, or a native iterator)"));
                    true
                }
            },
            Op::Logic { node, and, a, b, result, span, site } => self.attempt_logic(node, and, a, b, result, span, site),
            Op::Field { node, obj, name, result, write, span } => self.attempt_field(node, obj, &name, result, write, span),
            Op::Index { node, obj, key, key_lit, result, write, span } => {
                self.attempt_index(node, obj, key, key_lit, result, write, span)
            }
            Op::Call { callee, args, nodes, spans, results, span, pack } => self.attempt_call_value(callee, &args, &nodes, &spans, &results, span, pack),
            Op::Method { node, obj, name, args, spans, results, span } => {
                self.attempt_method(node, obj, &name, &args, &spans, &results, span)
            }
        }
    }

    pub(crate) fn attempt_logic(&mut self, node: NodeId, and: bool, a: ETy, b: ETy, result: ETy, span: Span, site: crate::check_dynamic::LogicSite) -> bool {
        if let Some(done) = self.logic_dynamic(node, and, a, b, result, span, site) {
            return done;
        }
        let na = self.st.node(a.ty).clone();
        let a_soft = a.soft != Soft::No;
        let b_soft = b.soft != Soft::No;
        match na {
            TyNode::Var if !self.defaults_round => return false,
            TyNode::Bool => {
                if and {
                    let nb = self.st.node(b.ty).clone();
                    match nb {
                        TyNode::Var if !self.defaults_round => return false,
                        TyNode::Bool | TyNode::Var => {
                            let bt = self.prim(TyNode::Bool);
                            self.unify(b.ty, bt, span);
                            self.unify(result.ty, bt, span);
                        }
                        _ => {
                            let fo = self.st.ty(TyNode::FalseOr(b.ty));
                            self.unify(result.ty, fo, span);
                        }
                    }
                    self.st.edge(a.null, result.null, span);
                    // An absent table read on the left yields nil; the result must remain optional.
                    if a_soft {
                        self.st.force(result.null, span);
                    }
                } else {
                    let bt = self.prim(TyNode::Bool);
                    self.unify(b.ty, bt, span);
                    self.unify(result.ty, bt, span);
                }
                self.info.logic.insert(node, LogicKind::BoolLeft);
            }
            TyNode::FalseOr(inner) => {
                if and {
                    self.error(span, "'and' on a 'false | T' value is unsupported");
                    return true;
                }
                self.info.logic.insert(node, LogicKind::FalseOrLeft);
                self.unify(inner, b.ty, span);
                self.unify(result.ty, b.ty, span);
            }
            _ => {
                if matches!(na, TyNode::Var) && !and {
                    // defaults round with an unknown left operand: `a or b` makes both
                    // operands one type, so decide the kind on that type (`false or true`
                    // must not be treated as a nil-only test)
                    self.unify(a.ty, b.ty, span);
                    if !matches!(self.st.node(a.ty), TyNode::Var) {
                        return self.attempt_logic(node, and, a, b, result, span, site);
                    }
                }
                self.info.logic.insert(node, LogicKind::ValueLeft);
                self.logic_checks.push((node, a.ty, and, result.ty, span));
                if and {
                    self.unify(result.ty, b.ty, span);
                    self.st.edge(a.null, result.null, span);
                    if a_soft {
                        self.st.force(result.null, span);
                    }
                } else {
                    self.unify(a.ty, b.ty, span);
                    self.unify(result.ty, b.ty, span);
                }
            }
        }
        self.st.edge(b.null, result.null, span);
        if b_soft {
            self.st.force(result.null, span);
        }
        true
    }

    pub(crate) fn do_field(&mut self, node: NodeId, obj: ETy, name: String, result: ETy, write: Option<ETy>, span: Span) {
        if !self.attempt_field(node, obj, &name, result, write, span) {
            self.pending.push(Op::Field { node, obj, name, result, write, span });
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn do_index(&mut self, node: NodeId, obj: ETy, key: ETy, key_lit: Option<String>, result: ETy, write: Option<ETy>, span: Span) {
        if !self.attempt_index(node, obj, key, key_lit.clone(), result, write, span) {
            self.pending.push(Op::Index { node, obj, key, key_lit, result, write, span });
        }
    }

    pub(crate) fn link_result(&mut self, result: ETy, v: ETy, span: Span) {
        self.unify(result.ty, v.ty, span);
        self.st.edge(v.null, result.null, span);
        self.set_soft(&result, v.soft);
    }

    pub(crate) fn attempt_field(&mut self, node: NodeId, obj: ETy, name: &str, result: ETy, write: Option<ETy>, span: Span) -> bool {
        if self.runtime_access(node, obj, Some(name), result, write, span) { return true; }
        match self.st.node(obj.ty).clone() {
            TyNode::Var => false,
            TyNode::Table(tab) => {
                let kind = self.st.tab(tab).kind;
                match kind {
                    // `t.name` on a table of unknown kind may be a map access with a
                    // string key; decide once other uses are known.
                    TKind::Unknown if !self.defaults_round => false,
                    TKind::Unknown | TKind::Record => {
                        self.ensure_kind(tab, TKind::Record, span);
                        self.info.access.insert(node, Access::Field(name.to_string()));
                        match write {
                            Some(v) => {
                                if let Some(sl) = self.field_slot(tab, name, span) {
                                    self.unify(result.ty, sl.ty, span);
                                    self.flow_write(node, v, sl, span);
                                }
                            }
                            None => {
                                if self.metatables.enabled {
                                    self.metatables.reads.entry(node).or_insert(crate::check_metatable::RecordRead {
                                        tab, name: name.to_string(), result, span,
                                    });
                                    return true;
                                }
                                let fv = self.field_read(tab, name, span);
                                self.link_result(result, fv, span);
                            }
                        }
                        true
                    }
                    TKind::Map => {
                        let s = self.str_();
                        self.attempt_index(node, obj, s, Some(name.to_string()), result, write, span)
                    }
                    TKind::Array => {
                        if self.st.tab(tab).packed && name == "n" {
                            if write.is_some() {
                                self.error(span, "assigning table.pack's n field is not supported");
                            }
                            self.info.packs.count_reads.insert(node);
                            let v = self.num();
                            self.link_result(result, v, span);
                            return true;
                        }
                        self.error(span, format!("cannot access field '{name}' of an array"));
                        true
                    }
                }
            }
            TyNode::Native(nt) => {
                self.native_field_access(node, &nt, obj.ty, name, result, write, span);
                true
            }
            TyNode::Namespace(r) => {
                if write.is_some() {
                    self.error(span, "cannot assign into a Rust crate namespace");
                    return true;
                }
                self.namespace_member(node, r, name, result, span);
                true
            }
            TyNode::Str => {
                self.error(span, format!("cannot access field '{name}' of a string (use s:{name}(...) for methods)"));
                true
            }
            _ => {
                let s = self.show(obj.ty);
                self.error(span, format!("cannot access field '{name}' of a {s} value"));
                true
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn attempt_index(&mut self, node: NodeId, obj: ETy, key: ETy, key_lit: Option<String>, result: ETy, write: Option<ETy>, span: Span) -> bool {
        if self.runtime_access(node, obj, key_lit.as_deref(), result, write, span) { return true; }
        if write.is_some() {
            self.info.packs.restricted.push((obj.ty, span, "writes to nil-preserving array slots are not supported"));
        }
        if self.metatables.general && key_lit.as_deref() == Some("__index") {
            if let Some(value) = write { self.metatables.index_writes.push((value, span)); }
        }
        match self.st.node(obj.ty).clone() {
            TyNode::Var => false,
            TyNode::Table(tab) => {
                let mut kind = self.st.tab(tab).kind;
                if self.metatables.general && kind == TKind::Unknown && key_lit.as_deref() == Some("__index") && write.is_some() {
                    self.ensure_kind(tab, TKind::Record, span);
                    kind = TKind::Record;
                }
                // A later attachment can constrain an empty literal to a record.
                if self.metatables.enabled && kind == TKind::Unknown && key_lit.is_some() && !self.defaults_round {
                    return false;
                }
                if kind == TKind::Unknown {
                    match self.st.node(key.ty) {
                        TyNode::Num | TyNode::NumVar => kind = TKind::Array,
                        TyNode::Str | TyNode::Bool => kind = TKind::Map,
                        _ => {
                            if !self.defaults_round {
                                return false;
                            }
                            kind = TKind::Map;
                        }
                    }
                    self.ensure_kind(tab, kind, span);
                }
                match kind {
                    TKind::Array => {
                        let n = self.prim(TyNode::Num);
                        self.unify(key.ty, n, span);
                        self.info.access.insert(node, Access::Array);
                        let el = self.elem_slot(tab);
                        if self.st.tab(tab).sparse && write.is_some() {
                            self.error(span, "writes to nil-preserving array slots are not supported");
                            return true;
                        }
                        match write {
                            // nil writes are allowed (remove last / no-op past end)
                            Some(v) => {
                                self.unify_write(node, v, el.ty, span);
                                self.unify(result.ty, el.ty, span);
                            }
                            None => {
                                let v = ETy { ty: el.ty, null: self.st.null_false, soft: Soft::Yes };
                                self.link_result(result, v, span);
                            }
                        }
                    }
                    TKind::Map => {
                        let ks = self.key_slot(tab);
                        let vs = self.val_slot(tab);
                        if self.is_any(ks.ty) { self.boxable(key.ty, span); } else { self.flow(key, ks, span); }
                        self.info.access.insert(node, Access::Map);
                        match write {
                            Some(v) => {
                                self.unify_write(node, v, vs.ty, span);
                                self.unify(result.ty, vs.ty, span);
                            }
                            None => {
                                let v = ETy { ty: vs.ty, null: self.st.null_false, soft: Soft::Yes };
                                self.link_result(result, v, span);
                            }
                        }
                    }
                    TKind::Record => match key_lit {
                        Some(name) => return self.attempt_field(node, obj, &name, result, write, span),
                        None => self.error(span, "records can only be indexed with field names (use a map type for dynamic keys)"),
                    },
                    TKind::Unknown => unreachable!(),
                }
                true
            }
            TyNode::Str => {
                self.error(span, "cannot index a string (use string.sub)");
                true
            }
            _ => {
                let s = self.show(obj.ty);
                self.error(span, format!("cannot index a {s} value"));
                true
            }
        }
    }

    // Calls

    pub(crate) fn call(&mut self, e: &Expr, f: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        if self.metatables.parent_calls.contains(&e.id) {
            return self.record_parent_call(e, args, want);
        }
        if let ExprKind::Name(n) = &f.kind {
            if let Some(Res::Local(s)) = self.res.res(n.id) {
                if let Some((b, field)) = self.info.builtin_aliases.get(&s).cloned() {
                    return self.builtin_call(e, b, field.as_deref(), args, want);
                }
            }
        }
        if let Some(b) = is_lib(f, self.res) {
            return self.builtin_call(e, b, None, args, want);
        }
        if let ExprKind::Field(lib, fname) = &f.kind {
            if let Some(b) = is_lib(lib, self.res) {
                return self.builtin_call(e, b, Some(&fname.text), args, want);
            }
        }
        let callee = self.expr(f);
        if self.runtime_type(callee.ty) {
            return self.runtime_invoke(e, args, want);
        }
        if let TyNode::Namespace(r) = self.st.node(callee.ty).clone() {
            return self.native_call(e, r, args, want);
        }
        self.need(callee, f.span, "attempt to call a nil value");
        if let ExprKind::Name(n) = &f.kind {
            if let Some(Res::Local(s)) = self.res.res(n.id) {
                if self.res.sym(s).is_static {
                    self.info.calls.insert(e.id, CallKind::Static(s));
                }
            }
        }
        self.info.calls.entry(e.id).or_insert(CallKind::Value);
        // a trailing `...` passes its run-time number of values
        let pack = match args.last() {
            Some(l) if self.is_pack(l) => Some(self.pack_value(l)),
            _ => None,
        };
        let (vals, spans) = if pack.is_some() {
            // the arguments before a trailing pack are single values
            self.args_single(&args[..args.len() - 1])
        } else {
            self.allow_pack = true;
            self.args_values(args)
        };
        let pack = pack.or_else(|| args.last().and_then(|l| self.info.pack_calls.get(&l.id).copied()));
        self.settle_record_calls();
        if want.is_none() && self.metatables.enabled && self.metatables.reads.contains_key(&f.id)
            && matches!(self.st.node(callee.ty), TyNode::Var)
        {
            self.error(e.span, "cannot determine how many values this call returns here; annotate the function's return type");
        }
        let n = self.result_count(callee.ty, want, e.span);
        if want.is_none() {
            if let Some(t) = self.callee_tail(callee.ty) {
                let t = self.of_slot(t);
                self.info.pack_calls.insert(e.id, t);
            }
        }
        if want.is_none() && self.arity_exempt != Some(e.id) {
            self.arity_guesses.push((callee, None, n, e.span));
        }
        let results: Vec<ETy> = (0..n).map(|_| self.fresh_result()).collect();
        let nodes: Vec<NodeId> = args.iter().map(|a| a.id).collect();
        if !self.attempt_call_value(callee, &vals, &nodes, &spans, &results, e.span, pack) {
            self.pending.push(Op::Call { callee, args: vals, nodes, spans, results: results.clone(), span: e.span, pack });
        }
        results
    }

    // Varargs

    /// One value of the current function's `...` (`local a = ...`): nil when
    /// there are fewer arguments, as in Luau.
    pub(crate) fn va_elem(&mut self) -> ETy {
        match self.fns.last().and_then(|f| f.vararg) {
            Some(s) => ETy { ty: s.ty, null: self.st.null_true, soft: Soft::No },
            // reported by the resolver
            None => self.fresh_result(),
        }
    }

    /// The elements of `...` passed on as they are (to another `...`, a table
    /// constructor or print): the element slot of the declaration.
    pub(crate) fn va_pack(&mut self) -> ETy {
        match self.fns.last().and_then(|f| f.vararg) {
            Some(s) => self.of_slot(s),
            None => self.fresh_result(),
        }
    }

    /// `...` or `select(i, ...)`: a value list whose length is known at run time.
    pub(crate) fn is_pack(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Vararg => true,
            ExprKind::Call(f, args) => {
                is_lib(f, self.res) == Some(Builtin::Select)
                    && args.len() == 2
                    && !matches!(&args[0].kind, ExprKind::Str(s) if s.as_slice() == b"#")
                    && matches!(args[1].kind, ExprKind::Vararg)
            }
            _ => false,
        }
    }

    /// Checks a pack used where its values are passed on as they are (the end of
    /// an argument list or table constructor); returns the element value.
    pub(crate) fn pack_value(&mut self, e: &Expr) -> ETy {
        if let ExprKind::Call(_, args) = &e.kind {
            self.select_call(e, args, Some(1));
            self.info.builtin_outs.remove(&e.id);
        }
        let el = self.va_pack();
        self.record(e, el)
    }

    /// `select("#", ...)` and `select(i, ...)` (only over `...`).
    pub(crate) fn select_call(&mut self, e: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        if args.len() != 2 || !matches!(args[1].kind, ExprKind::Vararg | ExprKind::Call(..) | ExprKind::Method(..)) {
            return self.select_fixed(e, args, want);
        }
        let count = matches!(args.first().map(|a| &a.kind), Some(ExprKind::Str(s)) if s.as_slice() == b"#");
        let over_call = args.len() == 2 && matches!(args[1].kind, ExprKind::Call(..) | ExprKind::Method(..));
        if args.len() != 2 || !(over_call || matches!(args[1].kind, ExprKind::Vararg)) {
            self.error(e.span, "select is supported as select(\"#\", ...) and select(i, ...), also over a call returning `...`");
            for a in args {
                self.expr(a);
            }
            let r = self.fresh_result();
            return vec![r; want.unwrap_or(1)];
        }
        self.expr(&args[0]);
        let el = if over_call {
            // select over a call returning `...`: its fixed results and its
            // tail form one list, so they share the tail's element type
            self.allow_pack = true;
            let fixed = self.exprs_all(&args[1..], None);
            match self.info.pack_calls.get(&args[1].id).copied() {
                Some(t) => {
                    for v in &fixed {
                        self.flow(*v, Slot { ty: t.ty, null: t.null }, args[1].span);
                    }
                    ETy { ty: t.ty, null: self.st.null_true, soft: Soft::No }
                }
                None => {
                    for v in &fixed { self.pack_boxable(v.ty, args[1].span); }
                    self.select_common_type(e.id, &fixed);
                    if !count {
                        let index = self.info.expr[&args[0].id];
                        self.expect(index, TyNode::Num, args[0].span, "bad argument #1 to 'select' (number expected)");
                    }
                    return self.select_fixed_result(e, count, want);
                }
            }
        } else {
            let el = self.va_elem();
            self.record(&args[1], el);
            el
        };
        if count {
            self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::SelectCount));
            let n = self.num();
            let mut r = vec![n];
            match want {
                Some(w) => {
                    r.truncate(w);
                    while r.len() < w {
                        let x = self.nil();
                        r.push(x);
                    }
                }
                None => {}
            }
            return r;
        }
        let i = self.info.expr[&args[0].id];
        self.expect(i, TyNode::Num, args[0].span, "bad argument #1 to 'select' (number expected)");
        self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::Select));
        match want {
            Some(n) => {
                let v = vec![el; n];
                self.info.builtin_outs.insert(e.id, v.clone());
                v
            }
            // `select(i, f())` keeps the run-time count: a pack where packs are
            // allowed (checked by `exprs_all`)
            None if over_call => {
                let t = ETy { null: self.info.pack_calls.get(&args[1].id).map(|t| t.null).unwrap_or(el.null), ..el };
                self.info.pack_calls.insert(e.id, t);
                vec![]
            }
            None => {
                self.error(e.span, PACK_MSG);
                vec![el]
            }
        }
    }

    /// Arguments that each give one value (those before a trailing pack).
    pub(crate) fn args_single(&mut self, args: &[Expr]) -> (Vec<ETy>, Vec<Span>) {
        let vals = args.iter().map(|a| self.expr(a)).collect();
        (vals, args.iter().map(|a| a.span).collect())
    }

    /// `table.unpack(t, i, j)`: the array's values from `i` to `j`, a run-time
    /// number of results like a function returning `...` (no fixed results).
    pub(crate) fn unpack_call(&mut self, e: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        if args.is_empty() || args.len() > 3 {
            self.error(e.span, format!("table.unpack expects 1 to 3 arguments, got {}", args.len()));
            for a in args {
                self.expr(a);
            }
            let r = self.fresh_result();
            return vec![r; want.unwrap_or(1)];
        }
        let t = self.expr(&args[0]);
        self.need(t, args[0].span, "bad argument #1 to 'unpack' (table expected, got nil)");
        let (tt, tab) = match self.st.node(t.ty).clone() {
            TyNode::Table(tab) if self.st.tab(tab).sparse => (t.ty, tab),
            _ => self.new_table_var(args[0].span),
        };
        self.ensure_kind(tab, TKind::Array, args[0].span);
        let el = self.elem_slot(tab);
        self.unify(t.ty, tt, args[0].span);
        let mut end_bound = None;
        for (index, a) in args[1..].iter().enumerate() {
            // `i` and `j` may be nil (their defaults)
            let v = self.expr(a);
            if index == 1 { end_bound = Some(v); }
            let n = self.prim(TyNode::Num);
            self.unify(v.ty, n, a.span);
        }
        self.info.packs.unpack_bounds.push((t.ty, end_bound, e.span));
        self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::TUnpack));
        let start_safe = args.get(1).is_none_or(|a| matches!(a.kind, ExprKind::Nil) || matches!(a.kind, ExprKind::Number(n) if n >= 1.0 && n < 2147483648.0));
        let end_default = args.get(2).is_none_or(|a| matches!(a.kind, ExprKind::Nil));
        let may_nil = self.st.tab(tab).sparse || !start_safe || !end_default;
        match want {
            Some(n) => {
                let v = ETy { ty: el.ty, null: self.st.null_true, soft: Soft::No };
                vec![v; n]
            }
            None => {
                let mut p = self.of_slot(el);
                if may_nil { p.null = self.st.null_true; }
                self.info.pack_calls.insert(e.id, p);
                vec![]
            }
        }
    }

    pub(crate) fn args_values(&mut self, args: &[Expr]) -> (Vec<ETy>, Vec<Span>) {
        let vals = self.exprs_all(args, None);
        let mut spans: Vec<Span> = args.iter().map(|a| a.span).collect();
        while spans.len() < vals.len() {
            spans.push(args.last().map(|a| a.span).unwrap_or_default());
        }
        (vals, spans)
    }

    /// Records the values a trailing call of a builtin's arguments
    /// expands to, when that is not exactly one (`math.atan2(two())`); the code
    /// generator passes them as separate arguments.
    pub(crate) fn note_multi_tail(&mut self, node: NodeId, args: &[Expr], vals: &[ETy]) {
        if multi_tail(args, vals.len()) {
            self.info.multi_tail.insert(node, vals[args.len() - 1..].to_vec());
        }
    }

    pub(crate) fn result_count(&mut self, callee: TyId, want: Option<usize>, span: Span) -> usize {
        match want {
            Some(n) => n,
            None => match self.st.node(callee).clone() {
                TyNode::Func(f) => match self.st.rets_known(f.rets) {
                    Some(r) => r.len(),
                    None => {
                        self.error(span, "cannot determine how many values this call returns here; annotate the function's return type");
                        1
                    }
                },
                _ => 1,
            },
        }
    }

    pub(crate) fn attempt_call_value(&mut self, callee: ETy, args: &[ETy], nodes: &[NodeId], spans: &[Span], results: &[ETy], span: Span, pack: Option<ETy>) -> bool {
        let f = match self.st.node(callee.ty).clone() {
            TyNode::Func(f) => f,
            TyNode::Var => {
                if !self.defaults_round {
                    return false;
                }
                // Unknown function value: shape it after this call.
                let params: Vec<Slot> = args
                    .iter()
                    .map(|_| {
                        let v = self.st.var();
                        self.st.slot(v)
                    })
                    .collect();
                let rets: Vec<Slot> = results
                    .iter()
                    .map(|_| {
                        let v = self.st.var();
                        self.st.slot(v)
                    })
                    .collect();
                let r = self.st.new_rets(RetsNode::Known(rets));
                let ft = self.st.ty(TyNode::Func(Rc::new(FuncTy { params, rets: r, vararg: None })));
                self.unify(callee.ty, ft, span);
                match self.st.node(callee.ty).clone() {
                    TyNode::Func(f) => f,
                    _ => return true,
                }
            }
            _ => {
                let s = self.show(callee.ty);
                self.error(span, format!("attempt to call a {s} value"));
                return true;
            }
        };
        let Some(rets) = self.st.rets_known(f.rets).cloned() else {
            return false;
        };
        for (i, p) in f.params.iter().enumerate() {
            match (args.get(i), pack) {
                (Some(a), _) => {
                    // an argument passed to an `any` parameter is boxed
                    self.flow_node(nodes.get(i).copied(), *a, *p, spans[i]);
                }
                // filled from the trailing `...` (nil when it runs out)
                (None, Some(v)) => {
                    let v = ETy { null: self.st.null_true, ..v };
                    self.flow(v, *p, span);
                }
                (None, None) => self.st.force(p.null, span),
            }
        }
        // extra arguments of a variadic function become its `...`
        if let Some(va) = f.vararg {
            for (i, a) in args.iter().enumerate().skip(f.params.len()) {
                // `...: any` takes values of any type (boxed)
                self.flow_node(nodes.get(i).copied(), *a, va, spans[i]);
            }
            if let Some(v) = pack {
                self.flow(v, va, span);
            }
        }
        let tail = self.st.rets_tail(f.rets);
        for (i, r) in results.iter().enumerate() {
            match (rets.get(i), tail) {
                (Some(s), _) => {
                    self.unify(r.ty, s.ty, span);
                    self.st.edge(s.null, r.null, span);
                }
                // a run-time-counted result: nil when there are fewer
                (None, Some(t)) => {
                    self.unify(r.ty, t.ty, span);
                    self.st.force(r.null, span);
                }
                (None, None) => self.st.force(r.null, span),
            }
        }
        true
    }

    pub(crate) fn method_call(&mut self, e: &Expr, o: &Expr, name: &Name, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        let obj = self.expr(o);
        if self.runtime_type(obj.ty) {
            for arg in args { self.expr(arg); }
            self.error(name.span, "method calls on runtime tables are unsupported; use a statically typed record method");
            return (0..want.unwrap_or(1)).map(|_| self.fresh_result()).collect();
        }
        self.need(obj, o.span, &format!("attempt to call method '{}' on a nil value", name.text));
        if matches!(name.text.as_str(), "find" | "match") {
            self.note_pattern(e.id, args.first(), name.text == "find", want);
        }
        if name.text == "gsub" {
            self.note_gsub(e.id, args.first(), args.get(1));
        }
        let (vals, spans) = self.args_values(args);
        self.note_multi_tail(e.id, args, &vals);
        self.settle_record_calls();
        self.prepare_record_method(e.id, obj, &name.text, name.span);
        self.settle_record_calls();
        let count = match want {
            Some(n) => n,
            None if matches!(self.st.node(obj.ty), TyNode::Str) && name.text == "gsub" => 2,
            None if matches!(self.st.node(obj.ty), TyNode::Str) && matches!(name.text.as_str(), "find" | "match") => {
                let caps = self.info.pattern_caps.get(&e.id).map(|c| c.len()).unwrap_or(0);
                if name.text == "find" { 2 + caps } else { caps.max(1) }
            }
            None => {
                let n = self.method_result_count(obj, &name.text);
                if self.arity_exempt != Some(e.id) {
                    self.arity_guesses.push((obj, Some(name.text.clone()), n, name.span));
                }
                if let Some(t) = self.method_tail(obj, &name.text) {
                    let t = self.of_slot(t);
                    self.info.pack_calls.insert(e.id, t);
                }
                n
            }
        };
        let results: Vec<ETy> = (0..count).map(|_| self.fresh_result()).collect();
        if !self.attempt_method(e.id, obj, &name.text, &vals, &spans, &results, name.span) {
            self.pending.push(Op::Method {
                node: e.id,
                obj,
                name: name.text.clone(),
                args: vals,
                spans,
                results: results.clone(),
                span: name.span,
            });
        }
        results
    }

    /// Records the captures of a `find`/`match` pattern whose value is
    /// known at compile time: a literal or a local that always holds one (`local p
    /// = "(%w+)"`). Any other pattern is compiled as one without captures (`find`
    /// gives 2 results, `match` 1); when `want` shows that the call site observes
    /// more results than that, the call goes into `pattern_full` and the run time
    /// rejects a pattern with captures instead of returning fewer values.
    pub(crate) fn note_pattern(&mut self, node: NodeId, p: Option<&Expr>, find: bool, want: Option<usize>) {
        if let Some(s) = p.and_then(|p| self.known_str(p)) {
            let caps = pattern_captures(&s);
            self.info.pattern_caps.insert(node, caps);
        } else if want.is_none_or(|n| n > if find { 2 } else { 1 }) {
            self.info.pattern_full.insert(node);
        }
    }

    /// What a `string.gsub` call needs from its pattern and replacement when their
    /// values are known at compile time: the pattern's captures (the arguments of a
    /// replacement function) and a replacement template (validated).
    fn note_gsub(&mut self, node: NodeId, pat: Option<&Expr>, repl: Option<&Expr>) {
        if let Some(p) = pat.and_then(|p| self.known_str(p)) {
            self.info.pattern_caps.insert(node, pattern_captures(&p));
        }
        if let Some(t) = repl.and_then(|r| self.known_str(r)) {
            self.info.gsub_templates.insert(node, t);
        }
    }

    /// The value of a string expression known at compile time.
    fn known_str(&self, p: &Expr) -> Option<Vec<u8>> {
        match &p.kind {
            ExprKind::Str(s) => Some(s.clone()),
            ExprKind::Paren(x) => self.known_str(x),
            ExprKind::Name(n) => match self.res.res(n.id) {
                Some(Res::Local(s)) => self.info.const_strs.get(&s).cloned(),
                _ => None,
            },
            _ => None,
        }
    }

    /// Result tail of a function type.
    pub(crate) fn callee_tail(&self, t: TyId) -> Option<Slot> {
        match self.st.node(t) {
            TyNode::Func(f) => self.st.rets_tail(f.rets),
            _ => None,
        }
    }

    /// Result tail of a record method.
    pub(crate) fn method_tail(&self, obj: ETy, name: &str) -> Option<Slot> {
        if let Some(slot) = self.record_method_slot(obj, name) {
            return self.callee_tail(slot.ty);
        }
        match self.st.node(obj.ty) {
            TyNode::Table(tab) => self.st.tab(*tab).fields.get(name).and_then(|sl| self.callee_tail(sl.ty)),
            _ => None,
        }
    }

    pub(crate) fn method_result_count(&mut self, obj: ETy, name: &str) -> usize {
        if let Some(slot) = self.record_method_slot(obj, name) {
            let span = match self.st.node(obj.ty) {
                TyNode::Table(tab) => self.st.tab(*tab).span,
                _ => Span::default(),
            };
            if !matches!(self.st.node(slot.ty), TyNode::Func(_)) {
                self.error(span, "cannot determine how many values this call returns here; annotate the function's return type");
                return 1;
            }
            return self.result_count(slot.ty, None, span);
        }
        match self.st.node(obj.ty).clone() {
            TyNode::Native(nt) => self.native_method_ret_count(nt.item, name).unwrap_or(1),
            TyNode::Table(tab) => match self.st.tab(tab).fields.get(name).copied() {
                Some(sl) => match self.st.node(sl.ty).clone() {
                    TyNode::Func(f) => self.st.rets_known(f.rets).map(|r| r.len()).unwrap_or(1),
                    _ => 1,
                },
                None => match self.st.tab(tab).native.clone() {
                    Some(crate::check_native::NativeRec::Struct(r, _)) => self.native_method_ret_count(r, name).unwrap_or(1),
                    _ => 1,
                },
            },
            _ => 1,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn attempt_method(&mut self, node: NodeId, obj: ETy, name: &str, args: &[ETy], spans: &[Span], results: &[ETy], span: Span) -> bool {
        match self.st.node(obj.ty).clone() {
            TyNode::Var => false,
            TyNode::Str => {
                let b = match name {
                    "len" => BuiltinFn::StrLen,
                    "sub" => BuiltinFn::StrSub,
                    "upper" => BuiltinFn::StrUpper,
                    "split" => BuiltinFn::StrSplit,
                    "reverse" => BuiltinFn::StrReverse,
                    "lower" => BuiltinFn::StrLower,
                    "rep" => BuiltinFn::StrRep,
                    "byte" => BuiltinFn::StrByte,
                    "find" => BuiltinFn::StrFind,
                    "match" => BuiltinFn::StrMatch,
                    "gsub" => BuiltinFn::StrGsub,
                    "gmatch" => {
                        self.error(span, "string.gmatch can only be used directly in a 'for ... in' loop");
                        return true;
                    }
                    _ => {
                        self.error(span, format!("string method '{name}' is not supported in this version"));
                        return true;
                    }
                };
                self.info.calls.insert(node, CallKind::Builtin(b));
                let mut all = vec![obj];
                all.extend_from_slice(args);
                let mut sp = vec![span];
                sp.extend_from_slice(spans);
                self.cur_call = node;
                let out = self.builtin_sig(b, &all, &sp, span);
                self.bind_results(results, &out, span);
                true
            }
            TyNode::Native(nt) => {
                self.native_method_call(node, nt.item, &nt.args, obj, name, args, spans, results, span);
                true
            }
            TyNode::Table(tab)
                if matches!(self.st.tab(tab).native, Some(crate::check_native::NativeRec::Struct(..)))
                    // a data field of the same name (`Attrs.family` vs `Attrs:family(..)`)
                    // does not hide the native method
                    && !self.st.tab(tab).fields.get(name).map(|s| matches!(self.st.node(s.ty), TyNode::Func(_))).unwrap_or(false) =>
            {
                let Some(crate::check_native::NativeRec::Struct(r, targs)) = self.st.tab(tab).native.clone() else { unreachable!() };
                self.native_method_call(node, r, &targs, obj, name, args, spans, results, span);
                true
            }
            TyNode::Table(tab) => {
                if self.metatables.enabled && self.st.tab(tab).native.is_none() {
                    if let Some(f) = self.prepare_record_method(node, obj, name, span) {
                        self.info.calls.insert(node, CallKind::RecordMethod(name.to_string()));
                        self.need(f, span, &format!("method '{name}' may be nil"));
                        let mut all = vec![obj];
                        all.extend_from_slice(args);
                        let mut all_spans = vec![span];
                        all_spans.extend_from_slice(spans);
                        return self.attempt_call_value(f, &all, &[], &all_spans, results, span, None);
                    }
                    return false;
                }
                if self.st.tab(tab).kind == TKind::Unknown && !self.st.tab(tab).fields.contains_key(name) && !self.defaults_round {
                    return false;
                }
                self.ensure_kind(tab, TKind::Record, span);
                let Some(sl) = self.field_slot(tab, name, span) else { return true };
                self.info.calls.insert(node, CallKind::RecordMethod(name.to_string()));
                let f = ETy { ty: sl.ty, null: sl.null, soft: Soft::No };
                self.need(f, span, &format!("method '{name}' may be nil"));
                let mut all = vec![obj];
                all.extend_from_slice(args);
                let mut sp = vec![span];
                sp.extend_from_slice(spans);
                if !self.attempt_call_value(f, &all, &[], &sp, results, span, None) {
                    self.pending.push(Op::Call { callee: f, args: all, nodes: Vec::new(), spans: sp, results: results.to_vec(), span, pack: None });
                }
                true
            }
            _ => {
                let s = self.show(obj.ty);
                self.error(span, format!("cannot call method '{name}' on a {s} value"));
                true
            }
        }
    }

    pub(crate) fn bind_results(&mut self, results: &[ETy], out: &[ETy], span: Span) {
        for (i, r) in results.iter().enumerate() {
            match out.get(i) {
                Some(v) => {
                    self.unify(r.ty, v.ty, span);
                    self.st.edge(v.null, r.null, span);
                }
                None => self.st.force(r.null, span),
            }
        }
    }

    // Builtins

    pub(crate) fn builtin_call(&mut self, e: &Expr, b: Builtin, field: Option<&str>, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        if field.is_none() {
            if let Some(out) = self.runtime_builtin(e, b, args, want) { return out; }
        }
        let span = e.span;
        let bf = match (b, field) {
            (Builtin::Require, None) => {
                if let Some(mi) = self.units.iter().find_map(|(r, _)| r.get(&e.id)).copied() {
                    self.info.calls.insert(e.id, CallKind::Require(mi));
                    return match self.info.module_value.get(mi).copied().flatten() {
                        Some(v) => vec![v],
                        None => vec![],
                    };
                }
                if let Some(c) = self.units.iter().find_map(|(_, r)| r.get(&e.id)).copied() {
                    self.info.calls.insert(e.id, CallKind::RequireRust);
                    let t = self.st.ty(TyNode::Namespace(self.world.root(c)));
                    return vec![self.val(t)];
                }
                self.error(span, "require() expects a literal path: \"./module\" or \"rust:crate\"");
                return vec![self.fresh_result()];
            }
            (Builtin::Print, None) => BuiltinFn::Print,
            (Builtin::ToString, None) => BuiltinFn::ToString,
            (Builtin::ToNumber, None) => BuiltinFn::ToNumber,
            (Builtin::Type, None) => BuiltinFn::Type,
            (Builtin::Next, None) => return self.next_call(e, args, want),
            (Builtin::Assert, None) => BuiltinFn::Assert,
            (Builtin::Error, None) => BuiltinFn::Error,
            (Builtin::Pcall, None) => BuiltinFn::Pcall,
            (Builtin::Xpcall, None) => return self.xpcall_call(e, args, want),
            (Builtin::Bit32, Some(n)) => return self.bit32_call(e, n, args, want),
            (Builtin::CollectGarbage, None) => BuiltinFn::CollectGarbage,
            (Builtin::TaskLib, Some(n)) => return self.task_call(e, n, args, want),
            (Builtin::CoroutineLib, Some(n)) => return self.coroutine_call(e, n, args, want),
            (Builtin::Await, None) => return self.await_call(e, args, want),
            (Builtin::Select, None) => return self.select_call(e, args, want),
            (Builtin::SetMetatable, None) => return self.record_parent_call(e, args, want),
            (Builtin::Ipairs | Builtin::Pairs, None) => {
                self.error(span, "ipairs/pairs can only be used directly in a 'for ... in' loop");
                return vec![self.fresh_result()];
            }
            (Builtin::StringLib, Some(n)) => match n {
                "len" => BuiltinFn::StrLen,
                "sub" => BuiltinFn::StrSub,
                "upper" => BuiltinFn::StrUpper,
                "split" => BuiltinFn::StrSplit,
                "reverse" => BuiltinFn::StrReverse,
                "lower" => BuiltinFn::StrLower,
                "format" => BuiltinFn::StrFormat,
                "rep" => BuiltinFn::StrRep,
                "byte" => BuiltinFn::StrByte,
                "char" => BuiltinFn::StrChar,
                "find" => BuiltinFn::StrFind,
                "match" => BuiltinFn::StrMatch,
                "gsub" => BuiltinFn::StrGsub,
                "gmatch" => {
                    self.error(span, "string.gmatch can only be used directly in a 'for ... in' loop");
                    return vec![self.fresh_result()];
                }
                _ => return self.unsupported_lib(span, "string", n),
            },
            (Builtin::Table, Some(n)) => match n {
                "freeze" => BuiltinFn::TFreeze,
                "isfrozen" => BuiltinFn::TIsFrozen,
                "move" => BuiltinFn::TMove,
                "insert" => BuiltinFn::TInsert,
                "remove" => BuiltinFn::TRemove,
                "concat" => BuiltinFn::TConcat,
                "create" if self.info.runtime_tables.constructors.contains(&e.id) => return self.runtime_create_clone(e, args, true, want),
                "clone" if self.info.runtime_tables.constructors.contains(&e.id) => return self.runtime_create_clone(e, args, false, want),
                "create" => BuiltinFn::TCreate,
                "clone" => BuiltinFn::TClone,
                "clear" => BuiltinFn::TClear,
                "sort" => BuiltinFn::TSort,
                "unpack" => return self.unpack_call(e, args, want),
                "pack" => return vec![self.pack_call(e, args)],
                _ => return self.unsupported_lib(span, "table", n),
            },
            (Builtin::Math, Some(n)) => match n {
                "floor" => BuiltinFn::MFloor,
                "tointeger" => BuiltinFn::MToInteger,
                "ceil" => BuiltinFn::MCeil,
                "sqrt" => BuiltinFn::MSqrt,
                "abs" => BuiltinFn::MAbs,
                "min" => BuiltinFn::MMin,
                "max" => BuiltinFn::MMax,
                _ => match MATH_FNS.iter().find(|(k, _, _)| *k == n) {
                    Some(&(k, lo, hi)) => BuiltinFn::MFn(k, lo, hi),
                    None => return self.unsupported_lib(span, "math", n),
                },
            },
            (_, Some(n)) => {
                self.error(span, format!("'{n}' cannot be called here"));
                return vec![self.fresh_result()];
            }
            (_, None) => {
                self.error(span, "this builtin cannot be called");
                return vec![self.fresh_result()];
            }
        };
        if matches!(bf, BuiltinFn::StrFind | BuiltinFn::StrMatch) {
            self.note_pattern(e.id, args.get(1), bf == BuiltinFn::StrFind, want);
        }
        if bf == BuiltinFn::StrGsub {
            self.note_gsub(e.id, args.get(1), args.get(2));
        }
        self.info.calls.insert(e.id, CallKind::Builtin(bf));
        if bf == BuiltinFn::Error {
            self.note_error_level(e, args);
        }
        let out = match bf {
            BuiltinFn::StrFormat => vec![self.string_format(e, args)],
            BuiltinFn::Pcall => {
                self.pcall_want = want;
                let r = self.pcall(e, args);
                self.pcall_want = None;
                r
            }
            BuiltinFn::Assert => {
                // assert(v, msg) returns v, known to be non-nil. A trailing call
                // gives its values as `v, msg` (`assert(f())`); its
                // message may be nil ("assertion failed!", as in Luau).
                let (vals, spans) = self.args_values(args);
                self.note_multi_tail(e.id, args, &vals);
                if vals.is_empty() || vals.len() > 2 {
                    self.error(span, format!("assert expects one or two arguments, got {}", vals.len()));
                    vec![]
                } else {
                    let v = vals[0];
                    self.test_value(&args[0], v);
                    if let Some(&m) = vals.get(1) {
                        if args.len() == 2 {
                            self.expect(m, TyNode::Str, spans[1], "bad argument #2 to 'assert' (string expected)");
                        } else {
                            let s = self.prim(TyNode::Str);
                            self.unify(m.ty, s, spans[1]);
                        }
                    }
                    vec![self.val(v.ty)]
                }
            }
            _ => {
                let exempt = std::mem::replace(&mut self.arity_exempt, if bf == BuiltinFn::Print { args.last().map(|a| a.id) } else { None });
                // `print(..., ...)`: the trailing `...` is printed at run time
                let (vals, spans) = match args.last() {
                    _ if bf == BuiltinFn::TSort && args.len() > 1 => {
                        let first = self.expr(&args[0]);
                        self.prepare_runtime_sort_callback(first, &args[1]);
                        let (mut rest, mut rest_spans) = self.args_values(&args[1..]);
                        rest.insert(0, first);
                        rest_spans.insert(0, args[0].span);
                        (rest, rest_spans)
                    }
                    Some(l) if bf == BuiltinFn::Print && self.is_pack(l) => {
                        let tail = self.pack_value(l);
                        if self.info.runtime_tables.enabled { self.runtime_printable(tail.ty, l.span); }
                        self.args_single(&args[..args.len() - 1])
                    }
                    _ => {
                        self.allow_pack = bf == BuiltinFn::Print;
                        self.args_values(args)
                    }
                };
                self.arity_exempt = exempt;
                if bf != BuiltinFn::Print {
                    self.note_multi_tail(e.id, args, &vals);
                }
                self.cur_call = e.id;
                let out = if let Some(out) = self.table_library_sig(bf, &vals, &spans, args, span) {
                    self.info.builtin_outs.insert(e.id, out.clone());
                    out
                } else { self.builtin_sig(bf, &vals, &spans, span) };
                if bf == BuiltinFn::ToString && self.info.runtime_tables.enabled && !vals.is_empty() {
                    self.runtime_box(&args[0], vals[0]);
                    self.runtime_out(e, crate::check_runtime_table::RuntimeCall::ToString, out, None)
                } else if bf == BuiltinFn::Print && self.info.runtime_tables.enabled {
                    for (value, span) in vals.iter().zip(&spans) { self.runtime_printable(value.ty, *span); }
                    self.runtime_out(e, crate::check_runtime_table::RuntimeCall::Print, out, None)
                } else { out }
            }
        };
        match want {
            Some(n) => {
                let mut r = out;
                r.truncate(n);
                while r.len() < n {
                    let x = self.nil();
                    r.push(x);
                }
                r
            }
            None => out,
        }
    }

    pub(crate) fn unsupported_lib(&mut self, span: Span, lib: &str, n: &str) -> Vec<ETy> {
        self.error(span, format!("{lib}.{n} is not supported in this version"));
        vec![self.fresh_result()]
    }

    pub(crate) fn arity(&mut self, span: Span, name: &str, args: &[ETy], min: usize, max: usize) -> bool {
        if args.len() < min || args.len() > max {
            let exp = if min == max {
                format!("{min}")
            } else if max == usize::MAX {
                format!("at least {min}")
            } else {
                format!("{min} to {max}")
            };
            self.error(span, format!("{name} expects {exp} argument(s), got {}", args.len()));
            return false;
        }
        true
    }

    pub(crate) fn expect(&mut self, v: ETy, t: TyNode, span: Span, what: &str) {
        let tt = self.prim(t);
        self.unify(v.ty, tt, span);
        self.need(v, span, what);
    }

    pub(crate) fn builtin_sig(&mut self, b: BuiltinFn, a: &[ETy], sp: &[Span], span: Span) -> Vec<ETy> {
        use BuiltinFn::*;
        if matches!(b, TInsert | TRemove | TConcat | TSort) {
            if let Some(v) = a.first() { self.info.packs.restricted.push((v.ty, span, "this table operation on a nil-preserving array is not supported")); }
        }
        if matches!(b, TInsert | TRemove | TConcat | TSort) && a.first().is_some_and(|v| matches!(self.st.node(v.ty), TyNode::Table(t) if self.st.tab(*t).sparse)) {
            self.error(span, "this table operation on a nil-preserving array is not supported");
            return vec![self.fresh_result()];
        }
        if b == TSort && a.first().is_some_and(|t| matches!(self.st.node(t.ty), TyNode::Table(tab) if self.st.tab(*tab).runtime)) {
            return self.runtime_sort_sig(a, span);
        }
        let arg_span = |i: usize| sp.get(i).copied().unwrap_or(span);
        match b {
            TClear => self.clear_sig(a, span),
            Next => unreachable!("next has table-dependent result types"),
            Print => vec![],
            TFreeze | TIsFrozen | TMove => unreachable!("runtime libraries are checked by table_library_sig"),
            SelectCount | Select => unreachable!("select is checked by select_call"),
            TUnpack | TPack | SelectFixed | SelectFixedCount | PcallPack => unreachable!("pack builtins have dedicated checking"),
            ToString => {
                self.arity(span, "tostring", a, 1, 1);
                vec![self.str_()]
            }
            Type => {
                self.arity(span, "type", a, 1, 1);
                vec![self.str_()]
            }
            ToNumber if a.len() == 1 && self.num_class(a[0].ty) == crate::check_int::NumClass::Int => {
                // integer → number: exact, checked at run time
                self.need(a[0], arg_span(0), "bad argument to 'tonumber' (got nil)");
                vec![self.num()]
            }
            ToNumber => {
                if self.arity(span, "tonumber", a, 1, 2) {
                    self.expect(a[0], TyNode::Str, arg_span(0), "bad argument to 'tonumber' (string expected, got nil)");
                    if let Some(base) = a.get(1) {
                        self.expect(*base, TyNode::Num, arg_span(1), "bad argument #2 to 'tonumber' (number expected, got nil)");
                    }
                }
                let n = self.prim(TyNode::Num);
                vec![ETy { ty: n, null: self.st.null_true, soft: Soft::No }]
            }
            Error => {
                self.arity(span, "error", a, 1, 2);
                vec![]
            }
            CollectGarbage => {
                if self.arity(span, "collectgarbage", a, 0, 1) && !a.is_empty() {
                    self.expect(a[0], TyNode::Str, arg_span(0), "bad argument #1 to 'collectgarbage' (string expected)");
                }
                vec![self.num()]
            }
            StrSplit => {
                for (v, sp) in a.iter().zip(sp) { self.boxable(v.ty, *sp); }
                let (ty, tab) = self.new_table_var(span);
                self.ensure_kind(tab, TKind::Array, span);
                let el = self.elem_slot(tab);
                let string = self.prim(TyNode::Str);
                self.unify(el.ty, string, span);
                vec![self.val(ty)]
            }
            StrLen | StrUpper | StrLower | StrReverse => {
                if self.arity(span, "string function", a, 1, 1) {
                    self.expect(a[0], TyNode::Str, arg_span(0), "bad argument (string expected, got nil)");
                }
                vec![if b == StrLen { self.num() } else { self.str_() }]
            }
            StrSub => {
                if self.arity(span, "string.sub", a, 2, 3) {
                    self.expect(a[0], TyNode::Str, arg_span(0), "bad argument #1 to 'sub' (string expected)");
                    self.expect(a[1], TyNode::Num, arg_span(1), "bad argument #2 to 'sub' (number expected)");
                    if let Some(j) = a.get(2) {
                        let n = self.prim(TyNode::Num);
                        self.unify(j.ty, n, arg_span(2));
                    }
                }
                vec![self.str_()]
            }
            StrRep => {
                if self.arity(span, "string.rep", a, 2, 2) {
                    self.expect(a[0], TyNode::Str, arg_span(0), "bad argument #1 to 'rep'");
                    self.expect(a[1], TyNode::Num, arg_span(1), "bad argument #2 to 'rep'");
                }
                vec![self.str_()]
            }
            StrByte => {
                if self.arity(span, "string.byte", a, 1, 2) {
                    self.expect(a[0], TyNode::Str, arg_span(0), "bad argument #1 to 'byte'");
                    if let Some(i) = a.get(1) {
                        self.expect(*i, TyNode::Num, arg_span(1), "bad argument #2 to 'byte'");
                    }
                }
                let n = self.prim(TyNode::Num);
                vec![ETy { ty: n, null: self.st.null_true, soft: Soft::No }]
            }
            StrChar => {
                for (i, x) in a.iter().enumerate() {
                    self.expect(*x, TyNode::Num, arg_span(i), "bad argument to 'char' (number expected)");
                }
                vec![self.str_()]
            }
            MFloor | MCeil | MSqrt | MAbs => {
                if self.arity(span, "math function", a, 1, 1) {
                    self.expect(a[0], TyNode::Num, arg_span(0), "bad argument (number expected, got nil)");
                }
                vec![self.num()]
            }
            MFn(name, lo, hi) => {
                if self.arity(span, &format!("math.{name}"), a, lo, hi) {
                    for (i, x) in a.iter().enumerate() {
                        self.expect(*x, TyNode::Num, arg_span(i), &format!("bad argument #{} to '{name}' (number expected, got nil)", i + 1));
                    }
                }
                (0..math_fn_results(name)).map(|_| self.num()).collect()
            }
            MToInteger => {
                if self.arity(span, "math.tointeger", a, 1, 1) {
                    self.expect(a[0], TyNode::Num, arg_span(0), "bad argument #1 to 'tointeger' (number expected, got nil)");
                }
                let i = self.prim(TyNode::Int);
                vec![ETy { ty: i, null: self.st.null_true, soft: Soft::No }]
            }
            MMin | MMax => {
                if self.arity(span, if b == MMin { "math.min" } else { "math.max" }, a, 1, usize::MAX) {
                    for (i, x) in a.iter().enumerate() {
                        self.expect(*x, TyNode::Num, arg_span(i), "bad argument (number expected, got nil)");
                    }
                }
                vec![self.num()]
            }
            TInsert => {
                if !self.arity(span, "table.insert", a, 2, 3) {
                    return vec![];
                }
                let (ty, tab) = self.new_table_var(span);
                self.unify(a[0].ty, ty, arg_span(0));
                self.need(a[0], arg_span(0), "bad argument #1 to 'insert' (table expected, got nil)");
                self.ensure_kind(tab, TKind::Array, arg_span(0));
                let el = self.elem_slot(tab);
                if a.len() == 3 {
                    self.expect(a[1], TyNode::Num, arg_span(1), "bad argument #2 to 'insert' (number expected)");
                }
                let v = *a.last().unwrap();
                self.flow(v, el, arg_span(a.len() - 1));
                vec![]
            }
            TRemove => {
                if !self.arity(span, "table.remove", a, 1, 2) {
                    return vec![self.fresh_result()];
                }
                let (ty, tab) = self.new_table_var(span);
                self.unify(a[0].ty, ty, arg_span(0));
                self.need(a[0], arg_span(0), "bad argument #1 to 'remove' (table expected, got nil)");
                self.ensure_kind(tab, TKind::Array, arg_span(0));
                if let Some(p) = a.get(1) {
                    self.expect(*p, TyNode::Num, arg_span(1), "bad argument #2 to 'remove' (number expected)");
                }
                let el = self.elem_slot(tab);
                vec![ETy { ty: el.ty, null: self.st.null_true, soft: Soft::No }]
            }
            TConcat => {
                if !self.arity(span, "table.concat", a, 1, 4) {
                    return vec![self.str_()];
                }
                let (ty, tab) = self.new_table_var(span);
                self.unify(a[0].ty, ty, arg_span(0));
                self.need(a[0], arg_span(0), "bad argument #1 to 'concat' (table expected, got nil)");
                self.ensure_kind(tab, TKind::Array, arg_span(0));
                let el = self.elem_slot(tab);
                let ev = self.val(el.ty);
                self.try_or_defer(Op::NumOrStr { e: ev, default_str: true, span: arg_span(0), what: "concatenate" });
                if let Some(s) = a.get(1) {
                    self.expect(*s, TyNode::Str, arg_span(1), "bad argument #2 to 'concat' (string expected)");
                }
                for (i, x) in a.iter().enumerate().skip(2) {
                    self.expect(*x, TyNode::Num, arg_span(i), "bad argument to 'concat' (number expected)");
                }
                vec![self.str_()]
            }
            TCreate => {
                if !self.arity(span, "table.create", a, 1, 2) {
                    return vec![self.fresh_result()];
                }
                self.expect(a[0], TyNode::Num, arg_span(0), "bad argument #1 to 'create' (number expected)");
                let (ty, tab) = self.new_table_var(span);
                self.ensure_kind(tab, TKind::Array, span);
                let el = self.elem_slot(tab);
                if let Some(v) = a.get(1) {
                    self.flow(*v, el, arg_span(1));
                }
                self.st.tab_mut(tab).ctors.push(vec![]);
                vec![self.val(ty)]
            }
            TClone => {
                if !self.arity(span, "table.clone", a, 1, 1) {
                    return vec![self.fresh_result()];
                }
                if self.metatables.enabled {
                    self.metatables.clones.push((a[0].ty, arg_span(0)));
                }
                let (ty, _) = self.new_table_var(span);
                self.unify(a[0].ty, ty, arg_span(0));
                self.need(a[0], arg_span(0), "bad argument #1 to 'clone' (table expected, got nil)");
                vec![self.val(a[0].ty)]
            }
            StrFind | StrMatch => {
                let nm = if b == StrFind { "string.find" } else { "string.match" };
                let max = if b == StrFind { 4 } else { 3 };
                if self.arity(span, nm, a, 2, max) {
                    if !self.is_any(a[0].ty) { self.expect(a[0], TyNode::Str, arg_span(0), "bad argument #1 (string expected)"); }
                    if !self.is_any(a[1].ty) { self.expect(a[1], TyNode::Str, arg_span(1), "bad argument #2 (pattern string expected)"); }
                    if let Some(i) = a.get(2) {
                        let n = self.prim(TyNode::Num);
                        self.unify(i.ty, n, arg_span(2));
                    }
                    if let Some(p) = a.get(3) {
                        let t = self.prim(TyNode::Bool);
                        self.unify(p.ty, t, arg_span(3));
                    }
                }
                let caps = self.info.pattern_caps.get(&self.cur_call).cloned().unwrap_or_default();
                let n = self.prim(TyNode::Num);
                let s = self.prim(TyNode::Str);
                let mut out = Vec::new();
                if b == StrFind {
                    out.push(ETy { ty: n, null: self.st.null_true, soft: Soft::No });
                    out.push(ETy { ty: n, null: self.st.null_true, soft: Soft::No });
                }
                if b == StrMatch && caps.is_empty() {
                    out.push(ETy { ty: s, null: self.st.null_true, soft: Soft::No });
                }
                for pos in caps {
                    // position captures are numbers, like Luau
                    out.push(ETy { ty: if pos { n } else { s }, null: self.st.null_true, soft: Soft::No });
                }
                self.info.builtin_outs.insert(self.cur_call, out.clone());
                out
            }
            StrGsub => self.gsub_sig(a, sp, span),
            StrGmatch => unreachable!("string.gmatch is checked by gmatch_for"),
            TSort => {
                if !self.arity(span, "table.sort", a, 1, 2) {
                    return vec![];
                }
                let (ty, tab) = self.new_table_var(span);
                self.unify(a[0].ty, ty, arg_span(0));
                self.need(a[0], arg_span(0), "bad argument #1 to 'sort' (table expected, got nil)");
                self.ensure_kind(tab, TKind::Array, arg_span(0));
                let el = self.elem_slot(tab);
                match a.get(1) {
                    Some(f) => {
                        let b = self.prim(TyNode::Bool);
                        let ps = vec![self.st.fixed_slot(el.ty, span, "sort arguments are never nil"), self.st.fixed_slot(el.ty, span, "sort arguments are never nil")];
                        let r = self.st.fixed_slot(b, span, "a sort comparator returns a boolean");
                        let rets = self.st.new_rets(RetsNode::Known(vec![r]));
                        let ft = self.st.ty(TyNode::Func(Rc::new(FuncTy { params: ps, rets, vararg: None })));
                        self.unify(f.ty, ft, arg_span(1));
                        self.need(*f, arg_span(1), "bad argument #2 to 'sort' (function expected, got nil)");
                    }
                    None => {
                        let ev = self.val(el.ty);
                        self.try_or_defer(Op::NumOrStr { e: ev, default_str: false, span: arg_span(0), what: "compare" });
                    }
                }
                vec![]
            }
            StrFormat | Pcall | Xpcall | Assert | Bit32(_) => unreachable!(),
        }
    }

    /// `string.gsub(s, pattern, repl, n)` gives the new string and the number of matches.
    /// `repl` is a template string, a `{[string]: string}` table, or a function of the
    /// pattern's captures that returns a string (or nil, keeping the match).
    fn gsub_sig(&mut self, a: &[ETy], sp: &[Span], span: Span) -> Vec<ETy> {
        let arg_span = |i: usize| sp.get(i).copied().unwrap_or(span);
        let out = vec![self.str_(), self.num()];
        self.info.builtin_outs.insert(self.cur_call, out.clone());
        if !self.arity(span, "string.gsub", a, 3, 4) {
            return out;
        }
        self.expect(a[0], TyNode::Str, arg_span(0), "bad argument #1 to 'gsub' (string expected, got nil)");
        self.expect(a[1], TyNode::Str, arg_span(1), "bad argument #2 to 'gsub' (string expected, got nil)");
        if let Some(n) = a.get(3) {
            self.expect(*n, TyNode::Num, arg_span(3), "bad argument #4 to 'gsub' (number expected, got nil)");
        }
        let repl = a[2];
        self.need(repl, arg_span(2), "bad argument #3 to 'gsub' (string/function/table expected, got nil)");
        let caps = self.info.pattern_caps.get(&self.cur_call).cloned();
        let mode = match self.st.node(repl.ty).clone() {
            TyNode::Str => {
                if let (Some(t), Some(caps)) = (self.info.gsub_templates.get(&self.cur_call).cloned(), &caps) {
                    self.check_template(&t, caps.len(), arg_span(2));
                }
                GsubMode::Template
            }
            TyNode::Table(_) => {
                let (ty, tab) = self.new_table_var(span);
                self.ensure_kind(tab, TKind::Map, arg_span(2));
                let (ks, vs) = (self.key_slot(tab), self.val_slot(tab));
                for slot in [ks, vs] {
                    let s = self.prim(TyNode::Str);
                    self.unify(slot.ty, s, arg_span(2));
                }
                self.unify(repl.ty, ty, arg_span(2));
                GsubMode::Table
            }
            TyNode::Func(_) => {
                let Some(caps) = caps else {
                    self.error(arg_span(1), "string.gsub with a function replacement needs a pattern known at compile time (a literal, or a local initialized with one and never reassigned)");
                    return out;
                };
                // one argument per capture (the whole match when there are none)
                let kinds = if caps.is_empty() { vec![false] } else { caps };
                let params: Vec<Slot> = kinds
                    .iter()
                    .map(|&pos| {
                        let t = self.prim(if pos { TyNode::Num } else { TyNode::Str });
                        self.st.fixed_slot(t, span, "gsub callback arguments are never nil")
                    })
                    .collect();
                let s = self.prim(TyNode::Str);
                let ret = self.st.slot(s);
                let rets = self.st.new_rets(RetsNode::Known(vec![ret]));
                let ft = self.st.ty(TyNode::Func(Rc::new(FuncTy { params, rets, vararg: None })));
                self.unify(repl.ty, ft, arg_span(2));
                GsubMode::Func(ret)
            }
            TyNode::Var => {
                self.error(arg_span(2), "cannot infer the replacement of string.gsub here; use a string, a table or a function whose type is known");
                return out;
            }
            _ => {
                let t = self.show(repl.ty);
                self.error(arg_span(2), format!("bad argument #3 to 'gsub' (string/function/table expected, got {t})"));
                return out;
            }
        };
        self.info.gsub_modes.insert(self.cur_call, mode);
        out
    }

    /// Rejects, at compile time, a literal replacement template that Luau would reject
    /// when the first match is replaced (`%2` with one capture, `%x`, a lone `%`).
    fn check_template(&mut self, template: &[u8], caps: usize, span: Span) {
        let mut bytes = template.iter();
        while let Some(&b) = bytes.next() {
            if b != b'%' {
                continue;
            }
            match bytes.next() {
                Some(b'%') => {}
                Some(&d @ b'0'..=b'9') => {
                    if d != b'0' && (d - b'0') as usize > caps.max(1) {
                        self.error(span, format!("invalid capture index %{} in the replacement string (the pattern has {caps} capture(s))", d as char));
                        return;
                    }
                }
                _ => {
                    self.error(span, "invalid use of '%' in the replacement string");
                    return;
                }
            }
        }
    }

    /// `for a, b in string.gmatch(s, p)` / `s:gmatch(p)`: the loop variables are the
    /// pattern's captures (the whole match when it has none); position captures are
    /// numbers. The pattern must be known at compile time.
    pub(crate) fn gmatch_for(&mut self, s: &Stat, names: &[Name], operands: &[&Expr], body: &Block, span: Span) {
        let [subject, pat] = operands else {
            self.error(span, format!("string.gmatch expects 2 arguments, got {}", operands.len()));
            return;
        };
        let sv = self.expr(subject);
        self.expect(sv, TyNode::Str, subject.span, "bad argument #1 to 'gmatch' (string expected, got nil)");
        let pv = self.expr(pat);
        self.expect(pv, TyNode::Str, pat.span, "bad argument #2 to 'gmatch' (string expected, got nil)");
        let Some(caps) = self.known_str(pat).map(|p| pattern_captures(&p)) else {
            self.error(pat.span, "string.gmatch needs a pattern known at compile time (a literal, or a local initialized with one and never reassigned)");
            return;
        };
        let kinds = if caps.is_empty() { vec![false] } else { caps };
        if names.len() > kinds.len() {
            self.error(names[kinds.len()].span, format!("the pattern gives {} value(s) per match, the loop binds {}", kinds.len(), names.len()));
            return;
        }
        self.kill_assigned(body);
        self.push_frame();
        for (n, &pos) in names.iter().zip(&kinds) {
            let slot = self.declare(n, None);
            let t = self.prim(if pos { TyNode::Num } else { TyNode::Str });
            let v = self.val(t);
            self.flow(v, slot, n.span);
        }
        self.info.fors.insert(s.id, ForKind::Gmatch);
        self.info.gmatch_caps.insert(s.id, kinds);
        self.block(body);
        self.pop_frame();
    }

    pub(crate) fn string_format(&mut self, e: &Expr, args: &[Expr]) -> ETy {
        let Some(first) = args.first() else {
            self.error(e.span, "string.format expects a format string");
            return self.str_();
        };
        let ExprKind::Str(fmt) = &first.kind else {
            self.error(first.span, "string.format requires a literal format string in this version");
            for a in args {
                self.expr(a);
            }
            return self.str_();
        };
        self.expr(first);
        let fmt = String::from_utf8_lossy(fmt).to_string();
        let pieces = match crate::fmtspec::parse(&fmt) {
            Ok(p) => p,
            Err(msg) => {
                self.error(first.span, msg);
                for a in &args[1..] {
                    self.expr(a);
                }
                return self.str_();
            }
        };
        let directives: Vec<&Directive> = pieces
            .iter()
            .filter_map(|p| match p {
                FmtPiece::Arg(d) => Some(d),
                FmtPiece::Lit(_) => None,
            })
            .collect();
        let rest = &args[1..];
        // a trailing call gives as many values as it returns
        let (vals, spans) = self.args_values(rest);
        self.note_multi_tail(e.id, rest, &vals);
        if vals.len() != directives.len() {
            self.error(e.span, format!("format string expects {} argument(s), got {}", directives.len(), vals.len()));
        }
        for ((&v, &sp), d) in vals.iter().zip(spans.iter()).zip(directives.iter()) {
            match d.conv {
                // integer directives take numbers, integers and numeric strings
                Conv::Signed | Conv::Unsigned(_) | Conv::Char => {
                    self.need(v, sp, "bad argument to 'format' (number expected, got nil)");
                    self.try_or_defer(Op::NumOrStr { e: v, default_str: false, span: sp, what: "format with an integer directive" });
                }
                Conv::Float(_) => self.expect(v, TyNode::Num, sp, "bad argument to 'format' (number expected, got nil)"),
                Conv::Str | Conv::Quoted => {}
            }
        }
        self.info.formats.insert(e.id, pieces);
        self.str_()
    }

    pub(crate) fn pcall(&mut self, e: &Expr, args: &[Expr]) -> Vec<ETy> {
        let want = self.pcall_want.take();
        if args.is_empty() {
            self.error(e.span, "pcall expects a function (and its arguments)");
            let b = self.bool_();
            return vec![b, self.fresh_result()];
        }
        let f = self.expr(&args[0]);
        self.need(f, args[0].span, "attempt to call a nil value");
        let (vals, spans, arg_pack) = if let Some(last) = args.last().filter(|a| args.len() > 1 && self.is_pack(a)) {
            let (vals, spans) = self.args_single(&args[1..args.len() - 1]);
            (vals, spans, Some(self.pack_value(last)))
        } else {
            self.allow_pack = true;
            let (vals, spans) = self.args_values(&args[1..]);
            let tail = args.last().filter(|_| args.len() > 1).and_then(|e| self.info.pack_calls.get(&e.id).copied());
            (vals, spans, tail)
        };
        // a function value whose type is not known yet (a builtin value) takes the
        // shape of this call
        if matches!(self.st.node(f.ty), TyNode::Var) {
            let params: Vec<Slot> = vals
                .iter()
                .map(|v| {
                    let t = self.st.var();
                    let s = self.st.slot(t);
                    self.unify(v.ty, t, e.span);
                    s
                })
                .collect();
            let rets = self.st.new_rets(RetsNode::Unknown);
            let ft = self.st.ty(TyNode::Func(Rc::new(FuncTy { params, rets, vararg: None })));
            self.unify(f.ty, ft, args[0].span);
            self.solve_pending_quick();
        }
        let rets = match self.st.node(f.ty).clone() {
            TyNode::Func(ft) => {
                if vals.len() > ft.params.len() && ft.vararg.is_none() {
                    self.error(e.span, format!("pcall passes {} argument(s) to a function taking {}", vals.len(), ft.params.len()));
                }
                for (i, p) in ft.params.iter().enumerate() {
                    match vals.get(i) {
                        Some(v) => {
                            self.flow_node(args.get(i + 1).map(|a| a.id), *v, *p, spans[i]);
                        }
                        None if arg_pack.is_some() => {
                            let v = ETy { null: self.st.null_true, ..arg_pack.unwrap_or(f) };
                            self.flow(v, *p, e.span);
                        }
                        None => self.st.force(p.null, e.span),
                    }
                }
                if let Some(vararg) = ft.vararg {
                    for (i, v) in vals.iter().enumerate().skip(ft.params.len()) {
                        self.flow_node(args.get(i + 1).map(|a| a.id), *v, vararg, spans[i]);
                    }
                    if let Some(v) = arg_pack { self.flow(v, vararg, e.span); }
                }
                match self.st.rets_known(ft.rets).cloned() {
                    Some(r) => r,
                    // the results come later (the function is a parameter whose type is
                    // decided by the call site): bind them when they are known
                    None if want.is_some() => return self.pcall_deferred(e, ft.rets, want.unwrap_or(2)),
                    None => {
                        self.error(args[0].span, "cannot determine the results of this function; annotate its return type");
                        vec![]
                    }
                }
            }
            _ => {
                let s = self.show(f.ty);
                self.error(args[0].span, format!("pcall expects a function, got {s}"));
                vec![]
            }
        };
        self.info.pcall_rets.insert(e.id, rets.len());
        // Luau returns only the success flag when f returns nothing, and only
        // false/message on failure even when f normally returns many values.
        // Exactly one result has the same two-slot count on both paths.
        if (want.is_none() && (self.exact_pcall || rets.len() != 1)) || self.callee_tail(f.ty).is_some() {
            let el = self.any_val();
            self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::PcallPack));
            for s in &rets { self.pack_boxable(s.ty, e.span); }
            if let Some(s) = self.callee_tail(f.ty) { self.pack_boxable(s.ty, e.span); }
            return match want {
                None => { self.info.pack_calls.insert(e.id, el); vec![] }
                Some(n) => {
                    let out = vec![el; n];
                    self.info.builtin_outs.insert(e.id, out.clone());
                    out
                }
            };
        }
        let inner = match rets.first() {
            Some(s) => *s,
            None => {
                let t = self.st.ty(TyNode::Nil);
                self.st.optional_slot(t, e.span)
            }
        };
        let pt = self.st.ty(TyNode::Pcall(inner));
        let b = self.bool_();
        let mut out = vec![b, self.val(pt)];
        let nonnull: Vec<bool> = rets.iter().skip(1).map(|s| !self.st.is_null(s.null)).collect();
        self.info.pcall_nonnull.insert(e.id, nonnull);
        self.pcall_checks.push((e.span, rets.iter().skip(1).map(|s| (*s, !self.st.is_null(s.null))).collect()));
        // further results: their value on success, nil on failure
        for s in rets.iter().skip(1) {
            out.push(ETy { ty: s.ty, null: self.st.null_true, soft: Soft::No });
        }
        out
    }

    /// `pcall(f)` whose function results are not known yet: the success flag, the
    /// first result (or the error message) and as many further results as the call
    /// site takes are typed now; the function's results are bound later.
    fn pcall_deferred(&mut self, e: &Expr, rets: RetsId, want: usize) -> Vec<ETy> {
        let t = self.st.var();
        let inner = self.st.slot(t);
        let pt = self.st.ty(TyNode::Pcall(inner));
        let b = self.bool_();
        let mut out = vec![b, self.val(pt)];
        let mut extras = Vec::new();
        for _ in 2..want {
            let v = self.st.var();
            let x = ETy { ty: v, null: self.st.null_true, soft: Soft::No };
            extras.push(x);
            out.push(x);
        }
        self.pending.push(Op::PcallRets { node: e.id, rets, inner, extras, span: e.span });
        out
    }

    pub(crate) fn attempt_pcall_rets(&mut self, node: NodeId, rets: RetsId, inner: Slot, extras: &[ETy], span: Span) -> bool {
        let Some(known) = self.st.rets_known(rets).cloned() else { return false };
        let first = match known.first() {
            Some(s) => *s,
            None => {
                let t = self.st.ty(TyNode::Nil);
                self.st.optional_slot(t, span)
            }
        };
        self.unify_slot(inner, first, span);
        for (i, x) in extras.iter().enumerate() {
            if let Some(s) = known.get(i + 1) {
                self.unify(x.ty, s.ty, span);
            }
        }
        self.info.pcall_rets.insert(node, known.len());
        let nonnull: Vec<bool> = known.iter().skip(1).map(|s| !self.st.is_null(s.null)).collect();
        self.info.pcall_nonnull.insert(node, nonnull);
        self.pcall_checks.push((span, known.iter().skip(1).map(|s| (*s, !self.st.is_null(s.null))).collect()));
        true
    }

    /// Resolves pending operations that are immediately decidable (used when a call
    /// needs the shape of a value right away).
    pub(crate) fn solve_pending_quick(&mut self) {
        let ops = std::mem::take(&mut self.pending);
        for op in ops {
            if !self.attempt(&op) {
                self.pending.push(op);
            }
        }
    }

    pub(crate) fn pending_count(&self) -> usize {
        self.pending.len()
    }

    // Finishing

    pub(crate) fn finish(&mut self) {
        if self.metatables.general_source && !self.metatables.general && self.metatables.clones.iter().any(|(ty, _)| {
            matches!(self.st.node(*ty), TyNode::Table(t) if self.st.tab(*t).parent.is_some())
        }) {
            self.activate_general_record_metatables();
            self.solve_pending();
        }
        self.validate_record_parents();
        // A left operand decided as "falsey only when nil" must not have become a
        // boolean (or `false | T`) later: that would make `false` truthy.
        for (callee, method, assumed, span) in std::mem::take(&mut self.arity_guesses) {
            let actual = match &method {
                Some(m) => Some(self.method_result_count(callee, m)),
                None => match self.st.node(callee.ty).clone() {
                    TyNode::Func(f) => self.st.rets_known(f.rets).map(|r| r.len()),
                    _ => None,
                },
            };
            if let Some(n) = actual.filter(|n| *n != assumed) {
                self.error(
                    span,
                    format!(
                        "the number of values this call returns was needed before its function type was known (assumed {assumed}, it returns {n}); annotate the function's type"
                    ),
                );
            }
        }
        for (node, aty, and, rty, span) in std::mem::take(&mut self.logic_checks) {
            match self.st.node(aty) {
                TyNode::Bool if !and || matches!(self.st.node(rty), TyNode::Bool) => {
                    // same constraints as the boolean form (both operands and the result boolean)
                    self.info.logic.insert(node, LogicKind::BoolLeft);
                }
                TyNode::Bool | TyNode::FalseOr(_) => {
                    let op = if and { "and" } else { "or" };
                    self.error(span, format!("cannot infer the type of the left operand of {op} early enough; add a type annotation"));
                }
                _ => {}
            }
        }
        for (span, slots) in std::mem::take(&mut self.pcall_checks) {
            if slots.iter().any(|(s, was_nonnull)| *was_nonnull && self.st.is_null(s.null)) {
                // a result first seen as never-nil became optional later: narrowing on
                // `ok` would be unsound, so require an explicit check
                self.error(span, "a result of this pcall may be nil even on success; check it explicitly (`if ok and v then`)");
            }
        }
        // integral literals nothing required to be integers are numbers
        for i in 0..self.st.tys.len() {
            if matches!(self.st.tys[i], TyNode::NumVar) {
                self.st.tys[i] = TyNode::Num;
            }
        }
        // Luau numeric values box as numbers; inspect inferred integers only after literal defaulting.
        for (ty, span) in std::mem::take(&mut self.dynamic.box_checks) {
            if !matches!(self.st.node(ty), TyNode::Var) { self.boxable(ty, span); }
        }
        // Table kinds nobody constrained: records if they have fields, arrays otherwise.
        for i in 0..self.st.tabs.len() {
            if self.st.tabs[i].link.is_none() && self.st.tabs[i].kind == TKind::Unknown {
                self.st.tabs[i].kind = if self.st.tabs[i].fields.is_empty() { TKind::Array } else { TKind::Record };
            }
        }
        // Generic native arguments must be determined.
        let insts = self.info.natives.clone();
        let mut reported = HashSet::new();
        for ni in &insts {
            let mut names: Vec<(&String, &TyId)> = ni.env.gens.iter().collect();
            names.sort();
            for (g, t) in names {
                // synthetic `impl Trait` parameters are inferred by rustc from the argument
                if g.starts_with("impl ") {
                    continue;
                }
                if matches!(self.st.node(*t), TyNode::Var) && reported.insert((ni.span, g.clone())) {
                    let msg = format!(
                        "ambiguous native generic argument '{}' in call to '{}': the arguments and expected result do not determine it; annotate the receiving local (e.g. `local x: number = ...`)",
                        g, ni.display
                    );
                    self.error(ni.span, msg);
                }
            }
        }
        let errs = self.st.solve_nulls();
        for (sp, m) in errs {
            self.error(sp, m);
        }
        self.validate_sparse_uses();
        self.finish_any_array_loops();
        self.validate_next_key_identity();
        self.validate_table_layout_options();
        for (v, span, what) in std::mem::take(&mut self.requirements) {
            if self.st.is_null(v.null) {
                self.error(span, format!("{what} (value may be nil; check it with `if x ~= nil` first)"));
            }
        }
        // Map key types must be hashable source values.
        for i in 0..self.st.tabs.len() {
            if self.st.tabs[i].link.is_none() && self.st.tabs[i].kind == TKind::Map {
                if let Some(k) = self.st.tabs[i].key {
                    match self.st.node(k.ty) {
                        TyNode::Num | TyNode::Int | TyNode::Str | TyNode::Bool | TyNode::Any | TyNode::Var | TyNode::Nil => {}
                        _ => {
                            let s = self.show(k.ty);
                            let sp = self.st.tabs[i].span;
                            self.error(sp, format!("map keys of type {s} are unsupported (use number, string or boolean keys)"));
                        }
                    }
                }
            }
        }
        self.validate_xpcall_boxes();
        self.validate_runtime_provenance();
        if self.errors.is_empty() { self.validate_type_expansion(); }
        self.errors.sort_by_key(|d| (d.span.file, d.span.line, d.span.col));
        self.errors.dedup_by(|a, b| a.span == b.span && a.msg == b.msg);
    }

    // Queries used by lowering

    /// Final softness of an expression value.
    pub fn soft(&self, s: Soft) -> bool {
        match s {
            Soft::No => false,
            Soft::Yes => true,
            Soft::Field(fid) => {
                let (tab, name) = &self.info.field_refs[fid as usize];
                !self.field_always_init(*tab, name)
            }
            Soft::Deferred(d) => self.info.soft_deferred[d as usize].map(|s| self.soft(s)).unwrap_or(false),
        }
    }

    pub fn field_always_init(&self, tab: TabId, name: &str) -> bool {
        self.st.tab(tab).ctors.iter().all(|c| c.iter().any(|f| f == name))
    }
}

fn kname(k: TKind) -> &'static str {
    match k {
        TKind::Unknown => "a table",
        TKind::Array => "an array",
        TKind::Map => "a map",
        TKind::Record => "a record",
    }
}

fn type_hint(t: &TabNode) -> String {
    match &t.hint {
        Some(h) => h.clone(),
        None => format!("{{{}}}", t.fields.keys().cloned().collect::<Vec<_>>().join(", ")),
    }
}

/// True when control never reaches the end of the block (return, error(), break,
/// continue, infinite loop, or an if/else whose branches all exit).
pub fn block_exits(b: &Block, res: &Resolution) -> bool {
    match b.stats.last() {
        None => false,
        Some(s) => stat_exits(s, res),
    }
}

fn stat_exits(s: &Stat, res: &Resolution) -> bool {
    match &s.kind {
        StatKind::Return(_) | StatKind::Break | StatKind::Continue => true,
        StatKind::Call(e) => is_error_call(e, res),
        StatKind::Do(b) => block_exits(b, res),
        StatKind::If(arms, Some(els)) => arms.iter().all(|(_, b)| block_exits(b, res)) && block_exits(els, res),
        StatKind::While(c, b) => matches!(c.kind, ExprKind::Bool(true)) && !has_break(b),
        StatKind::Repeat(b, c) => matches!(c.kind, ExprKind::Bool(false)) && !has_break(b),
        _ => false,
    }
}

pub fn is_error_call(e: &Expr, res: &Resolution) -> bool {
    if let ExprKind::Call(f, _) = &e.kind {
        return is_lib(f, res) == Some(Builtin::Error);
    }
    false
}

/// A `break` that targets this loop (not nested loops or functions).
pub fn has_break(b: &Block) -> bool {
    b.stats.iter().any(|s| match &s.kind {
        StatKind::Break => true,
        StatKind::Do(x) => has_break(x),
        StatKind::If(arms, els) => arms.iter().any(|(_, x)| has_break(x)) || els.as_ref().map(has_break).unwrap_or(false),
        _ => false,
    })
}

/// Native integer widths whose values are `integer` (exact) rather than `number`.
pub fn is_int_prim(p: &str) -> bool {
    matches!(p, "i64" | "u64" | "i128" | "u128")
}

/// Whether a pinned native primitive (`u32`, `char`, `bool`) has value type `n`.
pub(crate) fn nprim_matches(p: &str, n: &TyNode) -> bool {
    match n {
        TyNode::Bool => p == "bool",
        TyNode::Str => p == "char" || p == "str",
        TyNode::Int => is_int_prim(p),
        TyNode::NumVar => !matches!(p, "bool" | "char" | "str"),
        TyNode::Num => !matches!(p, "bool" | "char" | "str") && !is_int_prim(p),
        _ => false,
    }
}

/// Number of captures in a Lua pattern (`(` not escaped by `%`, outside sets).
/// Captures of a literal Lua pattern in order: `true` for a position capture `()`
/// (a number), `false` for a substring capture.
pub fn pattern_captures(p: &[u8]) -> Vec<bool> {
    let mut n = Vec::new();
    let mut i = 0;
    while i < p.len() {
        match p[i] {
            // `%bxy` takes two operand bytes (`%b()` is not a capture)
            b'%' if p.get(i + 1) == Some(&b'b') => i += 3,
            b'%' => i += 1,
            b'[' => {
                i += 1;
                if i < p.len() && p[i] == b'^' {
                    i += 1;
                }
                if i < p.len() {
                    i += 1; // a leading ']' is literal
                }
                while i < p.len() && p[i] != b']' {
                    if p[i] == b'%' {
                        i += 1;
                    }
                    i += 1;
                }
            }
            b'(' => n.push(p.get(i + 1) == Some(&b')')),
            _ => {}
        }
        i += 1;
    }
    n
}

fn literal_record_key(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Str(s) => String::from_utf8(s.clone()).ok(),
        ExprKind::Paren(inner) => literal_record_key(inner),
        _ => None,
    }
}
