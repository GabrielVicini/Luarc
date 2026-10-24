//! Name resolution: lexical scopes, symbol identities, captures and mutation facts.
//!
//! Facts computed here drive lowering:
//! * a local that is both captured by a closure and assigned after its declaration
//!   lives in a shared mutable cell;
//! * a `local function` that is never reassigned and captures nothing (except other
//!   such functions) becomes a plain Rust `fn` ("static function");
//! * narrowing is disabled for locals assigned from inside a nested closure.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ast::*;
use crate::diag::{Diagnostic, Span};

pub type SymId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymKind {
    Local,
    Param,
    ForVar,
    LocalFunc,
}

#[derive(Clone, Debug)]
pub struct Symbol {
    pub name: String,
    pub span: Span,
    pub kind: SymKind,
    /// Function (body id) that declares the symbol; module top level uses the
    /// module's pseudo function id.
    pub func: NodeId,
    pub assigned: bool,
    pub assigned_in_closure: bool,
    pub captured: bool,
    pub read: bool,
    pub is_static: bool,
    /// For `local function f`: the function body id.
    pub func_body: Option<NodeId>,
}

impl Symbol {
    /// Lives in a shared `Cell` (captured and mutated).
    pub fn is_cell(&self) -> bool {
        self.captured && self.assigned && !self.is_static
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    Print,
    ToString,
    ToNumber,
    Type,
    Assert,
    Error,
    Pcall,
    Xpcall,
    Ipairs,
    Pairs,
    Next,
    Require,
    Table,
    StringLib,
    Bit32,
    Math,
    Arg,
    CollectGarbage,
    TaskLib,
    CoroutineLib,
    Await,
    Select,
    SetMetatable,
    RawGet,
    RawSet,
    RawEqual,
    RawLen,
    GetMetatable,
}

pub fn builtin_by_name(n: &str) -> Option<Builtin> {
    Some(match n {
        "print" => Builtin::Print,
        "tostring" => Builtin::ToString,
        "tonumber" => Builtin::ToNumber,
        // `typeof` is `type` for every value this language has
        "type" | "typeof" => Builtin::Type,
        "assert" => Builtin::Assert,
        "error" => Builtin::Error,
        "pcall" => Builtin::Pcall,
        "xpcall" => Builtin::Xpcall,
        "ipairs" => Builtin::Ipairs,
        "pairs" => Builtin::Pairs,
        "next" => Builtin::Next,
        "require" => Builtin::Require,
        "table" => Builtin::Table,
        "string" => Builtin::StringLib,
        "math" => Builtin::Math,
        "bit32" => Builtin::Bit32,
        "arg" => Builtin::Arg,
        "collectgarbage" => Builtin::CollectGarbage,
        "task" => Builtin::TaskLib,
        "coroutine" => Builtin::CoroutineLib,
        "await" => Builtin::Await,
        "select" => Builtin::Select,
        "setmetatable" => Builtin::SetMetatable,
        "rawget" => Builtin::RawGet,
        "rawset" => Builtin::RawSet,
        "rawequal" => Builtin::RawEqual,
        "rawlen" => Builtin::RawLen,
        "getmetatable" => Builtin::GetMetatable,
        _ => return None,
    })
}

const UNSUPPORTED_GLOBALS: &[&str] = &[
    "next", "unpack",
    "loadstring", "load", "dofile", "getfenv", "setfenv", "os", "io", "debug",
    "utf8", "buffer", "_G", "newproxy", "gcinfo",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Res {
    Local(SymId),
    Builtin(Builtin),
}

#[derive(Clone, Debug, Default)]
pub struct FuncInfo {
    pub parent: Option<NodeId>,
    /// Free variables (symbols declared in enclosing functions), in first-use order.
    pub captures: Vec<SymId>,
    /// Set when this body belongs to `local function <sym>`.
    pub local_func_sym: Option<SymId>,
    /// The body refers to its own `local function` name (directly or from nested closures).
    pub self_referenced: bool,
    /// Declared with `...` (variadic).
    pub vararg: bool,
}

#[derive(Default)]
pub struct Resolution {
    pub names: HashMap<NodeId, Res>,
    pub decls: HashMap<NodeId, SymId>,
    pub syms: Vec<Symbol>,
    pub funcs: HashMap<NodeId, FuncInfo>,
    /// Locals of a `repeat` body (with `continue`) that its `until` condition reads:
    /// codegen evaluates the condition at each `continue`, so they get unique names.
    pub until_locals: HashSet<SymId>,
}

impl Resolution {
    pub fn sym(&self, id: SymId) -> &Symbol {
        &self.syms[id as usize]
    }
    pub fn res(&self, name_id: NodeId) -> Option<Res> {
        self.names.get(&name_id).copied()
    }
    pub fn decl(&self, name_id: NodeId) -> SymId {
        self.decls[&name_id]
    }
}

pub struct Resolver<'r> {
    pub r: &'r mut Resolution,
    scopes: Vec<HashMap<String, SymId>>,
    func_stack: Vec<NodeId>,
    loop_depth: Vec<u32>,
    pub errors: Vec<Diagnostic>,
}

impl<'r> Resolver<'r> {
    pub fn new(r: &'r mut Resolution) -> Self {
        Resolver { r, scopes: Vec::new(), func_stack: Vec::new(), loop_depth: Vec::new(), errors: Vec::new() }
    }

    /// Resolves one module. `module_func` is a pseudo function id for its top level.
    /// `repeat … until c` with `continue`: a `continue` jumps to the condition, so
    /// a body local the condition reads must be declared before every `continue`
    /// (Luau 0.743 rejects it otherwise). Records the locals the
    /// condition reads for codegen.
    fn until_after_continue(&mut self, b: &Block, c: &Expr) {
        let mut conts = Vec::new();
        continue_spans(b, &mut conts);
        if conts.is_empty() {
            return;
        }
        let body: HashMap<String, SymId> = self.scopes.last().cloned().unwrap_or_default();
        let mut names = Vec::new();
        expr_names(c, &mut names);
        let mut reported = HashSet::new();
        for n in names {
            let Some(Res::Local(s)) = self.r.res(n) else { continue };
            if !body.values().any(|&v| v == s) {
                continue;
            }
            self.r.until_locals.insert(s);
            let decl = self.r.sym(s).span;
            if let Some(k) = conts.iter().find(|k| (k.line, k.col) < (decl.line, decl.col)) {
                if reported.insert(s) {
                    let name = self.r.sym(s).name.clone();
                    self.errors.push(Diagnostic::new(
                        c.span,
                        format!("local '{name}' used in the repeat..until condition is undefined because the continue statement on line {} jumps over it", k.line),
                    ));
                }
            }
        }
    }

    pub fn module(&mut self, m: &Module, module_func: NodeId) {
        self.r.funcs.insert(module_func, FuncInfo::default());
        self.func_stack.push(module_func);
        self.loop_depth.push(0);
        self.scopes.push(HashMap::new());
        self.block_stats(&m.body);
        self.scopes.pop();
        self.loop_depth.pop();
        self.func_stack.pop();
    }

    /// Final whole-program pass: static functions (fixpoint).
    pub fn finish(&mut self) {
        loop {
            let mut changed = false;
            for i in 0..self.r.syms.len() {
                let s = &self.r.syms[i];
                if s.is_static || s.kind != SymKind::LocalFunc || s.assigned {
                    continue;
                }
                let body = s.func_body.unwrap();
                let ok = self.r.funcs[&body].captures.iter().all(|&c| c == i as SymId || self.r.syms[c as usize].is_static);
                if ok {
                    self.r.syms[i].is_static = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // Captures of static functions are calls to Rust `fn` items, not captured values.
        let statics: BTreeSet<SymId> =
            self.r.syms.iter().enumerate().filter(|(_, s)| s.is_static).map(|(i, _)| i as SymId).collect();
        for f in self.r.funcs.values_mut() {
            f.captures.retain(|c| !statics.contains(c));
        }
        // A self-recursive non-static local function refers to itself through a weak
        // self reference, not a captured value.
        let selfs: Vec<(NodeId, SymId)> =
            self.r.funcs.iter().filter_map(|(id, f)| f.local_func_sym.map(|s| (*id, s))).collect();
        for (id, s) in selfs {
            if self.r.syms[s as usize].assigned {
                continue; // reassigned: references must see the variable's current value
            }
            let f = self.r.funcs.get_mut(&id).unwrap();
            if f.captures.contains(&s) {
                f.captures.retain(|c| *c != s);
                f.self_referenced = true;
            }
        }
    }

    fn cur_func(&self) -> NodeId {
        *self.func_stack.last().unwrap()
    }

    fn declare(&mut self, n: &Name, kind: SymKind) -> SymId {
        let id = self.r.syms.len() as SymId;
        self.r.syms.push(Symbol {
            name: n.text.clone(),
            span: n.span,
            kind,
            func: self.cur_func(),
            assigned: false,
            assigned_in_closure: false,
            captured: false,
            read: false,
            is_static: false,
            func_body: None,
        });
        self.r.decls.insert(n.id, id);
        self.scopes.last_mut().unwrap().insert(n.text.clone(), id);
        id
    }

    fn lookup(&self, name: &str) -> Option<SymId> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    /// Records a use of `sym` from the current function, adding it to the capture
    /// lists of every function between the use and the declaration.
    fn note_use(&mut self, sym: SymId) {
        let decl_func = self.r.syms[sym as usize].func;
        for &f in self.func_stack.iter().rev() {
            if f == decl_func {
                break;
            }
            self.r.syms[sym as usize].captured = true;
            let info = self.r.funcs.get_mut(&f).unwrap();
            if !info.captures.contains(&sym) {
                info.captures.push(sym);
            }
        }
    }

    fn name_ref(&mut self, n: &Name, write: bool) {
        match self.lookup(&n.text) {
            Some(sym) => {
                self.r.names.insert(n.id, Res::Local(sym));
                self.note_use(sym);
                let in_closure = self.r.syms[sym as usize].func != self.cur_func();
                let s = &mut self.r.syms[sym as usize];
                if write {
                    s.assigned = true;
                    if in_closure {
                        s.assigned_in_closure = true;
                    }
                } else {
                    s.read = true;
                }
            }
            None => match builtin_by_name(&n.text) {
                Some(b) if !write => {
                    self.r.names.insert(n.id, Res::Builtin(b));
                }
                Some(_) => self.errors.push(Diagnostic::new(
                    n.span,
                    format!("cannot assign to builtin '{}'; declare a local with that name to shadow it", n.text),
                )),
                None => {
                    let msg = if UNSUPPORTED_GLOBALS.contains(&n.text.as_str()) {
                        format!("'{}' is not supported in this version of luarc", n.text)
                    } else if write {
                        format!("assignment to undeclared variable '{}' (globals are not supported; use 'local')", n.text)
                    } else {
                        format!("unknown variable '{}'", n.text)
                    };
                    self.errors.push(Diagnostic::new(n.span, msg));
                }
            },
        }
    }

    fn block(&mut self, b: &Block) {
        self.scopes.push(HashMap::new());
        self.block_stats(b);
        self.scopes.pop();
    }

    fn block_stats(&mut self, b: &Block) {
        for s in &b.stats {
            self.stat(s);
        }
    }

    fn func(&mut self, f: &FuncBody, local_sym: Option<SymId>) {
        self.r.funcs.insert(
            f.id,
            FuncInfo { parent: Some(self.cur_func()), local_func_sym: local_sym, vararg: f.vararg.is_some(), ..Default::default() },
        );
        self.func_stack.push(f.id);
        self.loop_depth.push(0);
        self.scopes.push(HashMap::new());
        for p in &f.params {
            self.declare(&p.name, SymKind::Param);
        }
        self.block_stats(&f.body);
        self.scopes.pop();
        self.loop_depth.pop();
        self.func_stack.pop();
    }

    fn loop_body(&mut self, b: &Block) {
        *self.loop_depth.last_mut().unwrap() += 1;
        self.block(b);
        *self.loop_depth.last_mut().unwrap() -= 1;
    }

    fn stat(&mut self, s: &Stat) {
        match &s.kind {
            StatKind::Local(names, exprs) => {
                for e in exprs {
                    self.expr(e);
                }
                for (n, _) in names {
                    self.declare(n, SymKind::Local);
                }
            }
            StatKind::LocalFunction(n, f) => {
                let sym = self.declare(n, SymKind::LocalFunc);
                self.r.syms[sym as usize].func_body = Some(f.id);
                self.func(f, Some(sym));
            }
            StatKind::Function(target, f) => {
                match &target.kind {
                    ExprKind::Name(n) => self.name_ref(n, true),
                    _ => self.expr(target),
                }
                self.func(f, None);
            }
            StatKind::Assign(targets, exprs) => {
                for t in targets {
                    self.target(t);
                }
                for e in exprs {
                    self.expr(e);
                }
            }
            StatKind::Compound(_, t, e) => {
                if let ExprKind::Name(n) = &t.kind {
                    self.name_ref(n, false);
                }
                self.target(t);
                self.expr(e);
            }
            StatKind::Call(e) => self.expr(e),
            StatKind::Do(b) => self.block(b),
            StatKind::While(c, b) => {
                self.expr(c);
                self.loop_body(b);
            }
            StatKind::Repeat(b, c) => {
                // The condition sees the body's locals.
                *self.loop_depth.last_mut().unwrap() += 1;
                self.scopes.push(HashMap::new());
                self.block_stats(b);
                self.expr(c);
                self.until_after_continue(b, c);
                self.scopes.pop();
                *self.loop_depth.last_mut().unwrap() -= 1;
            }
            StatKind::If(arms, els) => {
                for (c, b) in arms {
                    self.expr(c);
                    self.block(b);
                }
                if let Some(b) = els {
                    self.block(b);
                }
            }
            StatKind::NumFor(v, a, b, c, body) => {
                self.expr(a);
                self.expr(b);
                if let Some(c) = c {
                    self.expr(c);
                }
                self.scopes.push(HashMap::new());
                self.declare(v, SymKind::ForVar);
                self.loop_body(body);
                self.scopes.pop();
            }
            StatKind::GenFor(names, exprs, body) => {
                for e in exprs {
                    self.expr(e);
                }
                self.scopes.push(HashMap::new());
                for n in names {
                    self.declare(n, SymKind::ForVar);
                }
                self.loop_body(body);
                self.scopes.pop();
            }
            StatKind::Return(es) => {
                for e in es {
                    self.expr(e);
                }
            }
            StatKind::Break | StatKind::Continue => {
                if *self.loop_depth.last().unwrap() == 0 {
                    let w = if matches!(s.kind, StatKind::Break) { "break" } else { "continue" };
                    self.errors.push(Diagnostic::new(s.span, format!("'{w}' outside a loop")));
                }
            }
            StatKind::TypeAlias(..) => {}
        }
    }

    fn target(&mut self, t: &Expr) {
        match &t.kind {
            ExprKind::Name(n) => self.name_ref(n, true),
            ExprKind::Field(o, _) => self.expr(o),
            ExprKind::Index(o, k) => {
                self.expr(o);
                self.expr(k);
            }
            _ => self.expr(t),
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Nil | ExprKind::Bool(_) | ExprKind::Number(_) | ExprKind::Int(_) | ExprKind::Str(_) => {}
            ExprKind::Vararg => {
                // the main chunk is not variadic here (program arguments are `arg`), and
                // a nested function cannot see its parent's `...` (as in Luau)
                let vararg = self.r.funcs.get(&self.cur_func()).map(|f| f.vararg).unwrap_or(false);
                if !vararg {
                    self.errors.push(Diagnostic::new(e.span, "cannot use '...' outside of a vararg function"));
                }
            }
            ExprKind::Interp(parts) => {
                for p in parts {
                    if let InterpPart::Expr(x) = p {
                        self.expr(x);
                    }
                }
            }
            ExprKind::Name(n) => self.name_ref(n, false),
            ExprKind::Index(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Field(a, _) => self.expr(a),
            ExprKind::Call(f, args) => {
                self.expr(f);
                for a in args {
                    self.expr(a);
                }
            }
            ExprKind::Method(o, _, args) => {
                self.expr(o);
                for a in args {
                    self.expr(a);
                }
            }
            ExprKind::Function(f) => self.func(f, None),
            ExprKind::Table(items) => {
                for it in items {
                    match it {
                        TableItem::Pos(x) | TableItem::Named(_, x) => self.expr(x),
                        TableItem::Keyed(k, v) => {
                            self.expr(k);
                            self.expr(v);
                        }
                    }
                }
            }
            ExprKind::Binary(_, a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Unary(_, a) | ExprKind::Paren(a) | ExprKind::Cast(a, _) => self.expr(a),
            ExprKind::IfElse(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
        }
    }
}

/// Symbols assigned anywhere inside a block (used to drop narrowing at loop entry).
pub fn assigned_in_block(r: &Resolution, b: &Block, out: &mut BTreeSet<SymId>) {
    fn target(r: &Resolution, t: &Expr, out: &mut BTreeSet<SymId>) {
        if let ExprKind::Name(n) = &t.kind {
            if let Some(Res::Local(s)) = r.res(n.id) {
                out.insert(s);
            }
        }
    }
    for s in &b.stats {
        match &s.kind {
            StatKind::Assign(ts, _) => ts.iter().for_each(|t| target(r, t, out)),
            StatKind::Compound(_, t, _) => target(r, t, out),
            StatKind::Function(t, _) => target(r, t, out),
            StatKind::Do(b) | StatKind::While(_, b) | StatKind::Repeat(b, _) => assigned_in_block(r, b, out),
            StatKind::NumFor(_, _, _, _, b) | StatKind::GenFor(_, _, b) => assigned_in_block(r, b, out),
            StatKind::If(arms, els) => {
                for (_, b) in arms {
                    assigned_in_block(r, b, out);
                }
                if let Some(b) = els {
                    assigned_in_block(r, b, out);
                }
            }
            _ => {}
        }
    }
}

/// Spans of the `continue` statements that target the loop whose body is `b`
/// (not those of nested loops or functions).
fn continue_spans(b: &Block, out: &mut Vec<Span>) {
    for s in &b.stats {
        match &s.kind {
            StatKind::Continue => out.push(s.span),
            StatKind::Do(x) => continue_spans(x, out),
            StatKind::If(arms, els) => {
                for (_, x) in arms {
                    continue_spans(x, out);
                }
                if let Some(x) = els {
                    continue_spans(x, out);
                }
            }
            _ => {}
        }
    }
}

/// Name nodes an expression reads (not inside nested function bodies).
fn expr_names(e: &Expr, out: &mut Vec<NodeId>) {
    match &e.kind {
        ExprKind::Name(n) => out.push(n.id),
        ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) => {
            expr_names(a, out);
            expr_names(b, out);
        }
        ExprKind::Field(a, _) | ExprKind::Unary(_, a) | ExprKind::Paren(a) | ExprKind::Cast(a, _) => expr_names(a, out),
        ExprKind::Call(f, args) | ExprKind::Method(f, _, args) => {
            expr_names(f, out);
            args.iter().for_each(|a| expr_names(a, out));
        }
        ExprKind::IfElse(a, b, c) => {
            expr_names(a, out);
            expr_names(b, out);
            expr_names(c, out);
        }
        ExprKind::Interp(parts) => {
            for p in parts {
                if let InterpPart::Expr(x) = p {
                    expr_names(x, out);
                }
            }
        }
        ExprKind::Table(items) => {
            for it in items {
                match it {
                    TableItem::Pos(x) | TableItem::Named(_, x) => expr_names(x, out),
                    TableItem::Keyed(k, v) => {
                        expr_names(k, out);
                        expr_names(v, out);
                    }
                }
            }
        }
        ExprKind::Nil | ExprKind::Bool(_) | ExprKind::Number(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Function(_) | ExprKind::Vararg => {}
    }
}
