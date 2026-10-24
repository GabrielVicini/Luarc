//! Call-site specialization of local functions.
//!
//! The checker gives every binding one static type, so a function called with
//! arguments of different types would be a type error. A `local function f` that
//! is only ever called by name can instead be *copied per call site*: each call
//! gets its own copy (`f__s1`, `f__s2`, ...) whose parameters take that call's
//! argument types. This is classic monomorphization done on the syntax tree, before
//! type checking; the copies are ordinary functions to every later phase.
//!
//! Which functions are copied:
//! * functions with type parameters (`local function f<T>(x: T)`) always;
//! * functions containing `error(msg, level)` with a literal level of 2 or more
//!   always, because the copy knows its (only) caller's line;
//! * functions with unannotated parameters only in `lazy` mode, which the driver
//!   enables after the program failed to type check without it. Programs that
//!   check without specialization are never changed.
//!
//! A function is copied only if it is never reassigned, every use of its name is
//! the callee of a call, and it is not part of a recursive cycle with another
//! copied function. Self-recursion is fine: each copy calls itself. Callers are
//! copied before their callees, so a callee gets one copy per call in every copy
//! of its caller.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::ast::*;
use crate::ast_walk::*;
use crate::check::ModuleUnit;
use crate::diag::{Diagnostic, Span};
use crate::resolve::{Builtin, Res, Resolution, Resolver, SymId, SymKind};

/// Upper bound on the copies one program may get (guards exponential growth).
const MAX_COPIES: usize = 4000;

/// What the pre-pass found out about the program.
#[derive(Default, Clone, Debug)]
pub struct Needs {
    /// Functions with type parameters or `error(_, 2)` exist (specialize eagerly).
    pub eager: bool,
    /// Functions with unannotated parameters that could be copied exist.
    pub lazy: bool,
}

struct Site {
    name_id: NodeId,
    /// Position reported by `error(msg, 2)` inside the copy made for this call.
    span: Span,
}

struct Def {
    unit: usize,
    stat: NodeId,
    name: String,
    name_span: Span,
    stat_span: Span,
    generic: bool,
    level2: bool,
    unannotated: bool,
    is_copy: bool,
    sites: Vec<Site>,
    /// Sites located inside this function's own body (self-recursion).
    self_sites: usize,
    total_uses: usize,
    /// Local functions that contain a call of this one.
    callers: BTreeSet<SymId>,
}

struct Analysis<'r> {
    res: &'r Resolution,
    unit: usize,
    /// Enclosing functions, innermost last: `Some(sym)` for a `local function`.
    fstack: Vec<Option<SymId>>,
    defs: BTreeMap<SymId, Def>,
    /// `error` call with a literal level of 2 or more, by enclosing local function.
    level2: BTreeSet<SymId>,
    uses: HashMap<SymId, usize>,
    sites: Vec<(SymId, Site, Vec<SymId>)>,
}

fn is_error_builtin(res: &Resolution, f: &Expr) -> bool {
    matches!(&f.kind, ExprKind::Name(n) if res.res(n.id) == Some(Res::Builtin(Builtin::Error)))
}

impl VisitMut for Analysis<'_> {
    fn stat(&mut self, s: &mut Stat) {
        match &mut s.kind {
            StatKind::LocalFunction(n, f) => {
                let sym = self.res.decl(n.id);
                // an untyped `...` is unannotated too (its element type is one per function)
                let unannotated = f.params.iter().any(|p| p.ty.is_none()) || matches!(f.vararg, Some((_, None)));
                self.defs.insert(
                    sym,
                    Def {
                        unit: self.unit,
                        stat: s.id,
                        name: n.text.clone(),
                        name_span: n.span,
                        stat_span: s.span,
                        generic: !f.generics.is_empty(),
                        level2: false,
                        unannotated,
                        is_copy: f.call_site.is_some(),
                        sites: Vec::new(),
                        self_sites: 0,
                        total_uses: 0,
                        callers: BTreeSet::new(),
                    },
                );
                self.fstack.push(Some(sym));
            }
            StatKind::Function(..) => self.fstack.push(None),
            _ => {}
        }
    }
    fn exit_stat(&mut self, s: &mut Stat) {
        if matches!(s.kind, StatKind::LocalFunction(..) | StatKind::Function(..)) {
            self.fstack.pop();
        }
    }
    fn expr(&mut self, e: &mut Expr) {
        match &e.kind {
            ExprKind::Function(_) => self.fstack.push(None),
            ExprKind::Call(f, args) => {
                if is_error_builtin(self.res, f) {
                    if let (Some(lv), Some(Some(sym))) = (args.get(1), self.fstack.last()) {
                        if matches!(lv.kind, ExprKind::Number(n) if n >= 2.0) {
                            self.level2.insert(*sym);
                        }
                    }
                }
                if let ExprKind::Name(n) = &f.kind {
                    if let Some(Res::Local(sym)) = self.res.res(n.id) {
                        if self.res.sym(sym).kind == SymKind::LocalFunc {
                            // Luau reports the line where the call starts (`f(` of a call
                            // spread over several lines), i.e. its callee's line
                            let span = f.span;
                            let enclosing: Vec<SymId> = self.fstack.iter().flatten().copied().collect();
                            self.sites.push((sym, Site { name_id: n.id, span }, enclosing));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    fn exit_expr(&mut self, e: &mut Expr) {
        if matches!(e.kind, ExprKind::Function(_)) {
            self.fstack.pop();
        }
    }
    fn name(&mut self, n: &mut Name) {
        if let Some(Res::Local(sym)) = self.res.res(n.id) {
            *self.uses.entry(sym).or_insert(0) += 1;
        }
    }
}

fn resolve_all(units: &[ModuleUnit]) -> Resolution {
    let mut res = Resolution::default();
    let mut r = Resolver::new(&mut res);
    for u in units {
        r.module(&u.module, u.pseudo_func);
    }
    r.finish();
    res
}

fn analyze(units: &mut [ModuleUnit], res: &Resolution) -> BTreeMap<SymId, Def> {
    let mut a = Analysis { res, unit: 0, fstack: Vec::new(), defs: BTreeMap::new(), level2: BTreeSet::new(), uses: HashMap::new(), sites: Vec::new() };
    for (i, u) in units.iter_mut().enumerate() {
        a.unit = i;
        walk_block(&mut a, &mut u.module.body);
    }
    let mut defs = std::mem::take(&mut a.defs);
    for (sym, site, enclosing) in std::mem::take(&mut a.sites) {
        let Some(d) = defs.get_mut(&sym) else { continue };
        if enclosing.contains(&sym) {
            d.self_sites += 1;
        } else {
            for g in &enclosing {
                d.callers.insert(*g);
            }
            d.sites.push(site);
        }
    }
    for (sym, d) in defs.iter_mut() {
        d.total_uses = a.uses.get(sym).copied().unwrap_or(0);
        d.level2 = a.level2.contains(sym);
    }
    defs
}

/// Which functions are candidates, per mode.
fn candidates(res: &Resolution, defs: &BTreeMap<SymId, Def>, lazy: bool) -> BTreeSet<SymId> {
    let mut out = BTreeSet::new();
    for (sym, d) in defs {
        let wanted = d.generic || d.level2 || (lazy && d.unannotated);
        if wanted
            && !d.is_copy
            && !res.sym(*sym).assigned
            && !d.sites.is_empty()
            // every use is the callee of a call (the recursive ones included)
            && d.total_uses == d.sites.len() + d.self_sites
        {
            out.insert(*sym);
        }
    }
    out
}

/// Reports whether the program has functions to copy (cheap, one resolution).
pub fn needs(units: &mut [ModuleUnit]) -> Needs {
    let res = resolve_all(units);
    let defs = analyze(units, &res);
    Needs {
        eager: !candidates(&res, &defs, false).is_empty() || !unused_wanted(&res, &defs).is_empty(),
        lazy: !candidates(&res, &defs, true).is_empty(),
    }
}

/// Functions that would be copied per call but are never called: they stay as they are
/// (checked once) and count as their own copy, with their definition as the call site
/// (so an `error(msg, 2)` in an unused function is accepted).
fn unused_wanted(res: &Resolution, defs: &BTreeMap<SymId, Def>) -> Vec<(usize, NodeId, Span)> {
    defs.iter()
        .filter(|(sym, d)| {
            (d.generic || d.level2) && !d.is_copy && !res.sym(**sym).assigned && d.sites.is_empty() && d.total_uses == d.self_sites
        })
        .map(|(_, d)| (d.unit, d.stat, d.name_span))
        .collect()
}

fn mark_own_copy(units: &mut [ModuleUnit], unit: usize, stat: NodeId, span: Span) {
    struct Mark {
        stat: NodeId,
        span: Span,
    }
    impl VisitMut for Mark {
        fn stat(&mut self, s: &mut Stat) {
            if s.id == self.stat {
                if let StatKind::LocalFunction(_, f) = &mut s.kind {
                    f.call_site = Some(self.span);
                }
            }
        }
    }
    walk_block(&mut Mark { stat, span }, &mut units[unit].module.body);
}

/// Copies a function body with fresh node ids; records the new id of every old one.
struct Renumber<'a> {
    next: &'a mut NodeId,
    names: HashMap<NodeId, NodeId>,
    exprs: HashMap<NodeId, NodeId>,
}

impl Renumber<'_> {
    fn fresh(&mut self) -> NodeId {
        let id = *self.next;
        *self.next += 1;
        id
    }
}

impl VisitMut for Renumber<'_> {
    fn stat(&mut self, s: &mut Stat) {
        s.id = self.fresh();
    }
    fn expr(&mut self, e: &mut Expr) {
        let old = e.id;
        e.id = self.fresh();
        self.exprs.insert(old, e.id);
    }
    fn name(&mut self, n: &mut Name) {
        let old = n.id;
        n.id = self.fresh();
        self.names.insert(old, n.id);
    }
    fn func(&mut self, f: &mut FuncBody) {
        f.id = self.fresh();
    }
}

/// Renames the uses of `sym` (inside its own body) to the copy's name.
struct RenameSelf<'a> {
    res: &'a Resolution,
    sym: SymId,
    to: &'a str,
}

impl VisitMut for RenameSelf<'_> {
    fn name(&mut self, n: &mut Name) {
        if self.res.res(n.id) == Some(Res::Local(self.sym)) {
            n.text = self.to.to_string();
        }
    }
}

/// Renames the callee of each specialized call site; inserts the copies.
struct Apply<'a> {
    rename: &'a HashMap<NodeId, String>,
    def_stat: NodeId,
    copies: Option<Vec<Stat>>,
}

impl VisitMut for Apply<'_> {
    fn block(&mut self, b: &mut Block) {
        if let Some(pos) = b.stats.iter().position(|s| s.id == self.def_stat) {
            let copies = self.copies.take().unwrap_or_default();
            // the original is replaced by its copies (it has no remaining use)
            b.stats.splice(pos..=pos, copies);
        }
    }
    fn name(&mut self, n: &mut Name) {
        if let Some(to) = self.rename.get(&n.id) {
            n.text = to.clone();
        }
    }
}

/// Copies functions until none is left to copy. `lazy` includes functions that only
/// have unannotated parameters. `next_id` is the first unused node id. Returns the
/// number of copies made.
pub fn specialize(units: &mut [ModuleUnit], next_id: &mut NodeId, lazy: bool) -> Result<usize, Diagnostic> {
    let mut made = 0usize;
    let mut counter = 0usize;
    loop {
        let res = resolve_all(units);
        let defs = analyze(units, &res);
        let mut cand = candidates(&res, &defs, lazy);
        // calls among candidates; a function in a cycle with another is left alone
        let reach = |from: SymId, cand: &BTreeSet<SymId>| -> BTreeSet<SymId> {
            let mut seen = BTreeSet::new();
            let mut stack = vec![from];
            while let Some(x) = stack.pop() {
                // x calls y when x encloses a call site of y
                for (y, d) in defs.iter() {
                    if cand.contains(y) && d.callers.contains(&x) && seen.insert(*y) {
                        stack.push(*y);
                    }
                }
            }
            seen
        };
        let in_cycle: Vec<SymId> = cand.iter().copied().filter(|s| reach(*s, &cand).contains(s)).collect();
        for s in in_cycle {
            cand.remove(&s);
        }
        // a callee waits until all candidate callers are done
        let pick = cand.iter().copied().find(|s| defs[s].callers.iter().all(|g| !cand.contains(g)));
        let Some(sym) = pick else {
            for (unit, stat, span) in unused_wanted(&res, &defs) {
                mark_own_copy(units, unit, stat, span);
                made += 1;
            }
            return Ok(made);
        };
        let d = &defs[&sym];
        made += d.sites.len();
        if made > MAX_COPIES {
            return Err(Diagnostic::new(
                d.name_span,
                format!("too many specialized copies of functions (limit {MAX_COPIES}); annotate the parameter types of '{}' to avoid copying it per call", d.name),
            ));
        }
        // names of the copies; each copy is made from the original body
        let mut rename: HashMap<NodeId, String> = HashMap::new();
        let mut copies: Vec<Stat> = Vec::new();
        let body_ref = find_body(units, d.unit, d.stat);
        let Some(orig) = body_ref else { return Ok(made) };
        let unit = d.unit;
        for site in &d.sites {
            counter += 1;
            let new_name = format!("{}__s{}", d.name, counter);
            rename.insert(site.name_id, new_name.clone());
            let mut body = orig.clone();
            let mut me = RenameSelf { res: &res, sym, to: &new_name };
            walk_func(&mut me, &mut body);
            let mut rn = Renumber { next: &mut *next_id, names: HashMap::new(), exprs: HashMap::new() };
            walk_func(&mut rn, &mut body);
            // attributes and `require` calls are keyed by node ids
            let u = &mut units[unit];
            for (old, new) in &rn.names {
                if let Some(a) = u.module.attrs.get(old).copied() {
                    u.module.attrs.insert(*new, a);
                }
            }
            for (old, new) in &rn.exprs {
                if let Some(m) = u.requires.get(old).copied() {
                    u.requires.insert(*new, m);
                }
                if let Some(m) = u.rust_requires.get(old).copied() {
                    u.rust_requires.insert(*new, m);
                }
            }
            body.call_site = Some(site.span);
            let name_id = *next_id;
            let stat_id = *next_id + 1;
            *next_id += 2;
            copies.push(Stat {
                id: stat_id,
                span: d.stat_span,
                kind: StatKind::LocalFunction(Name { id: name_id, text: new_name, span: d.name_span }, Box::new(body)),
            });
        }
        let mut ap = Apply { rename: &rename, def_stat: d.stat, copies: Some(copies) };
        for u in units.iter_mut() {
            walk_block(&mut ap, &mut u.module.body);
        }
    }
}

fn find_body(units: &mut [ModuleUnit], unit: usize, stat: NodeId) -> Option<FuncBody> {
    struct Find {
        stat: NodeId,
        out: Option<FuncBody>,
    }
    impl VisitMut for Find {
        fn stat(&mut self, s: &mut Stat) {
            if s.id == self.stat {
                if let StatKind::LocalFunction(_, f) = &s.kind {
                    self.out = Some((**f).clone());
                }
            }
        }
    }
    let mut f = Find { stat, out: None };
    walk_block(&mut f, &mut units[unit].module.body);
    f.out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_module;

    fn units(src: &str) -> (Vec<ModuleUnit>, NodeId) {
        let mut next = 1;
        let m = parse_module(0, src, &mut next).expect("parse");
        let pseudo = next;
        next += 1;
        let u = ModuleUnit { module: m, pseudo_func: pseudo, ident: "m0".into(), requires: HashMap::new(), rust_requires: HashMap::new() };
        (vec![u], next)
    }

    /// Names of the top-level `local function`s, in order.
    fn functions(u: &[ModuleUnit]) -> Vec<String> {
        u[0].module
            .body
            .stats
            .iter()
            .filter_map(|s| match &s.kind {
                StatKind::LocalFunction(n, _) => Some(n.text.clone()),
                _ => None,
            })
            .collect()
    }

    /// Callee names of the top-level call statements, in order.
    fn callees(u: &[ModuleUnit]) -> Vec<String> {
        u[0].module
            .body
            .stats
            .iter()
            .filter_map(|s| match &s.kind {
                StatKind::Call(Expr { kind: ExprKind::Call(f, _), .. }) => match &f.kind {
                    ExprKind::Name(n) => Some(n.text.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    #[test]
    fn a_generic_function_gets_one_copy_per_call() {
        let (mut u, mut next) = units("local function id<T>(x: T): T return x end\nid(1)\nid('a')\nid(true)");
        let n = needs(&mut u);
        assert!(n.eager && n.lazy);
        assert_eq!(specialize(&mut u, &mut next, false).unwrap(), 3);
        assert_eq!(functions(&u), ["id__s1", "id__s2", "id__s3"]);
        assert_eq!(callees(&u), ["id__s1", "id__s2", "id__s3"]);
        // nothing is left to copy
        assert_eq!(specialize(&mut u, &mut next, false).unwrap(), 0);
    }

    #[test]
    fn unannotated_parameters_are_copied_only_in_lazy_mode() {
        let src = "local function f(a, b) return a end\nf(1, 2)\nf('x', 'y')";
        let (mut u, mut next) = units(src);
        let n = needs(&mut u);
        assert!(!n.eager && n.lazy);
        assert_eq!(specialize(&mut u, &mut next, false).unwrap(), 0);
        assert_eq!(functions(&u), ["f"]);
        assert_eq!(specialize(&mut u, &mut next, true).unwrap(), 2);
        assert_eq!(callees(&u), ["f__s1", "f__s2"]);
    }

    #[test]
    fn an_untyped_vararg_counts_as_unannotated() {
        let (mut u, mut next) = units("local function f(...) return (...) end\nf(1)\nf('a')");
        assert!(needs(&mut u).lazy);
        assert_eq!(specialize(&mut u, &mut next, true).unwrap(), 2);
        let (mut typed, _) = units("local function g(...: number) return (...) end\ng(1)\ng(2)");
        assert!(!needs(&mut typed).lazy);
    }

    #[test]
    fn annotated_functions_are_left_alone() {
        let (mut u, _) = units("local function f(a: number): number return a end\nf(1)\nf(2)");
        let n = needs(&mut u);
        assert!(!n.eager && !n.lazy);
    }

    #[test]
    fn a_function_used_as_a_value_is_not_copied() {
        let (mut u, mut next) = units("local function f(a) return a end\nlocal g = f\nf(1)\nf('x')");
        assert!(!needs(&mut u).lazy);
        assert_eq!(specialize(&mut u, &mut next, true).unwrap(), 0);
        assert_eq!(functions(&u), ["f"]);
    }

    #[test]
    fn a_reassigned_function_is_not_copied() {
        let (mut u, mut next) = units("local function f(a) return a end\nf = nil\nf(1)\nf('x')");
        assert_eq!(specialize(&mut u, &mut next, true).unwrap(), 0);
    }

    #[test]
    fn self_recursion_calls_the_copy_itself() {
        let src = "local function r(n, x) if n == 0 then return x end return r(n - 1, x) end\nr(2, 1)\nr(2, 'a')";
        let (mut u, mut next) = units(src);
        assert_eq!(specialize(&mut u, &mut next, true).unwrap(), 2);
        assert_eq!(functions(&u), ["r__s1", "r__s2"]);
        let StatKind::LocalFunction(_, f) = &u[0].module.body.stats[1].kind else { panic!("not a function") };
        let mut seen = Vec::new();
        struct Names<'a>(&'a mut Vec<String>);
        impl VisitMut for Names<'_> {
            fn expr(&mut self, e: &mut Expr) {
                if let ExprKind::Call(c, _) = &e.kind {
                    if let ExprKind::Name(n) = &c.kind {
                        self.0.push(n.text.clone());
                    }
                }
            }
        }
        let mut body = (**f).clone();
        walk_block(&mut Names(&mut seen), &mut body.body);
        assert_eq!(seen, ["r__s2"], "the copy calls itself, not the other copy or the original");
    }

    #[test]
    fn callers_are_copied_before_callees() {
        // each copy of `outer` gets its own copy of `inner`
        let src = "local function inner(x) return x end\nlocal function outer(y) return inner(y) end\nouter(1)\nouter('a')";
        let (mut u, mut next) = units(src);
        assert_eq!(specialize(&mut u, &mut next, true).unwrap(), 4);
        let names = functions(&u);
        assert_eq!(names.iter().filter(|n| n.starts_with("outer__")).count(), 2);
        assert_eq!(names.iter().filter(|n| n.starts_with("inner__")).count(), 2);
        assert!(!names.contains(&"inner".to_string()) && !names.contains(&"outer".to_string()));
    }

    #[test]
    fn mutually_recursive_functions_are_not_copied() {
        let src = "local a, b\nfunction a(x) return b(x) end\nfunction b(x) return a(x) end\na(1)\na('s')";
        let (mut u, mut next) = units(src);
        // both are assigned, not local functions: nothing to copy, nothing grows
        assert_eq!(specialize(&mut u, &mut next, true).unwrap(), 0);
    }

    #[test]
    fn error_level_two_makes_a_function_eager_and_records_the_call_line() {
        let src = "local function check(c)\n  if not c then error('x', 2) end\nend\n\ncheck(true)\ncheck(false)";
        let (mut u, mut next) = units(src);
        let n = needs(&mut u);
        assert!(n.eager);
        assert_eq!(specialize(&mut u, &mut next, false).unwrap(), 2);
        let lines: Vec<u32> = u[0]
            .module
            .body
            .stats
            .iter()
            .filter_map(|s| match &s.kind {
                StatKind::LocalFunction(_, f) => f.call_site.map(|c| c.line),
                _ => None,
            })
            .collect();
        assert_eq!(lines, [5, 6]);
    }

    #[test]
    fn an_unused_function_with_error_level_two_counts_as_its_own_copy() {
        let (mut u, mut next) = units("local function check(c) error('x', 2) end");
        assert!(needs(&mut u).eager);
        assert_eq!(specialize(&mut u, &mut next, false).unwrap(), 1);
        let StatKind::LocalFunction(_, f) = &u[0].module.body.stats[0].kind else { panic!("not a function") };
        assert!(f.call_site.is_some());
        assert!(!needs(&mut u).eager);
    }

    #[test]
    fn copies_have_fresh_node_ids() {
        let (mut u, mut next) = units("local function f<T>(x: T) return x end\nf(1)\nf(2)");
        specialize(&mut u, &mut next, false).unwrap();
        struct Ids(Vec<NodeId>);
        impl VisitMut for Ids {
            fn stat(&mut self, s: &mut Stat) {
                self.0.push(s.id);
            }
            fn expr(&mut self, e: &mut Expr) {
                self.0.push(e.id);
            }
            fn name(&mut self, n: &mut Name) {
                self.0.push(n.id);
            }
            fn func(&mut self, f: &mut FuncBody) {
                self.0.push(f.id);
            }
        }
        let mut ids = Ids(Vec::new());
        walk_block(&mut ids, &mut u[0].module.body);
        let mut distinct = ids.0.clone();
        distinct.sort();
        distinct.dedup();
        assert_eq!(distinct.len(), ids.0.len(), "every node id is unique");
        assert!(ids.0.iter().all(|i| *i < next));
    }
}
