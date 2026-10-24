//! Native trait implementations written as source tables.
//!
//! A native generic parameter bounded by a trait of an imported crate
//! (`fn run_app<A: ApplicationHandler<T>>(self, app: &mut A)`) accepts a source
//! table whose function fields are the trait's methods:
//!
//! ```lua
//! local app = { count = 0 }
//! function app:resumed(event_loop) ... end
//! event_loop:run_app(app)
//! ```
//!
//! Each method present in the table is checked against the trait's signature
//! (the table itself is `self`; `&T` arguments are lent for the call); a required
//! method the table lacks is an error; absent provided methods keep the trait's
//! default. Other fields are ordinary state. The generated Rust implements the
//! trait on a struct that holds the table and delegates to its functions.

use rustdoc_types as rd;

use crate::check::*;
use crate::check_native::NEnv;
use crate::diag::Span;
use crate::native::types::*;
use crate::native::world::ItemRef;
use crate::types::*;

/// One trait implemented by a source table at a native call.
#[derive(Clone, Debug)]
pub struct TraitImpl {
    pub trait_: ItemRef,
    /// The bound as written (`ApplicationHandler<T>`), for its arguments.
    pub bound: rd::Path,
    /// Trait generics bound for this use (`T`), `Self` = the table.
    pub env: NEnv,
    /// (method name, trait item, implemented by the table).
    pub methods: Vec<(String, ItemRef, bool)>,
    /// The table's source type.
    pub table: TyId,
}

impl<'a> Checker<'a> {
    /// Trait bounds a table could implement: traits of non-toolchain crates.
    pub(crate) fn implementable_bounds(&self, bounds: &[rd::GenericBound], krate: usize) -> Vec<(ItemRef, rd::Path)> {
        let w = self.world();
        let mut out = Vec::new();
        for p in trait_bounds(bounds) {
            if matches!(last_seg(&p.path), "Fn" | "FnMut" | "FnOnce") {
                continue;
            }
            let Some(tr) = w.resolve(krate, &p.id) else { continue };
            if w.std_path(tr).is_some() {
                continue; // std traits (Sized, Send, Display, ...) are not implemented by tables
            }
            if matches!(w.item(tr).map(|i| &i.inner), Some(rd::ItemEnum::Trait(_))) {
                out.push((tr, p.clone()));
            }
        }
        out
    }

    /// After a native call's arguments flowed: tables passed to trait-bounded
    /// generic parameters implement those traits.
    pub(crate) fn note_trait_args(&mut self, inst: usize, args: &[ETy], span: Span) {
        let w = self.world();
        let ni = self.info.natives[inst].clone();
        let Some(rd::Item { inner: rd::ItemEnum::Function(func), .. }) = w.item(ni.item) else { return };
        let skip = usize::from(matches!(ni.kind, crate::check_native::NKind::Method(_)));
        for (i, (_, t)) in func.sig.inputs.iter().skip(skip).enumerate() {
            let bounds = match t {
                rd::Type::Generic(n) => param_bounds(&func.generics, n),
                rd::Type::BorrowedRef { type_, .. } => match &**type_ {
                    rd::Type::Generic(n) => param_bounds(&func.generics, n),
                    rd::Type::ImplTrait(b) => b.clone(),
                    _ => continue,
                },
                rd::Type::ImplTrait(b) => b.clone(),
                _ => continue,
            };
            let traits = self.implementable_bounds(&bounds, ni.item.krate);
            if traits.is_empty() {
                continue;
            }
            let Some(a) = args.get(i) else { continue };
            // a table-backed implementation holds managed (thread-bound) values: a
            // `Send`/`Sync` bound is diagnosed here instead of failing in rustc with
            // the generated struct's internals
            if trait_bounds(&bounds).iter().any(|p| matches!(last_seg(&p.path), "Send" | "Sync")) {
                if let TyNode::Table(_) | TyNode::Var = self.st.node(a.ty) {
                    let tn = w.name(traits[0].0);
                    self.error(
                        span,
                        format!("a source table cannot implement '{tn}' here: the parameter also requires Send/Sync (native code may use it from another thread; source values stay on their owning thread)"),
                    );
                    continue;
                }
            }
            self.try_or_defer(Op::TraitImpl { inst, param: i, arg: *a, span });
        }
    }

    pub(crate) fn attempt_trait_impl(&mut self, inst: usize, param: usize, arg: ETy, span: Span) -> bool {
        let tab = match self.st.node(arg.ty).clone() {
            TyNode::Var => return false,
            TyNode::Table(t) => t,
            _ => return true, // a native value: rustc checks that it implements the trait
        };
        let root = self.st.tab_root(tab);
        if self.st.tab(root).native.is_some() {
            return true;
        }
        if self.st.tab(root).kind == TKind::Unknown {
            // `local t = {}; function t:m() ... end`: the method fields are added
            // once the table is known to be a record; check after that
            if self.defaults_round {
                self.ensure_kind(root, TKind::Record, span);
            }
            return false;
        }
        let w = self.world();
        let ni = self.info.natives[inst].clone();
        let Some(rd::Item { inner: rd::ItemEnum::Function(func), .. }) = w.item(ni.item) else { return true };
        let skip = usize::from(matches!(ni.kind, crate::check_native::NKind::Method(_)));
        let Some((_, pt)) = func.sig.inputs.get(param + skip).cloned() else { return true };
        let bounds = match &pt {
            rd::Type::Generic(n) => param_bounds(&func.generics, n),
            rd::Type::BorrowedRef { type_, .. } => match &**type_ {
                rd::Type::Generic(n) => param_bounds(&func.generics, n),
                rd::Type::ImplTrait(b) => b.clone(),
                _ => vec![],
            },
            rd::Type::ImplTrait(b) => b.clone(),
            _ => vec![],
        };
        let mut impls = Vec::new();
        for (tr, bound) in self.implementable_bounds(&bounds, ni.item.krate) {
            match self.table_impl(tr, &bound, &ni.env, arg.ty, root, span) {
                Ok(ti) => impls.push(ti),
                Err(m) => {
                    let tn = w.name(tr);
                    self.error(span, format!("the table passed to '{}' cannot implement {tn}: {m}", ni.display));
                }
            }
        }
        self.info.trait_impls.insert((inst, param), impls);
        true
    }

    fn table_impl(&mut self, tr: ItemRef, bound: &rd::Path, call_env: &NEnv, table: TyId, root: TabId, span: Span) -> Result<TraitImpl, String> {
        let w = self.world();
        let tn = w.name(tr);
        let rd::ItemEnum::Trait(t) = &w.item(tr).ok_or("trait not found")?.inner else { return Err("not a trait".into()) };
        if t.is_unsafe {
            return Err("unsafe traits are never implemented automatically".into());
        }
        // trait generics from the bound's arguments, in the calling environment
        let mut env = NEnv { krate: tr.krate, self_ty: Some(table), ..Default::default() };
        let targs = generic_type_args(bound);
        let mut k = 0;
        for gp in w.generics_of(tr) {
            if gp.kind != GKind::Type {
                continue;
            }
            let at = match targs.get(k) {
                Some(a) => self.n_arg(a, call_env, span)?,
                None => match &gp.default {
                    Some(d) => self.n_arg(d, &NEnv { krate: tr.krate, ..Default::default() }, span)?,
                    None => self.st.var(),
                },
            };
            env.gens.insert(gp.name.clone(), at);
            k += 1;
        }
        let mut methods = Vec::new();
        for it in w.trait_items(tr) {
            let item = w.item(it).ok_or("trait item")?;
            let name = item.name.clone().unwrap_or_default();
            match &item.inner {
                rd::ItemEnum::Function(f) => {
                    let has_field = self.st.tab(root).fields.contains_key(&name);
                    if !has_field {
                        if !f.has_body {
                            return Err(format!("the table has no function '{name}' (a required method of {tn})"));
                        }
                        methods.push((name, it, false));
                        continue;
                    }
                    if gparams(&f.generics).iter().any(|g| g.kind == GKind::Type) {
                        return Err(format!("method '{name}' is generic; generic trait methods cannot be implemented by a table"));
                    }
                    let ft = self.trait_method_ty(f, &env, table, span).map_err(|m| format!("method '{name}': {m}"))?;
                    let fslot = self.st.tab(root).fields[&name];
                    if self.st.is_null(fslot.null) {
                        return Err(format!("method '{name}' may be nil"));
                    }
                    if !self.unify(fslot.ty, ft, span) {
                        return Err(format!("method '{name}' does not match the trait signature"));
                    }
                    methods.push((name, it, true));
                }
                rd::ItemEnum::AssocType { type_: None, .. } => {
                    return Err(format!("{tn} has an associated type '{name}' that a table cannot define"));
                }
                _ => {}
            }
        }
        Ok(TraitImpl { trait_: tr, bound: bound.clone(), env, methods, table })
    }

    /// Source function type of a trait method implemented by a table: the table
    /// is the first parameter (`self`).
    fn trait_method_ty(&mut self, f: &rd::Function, env: &NEnv, table: TyId, span: Span) -> Result<TyId, String> {
        let mut params = Vec::new();
        for (i, (pn, pt)) in f.sig.inputs.iter().enumerate() {
            if i == 0 {
                if pn != "self" {
                    return Err("associated functions without `self` cannot be implemented by a table".into());
                }
                params.push(self.st.fixed_slot(table, span, "self is never nil"));
                continue;
            }
            params.push(self.n_slot(pt, env, span).map_err(|m| format!("parameter {pn}: {m}"))?);
        }
        let rets = match &f.sig.output {
            None => vec![],
            Some(t) => self.n_rets(t, env, span)?.0,
        };
        let r = self.st.new_rets(RetsNode::Known(rets));
        Ok(self.st.ty(TyNode::Func(std::rc::Rc::new(FuncTy { params, rets: r, vararg: None }))))
    }
}
