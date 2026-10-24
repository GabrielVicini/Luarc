//! Type checking of uses of imported Rust APIs.
//!
//! Native signatures come from typed rustdoc JSON ([`World`]). They are mapped to
//! source types on demand, at the use site, with generic parameters instantiated
//! as inference variables (fixed by the arguments and the expected results) and
//! impl/trait generics bound by matching the receiver's type arguments. Anything
//! a signature uses that has no source representation produces an item-level
//! diagnostic at the call site; other items of the crate stay usable.

use std::collections::HashMap;
use std::rc::Rc;

use rustdoc_types as rd;

use crate::check::*;
use crate::diag::Span;
use crate::native::types::*;
use crate::native::world::{CrateIx, ItemRef, World};
use crate::types::*;

/// Generic environment for mapping a native signature.
#[derive(Clone, Debug, Default)]
pub struct NEnv {
    /// Crate whose ids the mapped types use.
    pub krate: CrateIx,
    pub gens: HashMap<String, TyId>,
    pub self_ty: Option<TyId>,
    /// Associated types of the impl in scope (`Self::Item`), with their crate.
    pub assoc: HashMap<String, (CrateIx, rd::Type)>,
    /// Generic parameters that are callbacks (`F: FnMut(..)`), with their bounds.
    pub callbacks: HashMap<String, Vec<rd::GenericBound>>,
    /// Concrete rustdoc types of generic parameters, where known (`L = Option<&str>`).
    pub rd: HashMap<String, (CrateIx, rd::Type)>,
}

impl NEnv {
    pub fn in_crate(&self, krate: CrateIx) -> NEnv {
        NEnv { krate, ..self.clone() }
    }
}

/// A mapped native value type.
#[derive(Clone, Copy, Debug)]
pub struct NV {
    pub ty: TyId,
    pub opt: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Recv {
    Ref,
    Mut,
    Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NKind {
    Function,
    AssocFn,
    Method(Recv),
    /// Tuple/struct variant constructor.
    VariantCtor,
    /// Unit variant value.
    VariantConst,
    Const,
    AssocConst,
    /// Public field read on a handle.
    FieldGet(String),
    /// Public field write on a handle.
    FieldSet(String),
    /// Enum variant payload accessor (`e.Resized`).
    Payload(String),
    /// `Iterator::next` of a native iterator driving a `for` loop.
    IterNext,
    /// `await(x)` on a native value implementing `Future` (consumes it).
    AwaitNative,
}

/// One use of a native item, with everything wrapper generation needs.
#[derive(Clone, Debug)]
pub struct NativeInst {
    pub kind: NKind,
    /// The function / variant / constant item.
    pub item: ItemRef,
    /// The owning type (assoc items, methods, variants, fields) and its arguments.
    pub owner: Option<(ItemRef, Vec<TyId>)>,
    /// The impl block providing a method (None for trait-default methods).
    pub imp: Option<ItemRef>,
    /// The trait providing a method, when it is a trait method.
    pub trait_: Option<ItemRef>,
    pub env: NEnv,
    pub span: Span,
    /// Source-side parameter slots (receiver excluded).
    pub params: Vec<Slot>,
    pub rets: Vec<Slot>,
    pub recv: Option<TyId>,
    /// `Result` return: `Err` becomes a language error.
    pub fallible: bool,
    pub display: String,
    /// Deref steps from the receiver to the method's owner (`PathBuf` → `Path`).
    pub deref: u8,
}

fn prim_kind(p: &str) -> Option<&'static str> {
    Some(match p {
        "bool" => "bool",
        "char" | "str" => "str",
        "f32" | "f64" | "i8" | "i16" | "i32" | "isize" | "u8" | "u16" | "u32" | "usize" => "num",
        "i64" | "u64" | "i128" | "u128" => "int",
        _ => return None,
    })
}

impl<'a> Checker<'a> {
    pub(crate) fn world(&self) -> &'a World {
        self.world
    }

    fn prim_value(&mut self, p: &str) -> Result<TyId, String> {
        match prim_kind(p) {
            Some("bool") => Ok(self.st.ty(TyNode::Bool)),
            Some("str") => Ok(self.st.ty(TyNode::Str)),
            Some("num") => Ok(self.st.ty(TyNode::Num)),
            Some(_) => Ok(self.st.ty(TyNode::Int)),
            None => Err(format!("primitive type {p} has no source representation")),
        }
    }

    /// Type argument of a native generic type (numeric widths are kept).
    pub(crate) fn n_arg(&mut self, t: &rd::Type, env: &NEnv, span: Span) -> Result<TyId, String> {
        match t {
            rd::Type::Primitive(p) if prim_kind(p).is_some() => Ok(self.st.ty(TyNode::NPrim(p.as_str().into()))),
            rd::Type::Tuple(ts) if ts.is_empty() => Ok(self.st.ty(TyNode::Nil)),
            rd::Type::Generic(n) if n != "Self" => match env.gens.get(n) {
                Some(t) => Ok(*t),
                None => Err(format!("unbound generic parameter {n}")),
            },
            _ => Ok(self.n_val(t, env, span)?.ty),
        }
    }

    /// Source value type of a native type.
    pub(crate) fn n_val(&mut self, t: &rd::Type, env: &NEnv, span: Span) -> Result<NV, String> {
        let w = self.world();
        let v = |ty| NV { ty, opt: false };
        match t {
            rd::Type::Primitive(p) => Ok(v(self.prim_value(p)?)),
            rd::Type::Tuple(ts) if ts.is_empty() => Ok(v(self.st.ty(TyNode::Nil))),
            rd::Type::Tuple(ts) => {
                // nested tuple value: a record `{_1, _2, ...}`
                let tab = self.st.new_tab(TKind::Record, span);
                for (i, x) in ts.iter().enumerate() {
                    let s = self.n_slot(x, env, span)?;
                    self.st.tab_mut(tab).fields.insert(format!("_{}", i + 1), s);
                }
                let names: Vec<String> = (1..=ts.len()).map(|i| format!("_{i}")).collect();
                let t = self.st.tab_mut(tab);
                t.closed = true;
                t.ctors.push(names);
                t.native = Some(NativeRec::Tuple(ts.len()));
                Ok(v(self.st.ty(TyNode::Table(tab))))
            }
            rd::Type::Slice(e) | rd::Type::Array { type_: e, .. } => {
                if matches!(&**e, rd::Type::Primitive(p) if p == "u8") {
                    return Ok(v(self.st.ty(TyNode::Str)));
                }
                self.n_array(e, env, span)
            }
            rd::Type::BorrowedRef { type_, .. } => {
                // `&Path`, `&OsStr`: values of the owned form (an immutable copy)
                if let rd::Type::ResolvedPath(p) = &**type_ {
                    if w.std_kind_id(env.krate, &p.id).is_none() {
                        if let Some(r) = w.resolve(env.krate, &p.id) {
                            if let Some(t) = self.owned_form(r, span) {
                                return Ok(v(t));
                            }
                        }
                    }
                }
                self.n_val(type_, env, span)
            }
            rd::Type::Generic(n) if n == "Self" => match env.self_ty {
                Some(t) => Ok(v(t)),
                None => Err("Self outside an impl".into()),
            },
            rd::Type::Generic(n) if env.rd.contains_key(n) => {
                let (c, t) = env.rd[n].clone();
                self.n_val(&t, &NEnv { krate: c, ..Default::default() }, span)
            }
            rd::Type::Generic(n) => {
                if env.callbacks.contains_key(n) {
                    return Err(format!("callback {n} used in a non-parameter position"));
                }
                match env.gens.get(n) {
                    Some(t) => {
                        let t = *t;
                        // a pinned numeric argument is an ordinary number as a value
                        match self.st.node(t).clone() {
                            TyNode::NPrim(p) => Ok(v(self.prim_value(&p)?)),
                            _ => Ok(v(t)),
                        }
                    }
                    None => Err(format!("unbound generic parameter {n}")),
                }
            }
            rd::Type::ResolvedPath(p) => {
                if let Some(k) = w.std_kind_id(env.krate, &p.id) {
                    return self.n_std(k, p, env, span);
                }
                let Some(r) = w.resolve(env.krate, &p.id) else {
                    return Err(format!("type {} is not available (its crate is not public or not loaded)", p.path));
                };
                self.n_path(r, p, env, span)
            }
            rd::Type::QualifiedPath { name, self_type, trait_, .. } => {
                if matches!(&**self_type, rd::Type::Generic(s) if s == "Self") {
                    if let Some((c, at)) = env.assoc.get(name).cloned() {
                        return self.n_val(&at, &env.in_crate(c), span);
                    }
                }
                let tn = trait_.as_ref().map(|t| t.path.clone()).unwrap_or_default();
                Err(format!("associated type <_ as {tn}>::{name} could not be resolved"))
            }
            rd::Type::ImplTrait(bounds) => self.n_impl_trait(bounds, env, span),
            rd::Type::DynTrait(_) => Err("trait objects are unsupported in this position".into()),
            rd::Type::FunctionPointer(_) => Err("function pointers are unsupported".into()),
            rd::Type::RawPointer { .. } => Err("raw pointers are unsupported".into()),
            rd::Type::Infer | rd::Type::Pat { .. } => Err("unrecognized type".into()),
        }
    }

    pub(crate) fn n_array(&mut self, e: &rd::Type, env: &NEnv, span: Span) -> Result<NV, String> {
        // `[Option<T>]` (descriptor lists such as `color_attachments`): source arrays
        // hold the present elements (arrays cannot contain nil); a None element
        // in a native result raises when converted
        let el = self.n_val(e, env, span)?;
        let tab = self.st.new_tab(TKind::Array, span);
        let s = self.st.fixed_slot(el.ty, span, "arrays cannot contain nil");
        self.st.tab_mut(tab).elem = Some(s);
        Ok(NV { ty: self.st.ty(TyNode::Table(tab)), opt: false })
    }

    pub(crate) fn n_slot(&mut self, t: &rd::Type, env: &NEnv, span: Span) -> Result<Slot, String> {
        let nv = self.n_val(t, env, span)?;
        Ok(if nv.opt {
            self.st.optional_slot(nv.ty, span)
        } else {
            self.st.fixed_slot(nv.ty, span, "the native signature does not accept nil (not an Option)")
        })
    }

    fn n_path(&mut self, r: ItemRef, p: &rd::Path, env: &NEnv, span: Span) -> Result<NV, String> {
        let w = self.world();
        if let Some(k) = w.std_kind(r) {
            return self.n_std(k, p, env, span);
        }
        self.n_adt(r, p, env, span)
    }

    fn n_std(&mut self, k: StdKind, p: &rd::Path, env: &NEnv, span: Span) -> Result<NV, String> {
        let targs = generic_type_args(p);
        let v = |ty| NV { ty, opt: false };
        {
            let arg = |i: usize| targs.get(i).cloned();
            return match k {
                StdKind::String => Ok(v(self.st.ty(TyNode::Str))),
                StdKind::Cow | StdKind::Box | StdKind::Arc | StdKind::Rc => {
                    let inner = arg(0).ok_or("missing type argument")?;
                    match &inner {
                        rd::Type::Primitive(s) if s == "str" => Ok(v(self.st.ty(TyNode::Str))),
                        rd::Type::Slice(e) if matches!(&**e, rd::Type::Primitive(b) if b == "u8") => Ok(v(self.st.ty(TyNode::Str))),
                        rd::Type::DynTrait(_) => Err(format!("{} of a trait object is unsupported here", last_seg(&p.path))),
                        _ => self.n_val(&inner, env, span),
                    }
                }
                StdKind::Vec | StdKind::VecDeque | StdKind::HashSet | StdKind::BTreeSet => {
                    let inner = arg(0).ok_or("missing type argument")?;
                    if k == StdKind::Vec && matches!(&inner, rd::Type::Primitive(b) if b == "u8") {
                        return Ok(v(self.st.ty(TyNode::Str)));
                    }
                    self.n_array(&inner, env, span)
                }
                StdKind::Option => {
                    let inner = arg(0).ok_or("missing type argument")?;
                    let iv = self.n_val(&inner, env, span)?;
                    if iv.opt {
                        // Option<Option<T>>: `{value: T?}` keeps None and Some(None) distinct
                        let tab = self.st.new_tab(TKind::Record, span);
                        let s = self.st.optional_slot(iv.ty, span);
                        let t = self.st.tab_mut(tab);
                        t.fields.insert("value".into(), s);
                        t.closed = true;
                        t.ctors.push(vec!["value".into()]);
                        t.native = Some(NativeRec::OptBox);
                        return Ok(NV { ty: self.st.ty(TyNode::Table(tab)), opt: true });
                    }
                    Ok(NV { ty: iv.ty, opt: true })
                }
                StdKind::Result => Err("nested Result values have no source representation in this position".into()),
                StdKind::HashMap | StdKind::BTreeMap => {
                    let kt = self.n_val(&arg(0).ok_or("missing key type")?, env, span)?;
                    let vt = self.n_val(&arg(1).ok_or("missing value type")?, env, span)?;
                    if kt.opt || vt.opt {
                        return Err("maps with optional keys or values are unsupported".into());
                    }
                    let tab = self.st.new_tab(TKind::Map, span);
                    let ks = self.st.fixed_slot(kt.ty, span, "map keys cannot be nil");
                    let vs = self.st.fixed_slot(vt.ty, span, "map values cannot be nil");
                    let t = self.st.tab_mut(tab);
                    t.key = Some(ks);
                    t.val = Some(vs);
                    Ok(v(self.st.ty(TyNode::Table(tab))))
                }
                StdKind::Range | StdKind::RangeInclusive => {
                    let et = self.n_val(&arg(0).ok_or("missing type argument")?, env, span)?;
                    let tab = self.st.new_tab(TKind::Record, span);
                    for f in ["start", "end"] {
                        let s = self.st.fixed_slot(et.ty, span, "range bounds cannot be nil");
                        self.st.tab_mut(tab).fields.insert(f.into(), s);
                    }
                    let t = self.st.tab_mut(tab);
                    t.closed = true;
                    t.ctors.push(vec!["start".into(), "end".into()]);
                    t.native = Some(NativeRec::Range(k == StdKind::RangeInclusive));
                    Ok(v(self.st.ty(TyNode::Table(tab))))
                }
            };
        }
    }

    fn n_adt(&mut self, r: ItemRef, p: &rd::Path, env: &NEnv, span: Span) -> Result<NV, String> {
        let w = self.world();
        let targs = generic_type_args(p);
        let v = |ty| NV { ty, opt: false };
        match w.item(r).map(|i| &i.inner) {
            Some(rd::ItemEnum::TypeAlias(a)) => {
                // expand the alias with its arguments substituted
                let mut aenv = env.in_crate(r.krate);
                let params = gparams(&a.generics);
                let mut ai = 0;
                for gp in &params {
                    if gp.kind == GKind::Lifetime {
                        continue;
                    }
                    let at = match targs.get(ai) {
                        Some(x) => self.n_arg(x, env, span)?,
                        None => match &gp.default {
                            Some(d) => self.n_arg(d, &aenv, span)?,
                            None => self.st.var(),
                        },
                    };
                    ai += 1;
                    aenv.gens.insert(gp.name.clone(), at);
                }
                self.n_val(&a.type_.clone(), &aenv, span)
            }
            Some(rd::ItemEnum::Struct(_) | rd::ItemEnum::Enum(_) | rd::ItemEnum::Union(_)) => {
                let mut args = Vec::new();
                let mut rd_args: HashMap<String, (CrateIx, rd::Type)> = HashMap::new();
                let params = w.generics_of(r);
                let mut ai = 0;
                for gp in &params {
                    if gp.kind == GKind::Lifetime {
                        continue;
                    }
                    // a concrete argument (no generic of the caller): kept as rustdoc type so
                    // fields of that parameter convert as the real type (`L = Option<&str>`)
                    if let Some(x) = targs.get(ai) {
                        if !crate::native::wrap::contains_generic(x) {
                            rd_args.insert(gp.name.clone(), (env.krate, x.clone()));
                        } else if let rd::Type::Generic(n) = x {
                            if let Some(c) = env.rd.get(n) {
                                rd_args.insert(gp.name.clone(), c.clone());
                            }
                        }
                    }
                    let at = match targs.get(ai) {
                        Some(x) => self.n_arg(x, env, span)?,
                        None => match &gp.default {
                            Some(d) => {
                                let denv = NEnv { krate: r.krate, ..Default::default() };
                                self.n_arg(d, &denv, span)?
                            }
                            None => self.st.var(),
                        },
                    };
                    ai += 1;
                    args.push(at);
                }
                Ok(v(self.native_adt_ty_rd(r, args, rd_args, span)))
            }
            Some(rd::ItemEnum::Trait(_)) => Err(format!("trait {} used as a type", p.path)),
            _ => Err(format!("type {} is not supported", p.path)),
        }
    }

    /// Source type of a native struct/enum instantiation: a record table or a handle.
    pub(crate) fn native_adt_ty(&mut self, r: ItemRef, args: Vec<TyId>, span: Span) -> TyId {
        self.native_adt_ty_rd(r, args, HashMap::new(), span)
    }

    pub(crate) fn native_adt_ty_rd(&mut self, r: ItemRef, args: Vec<TyId>, rd_args: HashMap<String, (CrateIx, rd::Type)>, span: Span) -> TyId {
        let w = self.world();
        if w.repr(&self.facts, r) == Repr::Record {
            let tab = self.native_record_tab(r, args, rd_args, span);
            return self.st.ty(TyNode::Table(tab));
        }
        let key = w.type_key(r);
        self.st.ty(TyNode::Native(Rc::new(NativeTy { key, item: r, args })))
    }

    fn native_record_tab(&mut self, r: ItemRef, args: Vec<TyId>, rd_args: HashMap<String, (CrateIx, rd::Type)>, span: Span) -> TabId {
        let w = self.world();
        let cache_key = (r, args.clone());
        if args.is_empty() && rd_args.is_empty() {
            if let Some(t) = self.native_records.get(&cache_key) {
                return *t;
            }
        }
        let tab = self.st.new_tab(TKind::Record, span);
        self.native_records.insert(cache_key, tab);
        let fields = w.public_fields(r).unwrap_or_default();
        let mut env = NEnv { krate: r.krate, ..Default::default() };
        let mut ai = 0;
        for gp in w.generics_of(r) {
            if gp.kind != GKind::Lifetime {
                if let Some(a) = args.get(ai) {
                    env.gens.insert(gp.name.clone(), *a);
                }
                ai += 1;
            }
        }
        if matches!(w.item(r).map(|i| &i.inner), Some(rd::ItemEnum::Enum(_))) {
            // borrowing enum: `{Variant = payload?, ...}` (unit variants: `true`);
            // variants whose payload has no source form are left out
            for v in w.variants(r) {
                let ty = match &v.shape {
                    VariantShape::Unit => Ok(self.st.ty(TyNode::Bool)),
                    VariantShape::Tuple(ts) if ts.len() == 1 => self.n_slot(&ts[0], &env, span).map(|s| s.ty),
                    VariantShape::Tuple(ts) => self.n_val(&rd::Type::Tuple(ts.clone()), &env, span).map(|x| x.ty),
                    _ => continue,
                };
                if let Ok(t) = ty {
                    let s = self.st.optional_slot(t, span);
                    self.st.tab_mut(tab).fields.insert(v.name.clone(), s);
                }
            }
            let t = self.st.tab_mut(tab);
            t.closed = true;
            t.native = Some(NativeRec::Enum(r, args));
            t.hint = Some(w.name(r));
            return tab;
        }
        if !rd_args.is_empty() {
            if std::env::var_os("LUARC_DEBUG_RD").is_some() {
                eprintln!("record tab {tab} for {} rd {:?}", w.name(r), rd_args.keys().collect::<Vec<_>>());
            }
            self.info.record_rd_args.insert(tab, rd_args.clone());
        }
        for (name, ft) in &fields {
            let s = match match ft {
                rd::Type::Generic(g) if rd_args.contains_key(g) => {
                    let (c, t) = rd_args[g].clone();
                    self.n_slot(&t, &NEnv { krate: c, ..Default::default() }, span)
                }
                _ => self.n_slot(ft, &env, span),
            } {
                Ok(s) => s,
                Err(e) => {
                    self.error(span, format!("record field '{name}' of {}: {e}", w.name(r)));
                    let v = self.st.var();
                    self.st.slot(v)
                }
            };
            self.st.tab_mut(tab).fields.insert(name.clone(), s);
        }
        let t = self.st.tab_mut(tab);
        t.closed = true;
        t.native = Some(NativeRec::Struct(r, args));
        t.hint = Some(w.name(r));
        t.ctors.push(fields.iter().map(|f| f.0.clone()).collect());
        tab
    }

    fn n_impl_trait(&mut self, bounds: &[rd::GenericBound], env: &NEnv, span: Span) -> Result<NV, String> {
        // `impl Future<Output = T>`: a native future
        for p in trait_bounds(bounds) {
            if last_seg(&p.path) == "Future" {
                let out = assoc_constraints(p).into_iter().find(|(n, _)| n == "Output").map(|(_, t)| t).unwrap_or(rd::Type::Tuple(vec![]));
                let (rs, _) = self.n_rets(&out, env, span)?;
                let ft = self.future_ty(rs);
                return Ok(NV { ty: ft, opt: false });
            }
        }
        for p in trait_bounds(bounds) {
            let n = last_seg(&p.path);
            if matches!(n, "Fn" | "FnMut" | "FnOnce") {
                return Err("returns a callback (retained callbacks need a registration protocol)".into());
            }
        }
        let names: Vec<String> = trait_bounds(bounds).iter().map(|p| p.path.clone()).collect();
        let _ = env;
        Err(format!("returns an opaque `impl {}` value", names.join(" + ")))
    }

    // Environments

    /// Environment of a type's own generic parameters bound to `args`.
    pub(crate) fn type_env(&self, owner: ItemRef, args: &[TyId], self_ty: TyId) -> NEnv {
        let w = self.world();
        let mut env = NEnv { krate: owner.krate, self_ty: Some(self_ty), ..Default::default() };
        env.rd = self.self_rd(self_ty);
        let mut ai = 0;
        for gp in w.generics_of(owner) {
            if gp.kind == GKind::Lifetime {
                continue;
            }
            if let Some(a) = args.get(ai) {
                env.gens.insert(gp.name, *a);
            }
            ai += 1;
        }
        env
    }

    /// Binds an impl block's generics by matching its `for` type against the
    /// receiver's arguments. `None` when the impl does not apply to them.
    pub(crate) fn impl_env(&mut self, imp: ItemRef, owner: ItemRef, args: &[TyId], self_ty: TyId, span: Span) -> Option<NEnv> {
        let w = self.world();
        let rd::ItemEnum::Impl(i) = &w.item(imp)?.inner else { return None };
        let owner_rd = self.self_rd(self_ty);
        let owner_params: Vec<String> = w.generics_of(owner).into_iter().filter(|g| g.kind != GKind::Lifetime).map(|g| g.name).collect();
        let mut env = NEnv { krate: imp.krate, self_ty: Some(self_ty), ..Default::default() };
        if let rd::Type::ResolvedPath(fp) = &i.for_ {
            let fargs = generic_type_args(fp);
            for (k, fa) in fargs.iter().enumerate() {
                let Some(&have) = args.get(k) else { continue };
                match fa {
                    rd::Type::Generic(n) => {
                        env.gens.insert(n.clone(), have);
                        if let Some(x) = owner_params.get(k).and_then(|p| owner_rd.get(p)) {
                            env.rd.insert(n.clone(), x.clone());
                        }
                    }
                    rd::Type::Primitive(p) => {
                        // `impl Foo<u32>`: applies only to that instantiation
                        if let TyNode::NPrim(q) = self.st.node(have).clone() {
                            if &*q != p.as_str() {
                                return None;
                            }
                        }
                        if matches!(self.st.node(have), TyNode::Var) {
                            let t = self.st.ty(TyNode::NPrim(p.as_str().into()));
                            self.unify(have, t, span);
                        }
                    }
                    // `impl EventLoop<()>`: the receiver's argument is that type
                    other if !crate::native::wrap::contains_generic(other) => {
                        let ienv = NEnv { krate: imp.krate, ..Default::default() };
                        if let Ok(t) = self.n_arg(other, &ienv, span) {
                            if !self.unify(have, t, span) {
                                return None;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        for gp in gparams(&i.generics) {
            if gp.kind == GKind::Type && !env.gens.contains_key(&gp.name) {
                let bounds = param_bounds(&i.generics, &gp.name);
                if fn_bound(&bounds).is_some() {
                    env.callbacks.insert(gp.name.clone(), bounds);
                } else {
                    let v = self.st.var();
                    env.gens.insert(gp.name, v);
                }
            }
        }
        for it in w.impl_items(imp) {
            if let Some(rd::Item { name: Some(n), inner: rd::ItemEnum::AssocType { type_: Some(t), .. }, .. }) = w.item(it) {
                env.assoc.insert(n.clone(), (imp.krate, t.clone()));
            }
        }
        let _ = (owner, span);
        Some(env)
    }

    // Lookup

    /// Finds a method or associated function of a type: inherent impls first, then
    /// trait impls (trait default methods included).
    pub(crate) fn native_assoc(&mut self, owner: ItemRef, name: &str) -> Result<Option<(ItemRef, ItemRef, Option<ItemRef>)>, String> {
        let w = self.world();
        let impls = w.impls_of(owner);
        for &imp in &impls {
            let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = w.item(imp) else { continue };
            if i.trait_.is_some() || i.is_synthetic || i.is_negative {
                continue;
            }
            for it in w.impl_items(imp) {
                let item = w.item(it).unwrap();
                if item.name.as_deref() == Some(name)
                    && matches!(item.visibility, rd::Visibility::Public)
                    && !crate::native::world::is_hidden(item)
                    && matches!(item.inner, rd::ItemEnum::Function(_) | rd::ItemEnum::AssocConst { .. })
                {
                    return Ok(Some((it, imp, None)));
                }
            }
        }
        let mut found: Vec<(ItemRef, ItemRef, ItemRef)> = Vec::new();
        for &imp in &impls {
            let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = w.item(imp) else { continue };
            let Some(tp) = &i.trait_ else { continue };
            if i.is_synthetic || i.is_negative || i.blanket_impl.is_some() {
                continue;
            }
            let Some(tr) = w.resolve(imp.krate, &tp.id) else { continue };
            let in_impl = w.impl_items(imp).into_iter().find(|x| w.item(*x).and_then(|i| i.name.as_deref()) == Some(name));
            let in_trait = w.trait_items(tr).into_iter().find(|x| w.item(*x).and_then(|i| i.name.as_deref()) == Some(name));
            match (in_impl, in_trait) {
                (Some(f), _) if matches!(w.item(f).map(|i| &i.inner), Some(rd::ItemEnum::Function(_))) => found.push((f, imp, tr)),
                (None, Some(f)) if matches!(w.item(f).map(|i| &i.inner), Some(rd::ItemEnum::Function(_))) => found.push((f, imp, tr)),
                _ => {}
            }
        }
        found.dedup_by_key(|x| x.2);
        match found.len() {
            0 => Ok(None),
            1 => Ok(Some((found[0].0, found[0].1, Some(found[0].2)))),
            _ => {
                let traits: Vec<String> = found.iter().map(|f| w.name(f.2)).collect();
                Err(format!("'{name}' is provided by several traits ({}); the call is ambiguous", traits.join(", ")))
            }
        }
    }

    /// Instantiates a function item (free function, associated function, method or
    /// trait method) for one call site.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn instantiate_native(
        &mut self,
        f: ItemRef,
        owner: Option<(ItemRef, Vec<TyId>)>,
        imp: Option<ItemRef>,
        trait_: Option<ItemRef>,
        self_ty: Option<TyId>,
        span: Span,
        display: String,
    ) -> Result<usize, String> {
        let w = self.world();
        let item = w.item(f).ok_or("item not found")?;
        let rd::ItemEnum::Function(func) = &item.inner else { return Err("not a function".into()) };
        let func = func.clone();
        if func.header.is_unsafe {
            return Err("unsafe functions are never imported automatically".into());
        }
        if !matches!(func.header.abi, rd::Abi::Rust) {
            return Err("non-Rust ABI".into());
        }
        if func.sig.is_c_variadic {
            return Err("C-variadic functions are unsupported".into());
        }
        // generic environment: owner type, impl, trait, then the function's own generics
        let mut env = match (&owner, self_ty) {
            (Some((o, args)), Some(st)) => match imp {
                Some(i) => self.impl_env(i, *o, args, st, span).ok_or("the impl does not apply to these type arguments")?,
                None => self.type_env(*o, args, st),
            },
            _ => NEnv { krate: f.krate, ..Default::default() },
        };
        if let (Some(tr), Some(i)) = (trait_, imp) {
            // trait generics come from the impl's trait reference
            let tparams = w.generics_of(tr);
            if let Some(rd::Item { inner: rd::ItemEnum::Impl(ii), .. }) = w.item(i) {
                if let Some(tp) = &ii.trait_ {
                    let targs = generic_type_args(tp);
                    let ienv = env.clone();
                    let mut k = 0;
                    for gp in tparams.iter().filter(|g| g.kind == GKind::Type) {
                        if let Some(a) = targs.get(k) {
                            let t = self.n_arg(a, &ienv, span)?;
                            env.gens.insert(gp.name.clone(), t);
                        }
                        k += 1;
                    }
                }
            }
        }
        env.krate = f.krate;
        for gp in gparams(&func.generics) {
            if gp.kind != GKind::Type {
                continue;
            }
            let bounds = param_bounds(&func.generics, &gp.name);
            if fn_bound(&bounds).is_some() {
                if has_send(&bounds) {
                    return Err(format!(
                        "callback parameter {} must be Send: native code may call it from another thread, and source functions stay on their owning thread",
                        gp.name
                    ));
                }
                env.callbacks.insert(gp.name.clone(), bounds);
            } else {
                let v = self.st.var();
                env.gens.insert(gp.name.clone(), v);
            }
        }
        // `I: IntoIterator<Item = T>`: a source array of T
        for gp in gparams(&func.generics) {
            if gp.kind != GKind::Type {
                continue;
            }
            let bounds = param_bounds(&func.generics, &gp.name);
            if let (Some(item), Some(&g)) = (into_iter_item(&bounds), env.gens.get(&gp.name)) {
                let arr = self.n_array(&item, &env, span)?;
                self.unify(g, arr.ty, span);
            }
        }
        // receiver and parameters
        let mut kind = if owner.is_some() { NKind::AssocFn } else { NKind::Function };
        let mut params = Vec::new();
        for (i, (pname, pty)) in func.sig.inputs.iter().enumerate() {
            if i == 0 && pname == "self" {
                let r = match pty {
                    rd::Type::Generic(s) if s == "Self" => Recv::Value,
                    rd::Type::BorrowedRef { is_mutable, type_, .. } if matches!(&**type_, rd::Type::Generic(s) if s == "Self") => {
                        if *is_mutable {
                            Recv::Mut
                        } else {
                            Recv::Ref
                        }
                    }
                    _ => return Err("receiver type (Box/Rc/Pin self) is unsupported".into()),
                };
                kind = NKind::Method(r);
                continue;
            }
            let s = self.n_param(pty, &env, span).map_err(|e| format!("parameter {pname}: {e}"))?;
            params.push(s);
        }
        let (rets, fallible) = match &func.sig.output {
            None => (Vec::new(), false),
            Some(t) => self.n_rets(t, &env, span).map_err(|e| format!("result: {e}"))?,
        };
        // `async fn`: a native future yielding the declared results
        let (rets, fallible) = if func.header.is_async {
            let ft = self.future_ty(rets);
            (vec![self.st.fixed_slot(ft, span, "futures are never nil")], false)
        } else {
            (rets, fallible)
        };
        let recv = if matches!(kind, NKind::Method(_)) { self_ty } else { None };
        self.info.natives.push(NativeInst { kind, item: f, owner, imp, trait_, env, span, params, rets, recv, fallible, display, deref: 0 });
        Ok(self.info.natives.len() - 1)
    }

    /// Slot of a native parameter; callbacks become source function types.
    fn n_param(&mut self, t: &rd::Type, env: &NEnv, span: Span) -> Result<Slot, String> {
        if let Some((sig_in, sig_out, _, _retained, send)) = self.callback_sig(t, env) {
            if send {
                return Err("the callback must be Send: native code may call it from another thread, and source functions stay on their owning thread".into());
            }
            let mut ps = Vec::new();
            for x in &sig_in {
                if matches!(x, rd::Type::BorrowedRef { type_, .. } if matches!(&**type_, rd::Type::Primitive(p) if p != "str")) {
                    return Err("callback receives a reference to a number".into());
                }
                ps.push(self.n_slot(x, env, span)?);
            }
            let rets = match &sig_out {
                None => Vec::new(),
                Some(o) => {
                    if matches!(o, rd::Type::BorrowedRef { .. }) {
                        return Err("callbacks returning borrowed values are unsupported".into());
                    }
                    vec![self.n_slot(o, env, span)?]
                }
            };
            let r = self.st.new_rets(RetsNode::Known(rets));
            let ft = self.st.ty(TyNode::Func(Rc::new(FuncTy { params: ps, rets: r, vararg: None })));
            return Ok(self.st.fixed_slot(ft, span, "callbacks cannot be nil"));
        }
        match t {
            rd::Type::ImplTrait(b) if into_iter_item(b).is_some() => {
                let arr = self.n_array(&into_iter_item(b).unwrap(), env, span)?;
                Ok(self.st.fixed_slot(arr.ty, span, "the native signature does not accept nil (not an Option)"))
            }
            rd::Type::ImplTrait(_) => {
                // `impl Trait` argument: an anonymous generic chosen from the source value
                let v = self.st.var();
                Ok(self.st.fixed_slot(v, span, "the native signature does not accept nil (not an Option)"))
            }
            rd::Type::Primitive(p) if crate::check::is_int_prim(p) => {
                // an i64/u64 parameter takes an integer, or a number converted exactly
                let v = self.st.var();
                self.try_or_defer(crate::check::Op::IntParam { ty: v });
                Ok(self.st.fixed_slot(v, span, "the native signature does not accept nil (not an Option)"))
            }
            _ => self.n_slot(t, env, span),
        }
    }

    /// Callback parameter shape: (inputs, output, trait name, retained ('static:
    /// native code may keep it after the call), Send (cross-thread)).
    pub(crate) fn callback_sig(&self, t: &rd::Type, env: &NEnv) -> Option<(Vec<rd::Type>, Option<rd::Type>, String, bool, bool)> {
        let w = self.world();
        match t {
            rd::Type::Generic(n) => {
                let b = env.callbacks.get(n)?;
                let (tn, i, o) = fn_bound(b)?;
                Some((i, o, tn, has_static_or_send(b), has_send(b)))
            }
            rd::Type::ImplTrait(b) => {
                let (tn, i, o) = fn_bound(b)?;
                Some((i, o, tn, has_static_or_send(b), has_send(b)))
            }
            rd::Type::BorrowedRef { type_, .. } => match &**type_ {
                rd::Type::DynTrait(dt) => {
                    let bounds: Vec<rd::GenericBound> = dt
                        .traits
                        .iter()
                        .map(|p| rd::GenericBound::TraitBound { trait_: p.trait_.clone(), generic_params: vec![], modifier: rd::TraitBoundModifier::None })
                        .collect();
                    let (tn, i, o) = fn_bound(&bounds)?;
                    let send = dt.traits.iter().any(|p| matches!(last_seg(&p.trait_.path), "Send" | "Sync"));
                    Some((i, o, tn, dt.lifetime.as_deref() == Some("'static"), send))
                }
                _ => None,
            },
            rd::Type::ResolvedPath(p) => {
                if w.std_kind_id(env.krate, &p.id) != Some(StdKind::Box) {
                    return None;
                }
                let inner = generic_type_args(p).into_iter().next()?;
                let rd::Type::DynTrait(dt) = inner else { return None };
                let bounds: Vec<rd::GenericBound> = dt
                    .traits
                    .iter()
                    .map(|p| rd::GenericBound::TraitBound { trait_: p.trait_.clone(), generic_params: vec![], modifier: rd::TraitBoundModifier::None })
                    .collect();
                let (tn, i, o) = fn_bound(&bounds)?;
                let send = dt.traits.iter().any(|p| matches!(last_seg(&p.trait_.path), "Send" | "Sync"));
                Some((i, o, tn, true, send))
            }
            _ => None,
        }
    }

    /// Result slots of a native function: `Result` peeled (fallible), a tuple
    /// spread into multiple results, `()` into none.
    pub(crate) fn n_rets(&mut self, t: &rd::Type, env: &NEnv, span: Span) -> Result<(Vec<Slot>, bool), String> {
        let (inner, fallible) = self.peel_result(t, env);
        match &inner {
            rd::Type::Tuple(ts) if ts.is_empty() => Ok((Vec::new(), fallible)),
            rd::Type::Tuple(ts) => {
                let mut out = Vec::new();
                for x in ts {
                    out.push(self.n_slot(x, env, span)?);
                }
                Ok((out, fallible))
            }
            other => Ok((vec![self.n_slot(other, env, span)?], fallible)),
        }
    }

    /// `Result<T, E>` (also through aliases such as `io::Result<T>`) → (T, true).
    pub(crate) fn peel_result(&self, t: &rd::Type, env: &NEnv) -> (rd::Type, bool) {
        let w = self.world();
        if let rd::Type::ResolvedPath(p) = t {
            if w.std_kind_id(env.krate, &p.id) == Some(StdKind::Result) {
                if let Some(ok) = generic_type_args(p).into_iter().next() {
                    return (ok, true);
                }
            }
            if let Some(r) = w.resolve(env.krate, &p.id) {
                if w.std_kind(r) == Some(StdKind::Result) {
                    if let Some(ok) = generic_type_args(p).into_iter().next() {
                        return (ok, true);
                    }
                }
                if let Some(rd::Item { inner: rd::ItemEnum::TypeAlias(a), .. }) = w.item(r) {
                    if let rd::Type::ResolvedPath(ap) = &a.type_ {
                        if let Some(ar) = w.resolve(r.krate, &ap.id) {
                            if w.std_kind(ar) == Some(StdKind::Result) {
                                // substitute the alias' first parameter with our argument
                                if let (Some(ok), Some(first)) = (generic_type_args(p).into_iter().next(), gparams(&a.generics).into_iter().find(|g| g.kind == GKind::Type)) {
                                    if matches!(generic_type_args(ap).first(), Some(rd::Type::Generic(n)) if *n == first.name) {
                                        return (ok, true);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        (t.clone(), false)
    }

    /// Resolves an annotation path `alias.Type.Path` to a native type item.
    pub(crate) fn native_type_annotation(&mut self, root: ItemRef, path: &[String], sp: Span) -> Option<TyId> {
        let w = self.world();
        let mut cur = root;
        for seg in path {
            cur = w.lookup(cur, seg)?;
        }
        match w.item(cur).map(|i| &i.inner) {
            Some(rd::ItemEnum::Struct(_) | rd::ItemEnum::Enum(_) | rd::ItemEnum::Union(_)) => {
                let n = w.generics_of(cur).iter().filter(|g| g.kind != GKind::Lifetime).count();
                let args: Vec<TyId> = (0..n).map(|_| self.st.var()).collect();
                Some(self.native_adt_ty(cur, args, sp))
            }
            Some(rd::ItemEnum::TypeAlias(a)) => {
                let a = a.clone();
                let env = NEnv { krate: cur.krate, ..Default::default() };
                self.n_val(&a.type_, &env, sp).ok().map(|nv| nv.ty)
            }
            _ => None,
        }
    }
}

/// Native record kinds attached to record tables.
#[derive(Clone, Debug, PartialEq)]
pub enum NativeRec {
    /// A public-field struct (with type arguments).
    Struct(ItemRef, Vec<TyId>),
    /// An enum that borrows (`BindingResource<'a>`): one optional field per
    /// variant, exactly one set; converted to the native value at the call that
    /// uses it, where its borrows are valid.
    Enum(ItemRef, Vec<TyId>),
    /// A nested tuple `{_1, _2, ...}`.
    Tuple(usize),
    /// `Option<Option<T>>` as `{value = T?}`.
    OptBox,
    /// `Range` / `RangeInclusive` as `{start, end}`.
    Range(bool),
}

// Uses: namespaces, calls, methods, fields, variants, constants

impl<'a> Checker<'a> {
    fn display_of(&self, r: ItemRef) -> String {
        let w = self.world();
        let p = w.def_path(r);
        p[1..].join(".")
    }

    /// `ns.name` on a crate namespace (module, type, trait).
    pub(crate) fn namespace_member(&mut self, node: crate::ast::NodeId, r: ItemRef, name: &str, result: ETy, span: Span) {
        let w = self.world();
        let kind = w.item(r).map(|i| i.inner.clone());
        match kind {
            Some(rd::ItemEnum::Module(_)) => {
                let Some(t) = w.lookup(r, name) else {
                    let pkg = w.info(r.krate).package.clone();
                    let mut shown = self.display_of(r);
                    if !shown.is_empty() {
                        shown.push('.');
                    }
                    shown.push_str(name);
                    self.error(span, format!("crate '{pkg}' has no importable item '{shown}'"));
                    return;
                };
                match w.item(t).map(|i| &i.inner) {
                    Some(rd::ItemEnum::Constant { .. } | rd::ItemEnum::Static(_)) => {
                        let disp = self.display_of(t);
                        match self.instantiate_const(t, None, span, disp.clone()) {
                            Ok(inst) => self.const_result(node, inst, result, span),
                            Err(e) => self.error(span, format!("native item '{disp}' is unsupported: {e}")),
                        }
                    }
                    Some(_) => {
                        self.info.access.insert(node, Access::Namespace);
                        let t = self.st.ty(TyNode::Namespace(t));
                        let v = self.val(t);
                        self.link_result(result, v, span);
                    }
                    None => self.error(span, format!("item '{name}' is not available")),
                }
            }
            Some(rd::ItemEnum::TypeAlias(a)) => {
                // `Disc.new(...)` where `type Disc = Circle`: the aliased type's namespace
                if let rd::Type::ResolvedPath(p) = &a.type_ {
                    if let Some(t) = w.resolve(r.krate, &p.id) {
                        // the alias's concrete arguments (`RequestAdapterOptions<'a, 'b> =
                        // RequestAdapterOptionsBase<&'a Surface<'b>>`) instantiate the type
                        let mut m: HashMap<String, (CrateIx, rd::Type)> = HashMap::new();
                        let targs = generic_type_args(p);
                        for (gp, x) in w.generics_of(t).iter().filter(|g| g.kind != GKind::Lifetime).zip(targs.iter()) {
                            if !crate::native::wrap::contains_generic(x) {
                                m.insert(gp.name.clone(), (r.krate, x.clone()));
                            }
                        }
                        self.pending_alias_args = Some(m);
                        return self.namespace_member(node, t, name, result, span);
                    }
                }
                self.error(span, format!("type alias {} does not name a type with associated items", w.name(r)));
            }
            Some(rd::ItemEnum::Struct(_) | rd::ItemEnum::Enum(_) | rd::ItemEnum::Union(_)) => {
                let tname = w.name(r);
                if let Some(v) = w.variants(r).into_iter().find(|v| v.name == name) {
                    let disp = format!("{tname}.{name}");
                    if matches!(v.shape, VariantShape::Unit) {
                        match self.instantiate_variant(v.item, r, span, disp.clone(), false) {
                            Ok(inst) => self.const_result(node, inst, result, span),
                            Err(e) => self.error(span, format!("native item '{disp}' is unsupported: {e}")),
                        }
                    } else {
                        self.ns_owner.insert(v.item, (r, None));
                        self.info.access.insert(node, Access::Namespace);
                        let t = self.st.ty(TyNode::Namespace(v.item));
                        let vv = self.val(t);
                        self.link_result(result, vv, span);
                    }
                    return;
                }
                match self.native_assoc(r, name) {
                    Ok(Some((f, imp, tr))) => {
                        let disp = format!("{tname}.{name}");
                        if matches!(w.item(f).map(|i| &i.inner), Some(rd::ItemEnum::AssocConst { .. })) {
                            match self.instantiate_const(f, Some(r), span, disp.clone()) {
                                Ok(inst) => self.const_result(node, inst, result, span),
                                Err(e) => self.error(span, format!("native item '{disp}' is unsupported: {e}")),
                            }
                            return;
                        }
                        self.ns_owner.insert(f, (r, Some((imp, tr))));
                        if let Some(m) = self.pending_alias_args.take() {
                            self.ns_rd_args.insert(f, m);
                        }
                        self.info.access.insert(node, Access::Namespace);
                        let t = self.st.ty(TyNode::Namespace(f));
                        let vv = self.val(t);
                        self.link_result(result, vv, span);
                    }
                    Ok(None) => self.error(span, format!("native type {tname} has no associated item '{name}'")),
                    Err(e) => self.error(span, e),
                }
            }
            _ => {
                let d = self.display_of(r);
                self.error(span, format!("'{d}' has no member '{name}'"))
            }
        }
    }

    fn const_result(&mut self, node: crate::ast::NodeId, inst: usize, result: ETy, span: Span) {
        let ret = self.info.natives[inst].rets[0];
        self.info.access.insert(node, Access::NativeConst(inst));
        let v = ETy { ty: ret.ty, null: ret.null, soft: Soft::No };
        self.link_result(result, v, span);
    }

    /// Constants, statics and associated constants.
    fn instantiate_const(&mut self, c: ItemRef, owner: Option<ItemRef>, span: Span, display: String) -> Result<usize, String> {
        let w = self.world();
        let (ty, kind) = match w.item(c).map(|i| &i.inner) {
            Some(rd::ItemEnum::Constant { type_, .. }) => (type_.clone(), NKind::Const),
            Some(rd::ItemEnum::Static(s)) => (s.type_.clone(), NKind::Const),
            Some(rd::ItemEnum::AssocConst { type_, .. }) => (type_.clone(), NKind::AssocConst),
            _ => return Err("not a constant".into()),
        };
        let (env, own) = match owner {
            Some(o) => {
                let n = w.generics_of(o).iter().filter(|g| g.kind != GKind::Lifetime).count();
                let args: Vec<TyId> = (0..n).map(|_| self.st.var()).collect();
                let st = self.native_adt_ty(o, args.clone(), span);
                (self.type_env(o, &args, st), Some((o, args)))
            }
            None => (NEnv { krate: c.krate, ..Default::default() }, None),
        };
        let env = env.in_crate(c.krate);
        let s = self.n_slot(&ty, &env, span)?;
        self.info.natives.push(NativeInst {
            kind,
            item: c,
            owner: own,
            imp: None,
            trait_: None,
            env,
            span,
            params: vec![],
            rets: vec![s],
            recv: None,
            fallible: false,
            display,
            deref: 0,
        });
        Ok(self.info.natives.len() - 1)
    }

    /// Enum variant: a unit value or a tuple-variant constructor.
    fn instantiate_variant(&mut self, v: ItemRef, owner: ItemRef, span: Span, display: String, ctor: bool) -> Result<usize, String> {
        let w = self.world();
        let info = w.variants(owner).into_iter().find(|x| x.item == v).ok_or("variant not found")?;
        let n = w.generics_of(owner).iter().filter(|g| g.kind != GKind::Lifetime).count();
        let args: Vec<TyId> = (0..n).map(|_| self.st.var()).collect();
        let self_ty = self.native_adt_ty(owner, args.clone(), span);
        let env = self.type_env(owner, &args, self_ty);
        let mut params = Vec::new();
        match (&info.shape, ctor) {
            (VariantShape::Unit, false) => {}
            (VariantShape::Tuple(ts), true) => {
                for (i, t) in ts.iter().enumerate() {
                    params.push(self.n_slot(t, &env, span).map_err(|e| format!("field {i}: {e}"))?);
                }
            }
            (VariantShape::Struct(_), true) => {
                return Err("struct-like variants cannot be constructed from source in this version".into())
            }
            (VariantShape::Opaque, _) => return Err("the variant has private fields".into()),
            _ => return Err("not a constructor".into()),
        }
        let ret = self.st.fixed_slot(self_ty, span, "enum values are never nil");
        self.info.natives.push(NativeInst {
            kind: if ctor { NKind::VariantCtor } else { NKind::VariantConst },
            item: v,
            owner: Some((owner, args)),
            imp: None,
            trait_: None,
            env,
            span,
            params,
            rets: vec![ret],
            recv: None,
            fallible: false,
            display,
            deref: 0,
        });
        Ok(self.info.natives.len() - 1)
    }

    pub(crate) fn native_invoke(
        &mut self,
        node: crate::ast::NodeId,
        inst: usize,
        recv: Option<ETy>,
        args: &[ETy],
        spans: &[Span],
        span: Span,
    ) -> Vec<ETy> {
        self.info.calls.insert(node, CallKind::Native(inst));
        let ni = self.info.natives[inst].clone();
        if let (Some(r), Some(rt)) = (recv, ni.recv) {
            self.unify(r.ty, rt, span);
        }
        if args.len() != ni.params.len() {
            self.error(span, format!("native function '{}' expects {} argument(s), got {}", ni.display, ni.params.len(), args.len()));
        }
        for (i, p) in ni.params.iter().enumerate() {
            if let Some(a) = args.get(i) {
                self.flow(*a, *p, spans[i]);
            }
        }
        self.note_trait_args(inst, args, span);
        ni.rets.iter().map(|s| ETy { ty: s.ty, null: s.null, soft: Soft::No }).collect()
    }

    /// `ns.f(args)` where `ns.f` names a native function, associated function or
    /// tuple-variant constructor.
    pub(crate) fn native_call(&mut self, e: &crate::ast::Expr, r: ItemRef, args: &[crate::ast::Expr], want: Option<usize>) -> Vec<ETy> {
        let w = self.world();
        let (vals, spans) = self.args_values(args);
        let kind = w.item(r).map(|i| i.inner.clone());
        let res = match (kind, self.ns_owner.get(&r).cloned()) {
            (Some(rd::ItemEnum::Function(_)), None) => {
                let disp = self.display_of(r);
                self.instantiate_native(r, None, None, None, None, e.span, disp.clone()).map_err(|m| (disp, m))
            }
            (Some(rd::ItemEnum::Function(_)), Some((owner, Some((imp, tr))))) => {
                let disp = format!("{}.{}", w.name(owner), w.name(r));
                let rdm = self.ns_rd_args.get(&r).cloned().unwrap_or_default();
                if std::env::var_os("LUARC_DEBUG_RD").is_some() {
                    eprintln!("rd args for {}: {:?}", disp, rdm.keys().collect::<Vec<_>>());
                }
                let mut targs: Vec<TyId> = Vec::new();
                for gp in w.generics_of(owner).iter().filter(|g| g.kind != GKind::Lifetime) {
                    let t = match rdm.get(&gp.name) {
                        Some((c, x)) => self.n_arg(x, &NEnv { krate: *c, ..Default::default() }, e.span).unwrap_or_else(|_| self.st.var()),
                        None => self.st.var(),
                    };
                    targs.push(t);
                }
                let st = self.native_adt_ty_rd(owner, targs.clone(), rdm, e.span);
                self.instantiate_native(r, Some((owner, targs)), Some(imp), tr, Some(st), e.span, disp.clone()).map_err(|m| (disp, m))
            }
            (Some(rd::ItemEnum::Variant(_)), Some((owner, None))) => {
                let disp = format!("{}.{}", w.name(owner), w.name(r));
                self.instantiate_variant(r, owner, e.span, disp.clone(), true).map_err(|m| (disp, m))
            }
            (Some(rd::ItemEnum::Module(_)), _) => {
                self.error(e.span, "a crate namespace cannot be called");
                return vec![self.fresh_result()];
            }
            _ => {
                let d = self.display_of(r);
                self.error(e.span, format!("'{d}' is not a callable function"));
                return vec![self.fresh_result()];
            }
        };
        let out = match res {
            Ok(inst) => {
                if matches!(self.info.natives[inst].kind, NKind::Method(_)) {
                    let d = self.info.natives[inst].display.clone();
                    self.error(e.span, format!("'{d}' is a method; call it on a value with ':'"));
                }
                self.native_invoke(e.id, inst, None, &vals, &spans, e.span)
            }
            Err((d, m)) => {
                self.error(e.span, format!("native item '{d}' is unsupported: {m}"));
                return vec![self.fresh_result()];
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

    /// `obj:name(args)` on a native handle or native record.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn native_method_call(
        &mut self,
        node: crate::ast::NodeId,
        owner: ItemRef,
        targs: &[TyId],
        obj: ETy,
        name: &str,
        args: &[ETy],
        spans: &[Span],
        results: &[ETy],
        span: Span,
    ) {
        let w = self.world();
        let tname = w.name(owner);
        let disp = format!("{tname}:{name}");
        if self.adapters.close_method(w, owner, name) {
            self.info.natives.push(NativeInst {
                kind: NKind::Method(Recv::Ref),
                item: owner,
                owner: Some((owner, targs.to_vec())),
                imp: None,
                trait_: None,
                env: NEnv { krate: owner.krate, ..Default::default() },
                span,
                params: vec![],
                rets: vec![],
                recv: Some(obj.ty),
                fallible: false,
                display: disp,
                deref: 0,
            });
            let inst = self.info.natives.len() - 1;
            self.info.closes.insert(inst);
            let out = self.native_invoke(node, inst, Some(obj), args, spans, span);
            self.bind_results(results, &out, span);
            return;
        }
        let rust_name = self.adapters.rust_name(w, owner, name).unwrap_or_else(|| name.to_string());
        match self.native_assoc(owner, &rust_name) {
            Ok(Some((f, imp, tr))) => {
                if !matches!(w.item(f).map(|i| &i.inner), Some(rd::ItemEnum::Function(_))) {
                    self.error(span, format!("'{disp}' is not a method"));
                    return;
                }
                match self.instantiate_native(f, Some((owner, targs.to_vec())), Some(imp), tr, Some(obj.ty), span, disp.clone()) {
                    Ok(inst) => {
                        if !matches!(self.info.natives[inst].kind, NKind::Method(_)) {
                            self.error(span, format!("'{tname}.{name}' is an associated function, not a method; call it as {tname}.{name}(...)"));
                        }
                        let out = self.native_invoke(node, inst, Some(obj), args, spans, span);
                        self.bind_results(results, &out, span);
                    }
                    Err(m) => self.error(span, format!("native type {tname} has no supported method '{name}' (unsupported: {m})")),
                }
            }
            Ok(None) => {
                if !self.deref_method_call(node, owner, targs, obj, name, &rust_name, args, spans, results, span) {
                    self.error(span, format!("native type {tname} has no supported method '{name}'"));
                }
            }
            Err(m) => self.error(span, m),
        }
    }

    /// Method of a `Deref` target (`PathBuf` → `Path::join`), up to three steps.
    #[allow(clippy::too_many_arguments)]
    fn deref_method_call(
        &mut self,
        node: crate::ast::NodeId,
        owner: ItemRef,
        targs: &[TyId],
        obj: ETy,
        name: &str,
        rust_name: &str,
        args: &[ETy],
        spans: &[Span],
        results: &[ETy],
        span: Span,
    ) -> bool {
        let w = self.world();
        let (mut cur, mut cur_args, mut cur_ty) = (owner, targs.to_vec(), obj.ty);
        for steps in 1..=3u8 {
            let Some(t) = self.deref_target(cur, &cur_args, cur_ty, span) else { return false };
            let TyNode::Native(nt) = self.st.node(t).clone() else { return false };
            if let Ok(Some((f, imp, tr))) = self.native_assoc(nt.item, rust_name) {
                if !matches!(w.item(f).map(|i| &i.inner), Some(rd::ItemEnum::Function(_))) {
                    return false;
                }
                let disp = format!("{}:{name}", w.name(nt.item));
                match self.instantiate_native(f, Some((nt.item, nt.args.clone())), Some(imp), tr, Some(t), span, disp.clone()) {
                    Ok(inst) => {
                        match self.info.natives[inst].kind {
                            NKind::Method(Recv::Value) => {
                                self.error(span, format!("'{disp}' consumes its receiver, which is reached through Deref from {}; it cannot be moved out", w.name(owner)));
                                return true;
                            }
                            NKind::Method(_) => {}
                            _ => {
                                self.error(span, format!("'{}.{name}' is an associated function, not a method", w.name(nt.item)));
                                return true;
                            }
                        }
                        self.info.natives[inst].recv = Some(obj.ty);
                        self.info.natives[inst].deref = steps;
                        let out = self.native_invoke(node, inst, Some(obj), args, spans, span);
                        self.bind_results(results, &out, span);
                    }
                    Err(m) => self.error(span, format!("native type {} has no supported method '{name}' (unsupported: {m})", w.name(nt.item))),
                }
                return true;
            }
            cur = nt.item;
            cur_args = nt.args.clone();
            cur_ty = t;
        }
        false
    }

    pub(crate) fn native_method_ret_count(&mut self, owner: ItemRef, name: &str) -> Option<usize> {
        let w = self.world();
        let rust_name = self.adapters.rust_name(w, owner, name).unwrap_or_else(|| name.to_string());
        let (f, _, _) = self.native_assoc(owner, &rust_name).ok()??;
        let rd::ItemEnum::Function(func) = &w.item(f)?.inner else { return None };
        let Some(out) = &func.sig.output else { return Some(0) };
        let env = NEnv { krate: f.krate, ..Default::default() };
        let (inner, _) = self.peel_result(out, &env);
        Some(match inner {
            rd::Type::Tuple(ts) => ts.len(),
            _ => 1,
        })
    }

    /// `obj.name` on a native handle: a public field, or an enum variant's payload.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn native_field_access(
        &mut self,
        node: crate::ast::NodeId,
        nt: &NativeTy,
        obj_ty: TyId,
        name: &str,
        result: ETy,
        write: Option<ETy>,
        span: Span,
    ) {
        let w = self.world();
        let tname = w.name(nt.item);
        let env = self.type_env(nt.item, &nt.args, obj_ty);
        if w.is_enum(nt.item) {
            let Some(v) = w.variants(nt.item).into_iter().find(|v| v.name == name) else {
                let names: Vec<String> = w.variants(nt.item).into_iter().map(|v| v.name).collect();
                self.error(span, format!("enum {tname} has no variant '{name}' (variants: {})", names.join(", ")));
                return;
            };
            if write.is_some() {
                self.error(span, format!("cannot assign to variant '{name}' of enum {tname}"));
                return;
            }
            let payload: Result<NV, String> = match &v.shape {
                VariantShape::Unit => Ok(NV { ty: self.st.ty(TyNode::Bool), opt: false }),
                VariantShape::Tuple(ts) if ts.len() == 1 => match self.n_val(&ts[0], &env, span) {
                    Ok(nv) if nv.opt => Err("an optional payload cannot be read through an optional accessor".into()),
                    Ok(nv) => Ok(NV { ty: nv.ty, opt: true }),
                    Err(e) => Err(e),
                },
                VariantShape::Tuple(ts) => {
                    let fs: Vec<(String, rd::Type)> = ts.iter().enumerate().map(|(i, t)| (format!("_{}", i + 1), t.clone())).collect();
                    self.payload_record(&fs, &env, span).map(|ty| NV { ty, opt: true })
                }
                VariantShape::Struct(fs) => self.payload_record(fs, &env, span).map(|ty| NV { ty, opt: true }),
                VariantShape::Opaque => Err("the variant has private fields".into()),
            };
            match payload {
                Ok(nv) => {
                    let s = if nv.opt { self.st.optional_slot(nv.ty, span) } else { self.st.fixed_slot(nv.ty, span, "payload") };
                    self.info.natives.push(NativeInst {
                        kind: NKind::Payload(name.to_string()),
                        item: v.item,
                        owner: Some((nt.item, nt.args.clone())),
                        imp: None,
                        trait_: None,
                        env,
                        span,
                        params: vec![],
                        rets: vec![s],
                        recv: Some(obj_ty),
                        fallible: false,
                        display: format!("{tname}.{name}"),
                        deref: 0,
                    });
                    let inst = self.info.natives.len() - 1;
                    self.info.access.insert(node, Access::NativeField(inst, None));
                    self.link_result(result, ETy { ty: s.ty, null: s.null, soft: Soft::No }, span);
                }
                Err(m) => self.error(span, format!("payload of {tname}.{name} is unsupported: {m}")),
            }
            return;
        }
        let Some((_, fty)) = w.readable_fields(nt.item).into_iter().find(|(n, _)| n == name) else {
            self.error(span, format!("native type {tname} has no public field '{name}' (call methods with ':')"));
            return;
        };
        let s = match self.n_slot(&fty, &env, span) {
            Ok(s) => s,
            Err(m) => {
                self.error(span, format!("field '{name}' of {tname} is unsupported: {m}"));
                return;
            }
        };
        let mk = |ck: &mut Self, kind: NKind| -> usize {
            ck.info.natives.push(NativeInst {
                kind,
                item: nt.item,
                owner: Some((nt.item, nt.args.clone())),
                imp: None,
                trait_: None,
                env: env.clone(),
                span,
                params: vec![s],
                rets: vec![s],
                recv: Some(obj_ty),
                fallible: false,
                display: format!("{tname}.{name}"),
                deref: 0,
            });
            ck.info.natives.len() - 1
        };
        let get = mk(self, NKind::FieldGet(name.to_string()));
        match write {
            Some(v) => {
                let set = mk(self, NKind::FieldSet(name.to_string()));
                self.info.access.insert(node, Access::NativeField(get, Some(set)));
                self.unify(result.ty, s.ty, span);
                self.flow(v, s, span);
            }
            None => {
                self.info.access.insert(node, Access::NativeField(get, None));
                self.link_result(result, ETy { ty: s.ty, null: s.null, soft: Soft::No }, span);
            }
        }
    }

    /// A source record holding a variant's payload fields.
    fn payload_record(&mut self, fields: &[(String, rd::Type)], env: &NEnv, span: Span) -> Result<TyId, String> {
        let tab = self.st.new_tab(TKind::Record, span);
        for (n, t) in fields {
            let s = self.n_slot(t, env, span)?;
            self.st.tab_mut(tab).fields.insert(n.clone(), s);
        }
        let t = self.st.tab_mut(tab);
        t.closed = true;
        t.ctors.push(fields.iter().map(|f| f.0.clone()).collect());
        Ok(self.st.ty(TyNode::Table(tab)))
    }
}

impl<'a> Checker<'a> {
    /// Whether a native type is an `Option<_>`.
    pub(crate) fn peel_option_ty(&self, t: &rd::Type, env: &NEnv) -> bool {
        let w = self.world();
        match t {
            rd::Type::ResolvedPath(p) => {
                if w.std_kind_id(env.krate, &p.id) == Some(StdKind::Option) {
                    return true;
                }
                // through an alias (`Label<'a> = Option<&'a str>`)
                if let Some(r) = w.resolve(env.krate, &p.id) {
                    if let Some(rd::Item { inner: rd::ItemEnum::TypeAlias(a), .. }) = w.item(r) {
                        return self.peel_option_ty(&a.type_.clone(), &NEnv { krate: r.krate, ..Default::default() });
                    }
                }
                false
            }
            rd::Type::Generic(n) => match env.rd.get(n) {
                Some((c, x)) => self.peel_option_ty(x, &NEnv { krate: *c, ..Default::default() }),
                None => false,
            },
            _ => false,
        }
    }
}

impl<'a> Checker<'a> {
    /// Concrete rustdoc arguments of a native record type (by parameter name).
    pub(crate) fn self_rd(&self, t: TyId) -> HashMap<String, (CrateIx, rd::Type)> {
        match self.st.node(t) {
            TyNode::Table(tab) => self.info.record_rd_args.get(&self.st.tab_root(*tab)).cloned().unwrap_or_default(),
            _ => HashMap::new(),
        }
    }
}
