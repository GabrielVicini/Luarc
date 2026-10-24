//! Generation of wrapper functions between source values and imported Rust items.
//!
//! Every native use in the program goes through one generated wrapper per
//! instantiation. A wrapper:
//! 1. converts each source argument into its native form, staging borrowed
//!    parts (string slices, `&T` handle borrows, slices, descriptor records with
//!    references) in locals that live for exactly the duration of the call;
//! 2. consumes by-value handles last, after every fallible conversion, so a
//!    failed conversion never consumes an object;
//! 3. calls the Rust item (an explicit turbofish for generic functions);
//! 4. converts the result back (`Result::Err` becomes a language error, tuples
//!    become multiple results, owned data becomes new tables, objects become
//!    handles, borrowed parts of handles become owner-retaining views).
//!
//! Rust's type checker validates every wrapper; a rejected instantiation is
//! reported at the source call site by the build driver.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use rustdoc_types as rd;

use crate::check_native::{NEnv, NKind, NativeInst, NativeRec, Recv};
use crate::codegen::{native_ident, rust_ident, rust_str_lit, tuple_ty, Gen};
use crate::native::types::*;
use crate::native::world::ItemRef;
use crate::types::{TKind, TyId, TyNode};

fn ident_part(s: &str) -> String {
    let mut o = String::new();
    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            o.push(c);
        } else if !o.ends_with('_') {
            o.push('_');
        }
    }
    o.trim_matches('_').to_string()
}

#[derive(Default)]
pub struct WCtx {
    /// Staging statements (run before the call; their locals outlive it).
    pub pre: String,
    /// Handles consumed by the call: (place, method) — checked together, taken last.
    pub takes: Vec<(String, String)>,
    /// Arrays of handles consumed by the call: (snapshot name, item name). Their
    /// elements join the `takes` check, and their conversion runs after it.
    pub take_arrays: Vec<(String, String)>,
    /// Statements run after the call (write-back of `&mut` records).
    pub post: String,
    pub callbacks: bool,
    pub n: u32,
    /// Name of the item for consumption messages.
    pub what: String,
}

impl WCtx {
    pub fn tmp(&mut self, base: &str) -> String {
        self.n += 1;
        format!("__{base}{}", self.n)
    }
}

/// How a by-value handle argument is produced.
enum ByValue {
    Copy,
    SharedClone,
    Consume,
}

impl<'a> Gen<'a> {
    pub(crate) fn w(&self) -> &'a crate::native::world::World {
        self.ck.world
    }

    // Naming

    /// Public Rust path of a native item.
    pub(crate) fn item_path(&self, r: ItemRef) -> Result<String, String> {
        if let Some(p) = self.w().rust_path(r) {
            return Ok(p);
        }
        // only reachable through a public alias: the alias names it in paths
        if let Some((_, p)) = self.w().alias_for(r) {
            return Ok(p);
        }
        self.w().rust_path(r).ok_or_else(|| format!("{} is not reachable through a public path of a dependency", self.w().def_path(r).join("::")))
    }

    /// Native type a source type converts to by default (`number` → `f64`,
    /// `string` → `String`, native handles → their Rust type).
    pub(crate) fn src_rust(&mut self, t: TyId) -> Result<String, String> {
        Ok(match self.node(t) {
            TyNode::Num => "f64".into(),
            TyNode::Int => "i128".into(),
            TyNode::NPrim(p) => p.to_string(),
            TyNode::Str => "String".into(),
            TyNode::Bool => "bool".into(),
            TyNode::Nil => "()".into(),
            TyNode::Native(nt) => self.handle_inner_ty(nt.item, &nt.args)?,
            TyNode::Table(tab) => {
                let tn = self.ck.st.tab(tab).clone();
                match (&tn.native, tn.kind) {
                    (Some(NativeRec::Struct(r, args)), _) => {
                        let rd = self.ck.info.record_rd_args.get(&self.ck.st.tab_root(tab)).cloned();
                        self.adt_ty_rd(*r, args, "'static", rd.as_ref())?
                    }
                    (Some(NativeRec::Enum(r, args)), _) => self.adt_ty_rd(*r, args, "'static", None)?,
                    (_, TKind::Array) => format!("Vec<{}>", self.src_rust(tn.elem.map(|s| s.ty).unwrap_or(t))?),
                    (_, TKind::Map) => format!(
                        "std::collections::HashMap<{}, {}>",
                        self.src_rust(tn.key.map(|s| s.ty).unwrap_or(t))?,
                        self.src_rust(tn.val.map(|s| s.ty).unwrap_or(t))?
                    ),
                    _ => return Err(format!("a {} value cannot instantiate a native generic parameter", self.ck.show(t))),
                }
            }
            _ => return Err(format!("a {} value cannot instantiate a native generic parameter", self.ck.show(t))),
        })
    }

    /// `path<args>` of a struct/enum instantiation; lifetimes become `lt`.
    pub(crate) fn adt_ty(&mut self, r: ItemRef, args: &[TyId], lt: &str) -> Result<String, String> {
        self.adt_ty_rd(r, args, lt, None)
    }

    /// Like [`Gen::adt_ty`]; concrete rustdoc arguments (`rd`) render as written.
    pub(crate) fn adt_ty_rd(&mut self, r: ItemRef, args: &[TyId], lt: &str, rd: Option<&HashMap<String, (usize, rd::Type)>>) -> Result<String, String> {
        if self.w().rust_path(r).is_none() {
            if let Some((a, path)) = self.w().alias_for(r) {
                // named by its alias: the alias's own (lifetime) parameters
                let ps: Vec<String> = self.w().generics_of(a).iter().map(|g| if g.kind == GKind::Lifetime { lt.to_string() } else { "_".to_string() }).collect();
                return Ok(if ps.is_empty() { path } else { format!("{path}<{}>", ps.join(", ")) });
            }
        }
        let base = self.item_path(r)?;
        let params = self.w().generics_of(r);
        let mut parts = Vec::new();
        let mut ai = 0;
        for gp in &params {
            match gp.kind {
                GKind::Lifetime => parts.push(lt.to_string()),
                _ => {
                    if let Some((c, t)) = rd.and_then(|m| m.get(&gp.name)).cloned() {
                        parts.push(self.rty(&t, &NEnv { krate: c, ..Default::default() }, lt)?);
                        ai += 1;
                        continue;
                    }
                    match args.get(ai) {
                        Some(a) => parts.push(self.src_rust(*a)?),
                        None => parts.push("_".into()),
                    }
                    ai += 1;
                }
            }
        }
        Ok(if parts.is_empty() { base } else { format!("{base}<{}>", parts.join(", ")) })
    }

    /// Whether handles of this type share the native object (`Arc<T>`): a
    /// `Send + Sync`, non-`Clone` type used only through `&self`.
    pub(crate) fn shared_repr(&self, r: ItemRef) -> bool {
        let w = self.w();
        let traits = w.trait_names(r);
        if !traits.contains("Send") || !traits.contains("Sync") || traits.contains("Clone") || traits.contains("Copy") {
            return false;
        }
        // reading an enum's payload moves it out of the value
        if matches!(w.item(r), Some(rd::Item { inner: rd::ItemEnum::Enum(_), .. })) {
            return false;
        }
        // every method of every impl (inherent and trait impls such as `Write` for
        // `File`) must take `&self`: a shared object is never mutated or moved
        let mut any_ref = false;
        for imp in w.impls_of(r) {
            let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = w.item(imp) else { continue };
            if i.blanket_impl.is_some() || i.is_synthetic || !matches!(&i.for_, rd::Type::ResolvedPath(_)) {
                continue;
            }
            // `Drop::drop` runs once the last owner releases it
            if i.trait_.as_ref().map(|t| last_seg(&t.path) == "Drop").unwrap_or(false) {
                continue;
            }
            let inherent = i.trait_.is_none();
            for it in w.impl_items(imp) {
                let Some(rd::Item { inner: rd::ItemEnum::Function(f), visibility, .. }) = w.item(it) else { continue };
                if inherent && !matches!(visibility, rd::Visibility::Public) {
                    continue;
                }
                match f.sig.inputs.first() {
                    Some((n, rd::Type::BorrowedRef { is_mutable: false, .. })) if n == "self" => any_ref = true,
                    Some((n, _)) if n == "self" => return false,
                    _ => {}
                }
            }
        }
        any_ref
    }

    /// Rust type stored in `lr::Handle<..>` for a native type.
    pub(crate) fn handle_inner_ty(&mut self, r: ItemRef, args: &[TyId]) -> Result<String, String> {
        let t = self.adt_ty(r, args, "'static")?;
        Ok(if self.shared_repr(r) { format!("std::sync::Arc<{t}>") } else { t })
    }

    /// Renders a rustdoc type in the wrapper's environment.
    pub(crate) fn rty(&mut self, t: &rd::Type, env: &NEnv, lt: &str) -> Result<String, String> {
        let w = self.w();
        Ok(match t {
            rd::Type::Primitive(p) => p.clone(),
            rd::Type::Tuple(ts) => {
                let v: Result<Vec<String>, String> = ts.iter().map(|x| self.rty(x, env, lt)).collect();
                tuple_ty(&v?)
            }
            rd::Type::Slice(e) => format!("[{}]", self.rty(e, env, lt)?),
            rd::Type::Array { type_, len } => format!("[{}; {len}]", self.rty(type_, env, lt)?),
            rd::Type::BorrowedRef { is_mutable, type_, .. } => {
                format!("&{}{}", if *is_mutable { "mut " } else { "" }, self.rty(type_, env, lt)?)
            }
            rd::Type::Generic(n) if n == "Self" => match env.self_ty {
                Some(s) => self.src_rust(s)?,
                // inside a generated trait impl
                None => "Self".into(),
            },
            rd::Type::Generic(n) if env.rd.contains_key(n) => {
                let (c, t2) = env.rd[n].clone();
                return self.rty(&t2, &NEnv { krate: c, ..Default::default() }, lt);
            }
            rd::Type::Generic(n) => match env.gens.get(n) {
                Some(g) => self.src_rust(*g)?,
                None => "_".into(),
            },
            rd::Type::ResolvedPath(p) => {
                let base = match w.std_kind_id(env.krate, &p.id) {
                    Some(k) => k.std_path().to_string(),
                    None => {
                        let r = w.resolve(env.krate, &p.id).ok_or_else(|| format!("type {} is not available", p.path))?;
                        match w.item(r).map(|i| &i.inner) {
                            Some(rd::ItemEnum::Trait(_)) => return Err(format!("trait {} in type position", p.path)),
                            _ => self.item_path(r)?,
                        }
                    }
                };
                match p.args.as_deref() {
                    Some(rd::GenericArgs::AngleBracketed { args, constraints }) if !args.is_empty() || !constraints.is_empty() => {
                        let mut parts = Vec::new();
                        for a in args {
                            parts.push(match a {
                                rd::GenericArg::Lifetime(_) => lt.to_string(),
                                rd::GenericArg::Type(t) => self.rty(t, env, lt)?,
                                rd::GenericArg::Const(c) => c.expr.clone(),
                                rd::GenericArg::Infer => "_".into(),
                            });
                        }
                        // trailing defaulted parameters are left implicit
                        format!("{base}<{}>", parts.join(", "))
                    }
                    _ => base,
                }
            }
            rd::Type::QualifiedPath { name, self_type, .. } => {
                if matches!(&**self_type, rd::Type::Generic(s) if s == "Self") {
                    if let Some((c, at)) = env.assoc.get(name).cloned() {
                        return self.rty(&at, &env.in_crate(c), lt);
                    }
                }
                "_".into()
            }
            _ => "_".into(),
        })
    }

    // Handles

    /// Helpers constructing a handle for a native Rust type (once per type).
    /// Returns (constructor fn, meta static).
    pub(crate) fn handle_support(&mut self, rust_ty: &str, short: &str) -> (String, String) {
        let name = ident_part(rust_ty);
        let name = if name.len() > 60 { format!("{}_{:x}", &name[..40], fx(rust_ty)) } else { name };
        let meta = format!("META_{}", name.to_uppercase());
        let key = format!("{rust_ty}#support");
        if !self.handle_makers.contains_key(&key) {
            let code = format!(
                "fn show_{name}(v: &{rust_ty}, out: &mut Vec<u8>) {{\n    lr::show_native!(v, out)\n}}\nfn eq_{name}(a: &{rust_ty}, b: &{rust_ty}) -> Option<bool> {{\n    lr::eq_native!(a, b)\n}}\n/// Formatting and equality of `{short}` handles.\npub static {meta}: lr::HandleMeta<{rust_ty}> = lr::HandleMeta {{ type_name: {}, show: show_{name}, eq: eq_{name} }};\n",
                rust_str_lit(short)
            );
            self.handle_makers.insert(key, code);
        }
        (format!("mk_{name}"), meta)
    }

    fn mk_handle(&mut self, r: ItemRef, args: &[TyId], expr: &str, owner: Option<&str>) -> Result<String, String> {
        let inner = self.handle_inner_ty(r, args)?;
        let short = self.w().name(r);
        let (_, meta) = self.handle_support(&inner, &short);
        let v = if self.shared_repr(r) { format!("std::sync::Arc::new({expr})") } else { expr.to_string() };
        Ok(match owner {
            Some(o) => format!("lr::Handle::with_owner({v}, &{meta}, {o}.as_owner())"),
            None => format!("lr::Handle::new({v}, &{meta})"),
        })
    }

    fn by_value_mode(&self, r: ItemRef) -> ByValue {
        let traits = self.w().trait_names(r);
        if traits.contains("Copy") {
            ByValue::Copy
        } else if self.shared_repr(r) {
            ByValue::SharedClone
        } else {
            ByValue::Consume
        }
    }

    /// A by-value native argument from a handle.
    fn handle_by_value(&mut self, r: ItemRef, place: &str, w: &mut WCtx, want_arc: bool) -> String {
        match self.by_value_mode(r) {
            ByValue::Copy => format!("*{place}.get()?"),
            ByValue::SharedClone if want_arc => format!("(*{place}.get()?).clone()"),
            ByValue::SharedClone | ByValue::Consume => {
                let t = w.tmp("own");
                w.takes.push((place.to_string(), t.clone()));
                if self.shared_repr(r) && !want_arc {
                    let _ = writeln!(w.pre, "    {place}.check_unshared({})?;", rust_str_lit(&self.w().name(r)));
                    format!("lr::conv::unwrap_shared({t}, {})?", rust_str_lit(&self.w().name(r)))
                } else {
                    t
                }
            }
        }
    }

    // Arguments

    /// Bounds governing how a generic/`impl Trait` argument is produced.
    fn bound_names(bounds: &[rd::GenericBound]) -> Vec<String> {
        trait_bounds(bounds).iter().map(|p| last_seg(&p.path).to_string()).collect()
    }

    fn wants_bytes(bounds: &[rd::GenericBound]) -> bool {
        trait_bounds(bounds).iter().any(|p| {
            let n = last_seg(&p.path);
            let inner = generic_type_args(p);
            (n == "AsRef" || n == "Into" || n == "Borrow")
                && inner.iter().any(|t| match t {
                    rd::Type::Slice(e) => matches!(&**e, rd::Type::Primitive(b) if b == "u8"),
                    rd::Type::ResolvedPath(v) => v.path.ends_with("Vec") && generic_type_args(v).iter().any(|x| matches!(x, rd::Type::Primitive(b) if b == "u8")),
                    _ => false,
                })
        })
    }

    /// A generic or `impl Trait` argument: the native form is chosen from the
    /// source value's type and the parameter's bounds; rustc validates the bounds.
    fn generic_arg(&mut self, bounds: &[rd::GenericBound], place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let names = Self::bound_names(bounds);
        let by_ref = names.iter().any(|n| matches!(n.as_str(), "AsRef" | "Borrow" | "Display" | "Debug" | "Hash" | "ToString"));
        Ok(match self.node(src) {
            TyNode::Int => place.to_string(),
            TyNode::NPrim(p) if crate::check::is_int_prim(&p) => format!("lr::int::from_int::<{p}>({place})?"),
            TyNode::Num => place.to_string(),
            TyNode::NPrim(p) => format!("lr::conv::from_num::<{p}>({place})?"),
            TyNode::Bool => place.to_string(),
            TyNode::Str => {
                if Self::wants_bytes(bounds) {
                    format!("{place}.as_bytes().to_vec()")
                } else {
                    format!("{place}.to_utf8_string()?")
                }
            }
            TyNode::Native(nt) => {
                if by_ref {
                    let g = w.tmp("g");
                    let _ = writeln!(w.pre, "    let {g} = {place}.get()?;");
                    if self.shared_repr(nt.item) {
                        format!("&**{g}")
                    } else {
                        format!("&*{g}")
                    }
                } else {
                    self.handle_by_value(nt.item, place, w, true)
                }
            }
            TyNode::Table(tab) => {
                let tn = self.ck.st.tab(tab).clone();
                match (&tn.native, tn.kind) {
                    (Some(NativeRec::Struct(..)), _) => self.record_in(place, src, w)?,
                    (Some(NativeRec::Enum(..)), _) => self.enum_in(place, src, w)?,
                    (_, TKind::Array) => {
                        let el = tn.elem.map(|s| s.ty).unwrap_or(src);
                        let e = w.tmp("e");
                        let mut inner = WCtx { n: w.n + 100, what: w.what.clone(), ..Default::default() };
                        let c = self.generic_arg(&[], &e, el, &mut inner)?;
                        w.n = inner.n;
                        let unshared = take_unshared_checks(&mut inner);
                        if !inner.takes.is_empty() && inner.pre.is_empty() {
                            // an array of objects consumed by the call (`queue:submit({encoder:finish()})`):
                            // every element is checked first, then all are taken
                            let hs = w.tmp("hs");
                            let what = rust_str_lit(&w.what);
                            let _ = writeln!(w.pre, "    let {hs} = {place}.snapshot();");
                            if !unshared.is_empty() {
                                let _ = writeln!(w.pre, "    for {e} in &{hs} {{ {unshared} }}");
                            }
                            w.take_arrays.push((hs.clone(), what.clone()));
                            let take = inner.takes[0].1.clone();
                            let c2 = replace_ident(&c, &take, &format!("{e}.take({what})?"));
                            return Ok(format!("{hs}.iter().map(|{e}| -> lr::LResult<_> {{ Ok({c2}) }}).collect::<lr::LResult<Vec<_>>>()?"));
                        }
                        if !inner.pre.is_empty() && inner.takes.is_empty() {
                            return self.staged_generic_vec(place, el, w);
                        }
                        if !inner.pre.is_empty() || !inner.takes.is_empty() {
                            return Err("arrays mixing borrowed and consumed values are unsupported here".into());
                        }
                        format!("{place}.snapshot().into_iter().map(|{e}| -> lr::LResult<_> {{ Ok({c}) }}).collect::<lr::LResult<Vec<_>>>()?")
                    }
                    _ => return Err(format!("a {} value cannot instantiate a native generic parameter", self.ck.show(src))),
                }
            }
            _ => return Err(format!("a {} value cannot instantiate a native generic parameter", self.ck.show(src))),
        })
    }

    /// Source value at `place` → native value of type `t` (an argument).
    pub(crate) fn conv_in(&mut self, t: &rd::Type, env: &NEnv, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let wd = self.w();
        if let Some(c) = self.callback_in(t, env, place, src, w)? {
            return Ok(c);
        }
        Ok(match t {
            rd::Type::Primitive(p) => match p.as_str() {
                "bool" => place.to_string(),
                "f64" => place.to_string(),
                "char" => format!("lr::conv::to_char(&{place})?"),
                _ if crate::check::is_int_prim(p) => match self.node(src) {
                    TyNode::Num => format!("lr::int::from_num_int::<{p}>({place})?"),
                    _ => format!("lr::int::from_int::<{p}>({place})?"),
                },
                _ => format!("lr::conv::from_num::<{p}>({place})?"),
            },
            rd::Type::Tuple(ts) if ts.is_empty() => "()".into(),
            rd::Type::Tuple(ts) => self.tuple_in(ts, env, place, src, w)?,
            rd::Type::Generic(n) if env.rd.contains_key(n) => {
                let (c, t2) = env.rd[n].clone();
                return self.conv_in(&t2, &NEnv { krate: c, ..Default::default() }, place, src, w);
            }
            rd::Type::Generic(n) if n != "Self" && matches!(self.node(src), TyNode::Native(_)) && self.cur_into.contains_key(n) => {
                // `BG` that only has to become `&BindGroup` / `Option<&BindGroup>`:
                // lend the object instead of consuming it
                let target = self.cur_into[n].clone();
                match &target {
                    rd::Type::BorrowedRef { is_mutable, type_, .. } => self.ref_in(type_, *is_mutable, env, place, src, w)?,
                    _ => match self.option_inner(&target, env) {
                        Some(rd::Type::BorrowedRef { is_mutable, type_, .. }) => format!("Some({})", self.ref_in(&type_, is_mutable, env, place, src, w)?),
                        _ => return Err("unexpected Into target".into()),
                    },
                }
            }
            rd::Type::Generic(n) if n != "Self" => {
                let b = self.cur_bounds.get(n).cloned().unwrap_or_default();
                match into_iter_item(&b) {
                    Some(item) => self.vec_in(&item, env, place, src, w)?,
                    None => self.generic_arg(&b, place, src, w)?,
                }
            }
            rd::Type::ImplTrait(bounds) => match into_iter_item(bounds) {
                Some(item) => self.vec_in(&item, env, place, src, w)?,
                None => self.generic_arg(bounds, place, src, w)?,
            },
            rd::Type::Generic(_) => self.value_in(place, src, w, env)?,
            rd::Type::BorrowedRef { is_mutable, type_, .. } => self.ref_in(type_, *is_mutable, env, place, src, w)?,
            rd::Type::Slice(_) | rd::Type::Array { .. } => {
                let rd::Type::Array { type_, len } = t else { return Err("unsized slice by value".into()) };
                let v = self.vec_in(type_, env, place, src, w)?;
                format!("lr::conv::to_fixed_array::<_, {len}>({v})?")
            }
            rd::Type::ResolvedPath(p) => {
                let sk = wd.std_kind_id(env.krate, &p.id);
                let targs = generic_type_args(p);
                match sk {
                    Some(StdKind::String) => format!("{place}.to_utf8_string()?"),
                    Some(StdKind::Vec) if matches!(targs.first(), Some(rd::Type::Primitive(b)) if b == "u8") => format!("{place}.as_bytes().to_vec()"),
                    Some(StdKind::Vec | StdKind::VecDeque) => {
                        let v = self.vec_in(&targs[0], env, place, src, w)?;
                        if sk == Some(StdKind::VecDeque) {
                            format!("std::collections::VecDeque::from({v})")
                        } else {
                            v
                        }
                    }
                    Some(StdKind::Option) => self.option_in(&targs[0], env, place, src, w)?,
                    Some(StdKind::Box) => format!("Box::new({})", self.conv_in(&targs[0], env, place, src, w)?),
                    Some(StdKind::Cow) => match targs.first() {
                        Some(rd::Type::Primitive(s)) if s == "str" => format!("std::borrow::Cow::Owned({place}.to_utf8_string()?)"),
                        _ => return Err("Cow parameters other than Cow<str> are unsupported".into()),
                    },
                    Some(StdKind::Range | StdKind::RangeInclusive) => {
                        let r_ = w.tmp("rg");
                        let _ = writeln!(w.pre, "    let {r_} = {place}.borrow();");
                        let el = self.record_field_src(src, "start")?;
                        let s = self.conv_in(&targs[0], env, &format!("{r_}.start.clone()"), el, w)?;
                        let e = self.conv_in(&targs[0], env, &format!("{r_}.end.clone()"), el, w)?;
                        if sk == Some(StdKind::Range) {
                            format!("({s})..({e})")
                        } else {
                            format!("({s})..=({e})")
                        }
                    }
                    Some(StdKind::HashMap | StdKind::BTreeMap) => return Err("map parameters are unsupported".into()),
                    Some(StdKind::Result) => return Err("Result parameters are unsupported".into()),
                    Some(StdKind::Arc | StdKind::Rc) => {
                        // a shared native object: pass the shared pointer itself
                        match self.node(src) {
                            TyNode::Native(nt) if self.shared_repr(nt.item) => format!("(*{place}.get()?).clone()"),
                            _ => {
                                let inner = self.conv_in(&targs[0], env, place, src, w)?;
                                let k = if sk == Some(StdKind::Arc) { "std::sync::Arc" } else { "std::rc::Rc" };
                                format!("{k}::new({inner})")
                            }
                        }
                    }
                    Some(StdKind::HashSet | StdKind::BTreeSet) => {
                        let v = self.vec_in(&targs[0], env, place, src, w)?;
                        format!("{v}.into_iter().collect()")
                    }
                    None => {
                        let r = wd.resolve(env.krate, &p.id).ok_or_else(|| format!("type {} is not available", p.path))?;
                        if let Some(rd::Item { inner: rd::ItemEnum::TypeAlias(a), .. }) = wd.item(r) {
                            // an alias (`Label<'a> = Option<&'a str>`): convert as its definition,
                            // its type parameters bound to the concrete arguments written here
                            let mut aenv = NEnv { krate: r.krate, ..Default::default() };
                            let targs = generic_type_args(p);
                            for (gp, x) in gparams(&a.generics).iter().filter(|g| g.kind == GKind::Type).zip(targs.iter()) {
                                if contains_generic(x) {
                                    return Err(format!("alias {} with generic arguments is unsupported here", p.path));
                                }
                                aenv.rd.insert(gp.name.clone(), (env.krate, x.clone()));
                            }
                            let at = a.type_.clone();
                            return self.conv_in(&at, &aenv, place, src, w);
                        }
                        self.value_in(place, src, w, env)?
                    }
                }
            }
            _ => return Err(format!("unsupported parameter type {}", self.rty(t, env, "'_").unwrap_or_default())),
        })
    }

    /// A value of the source type's own native form (records, handles by value).
    fn value_in(&mut self, place: &str, src: TyId, w: &mut WCtx, _env: &NEnv) -> Result<String, String> {
        Ok(match self.node(src) {
            TyNode::Native(nt) => self.handle_by_value(nt.item, place, w, false),
            TyNode::Table(tab) if matches!(self.ck.st.tab(tab).native, Some(NativeRec::Struct(..))) => self.record_in(place, src, w)?,
            TyNode::Table(tab) if matches!(self.ck.st.tab(tab).native, Some(NativeRec::Enum(..))) => self.enum_in(place, src, w)?,
            TyNode::Str => {
                // a path/OsString-like parameter receiving a string (validated UTF-8)
                format!("std::convert::From::from({place}.as_str()?)")
            }
            TyNode::Int => place.to_string(),
            TyNode::NPrim(p) if crate::check::is_int_prim(&p) => format!("lr::int::from_int::<{p}>({place})?"),
            TyNode::Num => place.to_string(),
            TyNode::NPrim(p) => format!("lr::conv::from_num::<{p}>({place})?"),
            TyNode::Bool => place.to_string(),
            _ => return Err(format!("a {} value has no native form here", self.ck.show(src))),
        })
    }

    fn vec_in(&mut self, el: &rd::Type, env: &NEnv, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        if let Some(inner_el) = self.option_inner(el, env) {
            // elements of `[Option<T>]` are present values
            let v = self.vec_in(&inner_el, env, place, src, w)?;
            return Ok(format!("{v}.into_iter().map(Some).collect::<Vec<_>>()"));
        }
        let elem_ty = match self.node(src) {
            TyNode::Table(tab) => self.ck.st.tab(tab).elem.map(|s| s.ty).unwrap_or(src),
            _ => src,
        };
        let e = w.tmp("e");
        let mut inner = WCtx { n: w.n + 1000, what: w.what.clone(), ..Default::default() };
        let c = self.conv_in(el, env, &e, elem_ty, &mut inner)?;
        w.n = inner.n;
        let unshared = take_unshared_checks(&mut inner);
        if !inner.takes.is_empty() && inner.pre.is_empty() {
            // objects consumed by the call: every element is checked, then all taken
            let hs = w.tmp("hs");
            let what = rust_str_lit(&w.what);
            let _ = writeln!(w.pre, "    let {hs} = {place}.snapshot();");
            if !unshared.is_empty() {
                let _ = writeln!(w.pre, "    for {e} in &{hs} {{ {unshared} }}");
            }
            w.take_arrays.push((hs.clone(), what.clone()));
            let take = inner.takes[0].1.clone();
            let c2 = replace_ident(&c, &take, &format!("{e}.take({what})?"));
            return Ok(format!("{hs}.iter().map(|{e}| -> lr::LResult<_> {{ Ok({c2}) }}).collect::<lr::LResult<Vec<_>>>()?"));
        }
        if !inner.takes.is_empty() {
            return Err("arrays of objects consumed by the call with borrowed parts are unsupported".into());
        }
        if !inner.pre.is_empty() {
            return self.staged_vec_in(el, env, place, elem_ty, w);
        }
        Ok(format!("{place}.snapshot().into_iter().map(|{e}| -> lr::LResult<_> {{ Ok({c}) }}).collect::<lr::LResult<Vec<_>>>()?"))
    }

    /// `Option<T>` → `T`.
    pub(crate) fn option_inner(&self, t: &rd::Type, env: &NEnv) -> Option<rd::Type> {
        if let rd::Type::ResolvedPath(p) = t {
            if self.w().std_kind_id(env.krate, &p.id) == Some(StdKind::Option) {
                return generic_type_args(p).into_iter().next();
            }
        }
        None
    }

    /// Arrays whose elements borrow (descriptor records with references, `&str`
    /// elements): stage each element's borrowed parts in vectors that outlive the
    /// call, then build the native vector borrowing from them.
    fn staged_vec_in(&mut self, el: &rd::Type, env: &NEnv, place: &str, elem_ty: TyId, w: &mut WCtx) -> Result<String, String> {
        let src = w.tmp("src");
        let _ = writeln!(w.pre, "    let {src} = {place}.snapshot();");
        // one staged element per source element, built by a per-element closure
        // whose staging locals are hoisted into vectors
        let i = w.tmp("i");
        let mut inner = WCtx { n: w.n + 1000, what: w.what.clone(), ..Default::default() };
        let ev = format!("{src}[{i}].clone()");
        let c = self.conv_in(el, env, &ev, elem_ty, &mut inner)?;
        w.n = inner.n;
        emit_staged(&inner.pre, &c, &ev, &src, &i, w)
    }

    /// `&T` / `&mut T` arguments.
    fn ref_in(&mut self, t: &rd::Type, mutable: bool, env: &NEnv, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let wd = self.w();
        if let Some(c) = self.callback_in(&rd::Type::BorrowedRef { lifetime: None, is_mutable: mutable, type_: Box::new(t.clone()) }, env, place, src, w)? {
            return Ok(c);
        }
        match t {
            rd::Type::Primitive(p) if p == "str" => {
                if mutable {
                    return Err("&mut str parameters are unsupported".into());
                }
                return Ok(format!("{place}.as_str()?"));
            }
            rd::Type::Slice(e) => {
                if mutable {
                    return Err("mutable slices into source tables need a write-back adapter".into());
                }
                if matches!(&**e, rd::Type::Primitive(b) if b == "u8") {
                    return Ok(format!("{place}.as_bytes()"));
                }
                let v = self.vec_in(e, env, place, src, w)?;
                let s = w.tmp("s");
                let _ = writeln!(w.pre, "    let {s}: Vec<_> = {v};");
                return Ok(format!("&{s}[..]"));
            }
            rd::Type::Primitive(_) => return Err("reference to a primitive".into()),
            _ => {}
        }
        // path-like parameters accept strings (`&Path`, `&OsStr`)
        if let rd::Type::ResolvedPath(p) = t {
            if matches!(self.node(src), TyNode::Str) {
                if wd.std_kind_id(env.krate, &p.id) == Some(StdKind::String) {
                    let s = w.tmp("p");
                    let _ = writeln!(w.pre, "    let {}{s} = {place}.to_utf8_string()?;", if mutable { "mut " } else { "" });
                    return Ok(format!("&{}{s}", if mutable { "mut " } else { "" }));
                }
                if let Some(r) = wd.resolve(env.krate, &p.id) {
                    let sp = wd.std_path(r).unwrap_or_default();
                    if sp.ends_with("path::Path") || sp.ends_with("ffi::os_str::OsStr") {
                        let s = w.tmp("p");
                        let _ = writeln!(w.pre, "    let {s} = {place}.as_str()?;");
                        return Ok(format!("{}::new({s})", self.item_path(r)?));
                    }
                }
            }
        }
        match self.node(src) {
            TyNode::Native(nt) => {
                let g = w.tmp("g");
                let deref = if self.shared_repr(nt.item) { "**" } else { "*" };
                if mutable {
                    let _ = writeln!(w.pre, "    let mut {g} = {place}.get_mut()?;");
                    Ok(format!("&mut {deref}{g}"))
                } else {
                    let _ = writeln!(w.pre, "    let {g} = {place}.get()?;");
                    Ok(format!("&{deref}{g}"))
                }
            }
            TyNode::Table(tab) if matches!(self.ck.st.tab(tab).native, Some(NativeRec::Enum(..))) && !mutable => {
                let r = w.tmp("en");
                let c = self.enum_in(place, src, w)?;
                let _ = writeln!(w.pre, "    let {r} = {c};");
                Ok(format!("&{r}"))
            }
            TyNode::Table(tab) if matches!(self.ck.st.tab(tab).native, Some(NativeRec::Struct(..))) => {
                let r = w.tmp("rec");
                let c = self.record_in(place, src, w)?;
                if mutable {
                    let _ = writeln!(w.pre, "    let mut {r} = {c};");
                    let back = self.record_out_assign(&r, place, src)?;
                    let _ = writeln!(w.post, "    {back}");
                    Ok(format!("&mut {r}"))
                } else {
                    let _ = writeln!(w.pre, "    let {r} = {c};");
                    Ok(format!("&{r}"))
                }
            }
            _ => {
                // `&T` of a value type (String, Vec, generic): stage an owned value
                let v = w.tmp("v");
                let c = self.conv_in(t, env, place, src, w)?;
                let _ = writeln!(w.pre, "    let {}{v} = {c};", if mutable { "mut " } else { "" });
                Ok(format!("&{}{v}", if mutable { "mut " } else { "" }))
            }
        }
    }

    /// `Option<T>` argument from an optional source value: staged borrows of the
    /// inner value become optional staged values.
    fn option_in(&mut self, inner_ty: &rd::Type, env: &NEnv, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let x = w.tmp("x");
        let xo = format!("{x}o");
        let _ = writeln!(w.pre, "    let {xo} = {place}.clone();");
        let mut inner_w = WCtx { n: w.n + 3000, what: w.what.clone(), ..Default::default() };
        let inner = self.conv_in(inner_ty, env, &format!("{x}.clone()"), src, &mut inner_w)?;
        w.n = inner_w.n;
        w.callbacks |= inner_w.callbacks;
        if !inner_w.takes.is_empty() {
            return Err("optional arguments consumed by the call are unsupported".into());
        }
        // staged borrows of the inner value become optional staged values
        let mut inner2 = inner.clone();
        let mut prev: Vec<(String, String)> = Vec::new();
        for line in inner_w.pre.lines() {
            let l = line.trim();
            let Some(rest) = l.strip_prefix("let ") else { return Err("unsupported staging".into()) };
            let (lhs, rhs) = rest.split_once(" = ").ok_or("unsupported staging")?;
            let mutable = lhs.starts_with("mut ");
            let name = lhs.trim_start_matches("mut ").split(':').next().unwrap().trim().to_string();
            // a declared type stays, wrapped (a staged `Vec<_>` is what tells
            // `collect` its target)
            let ann = lhs.split_once(':').map(|(_, t)| format!(": Option<{}>", t.trim())).unwrap_or_default();
            // earlier staged values are optional now: reach them through the Some
            let mut rhs = rhs.trim_end_matches(';').to_string();
            // a staged borrow reaches the value inside the option
            // itself rather than a temporary copy of it
            rhs = rhs.replace(&format!("{x}.clone()."), &format!("{x}."));
            for (n, acc) in &prev {
                rhs = replace_ident(&rhs, n, acc).replace(&format!("({acc})"), acc);
            }
            let rhs = rhs.as_str();
            let _ = writeln!(w.pre, "    let {}{name}{ann} = match &{xo} {{ Some({x}) => Some({rhs}), None => None }};", if mutable { "mut " } else { "" });
            let acc = if mutable { format!("(*{name}.as_mut().unwrap())") } else { format!("(*{name}.as_ref().unwrap())") };
            inner2 = replace_ident(&inner2, &name, &acc).replace(&format!("({acc})"), &acc);
            prev.push((name.clone(), acc));
        }
        let inner2 = inner2.replace(&format!("{x}.clone()."), &format!("{x}."));
        Ok(format!("match &{xo} {{ Some({x}) => Some({inner2}), None => None }}"))
    }

    fn is_enum_record(&self, t: TyId) -> bool {
        match self.node(t) {
            TyNode::Table(tab) => matches!(self.ck.st.tab(self.ck.st.tab_root(tab)).native, Some(NativeRec::Enum(..))),
            _ => false,
        }
    }

    /// Native payload type of an enum variant: its single field, or a tuple of
    /// its fields (shown to source code as a tuple record).
    fn variant_payload(v: &VariantInfo) -> Option<rd::Type> {
        match &v.shape {
            VariantShape::Tuple(ts) if ts.len() == 1 => Some(ts[0].clone()),
            VariantShape::Tuple(ts) => Some(rd::Type::Tuple(ts.clone())),
            _ => None,
        }
    }

    /// Borrowing enum record `{Variant = payload?, ...}` → native enum.
    /// Every variant's payload is converted like an optional argument
    /// (its borrows staged only when the field is set), exactly one field must
    /// be set, and the value is built here, inside the call that uses it, so
    /// `BindingResource::Buffer(BufferBinding { buffer: &*guard, .. })` borrows
    /// a guard that outlives the call.
    fn enum_in(&mut self, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let TyNode::Table(tab) = self.node(src) else { return Err("expected an enum record".into()) };
        let root = self.ck.st.tab_root(tab);
        let Some(NativeRec::Enum(r, args)) = self.ck.st.tab(root).native.clone() else { return Err("expected an enum record".into()) };
        let wd = self.w();
        let env = self.ck.type_env(r, &args, src);
        let ename = wd.name(r);
        let rname = self.record_name(root);
        let path = self.item_path(r)?;
        let rv = w.tmp("en");
        let _ = writeln!(w.pre, "    let {rv}: {rname} = {place}.borrow().clone();");
        let mut set = Vec::new();
        let mut arms = Vec::new();
        for v in wd.variants(r) {
            let Some(fslot) = self.ck.st.tab(root).fields.get(&v.name).copied() else { continue };
            let fplace = format!("{rv}.{}", rust_ident(&v.name));
            let vpath = format!("{path}::{}", native_ident(&v.name));
            let Some(pt) = Self::variant_payload(&v) else {
                // unit variant: `{Name = true}`
                let on = format!("{fplace} == Some(true)");
                set.push(on.clone());
                arms.push(format!("if {on} {{ {vpath} }}"));
                continue;
            };
            set.push(format!("{fplace}.is_some()"));
            // a variant whose payload cannot be converted fails only when used
            let mut vw = WCtx { n: w.n, what: w.what.clone(), ..Default::default() };
            match self.option_in(&pt, &env, &fplace, fslot.ty, &mut vw) {
                Ok(c) => {
                    w.n = vw.n;
                    w.pre.push_str(&vw.pre);
                    w.post.push_str(&vw.post);
                    w.takes.extend(vw.takes);
                    w.take_arrays.extend(vw.take_arrays);
                    w.callbacks |= vw.callbacks;
                    let cv = w.tmp("ev");
                    let _ = writeln!(w.pre, "    let {cv} = {c};");
                    let arm = match &v.shape {
                        VariantShape::Tuple(ts) if ts.len() > 1 => {
                            let ps: Vec<String> = (0..ts.len()).map(|i| format!("{cv}_{i}")).collect();
                            format!("if let Some(({},)) = {cv} {{ {vpath}({}) }}", ps.join(", "), ps.join(", "))
                        }
                        _ => format!("if let Some({cv}_v) = {cv} {{ {vpath}({cv}_v) }}"),
                    };
                    arms.push(arm);
                }
                Err(_) => arms.push(format!(
                    "if {fplace}.is_some() {{ lr::conv::unsupported_variant({}, {})? }}",
                    rust_str_lit(&ename),
                    rust_str_lit(&v.name)
                )),
            }
        }
        // a `let`, like every staging statement (arrays hoist them per element)
        let one = w.tmp("one");
        let _ = writeln!(w.pre, "    let {one}: () = lr::conv::one_variant(&[{}], {})?;", set.join(", "), rust_str_lit(&ename));
        arms.push("{ unreachable!(\"one variant is set\") }".into());
        Ok(format!("{{ {} }}", arms.join(" else ")))
    }

    /// Native borrowing enum → its record `{Variant = payload?, ...}`.
    fn enum_out(&mut self, expr: &str, dst: TyId, w: &mut WCtx) -> Result<String, String> {
        let TyNode::Table(tab) = self.node(dst) else { return Err("expected an enum record".into()) };
        let root = self.ck.st.tab_root(tab);
        let Some(NativeRec::Enum(r, args)) = self.ck.st.tab(root).native.clone() else { return Err("expected an enum record".into()) };
        let wd = self.w();
        let env = self.ck.type_env(r, &args, dst);
        let ename = wd.name(r);
        let rname = self.record_name(root);
        let path = self.item_path(r)?;
        let names: Vec<String> = self.ck.st.tab(root).fields.keys().cloned().collect();
        let fields_with = |set: &str, val: &str| -> String {
            names.iter().map(|n| if n == set { format!("{}: Some({val})", rust_ident(n)) } else { format!("{}: None", rust_ident(n)) }).collect::<Vec<_>>().join(", ")
        };
        let v = w.tmp("ev");
        let mut arms = Vec::new();
        for var in wd.variants(r) {
            let Some(fslot) = self.ck.st.tab(root).fields.get(&var.name).copied() else { continue };
            let vpath = format!("{path}::{}", native_ident(&var.name));
            match &var.shape {
                VariantShape::Unit => arms.push(format!("{vpath} => lr::Rec::new(crate::records::{rname} {{ {} }}),", fields_with(&var.name, "true"))),
                VariantShape::Tuple(ts) => {
                    let ps: Vec<String> = (0..ts.len()).map(|i| format!("{v}_{i}")).collect();
                    let (pt, pe) = if ts.len() == 1 { (ts[0].clone(), ps[0].clone()) } else { (rd::Type::Tuple(ts.clone()), format!("({},)", ps.join(", "))) };
                    let mut vw = WCtx { n: w.n, what: w.what.clone(), ..Default::default() };
                    match self.conv_out(&pt, &env, &pe, fslot.ty, &mut vw) {
                        Ok(c) if vw.pre.is_empty() && vw.post.is_empty() => {
                            w.n = vw.n;
                            arms.push(format!("{vpath}({}) => lr::Rec::new(crate::records::{rname} {{ {} }}),", ps.join(", "), fields_with(&var.name, &c)));
                        }
                        _ => arms.push(format!(
                            "{vpath}(..) => lr::conv::unsupported_variant({}, {})?,",
                            rust_str_lit(&ename),
                            rust_str_lit(&var.name)
                        )),
                    }
                }
                _ => {}
            }
        }
        arms.push(format!("#[allow(unreachable_patterns)] _ => lr::conv::unrepresentable(\"a {ename} variant with no source form\")?,"));
        Ok(format!("{{ match {expr} {{ {} }} }}", arms.join(" ")))
    }

    /// Constructor (`BindingResource.Buffer(b)`) or unit value of a borrowing
    /// enum: builds the record, no native value.
    fn enum_variant_wrapper(&mut self, ni: &NativeInst, name: &str) -> Result<String, String> {
        let dst = ni.rets[0].ty;
        let TyNode::Table(tab) = self.node(dst) else { return Err("expected an enum record".into()) };
        let root = self.ck.st.tab_root(tab);
        let rname = self.record_name(root);
        let vname = self.w().name(ni.item);
        let fslot = *self.ck.st.tab(root).fields.get(&vname).ok_or("this variant has no source form")?;
        let mut params = Vec::new();
        for (i, p) in ni.params.iter().enumerate() {
            let sty = self.slot_ty(*p);
            params.push(format!("a{i}: {sty}"));
        }
        let val = match ni.params.len() {
            0 => "true".to_string(),
            1 => "a0".to_string(),
            n => {
                // several fields: the tuple record
                let TyNode::Table(tt) = self.node(fslot.ty) else { return Err("expected a tuple record".into()) };
                let troot = self.ck.st.tab_root(tt);
                let tname = self.record_name(troot);
                let fs: Vec<String> = (0..n)
                    .map(|i| {
                        let f = format!("_{}", i + 1);
                        let v = if self.field_store_opt(troot, &f) { format!("Some(a{i})") } else { format!("a{i}") };
                        format!("{}: {v}", rust_ident(&f))
                    })
                    .collect();
                format!("lr::Rec::new(crate::records::{tname} {{ {} }})", fs.join(", "))
            }
        };
        let fields: Vec<String> = self
            .ck
            .st
            .tab(root)
            .fields
            .keys()
            .map(|n| if *n == vname { format!("{}: Some({val})", rust_ident(n)) } else { format!("{}: None", rust_ident(n)) })
            .collect();
        let rets_ty = self.rets_ty(&ni.rets);
        Ok(format!(
            "/// `{}` (a borrowing enum: built as a record of its variants)\npub fn {name}({}) -> lr::LResult<{rets_ty}> {{\n    Ok(lr::Rec::new(crate::records::{rname} {{ {} }}))\n}}\n",
            ni.display,
            params.join(", "),
            fields.join(", ")
        ))
    }

    /// Converts a source tuple record `{_1, _2, ...}` to a native tuple.
    /// This allows nested tuple values, such as the constants in wgpu's
    /// `PipelineCompilationOptions`, to be passed back to native code.
    fn tuple_in(&mut self, ts: &[rd::Type], env: &NEnv, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let TyNode::Table(tab) = self.node(src) else { return Err("expected a tuple record {_1, _2, ...}".into()) };
        let root = self.ck.st.tab_root(tab);
        let rv = w.tmp("tu");
        // typed: staged in an array, rustc must know it before the field reads
        let name = self.record_name(root);
        let _ = writeln!(w.pre, "    let {rv}: {name} = {place}.borrow().clone();");
        let mut parts = Vec::new();
        for (i, x) in ts.iter().enumerate() {
            let fname = format!("_{}", i + 1);
            let fslot = self.ck.st.tab(root).fields.get(&fname).copied().ok_or("tuple record field mismatch")?;
            let fplace = format!("{rv}.{}", rust_ident(&fname));
            let fv = if self.field_store_opt(root, &fname) && self.option_inner(x, env).is_none() {
                let msg = format!("tuple element {fname} is nil");
                format!("lr::present({fplace}.clone(), {})?", rust_str_lit(&msg))
            } else {
                format!("{fplace}.clone()")
            };
            let tmp = w.tmp("f");
            let _ = writeln!(w.pre, "    let {tmp} = {fv};");
            let c = self.conv_in(x, env, &tmp, fslot.ty, w)?;
            // like record_in: bind fallible conversions before building the value
            let c = if c.contains('?') && !w.takes.iter().any(|(_, t)| c.contains(t.as_str())) {
                let fc = w.tmp("fc");
                let _ = writeln!(w.pre, "    let {fc} = {c};");
                fc
            } else {
                c
            };
            parts.push(c);
        }
        Ok(format!("({},)", parts.join(", ")))
    }

    /// Source record (table) → native struct value.
    pub(crate) fn record_in(&mut self, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let TyNode::Table(tab) = self.node(src) else { return Err("expected a record".into()) };
        let root = self.ck.st.tab_root(tab);
        let Some(NativeRec::Struct(r, args)) = self.ck.st.tab(root).native.clone() else { return Err("expected a native record".into()) };
        let wd = self.w();
        let fields = wd.public_fields(r).ok_or("record has private fields")?;
        let path = self.item_path(r)?;
        let env = self.ck.type_env(r, &args, src);
        let rv = w.tmp("r");
        let _ = writeln!(w.pre, "    let {rv} = {place}.borrow().clone();");
        let mut parts = Vec::new();
        for (fname, fty) in &fields {
            let fslot = self.ck.st.tab(root).fields.get(fname).copied().ok_or("record field mismatch")?;
            let store_opt = self.field_store_opt(root, fname);
            let fplace = format!("{rv}.{}", rust_ident(fname));
            let (fty, fenv) = self.field_rd_type(root, fty, &env);
            let fis_opt = self.ck.peel_option_ty(&fty, &fenv);
            let fv = if store_opt && !fis_opt {
                let msg = format!("field '{fname}' of {} is nil", wd.name(r));
                format!("lr::present({fplace}.clone(), {})?", rust_str_lit(&msg))
            } else {
                format!("{fplace}.clone()")
            };
            let tmp = w.tmp("f");
            let _ = writeln!(w.pre, "    let {tmp} = {fv};");
            let c = self.conv_in(&fty, &fenv, &tmp, fslot.ty, w)?;
            // bind fallible conversions now, so building the struct cannot fail
            // after a consumed value has been taken
            let c = if c.contains('?') && !w.takes.iter().any(|(_, t)| c.contains(t.as_str())) {
                let fc = w.tmp("fc");
                let _ = writeln!(w.pre, "    let {fc} = {c};");
                fc
            } else {
                c
            };
            parts.push(format!("{}: {c}", native_ident(fname)));
        }
        Ok(format!("{path} {{ {} }}", parts.join(", ")))
    }

    fn record_field_src(&self, src: TyId, f: &str) -> Result<TyId, String> {
        let TyNode::Table(tab) = self.node(src) else { return Err("expected a record".into()) };
        Ok(self.ck.st.tab(tab).fields.get(f).ok_or("missing field")?.ty)
    }

    /// Writes a native struct back into a source record (after `&mut` calls).
    fn record_out_assign(&mut self, native: &str, place: &str, src: TyId) -> Result<String, String> {
        let mut w = WCtx::default();
        let rec = self.record_out(native, src, &mut w, true)?;
        Ok(format!("{{ {} let __nv = {rec}; let __old = std::mem::replace(&mut *{place}.borrow_mut(), __nv.borrow().clone()); lr::value::release(__old); }}", w.pre))
    }

    /// Callback parameters: a source closure lent to the native call.
    fn callback_in(&mut self, t: &rd::Type, env: &NEnv, place: &str, src: TyId, w: &mut WCtx) -> Result<Option<String>, String> {
        let Some((inputs, output, _tn, retained, _send)) = self.ck.callback_sig(t, env) else { return Ok(None) };
        // a retained callback ('static: kept by native code after the call) owns a
        // clone of the function value; while registered it keeps the function and
        // its captures alive, and dropping the registration releases them
        let fplace = if retained {
            let fv = w.tmp("cbf");
            let _ = writeln!(w.pre, "    let {fv} = {place}.clone();");
            fv
        } else {
            place.to_string()
        };
        let place = fplace.as_str();
        let f = match self.node(src) {
            TyNode::Func(f) => f,
            _ => return Err("callback argument is not a function".into()),
        };
        w.callbacks = true;
        let mut ps = Vec::new();
        let mut args = Vec::new();
        let mut cbw = WCtx { n: w.n + 2000, ..Default::default() };
        for (i, p) in inputs.iter().enumerate() {
            let pn = format!("p{i}");
            ps.push(format!("{pn}: {}", self.rty(p, env, "'_")?));
            let pt = f.params.get(i).map(|s| s.ty).unwrap_or(src);
            args.push(self.conv_out(p, env, &pn, pt, &mut cbw)?);
        }
        let rets = self.ck.st.rets_known(f.rets).cloned().unwrap_or_default();
        let (rt, body) = match &output {
            None => ("()".to_string(), format!("{place}.call({})?; Ok(())", tuple_ty(&args))),
            Some(o) => {
                let rty = rets.first().map(|s| s.ty).unwrap_or(src);
                let mut inner = WCtx { n: cbw.n + 100, ..Default::default() };
                let conv = self.conv_in(o, env, "__r", rty, &mut inner)?;
                if !inner.pre.is_empty() || !inner.takes.is_empty() {
                    return Err("callbacks returning borrowed values are unsupported".into());
                }
                (self.rty(o, env, "'_")?, format!("let __r = {place}.call({})?; Ok({conv})", tuple_ty(&args)))
            }
        };
        let c = w.tmp("cb");
        let mutable = matches!(t, rd::Type::BorrowedRef { is_mutable: true, .. });
        // Represent the callback expression as a raw leaf; the IR printer constructs
        // the coroutine boundary and its closure.
        let legacy_call = format!("(|| -> lr::LResult<{rt}> {{ {}{body} }})()", cbw.pre);
        let invocation = if self.ck.info.calls.values().any(|kind| matches!(kind, crate::check::CallKind::Coroutine(_))) {
            let body = crate::rir::RExpr::Raw(legacy_call);
            let protected = crate::rir::call("lr::callback::protect", vec![crate::rir::closure("", body)]);
            crate::rir::call("lr::callback::unwrap_or_unwind", vec![protected]).full()
        } else { format!("lr::callback::unwrap_or_unwind({legacy_call})") };
        let _ = writeln!(
            w.pre,
            "    let {}{c} = {}|{}| -> {rt} {{\n        {invocation}\n    }};",
            if mutable { "mut " } else { "" },
            if retained { "move " } else { "" },
            ps.join(", "),
        );
        Ok(Some(match t {
            rd::Type::BorrowedRef { is_mutable: false, .. } => format!("&{c}"),
            rd::Type::BorrowedRef { is_mutable: true, .. } => format!("&mut {c}"),
            rd::Type::ResolvedPath(p) if self.w().std_kind_id(env.krate, &p.id) == Some(StdKind::Box) => format!("Box::new({c})"),
            _ => c,
        }))
    }

    // Results

    /// Native value `expr` of type `t` → source value of type `dst`.
    pub(crate) fn conv_out(&mut self, t: &rd::Type, env: &NEnv, expr: &str, dst: TyId, w: &mut WCtx) -> Result<String, String> {
        let wd = self.w();
        Ok(match t {
            rd::Type::Primitive(p) => match p.as_str() {
                "bool" => expr.to_string(),
                "f64" => expr.to_string(),
                "f32" => format!("({expr} as f64)"),
                "char" => format!("lr::conv::from_char({expr})"),
                "str" => format!("lr::LStr::from({expr})"),
                _ if crate::check::is_int_prim(p) => format!("lr::int::to_int({expr})?"),
                _ => format!("lr::conv::to_num({expr})?"),
            },
            rd::Type::Tuple(ts) if ts.is_empty() => "()".into(),
            rd::Type::Tuple(ts) => {
                // nested tuple → record {_1, _2, ...}
                let TyNode::Table(tab) = self.node(dst) else { return Err("expected a tuple record".into()) };
                let root = self.ck.st.tab_root(tab);
                let name = self.record_name(root);
                let v = w.tmp("tu");
                let names: Vec<String> = (0..ts.len()).map(|i| format!("{v}_{i}")).collect();
                let mut fields = Vec::new();
                for (i, x) in ts.iter().enumerate() {
                    let fname = format!("_{}", i + 1);
                    let fslot = self.ck.st.tab(root).fields[&fname];
                    let c = self.conv_out(x, env, &names[i], fslot.ty, w)?;
                    let c = if self.field_store_opt(root, &fname) && !self.ck.st.is_null(fslot.null) { format!("Some({c})") } else { c };
                    fields.push(format!("{}: {c}", rust_ident(&fname)));
                }
                format!("{{ let {} = {expr}; lr::Rec::new(crate::records::{name} {{ {} }}) }}", tuple_ty(&names), fields.join(", "))
            }
            rd::Type::Slice(e) | rd::Type::Array { type_: e, .. } => {
                if matches!(&**e, rd::Type::Primitive(b) if b == "u8") {
                    return Ok(format!("lr::LStr::from_bytes(&{expr})"));
                }
                self.arr_out(e, env, &format!("{expr}.into_iter()"), dst, w)?
            }
            rd::Type::BorrowedRef { type_, .. } => self.ref_out(type_, env, expr, dst, w)?,
            rd::Type::Generic(n) if env.rd.contains_key(n) => {
                let (c, t2) = env.rd[n].clone();
                return self.conv_out(&t2, &NEnv { krate: c, ..Default::default() }, expr, dst, w);
            }
            rd::Type::Generic(n) if n == "Self" => {
                let st = env.self_ty.ok_or("Self outside an impl")?;
                self.src_out(expr, st, dst, w)?
            }
            rd::Type::Generic(n) => {
                let g = *env.gens.get(n).ok_or_else(|| format!("generic result {n} was not instantiated"))?;
                self.src_out(expr, g, dst, w)?
            }
            rd::Type::ResolvedPath(p) => {
                let sk = wd.std_kind_id(env.krate, &p.id);
                let targs = generic_type_args(p);
                match sk {
                    Some(StdKind::String) => format!("lr::LStr::from({expr})"),
                    Some(StdKind::Cow | StdKind::Box | StdKind::Arc | StdKind::Rc) => match targs.first() {
                        Some(rd::Type::Primitive(s)) if s == "str" => format!("lr::LStr::from(&*{expr})"),
                        Some(rd::Type::Slice(b)) if matches!(&**b, rd::Type::Primitive(x) if x == "u8") => format!("lr::LStr::from_bytes(&*{expr})"),
                        Some(inner) => {
                            let inner = inner.clone();
                            if sk == Some(StdKind::Box) {
                                self.conv_out(&inner, env, &format!("(*{expr})"), dst, w)?
                            } else {
                                return Err(format!("{} results are unsupported", last_seg(&p.path)));
                            }
                        }
                        None => return Err("missing type argument".into()),
                    },
                    Some(StdKind::Vec) if matches!(targs.first(), Some(rd::Type::Primitive(b)) if b == "u8") => format!("lr::LStr::from_vec({expr})"),
                    Some(StdKind::Vec | StdKind::VecDeque | StdKind::HashSet | StdKind::BTreeSet) => {
                        self.arr_out(&targs[0], env, &format!("{expr}.into_iter()"), dst, w)?
                    }
                    Some(StdKind::Option) => {
                        let x = w.tmp("x");
                        let iv = self.ck.peel_option_ty(&targs[0], env);
                        if iv {
                            // Option<Option<T>> → Option<{value = T?}>
                            let TyNode::Table(tab) = self.node(dst) else { return Err("expected an option box".into()) };
                            let root = self.ck.st.tab_root(tab);
                            let name = self.record_name(root);
                            let vslot = self.ck.st.tab(root).fields["value"];
                            let inner = self.conv_out(&targs[0], env, &x, vslot.ty, w)?;
                            format!("match {expr} {{ Some({x}) => Some(lr::Rec::new(crate::records::{name} {{ value: {inner} }})), None => None }}")
                        } else {
                            let c = self.conv_out(&targs[0], env, &x, dst, w)?;
                            format!("match {expr} {{ Some({x}) => Some({c}), None => None }}")
                        }
                    }
                    Some(StdKind::HashMap | StdKind::BTreeMap) => {
                        let TyNode::Table(tab) = self.node(dst) else { return Err("expected a map".into()) };
                        let tn = self.ck.st.tab(tab).clone();
                        let (kt, vt) = (tn.key.map(|s| s.ty).unwrap_or(dst), tn.val.map(|s| s.ty).unwrap_or(dst));
                        let (k, v) = (w.tmp("k"), w.tmp("v"));
                        let kc = self.conv_out(&targs[0], env, &k, kt, w)?;
                        let kc = if matches!(self.node(kt), TyNode::Num) { format!("lr::NumKey::new({kc})?") } else { kc };
                        let vc = self.conv_out(&targs[1], env, &v, vt, w)?;
                        let m = w.tmp("m");
                        let mty = self.rust_ty(dst);
                        format!("{{ let {m} = <{mty}>::new(); for ({k}, {v}) in {expr} {{ {m}.set({kc}, {vc}); }} {m} }}")
                    }
                    Some(StdKind::Range | StdKind::RangeInclusive) => {
                        let TyNode::Table(tab) = self.node(dst) else { return Err("expected a range record".into()) };
                        let root = self.ck.st.tab_root(tab);
                        let name = self.record_name(root);
                        let st = self.ck.st.tab(root).fields["start"].ty;
                        let x = w.tmp("rg");
                        let (sx, ex) = if sk == Some(StdKind::Range) {
                            (format!("{x}.start.clone()"), format!("{x}.end.clone()"))
                        } else {
                            (format!("{x}.start().clone()"), format!("{x}.end().clone()"))
                        };
                        let s = self.conv_out(&targs[0], env, &sx, st, w)?;
                        let e = self.conv_out(&targs[0], env, &ex, st, w)?;
                        format!("{{ let {x} = {expr}; lr::Rec::new(crate::records::{name} {{ start: {s}, end: {e} }}) }}")
                    }
                    Some(StdKind::Result) => return Err("nested Result results are unsupported".into()),
                    None => match wd.resolve(env.krate, &p.id).and_then(|r| wd.item(r).map(|i| (r, &i.inner))) {
                        Some((r, rd::ItemEnum::TypeAlias(a))) => {
                            let a = a.clone();
                            let mut aenv = env.in_crate(r.krate);
                            let mut k = 0;
                            for gp in gparams(&a.generics) {
                                if gp.kind != GKind::Lifetime {
                                    if let Some(x) = targs.get(k) {
                                        let t = self.ck_arg(x, env)?;
                                        aenv.gens.insert(gp.name, t);
                                    }
                                    k += 1;
                                }
                            }
                            self.conv_out(&a.type_, &aenv, expr, dst, w)?
                        }
                        _ => self.src_out(expr, dst, dst, w)?,
                    },
                }
            }
            _ => return Err(format!("unsupported result type {}", self.rty(t, env, "'_").unwrap_or_default())),
        })
    }

    /// Type argument used while expanding an alias during codegen.
    fn ck_arg(&mut self, t: &rd::Type, env: &NEnv) -> Result<TyId, String> {
        match t {
            rd::Type::Generic(n) => env.gens.get(n).copied().ok_or_else(|| format!("unbound {n}")),
            _ => Err("alias argument too complex for codegen".into()),
        }
    }

    /// A native value whose source form is given by source type `ty`.
    fn src_out(&mut self, expr: &str, ty: TyId, dst: TyId, w: &mut WCtx) -> Result<String, String> {
        let _ = w;
        Ok(match self.node(ty) {
            TyNode::Num => expr.to_string(),
            TyNode::Int => expr.to_string(),
            TyNode::NPrim(p) if crate::check::is_int_prim(&p) => format!("lr::int::to_int({expr})?"),
            TyNode::NPrim(p) if p.as_ref() == "f64" => expr.to_string(),
            TyNode::NPrim(p) if p.as_ref() == "f32" => format!("({expr} as f64)"),
            TyNode::NPrim(p) if p.as_ref() == "bool" => expr.to_string(),
            TyNode::NPrim(p) if p.as_ref() == "char" => format!("lr::conv::from_char({expr})"),
            TyNode::NPrim(_) => format!("lr::conv::to_num({expr})?"),
            TyNode::Str => format!("lr::LStr::from({expr})"),
            TyNode::Bool => expr.to_string(),
            TyNode::Nil => "()".into(),
            TyNode::Native(nt) => self.mk_handle(nt.item, &nt.args, expr, None)?,
            TyNode::Table(tab) => {
                let tn = self.ck.st.tab(tab).clone();
                match (&tn.native, tn.kind) {
                    (Some(NativeRec::Struct(..)), _) => self.record_out(expr, dst, w, false)?,
                    (Some(NativeRec::Enum(..)), _) => self.enum_out(expr, dst, w)?,
                    (_, TKind::Array) => {
                        let el = tn.elem.map(|s| s.ty).unwrap_or(ty);
                        let e = w.tmp("e");
                        let c = self.src_out(&e, el, el, w)?;
                        format!("lr::Arr::from_vec({expr}.into_iter().map(|{e}| -> lr::LResult<_> {{ Ok({c}) }}).collect::<lr::LResult<Vec<_>>>()?)")
                    }
                    _ => return Err(format!("a native value cannot be returned as {}", self.ck.show(ty))),
                }
            }
            _ => return Err(format!("a native value cannot be returned as {}", self.ck.show(ty))),
        })
    }

    fn arr_out(&mut self, el: &rd::Type, env: &NEnv, iter: &str, dst: TyId, w: &mut WCtx) -> Result<String, String> {
        if let Some(inner_el) = self.option_inner(el, env) {
            let it = format!("{iter}.map(|x| lr::present(x, \"the native sequence contains None\")).collect::<lr::LResult<Vec<_>>>()?.into_iter()");
            return self.arr_out(&inner_el, env, &it, dst, w);
        }
        let elem_ty = match self.node(dst) {
            TyNode::Table(tab) => self.ck.st.tab(tab).elem.map(|s| s.ty).unwrap_or(dst),
            _ => dst,
        };
        let e = w.tmp("e");
        let c = self.conv_out(el, env, &e, elem_ty, w)?;
        Ok(format!("lr::Arr::from_vec({iter}.map(|{e}| -> lr::LResult<_> {{ Ok({c}) }}).collect::<lr::LResult<Vec<_>>>()?)"))
    }

    /// Borrowed results: copied when the value is a value type (strings,
    /// numbers, `Copy` objects, records); borrowed objects need a view or chain.
    fn ref_out(&mut self, t: &rd::Type, env: &NEnv, expr: &str, dst: TyId, w: &mut WCtx) -> Result<String, String> {
        let wd = self.w();
        match t {
            rd::Type::Primitive(p) if p == "str" => return Ok(format!("lr::LStr::from({expr})")),
            rd::Type::Primitive(_) => return self.conv_out(t, env, &format!("(*{expr})"), dst, w),
            rd::Type::ResolvedPath(p) if wd.std_kind_id(env.krate, &p.id).is_none() => {
                // `&Path` → an owned `PathBuf` copy (the source type is the owned form)
                if let Some(r) = wd.resolve(env.krate, &p.id) {
                    if crate::check_iter::owned_form_type(wd, r).is_some() {
                        return self.src_out(&format!("std::borrow::ToOwned::to_owned({expr})"), dst, dst, w);
                    }
                }
            }
            rd::Type::Slice(e) => {
                if matches!(&**e, rd::Type::Primitive(b) if b == "u8") {
                    return Ok(format!("lr::LStr::from_bytes({expr})"));
                }
                let ee = (**e).clone();
                return self.arr_out(&ee, env, &format!("{expr}.iter().cloned()"), dst, w);
            }
            _ => {}
        }
        match self.node(dst) {
            TyNode::Native(nt) if wd.trait_names(nt.item).contains("Copy") => self.conv_out(t, env, &format!("(*{expr})"), dst, w),
            TyNode::Native(_) => {
                // a borrowed object inside converted data (a descriptor read back from
                // native code): there is no owner to view, so a present value is a
                // language error (method results are views, see view_result_wrapper)
                let ty = self.rust_ty(dst);
                let _ = expr;
                Ok(format!("lr::conv::unrepresentable::<{ty}>(\"a borrowed native object inside native data cannot be read from source (no owner to borrow from)\")?"))
            }
            _ => {
                // value types: copy the borrowed value (String, Vec, records, ...)
                let c = self.conv_out(t, env, &format!("{expr}.clone()"), dst, w)?;
                Ok(c)
            }
        }
    }

    /// Native struct value → new source record.
    pub(crate) fn record_out(&mut self, expr: &str, dst: TyId, w: &mut WCtx, _write_back: bool) -> Result<String, String> {
        let TyNode::Table(tab) = self.node(dst) else { return Err("expected a record".into()) };
        let root = self.ck.st.tab_root(tab);
        let Some(NativeRec::Struct(r, args)) = self.ck.st.tab(root).native.clone() else { return Err("expected a native record".into()) };
        let wd = self.w();
        let name = self.record_name(root);
        let env = self.ck.type_env(r, &args, dst);
        let v = w.tmp("rv");
        let mut fields = Vec::new();
        let nfields = wd.public_fields(r).unwrap_or_default();
        for (fname, fty) in &nfields {
            let fslot = self.ck.st.tab(root).fields[fname];
            let store_opt = self.field_store_opt(root, fname);
            let (fty, fenv) = self.field_rd_type(root, fty, &env);
            let c = self.conv_out(&fty, &fenv, &format!("{v}.{}", native_ident(fname)), fslot.ty, w)?;
            let c = if store_opt && !self.ck.peel_option_ty(&fty, &fenv) { format!("Some({c})") } else { c };
            fields.push(format!("{}: {c}", rust_ident(fname)));
        }
        for fname in self.ck.st.tab(root).fields.keys() {
            if !nfields.iter().any(|f| &f.0 == fname) {
                fields.push(format!("{}: None", rust_ident(fname)));
            }
        }
        Ok(format!("{{ let {v} = {expr}; lr::Rec::new(crate::records::{name} {{ {} }}) }}", fields.join(", ")))
    }

    // Wrappers

    /// Generates (once) the wrapper for a native instance; returns its path.
    pub(crate) fn native_wrapper(&mut self, inst: usize) -> String {
        let ni = self.ck.info.natives[inst].clone();
        let name = format!("w{inst}_{}", ident_part(&ni.display).to_lowercase());
        if !self.natives_used.contains_key(&inst) {
            let code = match self.wrapper_code(inst, &ni, &name) {
                Ok(c) => c,
                Err(e) => {
                    // unrepresentable instantiation: a wrapper that fails to compile
                    // with the reason, mapped back to the call site
                    format!("pub fn {name}() {{\n    compile_error!({});\n}}\n", rust_str_lit(&format!("luarc: {}: {e}", ni.display)))
                }
            };
            self.natives_used.insert(inst, code);
        }
        format!("crate::natives::{name}")
    }

    /// Path of the trait providing a method, with the type arguments of the impl
    /// that provides it (`From<f64>`): a generic trait named without them does not
    /// compile, and with several impls it would be ambiguous.
    fn trait_path(&mut self, ni: &NativeInst, tr: ItemRef) -> Result<String, String> {
        let base = self.item_path(tr)?;
        let Some(imp) = ni.imp else { return Ok(base) };
        let args = match self.w().item(imp).map(|it| &it.inner) {
            Some(rd::ItemEnum::Impl(im)) => im.trait_.as_ref().map(generic_type_args).unwrap_or_default(),
            _ => Vec::new(),
        };
        if args.is_empty() {
            return Ok(base);
        }
        let env = NEnv { krate: imp.krate, ..ni.env.clone() };
        let a: Result<Vec<String>, String> = args.iter().map(|t| self.rty(t, &env, "'_")).collect();
        Ok(format!("{base}<{}>", a?.join(", ")))
    }

    fn owner_ty(&mut self, ni: &NativeInst) -> Result<String, String> {
        let (o, args) = ni.owner.clone().ok_or("no owner type")?;
        let rd = self.record_rd(ni.env.self_ty.or(ni.recv));
        self.adt_ty_rd(o, &args, "'_", rd.as_ref())
    }

    /// Concrete rustdoc arguments of a native record type.
    pub(crate) fn record_rd(&self, t: Option<TyId>) -> Option<HashMap<String, (usize, rd::Type)>> {
        match self.node(t?) {
            TyNode::Table(tab) => self.ck.info.record_rd_args.get(&self.ck.st.tab_root(tab)).cloned(),
            _ => None,
        }
    }

    fn wrapper_code(&mut self, inst: usize, ni: &NativeInst, name: &str) -> Result<String, String> {
        let wd = self.w();
        let mut w = WCtx { what: ni.display.clone(), ..Default::default() };
        let mut params: Vec<String> = Vec::new();
        let mut args: Vec<String> = Vec::new();
        let recv_ty = match ni.recv {
            Some(t) => Some(self.rust_ty(t)),
            None => None,
        };
        if let Some(rt) = &recv_ty {
            params.push(format!("recv: &{rt}"));
        }
        let doc = format!("/// `{}`", ni.display);
        let rets_ty = self.rets_ty(&ni.rets);
        // adapter close(): deterministic release
        if self.ck.info.closes.contains(&inst) {
            return Ok(format!("{doc} (adapter: deterministic release)\npub fn {name}({}) -> lr::LResult<()> {{\n    recv.close()\n}}\n", params.join(", ")));
        }
        match &ni.kind {
            NKind::Const | NKind::AssocConst => {
                let expr = match ni.kind {
                    NKind::Const => {
                        let p = self.item_path(ni.item)?;
                        if matches!(wd.item(ni.item).map(|i| &i.inner), Some(rd::ItemEnum::Static(_))) {
                            format!("&{p}")
                        } else {
                            p
                        }
                    }
                    _ => format!("<{}>::{}", self.owner_ty(ni)?, wd.name(ni.item)),
                };
                let ty = match &wd.item(ni.item).unwrap().inner {
                    rd::ItemEnum::Constant { type_, .. } => type_.clone(),
                    rd::ItemEnum::Static(s) => rd::Type::BorrowedRef { lifetime: None, is_mutable: false, type_: Box::new(s.type_.clone()) },
                    rd::ItemEnum::AssocConst { type_, .. } => type_.clone(),
                    _ => return Err("not a constant".into()),
                };
                let c = self.conv_out(&ty, &ni.env, "__r", ni.rets[0].ty, &mut w)?;
                let c = self.opt_wrap(c, ni.rets[0], &ty, &ni.env);
                return Ok(format!("{doc}\npub fn {name}() -> lr::LResult<{rets_ty}> {{\n    let __r = {expr};\n{}    Ok({c})\n}}\n", w.pre));
            }
            NKind::VariantConst | NKind::VariantCtor if self.is_enum_record(ni.rets[0].ty) => return self.enum_variant_wrapper(ni, name),
            NKind::VariantConst => {
                let expr = format!("<{}>::{}", self.adt_ty(ni.owner.as_ref().unwrap().0, &ni.owner.as_ref().unwrap().1, "'static")?, wd.name(ni.item));
                let c = self.src_out(&expr, ni.rets[0].ty, ni.rets[0].ty, &mut w)?;
                return Ok(format!("{doc}\npub fn {name}() -> lr::LResult<{rets_ty}> {{\n    Ok({c})\n}}\n"));
            }
            NKind::FieldGet(f) | NKind::FieldSet(f) => return self.field_wrapper(ni, f, name, matches!(ni.kind, NKind::FieldSet(_))),
            NKind::Payload(v) => return self.payload_wrapper(ni, v, name),
            NKind::IterNext => return self.iter_next_wrapper(ni, name),
            NKind::AwaitNative => {
                let rt = self.rust_ty(ni.recv.ok_or("await receiver")?);
                let (c, out) = (ni.env.krate, ni.env.assoc.get("Output").map(|x| x.1.clone()));
                let _ = c;
                let out = match out {
                    Some(o) => o,
                    None => {
                        let (oc, ot) = self.future_impl_output(ni).ok_or("the Future impl has no Output type")?;
                        let _ = oc;
                        ot
                    }
                };
                let body = format!("    lr::handle::check_consumable(&[(recv as &dyn lr::handle::Consumable, {})])?;
", rust_str_lit(&ni.display));
                let w = WCtx::default();
                return self.future_wrapper(ni, name, &format!("/// `{}`", ni.display), &[format!("recv: &{rt}")], body, "recv.take(\"await\")?", &w, out);
            }
            _ => {}
        }
        // functions, methods, constructors
        let (inputs, output, generics) = match &wd.item(ni.item).unwrap().inner {
            rd::ItemEnum::Function(f) => (f.sig.inputs.clone(), f.sig.output.clone(), Some(f.generics.clone())),
            rd::ItemEnum::Variant(_) => {
                let v = wd.variants(ni.owner.as_ref().unwrap().0).into_iter().find(|v| v.item == ni.item).ok_or("variant")?;
                let VariantShape::Tuple(ts) = v.shape else { return Err("not a tuple variant".into()) };
                (ts.into_iter().enumerate().map(|(i, t)| (format!("f{i}"), t)).collect(), Some(rd::Type::Generic("Self".into())), None)
            }
            _ => return Err("not callable".into()),
        };
        self.cur_bounds = HashMap::new();
        self.cur_into = HashMap::new();
        if let Some(g) = &generics {
            for gp in gparams(g) {
                if gp.kind == GKind::Type {
                    let b = param_bounds(g, &gp.name);
                    if let Some(t) = into_target(g, &gp.name, &b) {
                        self.cur_into.insert(gp.name.clone(), t);
                    }
                    self.cur_bounds.insert(gp.name.clone(), b);
                }
            }
        }
        if let Some(v) = self.view_result_wrapper(ni, name, &inputs, output.as_ref()) {
            return v;
        }
        // receiver
        let mut pi = 0;
        let mut recv_arg: Option<String> = None;
        if let NKind::Method(r) = &ni.kind {
            let recv_src = ni.recv.unwrap();
            let is_rec = matches!(self.node(recv_src), TyNode::Table(_));
            let owner_item = ni.owner.as_ref().unwrap().0;
            // the stored Rust type of the receiver handle (a Deref source when deref > 0)
            let recv_item = match self.node(recv_src) {
                TyNode::Native(nt) => nt.item,
                _ => owner_item,
            };
            let deref = if !is_rec && self.shared_repr(recv_item) { "**" } else { "*" };
            recv_arg = Some(match (r, is_rec) {
                (Recv::Ref, false) => {
                    let _ = writeln!(w.pre, "    let __recv = recv.get()?;");
                    format!("&{deref}__recv")
                }
                (Recv::Mut, false) => {
                    let _ = writeln!(w.pre, "    let mut __recv = recv.get_mut()?;");
                    format!("&mut {deref}__recv")
                }
                (Recv::Value, false) => {
                    let v = self.handle_by_value(owner_item, "recv", &mut w, false);
                    v
                }
                (Recv::Ref, true) => {
                    let c = self.record_in("recv", recv_src, &mut w)?;
                    let _ = writeln!(w.pre, "    let __recv = {c};");
                    "&__recv".into()
                }
                (Recv::Mut, true) => {
                    let c = self.record_in("recv", recv_src, &mut w)?;
                    let _ = writeln!(w.pre, "    let mut __recv = {c};");
                    let back = self.record_out_assign("__recv", "recv", recv_src)?;
                    let _ = writeln!(w.post, "    {back}");
                    "&mut __recv".into()
                }
                (Recv::Value, true) => self.record_in("recv", recv_src, &mut w)?,
            });
            pi = 1;
        }
        let rd_params: Vec<(String, rd::Type)> = inputs[pi..].to_vec();
        for (i, (_pn, pt)) in rd_params.iter().enumerate() {
            let slot = ni.params[i];
            let sty = self.slot_ty(slot);
            params.push(format!("a{i}: {sty}"));
            let c = if let Some(impls) = self.ck.info.trait_impls.get(&(inst, i)).cloned().filter(|v| !v.is_empty()) {
                self.trait_impl_arg(&impls, pt, &format!("a{i}"), slot.ty, &mut w)?
            } else if self.is_null(slot.null) && !self.ck.peel_option_ty(pt, &ni.env) {
                return Err("an optional argument flows into a non-optional native parameter".into());
            } else {
                self.conv_in(pt, &ni.env, &format!("a{i}"), slot.ty, &mut w)?
            };
            args.push(c);
        }
        if let Some(r) = recv_arg {
            args.insert(0, r);
        }
        // arguments with `?` are evaluated before the guarded call; consumption last
        let mut staged = Vec::new();
        for (i, a) in args.iter_mut().enumerate() {
            if a.contains('?') || w.callbacks {
                let t = format!("__arg{i}");
                staged.push(format!("    let {t} = {a};"));
                *a = t;
            }
        }
        // Staging statements that use a consumed value run after the consumption.
        // Names are matched as whole identifiers (`__own1` must not match `__own10`);
        // an array of consumed handles is "used" where its snapshot is iterated.
        let consumed = |l: &str| {
            w.takes.iter().any(|(_, t)| mentions(l, t)) || w.take_arrays.iter().any(|(hs, _)| l.contains(&format!("{hs}.iter()")))
        };
        let (pre_early, pre_late): (Vec<&str>, Vec<&str>) = w.pre.lines().partition(|l| !consumed(l));
        let mut body = pre_early.iter().map(|l| format!("{l}\n")).collect::<String>();
        if !w.takes.is_empty() || !w.take_arrays.is_empty() {
            // every consumed handle (single arguments and array elements) is checked
            // together, so a failing call consumes none of them
            let list: Vec<String> = w.takes.iter().map(|(p, _)| format!("(&{p} as &dyn lr::handle::Consumable, {})", rust_str_lit(&ni.display))).collect();
            if w.take_arrays.is_empty() {
                let _ = writeln!(body, "    lr::handle::check_consumable(&[{}])?;", list.join(", "));
            } else {
                let _ = writeln!(body, "    {{\n        let mut __cl: Vec<(&dyn lr::handle::Consumable, &'static str)> = vec![{}];", list.join(", "));
                for (hs, what) in &w.take_arrays {
                    let _ = writeln!(body, "        __cl.extend({hs}.iter().map(|__h| (__h as &dyn lr::handle::Consumable, {what})));");
                }
                let _ = writeln!(body, "        lr::handle::check_consumable(&__cl)?;\n    }}");
            }
        }
        // takes happen after every other conversion succeeded; staged args that use
        // a taken value are emitted after the takes
        let late_names: Vec<String> = pre_late
            .iter()
            .filter_map(|l| l.trim().strip_prefix("let ").map(|r| r.trim_start_matches("mut ").split([' ', ':']).next().unwrap_or("").to_string()))
            .collect();
        let (early, late): (Vec<String>, Vec<String>) =
            staged.into_iter().partition(|s| !consumed(s) && !late_names.iter().any(|n| !n.is_empty() && mentions(s, n)));
        for s in &early {
            let _ = writeln!(body, "{s}");
        }
        for (p, t) in &w.takes {
            let _ = writeln!(body, "    let {t} = {p}.take({})?;", rust_str_lit(&wd.name(ni.item)));
        }
        for l in &pre_late {
            let _ = writeln!(body, "{l}");
        }
        for s in &late {
            let _ = writeln!(body, "{s}");
        }
        // the call
        let has_synth = generics.as_ref().map(|g| g.params.iter().any(|p| matches!(p.kind, rd::GenericParamDefKind::Type { is_synthetic: true, .. }))).unwrap_or(false);
        let own_gens: Vec<String> = generics
            .as_ref()
            .map(|g| g.params.iter().filter(|p| matches!(p.kind, rd::GenericParamDefKind::Type { is_synthetic: false, .. })).map(|p| p.name.clone()).collect())
            .unwrap_or_default();
        let turbofish = if own_gens.is_empty() || has_synth {
            String::new()
        } else {
            // a parameter that appears in an argument type is inferred by rustc from
            // the converted argument (whose native form the conversion chose);
            // only result-only parameters are named explicitly
            let mut gs = Vec::new();
            for g in &own_gens {
                let in_args = rd_params.iter().any(|(_, t)| mentions_generic(t, g));
                gs.push(match ni.env.gens.get(g) {
                    Some(t) if !in_args => self.src_rust(*t)?,
                    _ => "_".into(),
                });
            }
            format!("::<{}>", gs.join(", "))
        };
        let fname = wd.name(ni.item);
        let call = match &ni.kind {
            NKind::Function => format!("{}{turbofish}({})", self.item_path(ni.item)?, args.join(", ")),
            NKind::VariantCtor => format!("<{}>::{fname}({})", self.adt_ty(ni.owner.as_ref().unwrap().0, &ni.owner.as_ref().unwrap().1, "'_")?, args.join(", ")),
            _ => match ni.trait_ {
                // fully qualified, so a Deref'd receiver selects the target's impl
                Some(tr) => format!("<{} as {}>::{fname}({})", self.owner_ty(ni)?, self.trait_path(ni, tr)?, args.join(", ")),
                None => format!("<{}>::{fname}{turbofish}({})", self.owner_ty(ni)?, args.join(", ")),
            },
        };
        // Guard every native call because it may invoke a callback retained by an
        // earlier call. Callback errors must propagate through `pcall`.
        let call = format!("lr::callback::guard(|| {call})?");
        // identity shortcut (verified adapter metadata)
        if let (Some((o, _)), NKind::Method(Recv::Ref | Recv::Mut)) = (&ni.owner, &ni.kind) {
            if self.ck.adapters.returns_receiver(*o, &fname).is_some() {
                let _ = writeln!(body, "    let _ = {call};");
                let _ = writeln!(body, "    drop(__recv);");
                let _ = writeln!(body, "    Ok(recv.clone())");
                return Ok(format!("{doc} (returns its receiver: adapter metadata)\npub fn {name}({}) -> lr::LResult<{rets_ty}> {{\n{body}}}\n", params.join(", ")));
            }
        }
        if let Some(out_t) = self.future_output(ni, output.as_ref()) {
            return self.future_wrapper(ni, name, &doc, &params, body, &call, &w, out_t);
        }
        let _ = writeln!(body, "    let __r = {call};");
        body.push_str(&w.post);
        let out_t = match &output {
            None => rd::Type::Tuple(vec![]),
            Some(t) => t.clone(),
        };
        let (inner_t, fallible) = self.ck.peel_result(&out_t, &ni.env);
        if fallible {
            let _ = writeln!(
                body,
                "    let __r = match __r {{\n        Ok(v) => v,\n        Err(e) => return Err(lr::LuaError::native({}, lr::native_error_message!(e))),\n    }};",
                rust_str_lit(&ni.display)
            );
        }
        let retain = match (&ni.owner, &ni.kind) {
            (Some((o, _)), NKind::Method(_)) => self.ck.adapters.retains_owner(*o, &fname).is_some(),
            _ => false,
        };
        // scoped borrow (adapter): `forget` makes the result 'static and the receiver
        // stays locked until the result is released
        let scoped = match (&ni.owner, &ni.kind) {
            (Some((o, _)), NKind::Method(Recv::Mut)) => self.ck.adapters.scoped_borrow(*o, &fname).map(|(f, _)| f.to_string()),
            _ => None,
        };
        if let Some(f) = &scoped {
            if fallible {
                return Err("scoped_borrow of a fallible method is unsupported".into());
            }
            body = body.replace("    let __r = ", "    let __r0 = ");
            let _ = writeln!(body, "    let __r = __r0.{f}();");
        }
        let mut rw = WCtx { n: w.n + 5000, ..Default::default() };
        let result = match &inner_t {
            rd::Type::Tuple(ts) if ts.is_empty() => "()".to_string(),
            rd::Type::Tuple(ts) => {
                let names: Vec<String> = (0..ts.len()).map(|i| format!("__t{i}")).collect();
                let _ = writeln!(body, "    let {} = __r;", tuple_ty(&names));
                let mut cs = Vec::new();
                for (i, t) in ts.iter().enumerate() {
                    let c = self.conv_out(t, &ni.env, &names[i], ni.rets[i].ty, &mut rw)?;
                    cs.push(self.opt_wrap(c, ni.rets[i], t, &ni.env));
                }
                if cs.len() == 1 {
                    cs.remove(0)
                } else {
                    format!("({})", cs.join(", "))
                }
            }
            t => {
                let c = if scoped.is_some() {
                    match self.node(ni.rets[0].ty) {
                        TyNode::Native(nt) => {
                            let inner = self.handle_inner_ty(nt.item, &nt.args)?;
                            let short = self.w().name(nt.item);
                            let (_, meta) = self.handle_support(&inner, &short);
                            format!("lr::Handle::new_locking(__r, &{meta}, recv, {})?", rust_str_lit(&short))
                        }
                        _ => return Err("scoped_borrow applies only to methods returning native objects".into()),
                    }
                } else if retain {
                    match self.node(ni.rets[0].ty) {
                        TyNode::Native(nt) => self.mk_handle(nt.item, &nt.args, "__r", Some("recv"))?,
                        _ => return Err("retain_owner applies only to methods returning native objects".into()),
                    }
                } else {
                    self.conv_out(t, &ni.env, "__r", ni.rets[0].ty, &mut rw)?
                };
                self.opt_wrap(c, ni.rets[0], t, &ni.env)
            }
        };
        body.push_str(&rw.pre);
        let _ = writeln!(body, "    Ok({})", crate::codegen::strip(result));
        let mut d = format!("{doc} — `{}`", crate::native::world::fn_signature(wd, ni.item));
        if !ni.env.gens.is_empty() {
            let mut inst: Vec<String> = Vec::new();
            let mut keys: Vec<&String> = ni.env.gens.keys().collect();
            keys.sort();
            for k in keys {
                let t = ni.env.gens[k];
                inst.push(format!("{k}={}", self.src_rust(t).unwrap_or_else(|_| "_".into())));
            }
            let _ = write!(d, " [{}]", inst.join(", "));
        }
        Ok(format!("{d}\npub fn {name}({}) -> lr::LResult<{rets_ty}> {{\n{body}}}\n", params.join(", ")))
    }

    /// Wraps a converted value in `Some` when the source slot is optional but the
    /// native type is not an `Option`.
    pub(crate) fn opt_wrap(&self, c: String, slot: crate::types::Slot, t: &rd::Type, env: &NEnv) -> String {
        if self.is_null(slot.null) && !self.ck.peel_option_ty(t, env) {
            format!("Some({c})")
        } else {
            c
        }
    }

    /// The `Output` of a native future result (`async fn` or `impl Future`).
    fn future_output(&self, ni: &NativeInst, output: Option<&rd::Type>) -> Option<rd::Type> {
        let wd = self.w();
        if let Some(rd::Item { inner: rd::ItemEnum::Function(f), .. }) = wd.item(ni.item) {
            if f.header.is_async {
                return Some(output.cloned().unwrap_or(rd::Type::Tuple(vec![])));
            }
        }
        if let Some(rd::Type::ImplTrait(bounds)) = output {
            for p in trait_bounds(bounds) {
                if last_seg(&p.path) == "Future" {
                    return Some(assoc_constraints(p).into_iter().find(|(n, _)| n == "Output").map(|(_, t)| t).unwrap_or(rd::Type::Tuple(vec![])));
                }
            }
        }
        None
    }

    /// A call returning a native future: the future is created by the call (its
    /// arguments are converted and borrowed only for the call itself, so the
    /// future must not borrow them — rustc checks it) and wrapped in an
    /// `lr::task::Fut` whose output conversion runs when it completes.
    #[allow(clippy::too_many_arguments)]
    fn future_wrapper(&mut self, ni: &NativeInst, name: &str, doc: &str, params: &[String], mut body: String, call: &str, w: &WCtx, out_t: rd::Type) -> Result<String, String> {
        let TyNode::Future(frets) = self.node(ni.rets[0].ty) else { return Err("expected a future result".into()) };
        let _ = writeln!(body, "    let __f = {call};");
        body.push_str(&w.post);
        let (inner_t, fallible) = self.ck.peel_result(&out_t, &ni.env);
        let mut rw = WCtx { n: w.n + 7000, ..Default::default() };
        let mut inner = String::new();
        if fallible {
            let _ = writeln!(
                inner,
                "        let __r = match __r {{\n            Ok(v) => v,\n            Err(e) => return Err(lr::LuaError::native({}, lr::native_error_message!(e))),\n        }};",
                rust_str_lit(&ni.display)
            );
        }
        let result = match &inner_t {
            rd::Type::Tuple(ts) if ts.is_empty() => "()".to_string(),
            rd::Type::Tuple(ts) => {
                let names: Vec<String> = (0..ts.len()).map(|i| format!("__t{i}")).collect();
                let _ = writeln!(inner, "        let {} = __r;", tuple_ty(&names));
                let mut cs = Vec::new();
                for (i, t) in ts.iter().enumerate() {
                    let c = self.conv_out(t, &ni.env, &names[i], frets[i].ty, &mut rw)?;
                    cs.push(self.opt_wrap(c, frets[i], t, &ni.env));
                }
                if cs.len() == 1 {
                    cs.remove(0)
                } else {
                    format!("({})", cs.join(", "))
                }
            }
            t => {
                let c = self.conv_out(t, &ni.env, "__r", frets[0].ty, &mut rw)?;
                self.opt_wrap(c, frets[0], t, &ni.env)
            }
        };
        let fr = self.rets_ty(&frets);
        // The native future may borrow its receiver and arguments, so the task
        // owns them: shared parameters are cloned (a handle clone shares its
        // object) and the conversions and the call run inside the future, which
        // keeps them alive until it completes.
        let mut owned = String::new();
        let mut rebind = String::new();
        let mut movable = true;
        for p in params {
            let Some((n, t)) = p.split_once(':') else { continue };
            let (n, t) = (n.trim(), t.trim());
            if t.starts_with("&mut") {
                movable = false;
            } else if t.starts_with('&') {
                if t.contains("lr::Handle<") {
                    let _ = writeln!(owned, "    {n}.check_not_lent({})?;", rust_str_lit(&ni.display));
                }
                let _ = writeln!(owned, "    let {n} = {n}.to_owned();");
                let _ = writeln!(rebind, "        let {n} = &{n};");
            }
        }
        let (outer, body) = if movable {
            (owned, format!("{rebind}{}", body.lines().map(|l| format!("    {l}\n")).collect::<String>()))
        } else {
            (body, String::new())
        };
        Ok(format!(
            "{doc} — a native future\npub fn {name}({}) -> lr::LResult<lr::task::Fut<{fr}>> {{\n{outer}    Ok(lr::task::Fut::new(async move {{\n{body}        let __r = __f.await;\n{inner}{}        let __out: lr::LResult<{fr}> = Ok({});\n        __out\n    }}))\n}}\n",
            params.join(", "),
            rw.pre,
            crate::codegen::strip(result)
        ))
    }

    /// `&T` / `&mut T` / `Option<&T>` results of methods on handles where `T` is a
    /// native object: an owner-retaining **view**. The view re-applies the accessor
    /// (with its arguments, converted once to owned values) on every use, so it
    /// always reaches the object the native API lends — a different same-typed
    /// child stays a different object, never the receiver. Any exclusive access,
    /// consumption or close of the owner invalidates it. `None` when the result
    /// is not such a borrow.
    fn view_result_wrapper(&mut self, ni: &NativeInst, name: &str, inputs: &[(String, rd::Type)], output: Option<&rd::Type>) -> Option<Result<String, String>> {
        let wd = self.w();
        let NKind::Method(recv_kind @ (Recv::Ref | Recv::Mut)) = ni.kind.clone() else { return None };
        let out = output?;
        // `&T` or `Option<&T>`
        let (opt, inner) = match out {
            rd::Type::ResolvedPath(p) if wd.std_kind_id(ni.env.krate, &p.id) == Some(StdKind::Option) => (true, generic_type_args(p).into_iter().next()?),
            t => (false, t.clone()),
        };
        let rd::Type::BorrowedRef { is_mutable, type_, .. } = &inner else { return None };
        let dst = ni.rets.first()?.ty;
        let TyNode::Native(dnt) = self.node(dst) else { return None };
        if wd.trait_names(dnt.item).contains("Copy") {
            return None;
        }
        let recv_src = ni.recv?;
        let TyNode::Native(rnt) = self.node(recv_src) else { return None };
        let (owner_item, _) = ni.owner.clone()?;
        if self.ck.adapters.returns_receiver(owner_item, &wd.name(ni.item)).is_some() {
            return None;
        }
        if let rd::Type::ResolvedPath(p) = &**type_ {
            if let Some(r) = wd.resolve(ni.env.krate, &p.id) {
                if crate::check_iter::owned_form_type(wd, r).is_some() {
                    return None; // `&Path`: an owned copy (value semantics)
                }
            }
        }
        Some(self.view_result_code(ni, name, inputs, opt, *is_mutable, recv_kind, &rnt, &dnt))
    }

    #[allow(clippy::too_many_arguments)]
    fn view_result_code(
        &mut self,
        ni: &NativeInst,
        name: &str,
        inputs: &[(String, rd::Type)],
        opt: bool,
        result_mut: bool,
        recv_kind: Recv,
        rnt: &crate::types::NativeTy,
        dnt: &crate::types::NativeTy,
    ) -> Result<String, String> {
        let wd = self.w();
        if self.shared_repr(dnt.item) {
            return Err("borrowed results of shared (Arc) objects are unsupported".into());
        }
        if result_mut && recv_kind == Recv::Ref {
            return Err("a `&mut` result from a `&self` method (interior mutability) is unsupported".into());
        }
        let stored = self.handle_inner_ty(rnt.item, &rnt.args)?;
        let target = self.handle_inner_ty(dnt.item, &dnt.args)?;
        let (_, meta) = self.handle_support(&target, &wd.name(dnt.item));
        let mut params = vec![format!("recv: &lr::Handle<{stored}>")];
        let mut pre = String::new();
        let mut call_args = Vec::new();
        for (i, (_pn, pt)) in inputs.iter().skip(1).enumerate() {
            let slot = ni.params[i];
            let sty = self.slot_ty(slot);
            params.push(format!("a{i}: {sty}"));
            let v = format!("__va{i}");
            match pt {
                rd::Type::BorrowedRef { type_, is_mutable: false, .. } if matches!(&**type_, rd::Type::Primitive(s) if s == "str") => {
                    let _ = writeln!(pre, "    let {v} = a{i}.to_utf8_string()?;");
                    call_args.push(format!("{v}.as_str()"));
                }
                rd::Type::BorrowedRef { type_, is_mutable: false, .. }
                    if matches!(&**type_, rd::Type::Slice(e) if matches!(&**e, rd::Type::Primitive(b) if b == "u8")) =>
                {
                    let _ = writeln!(pre, "    let {v} = a{i}.as_bytes().to_vec();");
                    call_args.push(format!("&{v}[..]"));
                }
                rd::Type::BorrowedRef { .. } => {
                    return Err("a borrowed result of a call with borrowed object arguments is unsupported (the view could not re-apply the call)".into())
                }
                _ => {
                    let mut w = WCtx { what: ni.display.clone(), ..Default::default() };
                    let c = self.conv_in(pt, &ni.env, &format!("a{i}"), slot.ty, &mut w)?;
                    if !w.pre.is_empty() || !w.takes.is_empty() || w.callbacks {
                        return Err("a borrowed result of a call with staged, consumed or callback arguments is unsupported".into());
                    }
                    let _ = writeln!(pre, "    let {v} = {c};");
                    call_args.push(format!("{v}.clone()"));
                }
            }
        }
        let fname = wd.name(ni.item);
        let callee = match ni.trait_ {
            Some(tr) => format!("<{} as {}>::{fname}", self.owner_ty(ni)?, self.trait_path(ni, tr)?),
            None => format!("<{}>::{fname}", self.owner_ty(ni)?),
        };
        let rarg = if recv_kind == Recv::Mut { "&mut *o" } else { "&*o" };
        let mut all = vec![rarg.to_string()];
        all.extend(call_args);
        let call = format!("{callee}({})", all.join(", "));
        let proj_body = if opt { call } else { format!("Some({call})") };
        let disp = rust_str_lit(&ni.display);
        let body = if recv_kind == Recv::Mut || result_mut {
            format!(
                "    let __pm = lr::handle::proj_mut::<{stored}, {target}>(move |o| {proj_body});\n    let __present = {{\n        let mut __g = recv.get_mut()?;\n        __pm(&mut *__g).is_some()\n    }};\n    let __v = lr::Handle::view_with(recv, {disp}, None, Some(__pm), None, &{meta});\n"
            )
        } else {
            format!(
                "    let __pr = lr::handle::proj_ref::<{stored}, {target}>(move |o| {proj_body});\n    let __present = {{\n        let __g = recv.get()?;\n        __pr(&*__g).is_some()\n    }};\n    let __v = lr::Handle::view_with(recv, {disp}, Some(__pr), None, None, &{meta});\n"
            )
        };
        let rets_ty = self.rets_ty(&ni.rets);
        let ret = if opt { "Ok(if __present { Some(__v) } else { None })" } else { "let _ = __present;\n    Ok(__v)" };
        Ok(format!(
            "/// `{}` — a borrowed result: a view of the receiver (re-applies the accessor; invalidated when the owner changes).\npub fn {name}({}) -> lr::LResult<{rets_ty}> {{\n{pre}{body}    {ret}\n}}\n",
            ni.display,
            params.join(", ")
        ))
    }

    /// One step of a native iterator driving a source `for` loop: `None` ends the
    /// loop; an `Err` item becomes a language error.
    fn iter_next_wrapper(&mut self, ni: &NativeInst, name: &str) -> Result<String, String> {
        let recv_t = self.rust_ty(ni.recv.ok_or("iterator receiver")?);
        let (o, _) = ni.owner.clone().ok_or("iterator type")?;
        let deref = if self.shared_repr(o) { "**" } else { "*" };
        let owner_ty = self.owner_ty(ni)?;
        let tr = self.item_path(ni.trait_.ok_or("Iterator trait")?)?;
        let (c, item_t) = ni.env.assoc.get("Item").cloned().ok_or("the Iterator impl has no Item type")?;
        let ienv = ni.env.in_crate(c);
        let (inner, fallible) = self.ck.peel_result(&item_t, &ienv);
        let mut w = WCtx::default();
        let mut body = format!("    let __n = <{owner_ty} as {tr}>::next(&mut {deref}recv.get_mut()?);\n    let Some(__r) = __n else {{\n        return Ok(None);\n    }};\n");
        if fallible {
            let _ = writeln!(
                body,
                "    let __r = match __r {{\n        Ok(v) => v,\n        Err(e) => return Err(lr::LuaError::native({}, lr::native_error_message!(e))),\n    }};",
                rust_str_lit(&ni.display)
            );
        }
        let result = match &inner {
            rd::Type::Tuple(ts) if ni.rets.len() > 1 => {
                let names: Vec<String> = (0..ts.len()).map(|i| format!("__t{i}")).collect();
                let _ = writeln!(body, "    let {} = __r;", tuple_ty(&names));
                let mut cs = Vec::new();
                for (i, t) in ts.iter().enumerate() {
                    let c = self.conv_out(t, &ienv, &names[i], ni.rets[i].ty, &mut w)?;
                    cs.push(self.opt_wrap(c, ni.rets[i], t, &ienv));
                }
                format!("({})", cs.join(", "))
            }
            t => {
                let c = self.conv_out(t, &ienv, "__r", ni.rets[0].ty, &mut w)?;
                self.opt_wrap(c, ni.rets[0], t, &ienv)
            }
        };
        body.push_str(&w.pre);
        let rets_ty = self.rets_ty(&ni.rets);
        Ok(format!(
            "/// `{}`: one step of a native iterator.\npub fn {name}(recv: &{recv_t}) -> lr::LResult<Option<{rets_ty}>> {{\n{body}    Ok(Some({}))\n}}\n",
            ni.display,
            crate::codegen::strip(result)
        ))
    }

    fn field_wrapper(&mut self, ni: &NativeInst, f: &str, name: &str, setter: bool) -> Result<String, String> {
        let wd = self.w();
        let (o, args) = ni.owner.clone().unwrap();
        let fty = wd.readable_fields(o).into_iter().find(|x| x.0 == f).map(|x| x.1).ok_or("field")?;
        let inner = self.handle_inner_ty(o, &args)?;
        let deref = if self.shared_repr(o) { "**" } else { "*" };
        let slot = ni.rets[0];
        let sty = self.slot_ty(slot);
        let mut w = WCtx::default();
        let fid = native_ident(f);
        if setter {
            let c = self.conv_in(&fty, &ni.env, "v", slot.ty, &mut w)?;
            return Ok(format!(
                "/// Sets public field `{f}` of `{}`.\npub fn {name}(h: &lr::Handle<{inner}>, v: {sty}) -> lr::LResult<()> {{\n{}    let __v = {c};\n    let __old = std::mem::replace(&mut ({deref}h.get_mut()?).{fid}, __v);\n    lr::value::release(__old);\n    Ok(())\n}}\n",
                ni.display, w.pre
            ));
        }
        // value types are copied; borrowed objects become views of the owner
        if let TyNode::Native(fnt) = self.node(slot.ty) {
            if !wd.trait_names(fnt.item).contains("Copy") {
                // Borrowed views of shared owners must produce a source diagnostic.
                if self.shared_repr(fnt.item) {
                    return Err(format!(
                        "field '{f}' holds a {} by value, which luarc represents as a shared (Arc) object; a borrowed view of it is unsupported",
                        wd.name(fnt.item)
                    ));
                }
                let finner = self.handle_inner_ty(fnt.item, &fnt.args)?;
                let (_, meta) = self.handle_support(&finner, &wd.name(fnt.item));
                let drops = wd.trait_names(o).contains("Drop");
                let take = if drops || self.shared_repr(o) { "None".to_string() } else { format!("Some(|o: {inner}| Some(o.{fid}))") };
                // a shared (Arc) owner is never mutated through a view
                let get_mut = if self.shared_repr(o) { "None".to_string() } else { format!("Some(|o: &mut {inner}| Some(&mut o.{fid}))") };
                return Ok(format!(
                    "/// View of public field `{f}` of `{}` (valid while the owner is unchanged).\npub fn {name}(h: &lr::Handle<{inner}>) -> lr::LResult<{sty}> {{\n    Ok(lr::Handle::view(h, {}, |o: &{inner}| Some(&o.{fid}), {get_mut}, {take}, &{meta}))\n}}\n",
                    ni.display,
                    rust_str_lit(&ni.display)
                ));
            }
        }
        let c = self.conv_out(&fty, &ni.env, &format!("({deref}__g).{fid}.clone()"), slot.ty, &mut w)?;
        let c = self.opt_wrap(c, slot, &fty, &ni.env);
        Ok(format!(
            "/// Reads public field `{f}` of `{}` (a copy of its value).\npub fn {name}(h: &lr::Handle<{inner}>) -> lr::LResult<{sty}> {{\n    let __g = h.get()?;\n{}    Ok({c})\n}}\n",
            ni.display, w.pre
        ))
    }

    fn payload_wrapper(&mut self, ni: &NativeInst, variant: &str, name: &str) -> Result<String, String> {
        let wd = self.w();
        let (o, args) = ni.owner.clone().unwrap();
        let inner = self.handle_inner_ty(o, &args)?;
        // patterns name the enum without arguments (inferred)
        let path = self.item_path(o)?;
        let v = wd.variants(o).into_iter().find(|x| x.name == variant).ok_or("variant")?;
        let slot = ni.rets[0];
        let sty = self.slot_ty(slot);
        let mut w = WCtx::default();
        let body = match &v.shape {
            VariantShape::Unit => format!("    Ok(matches!(&*h.get()?, {path}::{variant}))\n"),
            VariantShape::Tuple(ts) if ts.len() == 1 => {
                let t = &ts[0];
                match self.node(slot.ty) {
                    TyNode::Native(fnt) if !wd.trait_names(fnt.item).contains("Copy") => {
                        let finner = self.handle_inner_ty(fnt.item, &fnt.args)?;
                        let (_, meta) = self.handle_support(&finner, &wd.name(fnt.item));
                        let take = if wd.trait_names(o).contains("Drop") {
                            "None".to_string()
                        } else {
                            format!("Some(|o: {inner}| match o {{ {path}::{variant}(x) => Some(x), _ => None }})")
                        };
                        format!(
                            "    if !matches!(&*h.get()?, {path}::{variant}(..)) {{\n        return Ok(None);\n    }}\n    Ok(Some(lr::Handle::view(h, {}, |o: &{inner}| match o {{ {path}::{variant}(x) => Some(x), _ => None }}, Some(|o: &mut {inner}| match o {{ {path}::{variant}(x) => Some(x), _ => None }}), {take}, &{meta})))\n",
                            rust_str_lit(&ni.display)
                        )
                    }
                    _ => {
                        let c = self.conv_out(t, &ni.env, "x.clone()", slot.ty, &mut w)?;
                        format!("    let __g = h.get()?;\n    Ok(match &*__g {{\n        {path}::{variant}(x) => {{ {} Some({c}) }}\n        _ => None,\n    }})\n", w.pre)
                    }
                }
            }
            VariantShape::Tuple(_) | VariantShape::Struct(_) => {
                let fields: Vec<(String, String, rd::Type)> = match &v.shape {
                    VariantShape::Tuple(ts) => ts.iter().enumerate().map(|(i, t)| (format!("_{}", i + 1), format!("f{i}"), t.clone())).collect(),
                    VariantShape::Struct(fs) => fs.iter().map(|(n, t)| (n.clone(), rust_ident(n), t.clone())).collect(),
                    _ => unreachable!(),
                };
                let TyNode::Table(tab) = self.node(slot.ty) else { return Err("payload record".into()) };
                let root = self.ck.st.tab_root(tab);
                let rname = self.record_name(root);
                let mut parts = Vec::new();
                // fields read through views are not bound by the copying pattern
                let mut viewed: HashSet<String> = HashSet::new();
                for (sname, bind, t) in &fields {
                    let fslot = self.ck.st.tab(root).fields[sname];
                    let c = match self.node(fslot.ty) {
                        TyNode::Native(fnt) if !wd.trait_names(fnt.item).contains("Copy") => {
                            let finner = self.handle_inner_ty(fnt.item, &fnt.args)?;
                            let (_, meta) = self.handle_support(&finner, &wd.name(fnt.item));
                            viewed.insert(bind.clone());
                            let fpat = match &v.shape {
                                VariantShape::Tuple(_) => format!(
                                    "{path}::{variant}({})",
                                    fields.iter().map(|f| if f.1 == *bind { "x".to_string() } else { "_".to_string() }).collect::<Vec<_>>().join(", ")
                                ),
                                _ => format!("{path}::{variant} {{ {}: x, .. }}", native_ident(sname)),
                            };
                            format!(
                                "lr::Handle::view(h, {}, |o: &{inner}| match o {{ {fpat} => Some(x), _ => None }}, Some(|o: &mut {inner}| match o {{ {fpat} => Some(x), _ => None }}), None, &{meta})",
                                rust_str_lit(&format!("{}.{sname}", ni.display))
                            )
                        }
                        _ => {
                            let c = self.conv_out(t, &ni.env, &format!("{bind}.clone()"), fslot.ty, &mut w)?;
                            if self.field_store_opt(root, sname) && !self.ck.st.is_null(fslot.null) {
                                format!("Some({c})")
                            } else {
                                c
                            }
                        }
                    };
                    parts.push(format!("{}: {c}", rust_ident(sname)));
                }
                let bound = |f: &(String, String, rd::Type)| if viewed.contains(&f.1) { "_".to_string() } else { f.1.clone() };
                let pat = match &v.shape {
                    VariantShape::Tuple(_) => format!("{path}::{variant}({})", fields.iter().map(bound).collect::<Vec<_>>().join(", ")),
                    _ => format!("{path}::{variant} {{ {} }}", fields.iter().map(|f| match bound(f) { b if b == native_ident(&f.0) => b, b => format!("{}: {b}", native_ident(&f.0)) }).collect::<Vec<_>>().join(", ")),
                };
                format!(
                    "    let __g = h.get()?;\n    Ok(match &*__g {{\n        {pat} => {{ {} Some(lr::Rec::new(crate::records::{rname} {{ {} }})) }}\n        _ => None,\n    }})\n",
                    w.pre,
                    parts.join(", ")
                )
            }
            VariantShape::Opaque => return Err("the variant has private fields".into()),
        };
        Ok(format!("/// Payload of `{}` (nil for other variants).\npub fn {name}(h: &lr::Handle<{inner}>) -> lr::LResult<{sty}> {{\n{body}}}\n", ni.display))
    }

    /// Assembles `src/natives.rs`; returns the file and wrapper line ranges.
    pub(crate) fn natives_file(&mut self) -> (String, Vec<(usize, usize, crate::diag::Span, String)>) {
        let mut out = String::from(
            "//! Wrappers for the imported Rust items used by this program. Generated by luarc.\n\n// staged array elements are cloned without knowing whether they are references\n#![allow(noop_method_call)]\n\n#[allow(unused_imports)]\nuse crate::lr;\n#[allow(unused_imports)]\nuse crate::records::*;\n\n",
        );
        let mut lines = Vec::new();
        let insts: Vec<(usize, String)> = self.natives_used.iter().map(|(k, v)| (*k, v.clone())).collect();
        for (inst, code) in insts {
            let start = out.lines().count() + 1;
            out.push_str(&crate::project::rustfmt(&code));
            out.push('\n');
            let end = out.lines().count();
            let ni = &self.ck.info.natives[inst];
            lines.push((start, end, ni.span, ni.display.clone()));
        }
        for code in self.handle_makers.values() {
            out.push_str(&crate::project::rustfmt(code));
            out.push('\n');
        }
        (out, lines)
    }
}

fn fx(s: &str) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Whether rustdoc type `t` mentions generic parameter `g`.
pub(crate) fn mentions_generic(t: &rd::Type, g: &str) -> bool {
    match t {
        rd::Type::Generic(n) => n == g,
        rd::Type::BorrowedRef { type_, .. } | rd::Type::Slice(type_) | rd::Type::RawPointer { type_, .. } => mentions_generic(type_, g),
        rd::Type::Array { type_, .. } => mentions_generic(type_, g),
        rd::Type::Tuple(ts) => ts.iter().any(|t| mentions_generic(t, g)),
        rd::Type::ResolvedPath(p) => generic_type_args(p).iter().any(|t| mentions_generic(t, g)),
        _ => false,
    }
}

/// Replaces whole-identifier occurrences of `name` in `code`.
/// `name` occurs in `code` as a whole identifier.
fn mentions(code: &str, name: &str) -> bool {
    replace_ident(code, name, "") != code
}

fn replace_ident(code: &str, name: &str, with: &str) -> String {
    let mut out: Vec<u8> = Vec::new();
    let b = code.as_bytes();
    let n = name.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i..].starts_with(n) {
            let before = i == 0 || !(b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_');
            let after = i + n.len() >= b.len() || !(b[i + n.len()].is_ascii_alphanumeric() || b[i + n.len()] == b'_');
            if before && after {
                out.extend_from_slice(with.as_bytes());
                i += n.len();
                continue;
            }
        }
        // bytes, not `as char`: non-ASCII text (string previews) must stay UTF-8
        out.push(b[i]);
        i += 1;
    }
    String::from_utf8(out).expect("identifier replacement keeps UTF-8")
}

impl<'a> Gen<'a> {
    /// `type Output = ...` of the `Future` impl an await instance refers to.
    fn future_impl_output(&self, ni: &NativeInst) -> Option<(usize, rd::Type)> {
        let w = self.w();
        let imp = ni.imp?;
        for it in w.impl_items(imp) {
            if let Some(rd::Item { name: Some(n), inner: rd::ItemEnum::AssocType { type_: Some(t), .. }, .. }) = w.item(it) {
                if n == "Output" {
                    return Some((imp.krate, t.clone()));
                }
            }
        }
        None
    }
}

impl<'a> Gen<'a> {
    /// A generic `IntoIterator`/`Vec` argument from an array whose elements borrow
    /// (records with `&T` fields, such as glyphon `TextArea`s): each element's
    /// staged parts are hoisted into vectors that outlive the call.
    fn staged_generic_vec(&mut self, place: &str, elem_ty: TyId, w: &mut WCtx) -> Result<String, String> {
        let src = w.tmp("src");
        let _ = writeln!(w.pre, "    let {src} = {place}.snapshot();");
        let i = w.tmp("i");
        let mut inner = WCtx { n: w.n + 1000, what: w.what.clone(), ..Default::default() };
        let ev = format!("{src}[{i}].clone()");
        let c = self.generic_arg(&[], &ev, elem_ty, &mut inner)?;
        w.n = inner.n;
        if !inner.takes.is_empty() || inner.callbacks {
            return Err("arrays of elements consumed by the call are unsupported here".into());
        }
        emit_staged(&inner.pre, &c, &ev, &src, &i, w)
    }
}

/// The borrowed type a generic parameter `name` is converted into: from a bound
/// `G: Into<T>` or a where-clause `T: From<G>`, when `T` is `&X` or
/// `Option<&X>` (wgpu's `set_bind_group<BG>` where `Option<&BindGroup>:
/// From<BG>`). Passing a reference then satisfies the bound without consuming
/// the source object.
fn into_target(g: &rd::Generics, name: &str, bounds: &[rd::GenericBound]) -> Option<rd::Type> {
    let is_ref = |t: &rd::Type| match t {
        rd::Type::BorrowedRef { .. } => true,
        rd::Type::ResolvedPath(p) if last_seg(&p.path) == "Option" => matches!(generic_type_args(p).first(), Some(rd::Type::BorrowedRef { .. })),
        _ => false,
    };
    let into = trait_bounds(bounds).into_iter().filter(|p| last_seg(&p.path) == "Into").filter_map(|p| generic_type_args(p).into_iter().next());
    let from = g.where_predicates.iter().filter_map(|w| match w {
        rd::WherePredicate::BoundPredicate { type_, bounds, .. } => trait_bounds(bounds)
            .into_iter()
            .any(|p| last_seg(&p.path) == "From" && matches!(generic_type_args(p).first(), Some(rd::Type::Generic(x)) if x == name))
            .then(|| type_.clone()),
        _ => None,
    });
    into.chain(from).find(is_ref)
}

/// Hoists the per-element staging statements `let NAME = EXPR;` of an array
/// conversion into vectors (one entry per source element `src[i]`) written to
/// `w.pre`, and returns the expression building the native vector from `c`.
///
/// Each use of a staged name becomes `NAME[i]` when it borrows or projects
/// (`&NAME`, `NAME.field`, `NAME.method()`, `NAME[j]` of a nested level). A use
/// that moves the value (an owned `String`, a nested struct) cannot move out of
/// an index, so it becomes `NAME[i].clone()`; for `Copy` values
/// this copies the value without changing its semantics.
fn emit_staged(pre: &str, c: &str, ev: &str, src: &str, i: &str, w: &mut WCtx) -> Result<String, String> {
    // a method call on the element (`.get()?` for a guard, `.borrow()` for a
    // record) reaches it in place: on the `.clone()` copy, a guard would borrow
    // a temporary
    let in_place = |s: &str| s.replace(&format!("{ev}."), &format!("{src}[{i}]."));
    let (pre_s, c_s) = (in_place(pre), in_place(c));
    let (pre, c) = (pre_s.as_str(), c_s.as_str());
    let mut lines: Vec<(String, String, String)> = Vec::new();
    for line in pre.lines() {
        let l = line.trim();
        let Some(rest) = l.strip_prefix("let ") else { return Err("unsupported staging".into()) };
        let (lhs, rhs) = rest.split_once(" = ").ok_or("unsupported staging")?;
        let name = lhs.trim_start_matches("mut ").split(':').next().unwrap_or("").trim().to_string();
        // a nested staged vector keeps its declared type, which rustc needs
        // before it can index the elements
        let ann = lhs.split_once(':').map(|(_, t)| t.trim().to_string()).unwrap_or_else(|| "_".into());
        lines.push((name, ann, rhs.trim_end_matches(';').to_string()));
    }
    // earlier staged names in `code` become vector accesses
    let rewrite = |code: &str, upto: usize| -> String {
        let mut out = code.to_string();
        for (n, _, _) in lines.iter().take(upto) {
            out = rewrite_uses(&out, n, |borrowed| if borrowed { format!("{n}[{i}]") } else { format!("{n}[{i}].clone()") });
        }
        out
    };
    for k in 0..lines.len() {
        let r2 = rewrite(&lines[k].2, k);
        let (name, ann, _) = &lines[k];
        let _ = writeln!(w.pre, "    let {name}: Vec<_> = (0..{src}.len()).map(|{i}| -> lr::LResult<{ann}> {{ Ok({r2}) }}).collect::<lr::LResult<_>>()?;");
    }
    let c2 = rewrite(c, lines.len());
    Ok(format!("(0..{src}.len()).map(|{i}| -> lr::LResult<_> {{ Ok({c2}) }}).collect::<lr::LResult<Vec<_>>>()?"))
}

/// A use of an identifier in generated code.
struct IdentUse {
    start: usize,
    end: usize,
    /// `&name`, `*name`, `name.field`, `name.method()` or `name[j]`: the value itself is
    /// not moved.
    borrowed: bool,
}

fn ident_uses(code: &str, name: &str) -> Vec<IdentUse> {
    let b = code.as_bytes();
    let n = name.as_bytes();
    let is_id = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let mut out = Vec::new();
    let mut i = 0;
    while i + n.len() <= b.len() {
        if b[i..].starts_with(n) && (i == 0 || !is_id(b[i - 1])) && (i + n.len() == b.len() || !is_id(b[i + n.len()])) {
            let e = i + n.len();
            let borrowed = (i > 0 && matches!(b[i - 1], b'&' | b'*')) || matches!(b.get(e), Some(b'.' | b'['));
            out.push(IdentUse { start: i, end: e, borrowed });
            i = e;
        } else {
            i += 1;
        }
    }
    out
}

/// Replaces each use of `name` with `with(borrowed)`.
fn rewrite_uses(code: &str, name: &str, with: impl Fn(bool) -> String) -> String {
    let mut out = String::new();
    let mut last = 0;
    for u in ident_uses(code, name) {
        out.push_str(&code[last..u.start]);
        out.push_str(&with(u.borrowed));
        last = u.end;
    }
    out.push_str(&code[last..]);
    out
}

/// Whether a rustdoc type mentions any generic parameter.
pub(crate) fn contains_generic(t: &rd::Type) -> bool {
    match t {
        rd::Type::Generic(_) | rd::Type::QualifiedPath { .. } | rd::Type::ImplTrait(_) | rd::Type::Infer => true,
        rd::Type::BorrowedRef { type_, .. } | rd::Type::Slice(type_) | rd::Type::RawPointer { type_, .. } => contains_generic(type_),
        rd::Type::Array { type_, .. } => contains_generic(type_),
        rd::Type::Tuple(ts) => ts.iter().any(contains_generic),
        rd::Type::ResolvedPath(p) => generic_type_args(p).iter().any(contains_generic),
        _ => false,
    }
}

impl<'a> Gen<'a> {
    /// A record field's type, with a generic parameter replaced by the concrete
    /// rustdoc argument of this instantiation (and the environment it lives in).
    pub(crate) fn field_rd_type(&self, root: crate::types::TabId, fty: &rd::Type, env: &NEnv) -> (rd::Type, NEnv) {
        if std::env::var_os("LUARC_DEBUG_RD").is_some() {
            eprintln!("field_rd_type root {root} {:?} has={} keys={:?}", fty, self.ck.info.record_rd_args.contains_key(&root), self.ck.info.record_rd_args.keys().collect::<Vec<_>>());
        }
        if let rd::Type::Generic(g) = fty {
            if let Some((c, t)) = self.ck.info.record_rd_args.get(&root).and_then(|m| m.get(g)).cloned() {
                return (t, NEnv { krate: c, ..Default::default() });
            }
        }
        (fty.clone(), env.clone())
    }
}

/// Moves the `check_unshared` lines of an array element's conversion out of its
/// staging (they run once per element in a loop over the array snapshot, before
/// any shared object is taken).
fn take_unshared_checks(inner: &mut WCtx) -> String {
    let (checks, rest): (Vec<&str>, Vec<&str>) = inner.pre.lines().partition(|l| l.contains(".check_unshared("));
    let checks = checks.iter().map(|l| l.trim()).collect::<Vec<_>>().join(" ");
    inner.pre = rest.iter().map(|l| format!("{l}\n")).collect();
    checks
}
