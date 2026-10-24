//! Classification of native Rust types into source representations.
//!
//! * Standard containers and scalars convert by value (`String`, `Vec<T>`,
//!   `Option<T>`, `HashMap`, ...).
//! * A struct whose fields are all public and value-convertible (and which is not
//!   `#[non_exhaustive]`) is a **record**: a source table converted per call.
//!   Records may have lifetime parameters and borrowed fields (descriptors such
//!   as `RenderPassDescriptor<'a>`): the borrowed parts are staged for exactly the
//!   duration of the call that receives the descriptor.
//! * Everything else (opaque structs, enums, unions) is a **handle**.

use std::cell::RefCell;
use std::collections::HashMap;

use rustdoc_types as rd;

use super::world::{is_non_exhaustive, ItemRef, World};

/// Standard-library types with built-in conversions, recognised by definition
/// path in a toolchain crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StdKind {
    String,
    Vec,
    VecDeque,
    Option,
    Result,
    Box,
    Cow,
    Arc,
    Rc,
    HashMap,
    BTreeMap,
    HashSet,
    BTreeSet,
    /// `core::ops::Range` family (`a..b`): converted from `{start, end}` records.
    Range,
    RangeInclusive,
}

pub fn std_kind_of_path(p: &str) -> Option<StdKind> {
    Some(match p {
        "alloc::string::String" | "std::string::String" => StdKind::String,
        "alloc::vec::Vec" | "std::vec::Vec" => StdKind::Vec,
        "alloc::collections::vec_deque::VecDeque" | "std::collections::vec_deque::VecDeque" => StdKind::VecDeque,
        "core::option::Option" | "std::option::Option" => StdKind::Option,
        "core::result::Result" | "std::result::Result" => StdKind::Result,
        "alloc::boxed::Box" | "std::boxed::Box" => StdKind::Box,
        "alloc::borrow::Cow" | "std::borrow::Cow" => StdKind::Cow,
        "alloc::sync::Arc" | "std::sync::Arc" => StdKind::Arc,
        "alloc::rc::Rc" | "std::rc::Rc" => StdKind::Rc,
        "std::collections::hash::map::HashMap" | "std::collections::HashMap" => StdKind::HashMap,
        "alloc::collections::btree::map::BTreeMap" | "std::collections::BTreeMap" => StdKind::BTreeMap,
        "std::collections::hash::set::HashSet" | "std::collections::HashSet" => StdKind::HashSet,
        "alloc::collections::btree::set::BTreeSet" | "std::collections::BTreeSet" => StdKind::BTreeSet,
        "core::ops::range::Range" | "std::ops::Range" => StdKind::Range,
        "core::ops::range::RangeInclusive" | "std::ops::RangeInclusive" => StdKind::RangeInclusive,
        _ => return None,
    })
}

/// Paths used by `Result`/`io::Result` style aliases are expanded by rustdoc's
/// own alias items; `std::io::Result<T>` is `Result<T, io::Error>`.
pub fn is_std_io_result(p: &str) -> bool {
    matches!(p, "std::io::error::Result" | "std::io::Result")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GKind {
    Lifetime,
    Type,
    Const,
}

#[derive(Clone, Debug)]
pub struct GParam {
    pub name: String,
    pub kind: GKind,
    pub default: Option<rd::Type>,
}

pub fn gparams(g: &rd::Generics) -> Vec<GParam> {
    g.params
        .iter()
        .map(|p| match &p.kind {
            rd::GenericParamDefKind::Lifetime { .. } => GParam { name: p.name.clone(), kind: GKind::Lifetime, default: None },
            rd::GenericParamDefKind::Type { default, .. } => GParam { name: p.name.clone(), kind: GKind::Type, default: default.clone() },
            rd::GenericParamDefKind::Const { .. } => GParam { name: p.name.clone(), kind: GKind::Const, default: None },
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Repr {
    Record,
    Handle,
}

#[derive(Clone, Debug)]
pub enum VariantShape {
    Unit,
    Tuple(Vec<rd::Type>),
    Struct(Vec<(String, rd::Type)>),
    /// Has private fields: cannot be constructed or destructured from source.
    Opaque,
}

#[derive(Clone, Debug)]
pub struct VariantInfo {
    pub name: String,
    pub item: ItemRef,
    pub shape: VariantShape,
}

/// Lazily computed facts about native types.
#[derive(Default)]
pub struct TypeFacts {
    repr: RefCell<HashMap<ItemRef, Repr>>,
}

impl World {
    pub fn generics_of(&self, r: ItemRef) -> Vec<GParam> {
        match self.item(r).map(|i| &i.inner) {
            Some(rd::ItemEnum::Struct(s)) => gparams(&s.generics),
            Some(rd::ItemEnum::Enum(e)) => gparams(&e.generics),
            Some(rd::ItemEnum::Union(u)) => gparams(&u.generics),
            Some(rd::ItemEnum::TypeAlias(a)) => gparams(&a.generics),
            Some(rd::ItemEnum::Trait(t)) => gparams(&t.generics),
            Some(rd::ItemEnum::Function(f)) => gparams(&f.generics),
            Some(rd::ItemEnum::Impl(i)) => gparams(&i.generics),
            _ => Vec::new(),
        }
    }

    pub fn std_kind(&self, r: ItemRef) -> Option<StdKind> {
        self.std_path(r).and_then(|p| std_kind_of_path(&p))
    }

    pub fn is_enum(&self, r: ItemRef) -> bool {
        matches!(self.item(r).map(|i| &i.inner), Some(rd::ItemEnum::Enum(_)))
    }

    /// Public named fields of a plain struct; `None` if the struct has private
    /// fields or is not a plain struct.
    pub fn public_fields(&self, r: ItemRef) -> Option<Vec<(String, rd::Type)>> {
        let Some(rd::Item { inner: rd::ItemEnum::Struct(s), .. }) = self.item(r) else { return None };
        let rd::StructKind::Plain { fields, has_stripped_fields } = &s.kind else { return None };
        if *has_stripped_fields {
            return None;
        }
        let mut out = Vec::new();
        for f in fields {
            let fi = self.crates[r.krate].doc.index.get(f)?;
            if !matches!(fi.visibility, rd::Visibility::Public) {
                return None;
            }
            let rd::ItemEnum::StructField(t) = &fi.inner else { return None };
            out.push((fi.name.clone().unwrap_or_default(), t.clone()));
        }
        Some(out)
    }

    /// Public fields readable on a handle (struct with some private fields).
    pub fn readable_fields(&self, r: ItemRef) -> Vec<(String, rd::Type)> {
        let Some(rd::Item { inner: rd::ItemEnum::Struct(s), .. }) = self.item(r) else { return Vec::new() };
        let rd::StructKind::Plain { fields, .. } = &s.kind else { return Vec::new() };
        fields
            .iter()
            .filter_map(|f| self.crates[r.krate].doc.index.get(f))
            .filter(|fi| matches!(fi.visibility, rd::Visibility::Public))
            .filter_map(|fi| match &fi.inner {
                rd::ItemEnum::StructField(t) => Some((fi.name.clone().unwrap_or_default(), t.clone())),
                _ => None,
            })
            .collect()
    }

    pub fn variants(&self, r: ItemRef) -> Vec<VariantInfo> {
        let Some(rd::Item { inner: rd::ItemEnum::Enum(e), .. }) = self.item(r) else { return Vec::new() };
        let doc = &self.crates[r.krate].doc;
        let mut out = Vec::new();
        for vid in &e.variants {
            let Some(v) = doc.index.get(vid) else { continue };
            let rd::ItemEnum::Variant(var) = &v.inner else { continue };
            let field_ty = |id: &rd::Id| -> Option<(String, rd::Type)> {
                let fi = doc.index.get(id)?;
                match &fi.inner {
                    rd::ItemEnum::StructField(t) => Some((fi.name.clone().unwrap_or_default(), t.clone())),
                    _ => None,
                }
            };
            let shape = match &var.kind {
                rd::VariantKind::Plain => VariantShape::Unit,
                rd::VariantKind::Tuple(fs) => {
                    if fs.iter().any(|f| f.is_none()) {
                        VariantShape::Opaque
                    } else {
                        match fs.iter().map(|f| field_ty(f.as_ref().unwrap()).map(|x| x.1)).collect::<Option<Vec<_>>>() {
                            Some(ts) => VariantShape::Tuple(ts),
                            None => VariantShape::Opaque,
                        }
                    }
                }
                rd::VariantKind::Struct { fields, has_stripped_fields } => {
                    if *has_stripped_fields {
                        VariantShape::Opaque
                    } else {
                        match fields.iter().map(field_ty).collect::<Option<Vec<_>>>() {
                            Some(fs) => VariantShape::Struct(fs),
                            None => VariantShape::Opaque,
                        }
                    }
                }
            };
            out.push(VariantInfo { name: v.name.clone().unwrap_or_default(), item: ItemRef { krate: r.krate, id: vid.0 }, shape });
        }
        out
    }

    pub fn non_exhaustive(&self, r: ItemRef) -> bool {
        self.item(r).map(is_non_exhaustive).unwrap_or(false)
    }

    /// Record or handle (see the module documentation).
    pub fn repr(&self, facts: &TypeFacts, r: ItemRef) -> Repr {
        if let Some(x) = facts.repr.borrow().get(&r) {
            return *x;
        }
        // provisional answer breaks recursion through self-referential types
        facts.repr.borrow_mut().insert(r, Repr::Handle);
        // An enum whose variants borrow native objects (`BindingResource<'a>`
        // holds `&Buffer`, `&Sampler`, `BufferBinding { buffer: &Buffer }`): a
        // handle would have to own the borrow, so it is a record of its
        // variants, converted inside the call that uses it.
        // Enums that borrow only plain data (glyphon `Family<'a>`:
        // `Name(&str)`) stay handles: calls such as `Attrs::family` keep them in
        // their result, which a value built inside the call cannot outlive.
        if let Some(rd::Item { inner: rd::ItemEnum::Enum(e), .. }) = self.item(r) {
            let borrows = gparams(&e.generics).iter().any(|g| g.kind == GKind::Lifetime);
            let ok = |v: &VariantInfo| match &v.shape {
                VariantShape::Unit => true,
                VariantShape::Tuple(ts) => ts.iter().all(|t| self.record_field_ok(facts, r.krate, t)),
                _ => false,
            };
            let objects = |v: &VariantInfo| matches!(&v.shape, VariantShape::Tuple(ts) if ts.iter().any(|t| self.borrows_object(facts, r.krate, t, 3)));
            let vs = self.variants(r);
            let v = if borrows && !self.has_self_methods(r) && vs.iter().any(|v| ok(v) && objects(v)) {
                Repr::Record
            } else {
                Repr::Handle
            };
            facts.repr.borrow_mut().insert(r, v);
            return v;
        }
        // Plain data only: a type with `&mut self` methods or `Display` is an object
        // (identity, formatting and equality come from Rust) even when its fields
        // are public; such handles still expose their fields.
        let traits = self.trait_names(r);
        let rec = !self.non_exhaustive(r)
            && !self.has_self_methods(r)
            && !traits.contains("Display")
            && match self.public_fields(r) {
                Some(fs) => !fs.is_empty() && fs.iter().all(|(_, t)| self.record_field_ok(facts, r.krate, t)),
                None => false,
            };
        let v = if rec { Repr::Record } else { Repr::Handle };
        facts.repr.borrow_mut().insert(r, v);
        v
    }

    /// Whether `t` holds a reference to a native object (a handle-represented
    /// type), directly or through slices, options and record structs, looking
    /// `depth` structs deep.
    fn borrows_object(&self, facts: &TypeFacts, c: usize, t: &rd::Type, depth: u32) -> bool {
        match t {
            rd::Type::BorrowedRef { type_, .. } => match &**type_ {
                rd::Type::ResolvedPath(p) => match self.resolve(c, &p.id) {
                    Some(r) if self.std_kind_id(c, &p.id).is_none() => {
                        matches!(self.item(r).map(|i| &i.inner), Some(rd::ItemEnum::Struct(_) | rd::ItemEnum::Enum(_))) && self.repr(facts, r) == Repr::Handle
                            || self.borrows_object(facts, c, type_, depth)
                    }
                    _ => false,
                },
                other => self.borrows_object(facts, c, other, depth),
            },
            rd::Type::Slice(e) | rd::Type::Array { type_: e, .. } => self.borrows_object(facts, c, e, depth),
            rd::Type::Tuple(ts) => ts.iter().any(|x| self.borrows_object(facts, c, x, depth)),
            rd::Type::ResolvedPath(p) => match self.std_kind_id(c, &p.id) {
                Some(_) => generic_type_args(p).iter().any(|a| self.borrows_object(facts, c, a, depth)),
                None if depth > 0 => match self.resolve(c, &p.id) {
                    Some(r) if self.repr(facts, r) == Repr::Record => {
                        self.public_fields(r).unwrap_or_default().iter().any(|(_, ft)| self.borrows_object(facts, r.krate, ft, depth - 1))
                    }
                    _ => false,
                },
                None => false,
            },
            _ => false,
        }
    }

    /// A field type that a record can hold: scalars, strings, containers of such,
    /// options, other records, handles (by value or borrowed), slices.
    fn record_field_ok(&self, facts: &TypeFacts, c: usize, t: &rd::Type) -> bool {
        match t {
            rd::Type::Primitive(p) => p != "never",
            rd::Type::Tuple(ts) => ts.iter().all(|x| self.record_field_ok(facts, c, x)),
            rd::Type::Array { type_, .. } | rd::Type::Slice(type_) => self.record_field_ok(facts, c, type_),
            // a borrowed object is staged from its handle without moving it
            // (descriptor records: `TextArea { buffer: &Buffer }`)
            rd::Type::BorrowedRef { type_, .. } => match &**type_ {
                rd::Type::ResolvedPath(p) if self.resolve(c, &p.id).and_then(|r| self.item(r)).map(|i| matches!(i.inner, rd::ItemEnum::Struct(_))).unwrap_or(false) => true,
                _ => self.record_field_ok(facts, c, type_),
            },
            rd::Type::Generic(_) => true,
            rd::Type::ResolvedPath(p) => {
                match self.std_kind_id(c, &p.id) {
                    Some(StdKind::Arc | StdKind::Rc) => return false,
                    Some(_) => return generic_type_args(p).iter().all(|a| self.record_field_ok(facts, c, a)),
                    None => {}
                }
                let Some(r) = self.resolve(c, &p.id) else { return false };
                match self.std_kind(r) {
                    Some(StdKind::Arc | StdKind::Rc) => false,
                    Some(_) => generic_type_args(p).iter().all(|a| self.record_field_ok(facts, c, a)),
                    None => match self.item(r).map(|i| &i.inner) {
                        // A field holding a native *object* by value: converting the
                        // record back to the native struct (a `&self` method, a `&T`
                        // argument) would move that object out of its handle, so
                        // the struct stays a handle. Copy types and
                        // nested records are values.
                        Some(rd::ItemEnum::Struct(_)) => self.trait_names(r).contains("Copy") || self.repr(facts, r) == Repr::Record,
                        Some(rd::ItemEnum::Enum(_)) => true,
                        Some(rd::ItemEnum::TypeAlias(_)) => true,
                        _ => false,
                    },
                }
            }
            _ => false,
        }
    }
}

/// Type arguments of a path (lifetimes and consts skipped).
pub fn generic_type_args(p: &rd::Path) -> Vec<rd::Type> {
    match p.args.as_deref() {
        Some(rd::GenericArgs::AngleBracketed { args, .. }) => {
            args.iter().filter_map(|a| if let rd::GenericArg::Type(t) = a { Some(t.clone()) } else { None }).collect()
        }
        _ => Vec::new(),
    }
}

/// All generic arguments of a path, positionally.
pub fn generic_args(p: &rd::Path) -> Vec<rd::GenericArg> {
    match p.args.as_deref() {
        Some(rd::GenericArgs::AngleBracketed { args, .. }) => args.clone(),
        _ => Vec::new(),
    }
}

/// Associated-type constraints of a path (`Iterator<Item = T>`).
pub fn assoc_constraints(p: &rd::Path) -> Vec<(String, rd::Type)> {
    match p.args.as_deref() {
        Some(rd::GenericArgs::AngleBracketed { constraints, .. }) => constraints
            .iter()
            .filter_map(|c| match &c.binding {
                rd::AssocItemConstraintKind::Equality(rd::Term::Type(t)) => Some((c.name.clone(), t.clone())),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

pub fn last_seg(p: &str) -> &str {
    p.rsplit("::").next().unwrap_or(p)
}

/// The trait bounds of an `impl Trait` or generic parameter, as (path, bound).
pub fn trait_bounds(bounds: &[rd::GenericBound]) -> Vec<&rd::Path> {
    bounds.iter().filter_map(|b| if let rd::GenericBound::TraitBound { trait_, .. } = b { Some(trait_) } else { None }).collect()
}

/// Bounds of a generic parameter, including where-clause predicates.
pub fn param_bounds(g: &rd::Generics, name: &str) -> Vec<rd::GenericBound> {
    let mut out = Vec::new();
    for p in &g.params {
        if p.name == name {
            if let rd::GenericParamDefKind::Type { bounds, .. } = &p.kind {
                out.extend(bounds.iter().cloned());
            }
        }
    }
    for w in &g.where_predicates {
        if let rd::WherePredicate::BoundPredicate { type_: rd::Type::Generic(n), bounds, .. } = w {
            if n == name {
                out.extend(bounds.iter().cloned());
            }
        }
    }
    out
}

pub fn has_static_or_send(bounds: &[rd::GenericBound]) -> bool {
    bounds.iter().any(|b| match b {
        rd::GenericBound::Outlives(l) => l == "'static",
        rd::GenericBound::TraitBound { trait_, .. } => matches!(last_seg(&trait_.path), "Send" | "Sync"),
        _ => false,
    })
}

/// A `Fn`/`FnMut`/`FnOnce` bound: (trait name, inputs, output).
pub fn fn_bound(bounds: &[rd::GenericBound]) -> Option<(String, Vec<rd::Type>, Option<rd::Type>)> {
    for b in bounds {
        if let rd::GenericBound::TraitBound { trait_, .. } = b {
            let n = last_seg(&trait_.path);
            if matches!(n, "Fn" | "FnMut" | "FnOnce") {
                if let Some(rd::GenericArgs::Parenthesized { inputs, output }) = trait_.args.as_deref() {
                    return Some((n.to_string(), inputs.clone(), output.clone()));
                }
            }
        }
    }
    None
}

impl World {
    /// Whether the type has public inherent methods taking `self` in any form.
    pub fn has_self_methods(&self, r: ItemRef) -> bool {
        for imp in self.impls_of(r) {
            let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = self.item(imp) else { continue };
            if i.trait_.is_some() {
                continue;
            }
            for it in self.impl_items(imp) {
                if let Some(rd::Item { inner: rd::ItemEnum::Function(f), visibility: rd::Visibility::Public, .. }) = self.item(it) {
                    // only mutating methods make a plain-data type an object: `&self`
                    // accessors and by-value builders (`fn with_x(self) -> Self`) work on
                    // value copies (descriptors such as wgpu `*Descriptor<L>` have
                    // `map_label(&self)`)
                    if matches!(f.sig.inputs.first(), Some((n, rd::Type::BorrowedRef { is_mutable: true, .. })) if n == "self") {
                        return true;
                    }
                }
            }
        }
        false
    }
}

/// A `Send`/`Sync` bound: the value may be used from another thread.
pub fn has_send(bounds: &[rd::GenericBound]) -> bool {
    bounds.iter().any(|b| matches!(b, rd::GenericBound::TraitBound { trait_, .. } if matches!(last_seg(&trait_.path), "Send" | "Sync")))
}

impl StdKind {
    /// Canonical public path (usable without loading the defining crate's model).
    pub fn std_path(self) -> &'static str {
        match self {
            StdKind::String => "std::string::String",
            StdKind::Vec => "std::vec::Vec",
            StdKind::VecDeque => "std::collections::VecDeque",
            StdKind::Option => "std::option::Option",
            StdKind::Result => "std::result::Result",
            StdKind::Box => "std::boxed::Box",
            StdKind::Cow => "std::borrow::Cow",
            StdKind::Arc => "std::sync::Arc",
            StdKind::Rc => "std::rc::Rc",
            StdKind::HashMap => "std::collections::HashMap",
            StdKind::BTreeMap => "std::collections::BTreeMap",
            StdKind::HashSet => "std::collections::HashSet",
            StdKind::BTreeSet => "std::collections::BTreeSet",
            StdKind::Range => "std::ops::Range",
            StdKind::RangeInclusive => "std::ops::RangeInclusive",
        }
    }
}

/// `IntoIterator<Item = T>` / `Iterator<Item = T>` bound: `T`.
pub fn into_iter_item(bounds: &[rd::GenericBound]) -> Option<rd::Type> {
    for p in trait_bounds(bounds) {
        if matches!(last_seg(&p.path), "IntoIterator" | "Iterator") {
            if let Some((_, t)) = assoc_constraints(p).into_iter().find(|(n, _)| n == "Item") {
                return Some(t);
            }
        }
    }
    None
}
