//! The native API universe of one compilation: every Rust crate whose public API
//! the program touches, as typed rustdoc JSON (`rustdoc-types`, format pinned by
//! [`FORMAT_VERSION`]).
//!
//! Crates are identified by package identity (`name@version`), never by printed
//! names, so two versions of one crate (or two crates defining `Error`) stay
//! distinct. References between crates (re-exports, types from dependency crates)
//! are resolved through each crate's `paths` table and the dependency edges Cargo
//! resolved. A reference to a crate that is not loaded yet is recorded in
//! [`World::missing`]; the frontend extracts it and re-checks (the set only grows,
//! so this terminates).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use rustdoc_types as rd;
use serde::{Deserialize, Serialize};

pub use rustdoc_types::FORMAT_VERSION;

/// Version of the pruned model written to the cache (part of cache keys).
pub const MODEL_VERSION: &str = "model-2";

pub type CrateIx = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemRef {
    pub krate: CrateIx,
    pub id: u32,
}

/// Identity of a loaded crate.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CrateInfo {
    /// Cargo package name (`wgpu-types`), or `std`/`core`/`alloc`.
    pub package: String,
    pub version: String,
    /// Rust crate name (`wgpu_types`).
    pub lib: String,
    /// `package@version` (toolchain crates: `std@<rustc version>`).
    pub key: String,
    /// A direct dependency of the project (nameable from generated code).
    pub direct: bool,
    /// Toolchain crate (`std`, `core`, `alloc`).
    pub toolchain: bool,
    /// Rust crate name of each dependency → its package key (renames resolved).
    pub deps: BTreeMap<String, String>,
    pub features: Vec<String>,
}

pub struct LoadedCrate {
    pub info: CrateInfo,
    pub doc: rd::Crate,
    /// Local item (path, kind) (as in `paths`) → id. The kind is part of the key:
    /// a trait and its derive macro share a path (`core::clone::Clone`).
    local_paths: HashMap<(Vec<String>, rd::ItemKind), u32>,
}

impl LoadedCrate {
    pub fn new(info: CrateInfo, doc: rd::Crate) -> LoadedCrate {
        let mut local_paths = HashMap::new();
        for (id, s) in &doc.paths {
            if s.crate_id == 0 {
                local_paths.insert((s.path.clone(), s.kind), id.0);
            }
        }
        LoadedCrate { info, doc, local_paths }
    }
}

/// Removes what luarc never reads (documentation, spans, links) and items that
/// are unusable on a stable toolchain, so cached models stay small.
pub fn prune(doc: &mut rd::Crate) {
    doc.index.retain(|_, it| {
        // stability of inherent/trait impl blocks is not enforced by rustc (a
        // stable method inside an impl block marked unstable stays usable); the
        // items inside are filtered by their own stability
        (matches!(it.inner, rd::ItemEnum::Impl(_)) || !matches!(it.stability.as_deref(), Some(rd::Stability { level: rd::StabilityLevel::Unstable, .. })))
            && !matches!(it.inner, rd::ItemEnum::Macro(_) | rd::ItemEnum::ProcMacro(_))
    });
    for it in doc.index.values_mut() {
        it.docs = None;
        it.span = None;
        it.links.clear();
    }
}

#[derive(Default)]
pub struct World {
    pub crates: Vec<LoadedCrate>,
    by_key: HashMap<String, CrateIx>,
    /// Package keys referenced but not loaded.
    pub missing: RefCell<BTreeSet<String>>,
    public_paths: RefCell<Option<HashMap<ItemRef, Vec<String>>>>,
    alias_for: RefCell<HashMap<ItemRef, (ItemRef, Vec<String>)>>,
}

pub fn is_hidden(it: &rd::Item) -> bool {
    it.attrs.iter().any(|a| matches!(a, rd::Attribute::Other(s) if s.contains("doc(hidden)")))
}

pub fn is_non_exhaustive(it: &rd::Item) -> bool {
    it.attrs.iter().any(|a| matches!(a, rd::Attribute::NonExhaustive))
}

impl World {
    pub fn add(&mut self, c: LoadedCrate) -> CrateIx {
        let ix = self.crates.len();
        self.by_key.insert(c.info.key.clone(), ix);
        self.crates.push(c);
        *self.public_paths.borrow_mut() = None;
        ix
    }

    pub fn by_key(&self, key: &str) -> Option<CrateIx> {
        self.by_key.get(key).copied()
    }

    pub fn info(&self, c: CrateIx) -> &CrateInfo {
        &self.crates[c].info
    }

    pub fn root(&self, c: CrateIx) -> ItemRef {
        ItemRef { krate: c, id: self.crates[c].doc.root.0 }
    }

    pub fn item(&self, r: ItemRef) -> Option<&rd::Item> {
        self.crates.get(r.krate)?.doc.index.get(&rd::Id(r.id))
    }

    pub fn name(&self, r: ItemRef) -> String {
        self.item(r).and_then(|i| i.name.clone()).unwrap_or_default()
    }

    /// Package key of the crate a crate refers to by Rust crate name.
    fn dep_key(&self, from: CrateIx, ext_name: &str) -> String {
        let info = &self.crates[from].info;
        if let Some(k) = info.deps.get(ext_name) {
            return k.clone();
        }
        // toolchain crates are shared by every crate of the compilation
        if let Some(c) = self.crates.iter().find(|c| c.info.toolchain && c.info.lib == ext_name) {
            return c.info.key.clone();
        }
        if matches!(ext_name, "std" | "core" | "alloc") {
            return format!("{ext_name}@toolchain");
        }
        // a crate reached through a re-export chain (glyphon re-exports cosmic_text,
        // which re-exports fontdb): the dependency of another loaded crate
        for c in &self.crates {
            if let Some(k) = c.info.deps.get(ext_name) {
                return k.clone();
            }
        }
        format!("{ext_name}@?")
    }

    /// Resolves an id used inside crate `c` to the item's defining crate.
    pub fn resolve(&self, c: CrateIx, id: &rd::Id) -> Option<ItemRef> {
        let doc = &self.crates.get(c)?.doc;
        if let Some(it) = doc.index.get(id) {
            if it.crate_id == 0 {
                return Some(ItemRef { krate: c, id: id.0 });
            }
        }
        let summary = doc.paths.get(id)?;
        if summary.crate_id == 0 {
            // local but pruned (unstable/macro) or not documented
            return doc.index.contains_key(id).then_some(ItemRef { krate: c, id: id.0 });
        }
        let ext = doc.external_crates.get(&summary.crate_id)?;
        let key = self.dep_key(c, &ext.name);
        let Some(t) = self.by_key(&key) else {
            // an inlined copy is usable while the defining crate is not loaded
            if doc.index.contains_key(id) {
                return Some(ItemRef { krate: c, id: id.0 });
            }
            if let Some(lib) = key.strip_suffix("@?") {
                // resolved by the driver from the package graph (by library name)
                self.missing.borrow_mut().insert(format!("lib:{lib}"));
            } else {
                self.missing.borrow_mut().insert(key);
            }
            return None;
        };
        let tc = &self.crates[t];
        if let Some(&tid) = tc.local_paths.get(&(summary.path.clone(), summary.kind)) {
            if tc.doc.index.contains_key(&rd::Id(tid)) {
                return Some(ItemRef { krate: t, id: tid });
            }
            return None;
        }
        // fall back: same name and kind, unique in the target crate
        let last = summary.path.last()?;
        let mut cands = tc.local_paths.iter().filter(|((p, k), tid)| p.last() == Some(last) && *k == summary.kind && tc.doc.index.contains_key(&rd::Id(**tid)));
        let first = cands.next()?;
        if cands.next().is_some() {
            return None;
        }
        Some(ItemRef { krate: t, id: *first.1 })
    }

    /// Definition path of an item (`["wgpu_types", "TextureFormat"]`).
    pub fn def_path(&self, r: ItemRef) -> Vec<String> {
        let c = &self.crates[r.krate];
        match c.doc.paths.get(&rd::Id(r.id)) {
            Some(s) => s.path.clone(),
            None => vec![c.info.lib.clone(), self.name(r)],
        }
    }

    /// Stable identity of a type: package identity + definition path.
    pub fn type_key(&self, r: ItemRef) -> String {
        format!("{}::{}", self.crates[r.krate].info.key, self.def_path(r)[1..].join("::"))
    }

    /// Canonical path text used to recognise standard types (`alloc::vec::Vec`).
    pub fn std_path(&self, r: ItemRef) -> Option<String> {
        let c = &self.crates[r.krate];
        if !c.info.toolchain && !matches!(c.info.lib.as_str(), "std" | "core" | "alloc") {
            return None;
        }
        Some(self.def_path(r).join("::"))
    }

    /// Public members of a module (re-exports and globs followed).
    pub fn members(&self, m: ItemRef) -> Vec<(String, ItemRef)> {
        let mut out = Vec::new();
        let mut seen = BTreeSet::new();
        self.members_into(m, &mut out, &mut seen);
        out
    }

    fn members_into(&self, m: ItemRef, out: &mut Vec<(String, ItemRef)>, seen: &mut BTreeSet<ItemRef>) {
        if !seen.insert(m) {
            return;
        }
        let Some(rd::Item { inner: rd::ItemEnum::Module(md), .. }) = self.item(m) else { return };
        for id in &md.items {
            let Some(it) = self.crates[m.krate].doc.index.get(id) else { continue };
            if !matches!(it.visibility, rd::Visibility::Public) || is_hidden(it) {
                continue;
            }
            match &it.inner {
                rd::ItemEnum::Use(u) => {
                    let Some(tid) = &u.id else { continue };
                    let Some(t) = self.resolve(m.krate, tid) else { continue };
                    if u.is_glob {
                        if matches!(self.item(t).map(|i| &i.inner), Some(rd::ItemEnum::Module(_))) {
                            self.members_into(t, out, seen);
                        }
                    } else {
                        out.push((u.name.clone(), t));
                    }
                }
                rd::ItemEnum::Impl(_) => {}
                _ => {
                    if let Some(n) = &it.name {
                        out.push((n.clone(), ItemRef { krate: m.krate, id: id.0 }));
                    }
                }
            }
        }
    }

    pub fn lookup(&self, m: ItemRef, name: &str) -> Option<ItemRef> {
        self.members(m).into_iter().find(|(n, _)| n == name).map(|(_, r)| r)
    }

    /// Resolves a dotted source path from a crate root.
    pub fn lookup_path(&self, c: CrateIx, path: &[String]) -> Option<ItemRef> {
        let mut cur = self.root(c);
        for seg in path {
            cur = self.lookup(cur, seg)?;
        }
        Some(cur)
    }

    /// A public path to an item from a crate the generated program depends on
    /// (direct dependencies and the standard library), shortest first.
    pub fn rust_path(&self, r: ItemRef) -> Option<String> {
        if self.public_paths.borrow().is_none() {
            *self.public_paths.borrow_mut() = Some(self.compute_public_paths());
        }
        if let Some(p) = self.public_paths.borrow().as_ref().unwrap().get(&r) {
            return Some(p.join("::"));
        }
        // a toolchain item not re-exported publicly: its definition path
        let c = &self.crates[r.krate].info;
        if c.toolchain {
            return Some(self.def_path(r).join("::"));
        }
        None
    }

    fn compute_public_paths(&self) -> HashMap<ItemRef, Vec<String>> {
        let mut out: HashMap<ItemRef, Vec<String>> = HashMap::new();
        let mut roots: Vec<CrateIx> = (0..self.crates.len()).filter(|&c| self.crates[c].info.direct).collect();
        // `std` names everything core/alloc re-export.
        roots.extend((0..self.crates.len()).filter(|&c| self.crates[c].info.lib == "std"));
        // without std loaded, core/alloc name their own items through public
        // re-exports (`core::num::NonZero`, not the private
        // `core::num::nonzero::NonZero`). Queued after std, so a std
        // path of the same length wins.
        roots.extend((0..self.crates.len()).filter(|&c| self.crates[c].info.toolchain && matches!(self.crates[c].info.lib.as_str(), "core" | "alloc")));
        let mut queue: VecDeque<(ItemRef, Vec<String>)> = VecDeque::new();
        for c in roots {
            let r = self.root(c);
            queue.push_back((r, vec![self.crates[c].info.lib.clone()]));
        }
        let mut seen_mod = BTreeSet::new();
        while let Some((m, path)) = queue.pop_front() {
            if !seen_mod.insert(m) {
                continue;
            }
            out.entry(m).or_insert_with(|| path.clone());
            for (name, t) in self.members(m) {
                let mut p = path.clone();
                p.push(name);
                match self.item(t).map(|i| &i.inner) {
                    Some(rd::ItemEnum::Module(_)) => queue.push_back((t, p)),
                    _ => {
                        let e = out.entry(t).or_insert_with(|| p.clone());
                        if p.len() < e.len() {
                            *e = p;
                        }
                    }
                }
            }
        }
        // a type reachable only through a public alias (`wgpu::TextureViewDescriptor<'a>
        // = wgpu_types::TextureViewDescriptor<Label<'a>>`) is named by the alias
        let aliases: Vec<(ItemRef, Vec<String>)> = out.iter().map(|(k, v)| (*k, v.clone())).collect();
        let mut via = self.alias_for.borrow_mut();
        for (a, path) in aliases {
            if let Some(rd::Item { inner: rd::ItemEnum::TypeAlias(al), .. }) = self.item(a) {
                if let rd::Type::ResolvedPath(p) = &al.type_ {
                    if let Some(t) = self.resolve(a.krate, &p.id) {
                        if !out.contains_key(&t) {
                            via.entry(t).or_insert((a, path));
                        }
                    }
                }
            }
        }
        out
    }

    /// The public alias naming a type that has no public path of its own.
    pub fn alias_for(&self, r: ItemRef) -> Option<(ItemRef, String)> {
        if self.public_paths.borrow().is_none() {
            *self.public_paths.borrow_mut() = Some(self.compute_public_paths());
        }
        self.alias_for.borrow().get(&r).map(|(a, p)| (*a, p.join("::")))
    }

    /// Impl blocks of a struct/enum/union (inherent and trait impls, including
    /// synthetic auto-trait impls).
    pub fn impls_of(&self, r: ItemRef) -> Vec<ItemRef> {
        let ids = match self.item(r).map(|i| &i.inner) {
            Some(rd::ItemEnum::Struct(s)) => s.impls.clone(),
            Some(rd::ItemEnum::Enum(e)) => e.impls.clone(),
            Some(rd::ItemEnum::Union(u)) => u.impls.clone(),
            _ => Vec::new(),
        };
        ids.iter().filter(|id| self.crates[r.krate].doc.index.contains_key(id)).map(|id| ItemRef { krate: r.krate, id: id.0 }).collect()
    }

    /// Names of traits implemented (non-negatively) for a type, by last path
    /// segment: `Clone`, `Copy`, `Display`, `Send`, ... Conditional impls count.
    pub fn trait_names(&self, r: ItemRef) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        for i in self.impls_of(r) {
            if let Some(rd::Item { inner: rd::ItemEnum::Impl(imp), .. }) = self.item(i) {
                if imp.is_negative || imp.blanket_impl.is_some() {
                    continue;
                }
                if let Some(t) = &imp.trait_ {
                    out.insert(t.path.rsplit("::").next().unwrap_or(&t.path).to_string());
                }
            }
        }
        out
    }

    /// Items of a trait definition.
    pub fn trait_items(&self, t: ItemRef) -> Vec<ItemRef> {
        match self.item(t).map(|i| &i.inner) {
            Some(rd::ItemEnum::Trait(tr)) => {
                tr.items.iter().filter(|id| self.crates[t.krate].doc.index.contains_key(id)).map(|id| ItemRef { krate: t.krate, id: id.0 }).collect()
            }
            _ => Vec::new(),
        }
    }

    pub fn impl_items(&self, i: ItemRef) -> Vec<ItemRef> {
        match self.item(i).map(|x| &x.inner) {
            Some(rd::ItemEnum::Impl(imp)) => {
                imp.items.iter().filter(|id| self.crates[i.krate].doc.index.contains_key(id)).map(|id| ItemRef { krate: i.krate, id: id.0 }).collect()
            }
            _ => Vec::new(),
        }
    }
}

/// Rendered signature of a function item (documentation and `luarc bindings`).
pub fn fn_signature(w: &World, f: ItemRef) -> String {
    let Some(it) = w.item(f) else { return String::new() };
    let rd::ItemEnum::Function(func) = &it.inner else { return it.name.clone().unwrap_or_default() };
    let gens: Vec<String> = func
        .generics
        .params
        .iter()
        .filter(|p| !matches!(p.kind, rd::GenericParamDefKind::Type { is_synthetic: true, .. }))
        .map(|p| p.name.clone())
        .collect();
    let ps: Vec<String> = func.sig.inputs.iter().map(|(n, t)| if n == "self" { render_self(t) } else { format!("{n}: {}", render(t)) }).collect();
    let ret = func.sig.output.as_ref().map(|t| format!(" -> {}", render(t))).unwrap_or_default();
    let g = if gens.is_empty() { String::new() } else { format!("<{}>", gens.join(", ")) };
    format!("fn {}{g}({}){ret}", it.name.clone().unwrap_or_default(), ps.join(", "))
}

fn render_self(t: &rd::Type) -> String {
    match t {
        rd::Type::BorrowedRef { is_mutable: true, .. } => "&mut self".into(),
        rd::Type::BorrowedRef { .. } => "&self".into(),
        _ => "self".into(),
    }
}

/// Human-readable rendering of a rustdoc type.
pub fn render(t: &rd::Type) -> String {
    match t {
        rd::Type::Primitive(p) | rd::Type::Generic(p) => p.clone(),
        rd::Type::Tuple(ts) => format!("({})", ts.iter().map(render).collect::<Vec<_>>().join(", ")),
        rd::Type::Slice(e) => format!("[{}]", render(e)),
        rd::Type::Array { type_, len } => format!("[{}; {len}]", render(type_)),
        rd::Type::BorrowedRef { lifetime, is_mutable, type_ } => {
            format!("&{}{}{}", lifetime.as_ref().map(|l| format!("{l} ")).unwrap_or_default(), if *is_mutable { "mut " } else { "" }, render(type_))
        }
        rd::Type::ResolvedPath(p) => {
            let base = p.path.rsplit("::").next().unwrap_or(&p.path).to_string();
            match p.args.as_deref() {
                Some(rd::GenericArgs::AngleBracketed { args, constraints }) if !args.is_empty() || !constraints.is_empty() => {
                    let mut parts: Vec<String> = args
                        .iter()
                        .map(|a| match a {
                            rd::GenericArg::Lifetime(l) => l.clone(),
                            rd::GenericArg::Type(t) => render(t),
                            rd::GenericArg::Const(c) => c.expr.clone(),
                            rd::GenericArg::Infer => "_".into(),
                        })
                        .collect();
                    for c in constraints {
                        if let rd::AssocItemConstraintKind::Equality(rd::Term::Type(t)) = &c.binding {
                            parts.push(format!("{} = {}", c.name, render(t)));
                        }
                    }
                    format!("{base}<{}>", parts.join(", "))
                }
                Some(rd::GenericArgs::Parenthesized { inputs, output }) => {
                    format!("{base}({}){}", inputs.iter().map(render).collect::<Vec<_>>().join(", "), output.as_ref().map(|o| format!(" -> {}", render(o))).unwrap_or_default())
                }
                _ => base,
            }
        }
        rd::Type::ImplTrait(bs) => format!("impl {}", bounds(bs)),
        rd::Type::DynTrait(d) => format!("dyn {}", d.traits.iter().map(|p| render(&rd::Type::ResolvedPath(p.trait_.clone()))).collect::<Vec<_>>().join(" + ")),
        rd::Type::QualifiedPath { name, self_type, trait_, .. } => match trait_ {
            Some(tr) => format!("<{} as {}>::{name}", render(self_type), tr.path),
            None => format!("{}::{name}", render(self_type)),
        },
        rd::Type::FunctionPointer(_) => "fn(..)".into(),
        rd::Type::RawPointer { is_mutable, type_ } => format!("*{} {}", if *is_mutable { "mut" } else { "const" }, render(type_)),
        rd::Type::Infer => "_".into(),
        rd::Type::Pat { type_, .. } => render(type_),
    }
}

pub fn bounds(bs: &[rd::GenericBound]) -> String {
    bs.iter()
        .map(|b| match b {
            rd::GenericBound::TraitBound { trait_, .. } => render(&rd::Type::ResolvedPath(trait_.clone())),
            rd::GenericBound::Outlives(l) => l.clone(),
            rd::GenericBound::Use(_) => "use<..>".into(),
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

impl World {
    /// Standard container kind of a type referenced from crate `c`, recognised
    /// from the referencing crate's own path table, so `String`, `Vec`,
    /// `Option`, ... need no toolchain model to be loaded.
    pub fn std_kind_id(&self, c: CrateIx, id: &rd::Id) -> Option<crate::native::types::StdKind> {
        let lc = self.crates.get(c)?;
        let s = lc.doc.paths.get(id)?;
        let crate_name = if s.crate_id == 0 { lc.info.lib.clone() } else { lc.doc.external_crates.get(&s.crate_id)?.name.clone() };
        if !matches!(crate_name.as_str(), "std" | "core" | "alloc") {
            return None;
        }
        crate::native::types::std_kind_of_path(&s.path.join("::"))
    }
}
