//! `luarc bindings <crate>`: every public item of a crate with its Rust
//! signature and support status (automatic / adapter-backed / unsupported with
//! the reason). Status comes from a dry-run instantiation with the same checker
//! code the compiler uses at call sites, so the report cannot drift from it.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use rustdoc_types as rd;

use crate::check::Checker;
use crate::diag::{SourceMap, Span};
use crate::native::adapters::AdapterSet;
use crate::native::types::{GKind, Repr, VariantShape};
use crate::native::world::{fn_signature, render, CrateIx, ItemRef, World};
use crate::resolve::Resolution;

pub struct Entry {
    pub path: String,
    pub kind: &'static str,
    pub signature: String,
    pub status: String,
}

pub struct Report {
    pub types: Vec<String>,
    pub items: Vec<Entry>,
    pub skipped: Vec<String>,
}

impl Report {
    pub fn counts(&self) -> (usize, usize, usize) {
        let auto = self.items.iter().filter(|e| e.status == "automatic").count();
        let adapter = self.items.iter().filter(|e| e.status.starts_with("adapter-backed")).count();
        (auto, adapter, self.items.len() - auto - adapter)
    }
}

pub fn report(world: &World, adapters: &AdapterSet, c: CrateIx) -> Report {
    let res = Resolution::default();
    let sm = SourceMap::default();
    let mut ck = Checker::new(&res, &sm, world, adapters);
    let mut rep = Report { types: Vec::new(), items: Vec::new(), skipped: Vec::new() };
    let mut seen = BTreeSet::new();
    walk(&mut ck, world, adapters, world.root(c), &[], &mut rep, &mut seen);
    rep.items.sort_by(|a, b| a.path.cmp(&b.path));
    rep
}

fn walk(ck: &mut Checker, w: &World, ad: &AdapterSet, m: ItemRef, path: &[String], rep: &mut Report, seen: &mut BTreeSet<ItemRef>) {
    if !seen.insert(m) {
        return;
    }
    for (name, t) in w.members(m) {
        let mut p = path.to_vec();
        p.push(name.clone());
        let dotted = p.join(".");
        let Some(it) = w.item(t) else { continue };
        match &it.inner {
            rd::ItemEnum::Module(_) => walk(ck, w, ad, t, &p, rep, seen),
            rd::ItemEnum::Function(_) => {
                let status = status_of(ck.instantiate_native(t, None, None, None, None, Span::default(), dotted.clone()), None);
                rep.items.push(Entry { path: dotted, kind: "fn", signature: fn_signature(w, t), status });
            }
            rd::ItemEnum::Constant { type_, .. } => {
                rep.items.push(Entry { path: dotted, kind: "const", signature: format!("const {name}: {}", render(type_)), status: "automatic".into() });
            }
            rd::ItemEnum::TypeAlias(a) => {
                let target = match &a.type_ {
                    rd::Type::ResolvedPath(rp) => w.resolve(t.krate, &rp.id).map(|r| w.name(r)).unwrap_or_else(|| render(&a.type_)),
                    other => render(other),
                };
                rep.types.push(format!("  {dotted:<28} alias of {target}"));
            }
            rd::ItemEnum::Struct(_) | rd::ItemEnum::Enum(_) | rd::ItemEnum::Union(_) => {
                if !seen.insert(t) {
                    // re-exported under another path: list the alias
                    rep.types.push(format!("  {dotted:<28} alias of {}", w.name(t)));
                    continue;
                }
                type_entries(ck, w, ad, t, &dotted, rep);
            }
            rd::ItemEnum::Trait(_) => rep.skipped.push(format!("  {dotted}: trait items are not imported (implement traits from source with a table)")),
            rd::ItemEnum::Static(_) => rep.items.push(Entry { path: dotted, kind: "static", signature: format!("static {name}"), status: "automatic".into() }),
            other => {
                let k = format!("{:?}", other).split(['(', ' ', '{']).next().unwrap_or("").to_lowercase();
                rep.skipped.push(format!("  {dotted}: {k} items are not imported"));
            }
        }
    }
}

fn status_of(r: Result<usize, String>, adapter: Option<String>) -> String {
    match (r, adapter) {
        (Ok(_), Some(a)) => format!("adapter-backed ({a})"),
        (Ok(_), None) => "automatic".into(),
        (Err(e), _) => format!("UNSUPPORTED: {e}"),
    }
}

fn type_entries(ck: &mut Checker, w: &World, ad: &AdapterSet, t: ItemRef, dotted: &str, rep: &mut Report) {
    let repr = w.repr(&ck.facts, t);
    let mut line = format!("  {dotted:<28} {}", if repr == Repr::Record { "record (by value)" } else { "handle" });
    if repr == Repr::Record {
        if let Some(fs) = w.public_fields(t) {
            let fs: Vec<String> = fs.iter().map(|(n, ty)| format!("{n}: {}", render(ty))).collect();
            let _ = write!(line, " {{{}}}", fs.join(", "));
        }
    } else if w.is_enum(t) {
        let vs: Vec<String> = w.variants(t).iter().map(|v| v.name.clone()).collect();
        let _ = write!(line, " enum [{}]", vs.join(", "));
    }
    rep.types.push(line);
    let n = w.generics_of(t).iter().filter(|g| g.kind != GKind::Lifetime).count();
    let tname = w.name(t);
    for v in w.variants(t) {
        let status = match v.shape {
            VariantShape::Opaque => "UNSUPPORTED: the variant has private fields".to_string(),
            VariantShape::Struct(_) => "automatic (inspected through the payload accessor)".to_string(),
            _ => "automatic".to_string(),
        };
        rep.items.push(Entry { path: format!("{dotted}.{}", v.name), kind: "variant", signature: v.name.clone(), status });
    }
    let mut names = BTreeSet::new();
    for imp in w.impls_of(t) {
        let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = w.item(imp) else { continue };
        if i.trait_.is_some() || i.is_synthetic {
            continue;
        }
        for f in w.impl_items(imp) {
            let Some(fi) = w.item(f) else { continue };
            if !matches!(fi.visibility, rd::Visibility::Public) || crate::native::world::is_hidden(fi) {
                continue;
            }
            let fname = fi.name.clone().unwrap_or_default();
            if !names.insert(fname.clone()) {
                continue;
            }
            match &fi.inner {
                rd::ItemEnum::Function(func) => {
                    let is_method = func.sig.inputs.first().map(|(n, _)| n == "self").unwrap_or(false);
                    let args: Vec<_> = (0..n).map(|_| ck.st.var()).collect();
                    let self_ty = ck.native_adt_ty(t, args.clone(), Span::default());
                    let sep = if is_method { ":" } else { "." };
                    let disp = format!("{tname}{sep}{fname}");
                    let r = ck.instantiate_native(f, Some((t, args)), Some(imp), None, Some(self_ty), Span::default(), disp);
                    let adapter = ad.describe(t, &fname);
                    let shown = format!("{dotted}{sep}{}", ad.source_name(t, &fname).unwrap_or(fname.clone()));
                    rep.items.push(Entry { path: shown, kind: if is_method { "method" } else { "assoc fn" }, signature: fn_signature(w, f), status: status_of(r, adapter) });
                }
                rd::ItemEnum::AssocConst { type_, .. } => {
                    rep.items.push(Entry { path: format!("{dotted}.{fname}"), kind: "const", signature: format!("const {fname}: {}", render(type_)), status: "automatic".into() });
                }
                _ => {}
            }
        }
    }
    for (m, a) in ad.closes_of(t) {
        rep.items.push(Entry { path: format!("{dotted}:{m}"), kind: "method", signature: format!("fn {m}(&self) (deterministic release)"), status: format!("adapter-backed ({a})") });
    }
}

pub fn render_report(world: &World, c: CrateIx, rep: &Report) -> String {
    let info = world.info(c);
    let mut s = String::new();
    let _ = writeln!(s, "crate {} {} (lib `{}`), features: [{}]", info.package, info.version, info.lib, info.features.join(", "));
    let _ = writeln!(s, "rustdoc JSON format {}\n", crate::native::world::FORMAT_VERSION);
    let _ = writeln!(s, "types:");
    for t in &rep.types {
        let _ = writeln!(s, "{t}");
    }
    let _ = writeln!(s, "\nitems:");
    for it in &rep.items {
        let _ = writeln!(s, "  {:<32} {:<9} {}\n  {:<32} {:<9} -> {}", it.path, it.kind, it.signature, "", "", it.status);
    }
    if !rep.skipped.is_empty() {
        let _ = writeln!(s, "\nnot imported:");
        for p in &rep.skipped {
            let _ = writeln!(s, "{}", p.trim_start().replacen("", "  ", 1));
        }
    }
    s
}
