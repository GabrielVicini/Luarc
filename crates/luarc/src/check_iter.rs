//! Native iteration (`for x in native do`), `Deref` targets for method lookup and
//! owned forms of borrowed unsized native types.

use rustdoc_types as rd;

use crate::check::*;
use crate::check_native::{NEnv, NKind, NativeInst};
use crate::diag::Span;
use crate::native::types::*;
use crate::native::world::ItemRef;
use crate::types::*;

impl<'a> Checker<'a> {
    /// The non-blanket impl of toolchain trait `trait_name` for `owner` itself.
    pub(crate) fn toolchain_trait_impl(&self, owner: ItemRef, trait_name: &str) -> Option<(ItemRef, ItemRef)> {
        let w = self.world();
        for imp in w.impls_of(owner) {
            let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = w.item(imp) else { continue };
            let Some(tp) = &i.trait_ else { continue };
            if i.is_negative || i.blanket_impl.is_some() || last_seg(&tp.path) != trait_name {
                continue;
            }
            // impls for `&T` / `&mut T` are not impls for the type itself
            if !matches!(&i.for_, rd::Type::ResolvedPath(_)) {
                continue;
            }
            let Some(tr) = w.resolve(imp.krate, &tp.id) else { continue };
            if w.std_path(tr).is_none() {
                continue;
            }
            return Some((imp, tr));
        }
        None
    }

    /// Instance of `Iterator::next` for a native iterator type. Its results are the
    /// item (a tuple item spreads over several loop variables); a `Result` item is
    /// peeled (an `Err` item raises a language error at the loop).
    fn iter_next_inst(&mut self, owner: ItemRef, args: &[TyId], self_ty: TyId, nvars: usize, span: Span) -> Result<Option<usize>, String> {
        let w = self.world();
        let Some((imp, tr)) = self.toolchain_trait_impl(owner, "Iterator") else { return Ok(None) };
        let env = self.impl_env(imp, owner, args, self_ty, span).ok_or("the Iterator impl does not apply to these type arguments")?;
        let (c, item_t) = env.assoc.get("Item").cloned().ok_or("the Iterator impl has no Item type")?;
        let ienv = env.in_crate(c);
        let (inner, fallible) = self.peel_result(&item_t, &ienv);
        let rets = match &inner {
            rd::Type::Tuple(ts) if nvars > 1 && ts.len() == nvars => {
                let mut out = Vec::new();
                for x in ts {
                    out.push(self.n_slot(x, &ienv, span)?);
                }
                out
            }
            other => vec![self.n_slot(other, &ienv, span)?],
        };
        let next = w
            .impl_items(imp)
            .into_iter()
            .find(|x| w.name(*x) == "next")
            .or_else(|| w.trait_items(tr).into_iter().find(|x| w.name(*x) == "next"))
            .ok_or("the Iterator impl has no next method")?;
        self.info.natives.push(NativeInst {
            kind: NKind::IterNext,
            item: next,
            owner: Some((owner, args.to_vec())),
            imp: Some(imp),
            trait_: Some(tr),
            env,
            span,
            params: vec![],
            rets,
            recv: Some(self_ty),
            fallible,
            display: format!("{}:next", w.name(owner)),
            deref: 0,
        });
        Ok(Some(self.info.natives.len() - 1))
    }

    /// Binds the loop variables of `for ... in v` over a native iterator, or over a
    /// native value implementing `IntoIterator` (the value is consumed).
    pub(crate) fn native_iter(&mut self, node: crate::ast::NodeId, nt: &NativeTy, ty: TyId, vars: &[Slot], span: Span) {
        let w = self.world();
        let tname = w.name(nt.item);
        let bind = |ck: &mut Self, next: usize| {
            let rets = ck.info.natives[next].rets.clone();
            if rets.len() != vars.len() && vars.len() > 1 {
                ck.error(span, format!("the iterator yields {} value(s), the loop binds {}", rets.len(), vars.len()));
            }
            for (v, r) in vars.iter().zip(rets.iter()) {
                let e = ETy { ty: r.ty, null: r.null, soft: Soft::No };
                ck.flow(e, *v, span);
            }
        };
        match self.iter_next_inst(nt.item, &nt.args, ty, vars.len(), span) {
            Ok(Some(next)) => {
                bind(self, next);
                self.info.fors.insert(node, ForKind::Native(None, next));
                return;
            }
            Ok(None) => {}
            Err(m) => {
                self.error(span, format!("cannot iterate over {tname}: {m}"));
                return;
            }
        }
        let Some((imp, tr)) = self.toolchain_trait_impl(nt.item, "IntoIterator") else {
            self.error(span, format!("native type {tname} is not an iterator (it implements neither Iterator nor IntoIterator)"));
            return;
        };
        let Some(f) = w.impl_items(imp).into_iter().find(|x| w.name(*x) == "into_iter") else {
            self.error(span, format!("{tname}: IntoIterator impl without into_iter"));
            return;
        };
        let into = match self.instantiate_native(f, Some((nt.item, nt.args.clone())), Some(imp), Some(tr), Some(ty), span, format!("{tname}:into_iter")) {
            Ok(i) => i,
            Err(m) => {
                self.error(span, format!("cannot iterate over {tname}: {m}"));
                return;
            }
        };
        let Some(it_ty) = self.info.natives[into].rets.first().map(|s| s.ty) else { return };
        match self.st.node(it_ty).clone() {
            TyNode::Native(it) => match self.iter_next_inst(it.item, &it.args, it_ty, vars.len(), span) {
                Ok(Some(next)) => {
                    bind(self, next);
                    self.info.fors.insert(node, ForKind::Native(Some(into), next));
                }
                Ok(None) => self.error(span, format!("{tname}:into_iter() does not return a native iterator")),
                Err(m) => self.error(span, format!("cannot iterate over {tname}: {m}")),
            },
            _ => self.error(span, format!("{tname}:into_iter() does not return a native iterator")),
        }
    }

    /// `impl Deref for T { type Target = U }`: the source type of `U`.
    pub(crate) fn deref_target(&mut self, owner: ItemRef, args: &[TyId], self_ty: TyId, span: Span) -> Option<TyId> {
        let (imp, _) = self.toolchain_trait_impl(owner, "Deref")?;
        let env = self.impl_env(imp, owner, args, self_ty, span)?;
        let (c, t) = env.assoc.get("Target").cloned()?;
        let nv = self.n_val(&t, &env.in_crate(c), span).ok()?;
        Some(nv.ty)
    }

    /// Owned form of a borrowed unsized native type (`&Path` → `PathBuf`,
    /// `&OsStr` → `OsString`), from its explicit non-generic `ToOwned` impl.
    pub(crate) fn owned_form(&mut self, r: ItemRef, span: Span) -> Option<TyId> {
        let (_, t, krate) = owned_form_type(self.world(), r)?;
        let env = NEnv { krate, ..Default::default() };
        self.n_val(&t, &env, span).ok().map(|nv| nv.ty)
    }
}

/// `impl ToOwned for T { type Owned = U }` (non-generic, toolchain trait): (impl, U, crate).
pub(crate) fn owned_form_type(w: &crate::native::world::World, r: ItemRef) -> Option<(ItemRef, rd::Type, usize)> {
    for imp in w.impls_of(r) {
        let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = w.item(imp) else { continue };
        let Some(tp) = &i.trait_ else { continue };
        if i.is_negative || i.blanket_impl.is_some() || last_seg(&tp.path) != "ToOwned" || !i.generics.params.is_empty() {
            continue;
        }
        for it in w.impl_items(imp) {
            if let Some(rd::Item { name: Some(n), inner: rd::ItemEnum::AssocType { type_: Some(t), .. }, .. }) = w.item(it) {
                if n == "Owned" {
                    return Some((imp, t.clone(), imp.krate));
                }
            }
        }
    }
    None
}
