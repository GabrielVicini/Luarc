//! Generated Rust trait implementations delegating to source tables.
//!
//! For a table passed where a native trait implementation is expected, the
//! generated code is
//!
//! ```text
//! pub struct ImplN { pub this: lr::Rec<R0>, pub err: lr::callback::ErrorSlot }
//! impl winit::application::ApplicationHandler<()> for ImplN {
//!     fn resumed(&mut self, p1: &winit::event_loop::ActiveEventLoop) { ... }
//! }
//! ```
//!
//! Each method lends `&T` / `&mut T` arguments for the duration of the call
//! (`lr::handle::lend`), converts owned arguments, calls the table's function
//! with the table as `self`, and converts the results back. Error channels, per
//! method shape:
//! * returns `()`: the error is stored in `err`, later callbacks are suppressed,
//!   an adapter-declared exit request runs (`event_loop.exit()`), and the native
//!   call that received the implementation reports it when it returns;
//! * returns `Result<T, E>`: returned directly as `E::from(message)`;
//! * returns another value: the unwind bridge (`unwrap_or_unwind`,
//!   caught by the owning call's `guard`), only valid when the native caller is
//!   Rust code (`panic = "unwind"` is required in the generated profile).

use std::fmt::Write as _;

use rustdoc_types as rd;

use crate::check_trait::TraitImpl;
use crate::codegen::{native_ident, rust_ident, tuple_ty, Gen};
use crate::native::types::*;
use crate::native::wrap::WCtx;
use crate::types::{TyId, TyNode};

impl<'a> Gen<'a> {
    /// The argument for a trait-bounded parameter receiving a source table.
    pub(crate) fn trait_impl_arg(&mut self, impls: &[TraitImpl], pt: &rd::Type, place: &str, src: TyId, w: &mut WCtx) -> Result<String, String> {
        let name = format!("Impl{}", self.impl_count);
        self.impl_count += 1;
        let this_ty = self.rust_ty(src);
        let mut code = format!(
            "/// A source table implementing {} (generated).\npub struct {name} {{\n    pub this: {this_ty},\n    pub err: lr::callback::ErrorSlot,\n}}\n",
            impls.iter().map(|t| self.w().name(t.trait_)).collect::<Vec<_>>().join(", ")
        );
        for ti in impls {
            let block = self.trait_impl_block(&name, ti)?;
            code.push_str(&block);
        }
        self.handle_makers.insert(format!("{name}#impl"), code);
        let v = w.tmp("impl");
        let e = w.tmp("ierr");
        let _ = writeln!(w.pre, "    let mut {v} = {name} {{ this: {place}.clone(), err: lr::callback::ErrorSlot::default() }};");
        let _ = writeln!(w.pre, "    let {e} = {v}.err.clone();");
        let _ = writeln!(w.post, "    {e}.take()?;");
        w.callbacks = true;
        Ok(match pt {
            rd::Type::BorrowedRef { is_mutable: true, .. } => format!("&mut {v}"),
            rd::Type::BorrowedRef { .. } => format!("&{v}"),
            _ => v,
        })
    }

    fn trait_impl_block(&mut self, name: &str, ti: &TraitImpl) -> Result<String, String> {
        let wd = self.w();
        let tpath = self.item_path(ti.trait_)?;
        let mut targs = Vec::new();
        for gp in wd.generics_of(ti.trait_) {
            if gp.kind == GKind::Type {
                let t = *ti.env.gens.get(&gp.name).ok_or("unbound trait parameter")?;
                targs.push(self.src_rust(t)?);
            }
        }
        let tref = if targs.is_empty() { tpath } else { format!("{tpath}<{}>", targs.join(", ")) };
        let mut env = ti.env.clone();
        env.self_ty = None; // `Self` is the generated struct
        let TyNode::Table(tab) = self.node(ti.table) else { return Err("trait implementation from a non-table".into()) };
        let root = self.ck.st.tab_root(tab);
        let on_error = self.ck.adapters.trait_error(ti.trait_).map(|(a, m)| (a.to_string(), m.to_string()));
        let mut out = format!("impl {tref} for {name} {{\n");
        for (mname, mitem, implemented) in &ti.methods {
            if !implemented {
                continue;
            }
            let Some(rd::Item { inner: rd::ItemEnum::Function(f), .. }) = wd.item(*mitem) else { continue };
            let f = f.clone();
            let fslot = self.ck.st.tab(root).fields[mname];
            let TyNode::Func(sft) = self.node(fslot.ty) else { return Err(format!("field '{mname}' is not a function")) };
            let store_opt = self.field_store_opt(root, mname);
            let recv = match f.sig.inputs.first().map(|x| &x.1) {
                Some(rd::Type::BorrowedRef { is_mutable: true, .. }) => "&mut self",
                Some(rd::Type::BorrowedRef { .. }) => "&self",
                _ => "self",
            };
            let mut sig = vec![recv.to_string()];
            let mut arg_names = Vec::new();
            for (i, (pn, pt)) in f.sig.inputs.iter().enumerate().skip(1) {
                sig.push(format!("p{i}: {}", self.rty(pt, &env, "'_")?));
                arg_names.push((i, pn.clone(), pt.clone()));
            }
            let (out_ty, result_kind) = match &f.sig.output {
                None => ("()".to_string(), 0),
                Some(t) => {
                    let (inner, fallible) = self.ck.peel_result(t, &env);
                    let _ = inner;
                    (self.rty(t, &env, "'_")?, if fallible { 1 } else { 2 })
                }
            };
            // the call: lend borrowed native objects, convert the rest
            let mut w = WCtx { what: mname.clone(), ..Default::default() };
            let mut call_args = vec!["self.this.clone()".to_string()];
            let mut lends: Vec<(String, String)> = Vec::new();
            for (k, (i, _pn, pt)) in arg_names.iter().enumerate() {
                let sty = sft.params.get(k + 1).map(|s| s.ty).ok_or("parameter count")?;
                let pv = format!("p{i}");
                match pt {
                    rd::Type::BorrowedRef { is_mutable, type_, .. } if matches!(self.node(sty), TyNode::Native(nt) if !wd.trait_names(nt.item).contains("Copy")) => {
                        let TyNode::Native(nt) = self.node(sty) else { unreachable!() };
                        let inner = self.handle_inner_ty(nt.item, &nt.args)?;
                        if self.shared_repr(nt.item) {
                            return Err(format!("parameter {pv} of {mname}: lending shared (Arc) objects is unsupported"));
                        }
                        let _ = type_;
                        let (_, meta) = self.handle_support(&inner, &wd.name(nt.item));
                        let h = format!("__h{i}");
                        let f = if *is_mutable { "lend_mut" } else { "lend" };
                        lends.push((format!("lr::handle::{f}({pv}, &{meta}, |{h}| "), String::new()));
                        call_args.push(format!("{h}.clone()"));
                    }
                    _ => {
                        let c = self.conv_out(pt, &env, &pv, sty, &mut w)?;
                        let c = self.opt_wrap(c, sft.params[k + 1], pt, &env);
                        call_args.push(c);
                    }
                }
            }
            let rets = self.ck.st.rets_known(sft.rets).cloned().unwrap_or_default();
            let ret_conv = match &f.sig.output {
                None => "()".to_string(),
                Some(t) => {
                    let (inner, _) = self.ck.peel_result(t, &env);
                    match (&inner, rets.len()) {
                        (rd::Type::Tuple(ts), _) if ts.is_empty() => "()".to_string(),
                        (rd::Type::Tuple(ts), n) if n == ts.len() => {
                            let mut cs = Vec::new();
                            for (j, x) in ts.iter().enumerate() {
                                cs.push(self.conv_in(x, &env, &format!("__v.{j}"), rets[j].ty, &mut w)?);
                            }
                            format!("({})", cs.join(", "))
                        }
                        (t, 1) => self.conv_in(t, &env, "__v", rets[0].ty, &mut w)?,
                        _ => return Err(format!("method '{mname}': result count mismatch")),
                    }
                }
            };
            if !w.takes.is_empty() {
                return Err(format!("method '{mname}': results consuming source objects are unsupported"));
            }
            let read = format!("self.this.borrow().{}.clone()", rust_ident(mname));
            let fread = if store_opt { format!("lr::present({read}, \"method missing from the table\")?") } else { read };
            let mut inner = format!("let __f = {fread};\n{}let __v = __f.call({})?;\nOk({ret_conv})", w.pre, tuple_ty(&call_args));
            for (open, _) in lends.iter().rev() {
                inner = format!("{open}{{\n{inner}\n}})");
            }
            let exit = match &on_error {
                Some((arg, m)) => match arg_names.iter().find(|(_, pn, _)| pn == arg) {
                    Some((i, _, _)) => format!(" p{i}.{m}();"),
                    None => String::new(),
                },
                None => String::new(),
            };
            let (early, ok, on_err) = match result_kind {
                0 => ("return;".to_string(), "v".to_string(), format!("{{ self.err.set(e);{exit} }}")),
                1 => (
                    "return Err(::std::convert::From::from(String::from(\"suppressed after an earlier source error\")));".to_string(),
                    "Ok(v)".to_string(),
                    "Err(::std::convert::From::from(e.msg.to_string_lossy()))".to_string(),
                ),
                _ => (
                    "return lr::callback::unwrap_or_unwind(Err(lr::LuaError::new(\"suppressed after an earlier source error\")));".to_string(),
                    "v".to_string(),
                    "lr::callback::unwrap_or_unwind(Err(e))".to_string(),
                ),
            };
            let _ = writeln!(
                out,
                "    #[allow(unused_variables)]
    fn {}({}) -> {out_ty} {{
        if self.err.is_set() {{
            {early}
        }}
        let __r = lr::callback::protect(|| {{
{inner}
        }});
        match __r {{
            Ok(v) => {ok},
            Err(e) => {on_err},
        }}
    }}",
                native_ident(mname),
                sig.join(", ")
            );
        }
        out.push_str("}\n");
        Ok(out)
    }
}
