//! Tasks and `await`.
//!
//! * `task.spawn(function() ... end)` starts a task; its function literal is a
//!   *task function* (no parameters, no results) in which `await(future)` may
//!   suspend. The compiler lowers it to a Rust future polled by the runtime
//!   executor (`lr::task`). `await` anywhere else is a compile error: ordinary
//!   functions never suspend, so callers never need effect annotations.
//! * `task.cancel(t)` drops a pending task (and what it retained);
//!   `task.run_ready()` polls woken tasks (an event loop calls it when its wake
//!   hook fires); `task.pending()` counts pending tasks.
//! * `await(f)` takes a native future (`impl Future`/`async fn` result) and
//!   yields its results; a native `Err` becomes a language error at the `await`.

use std::rc::Rc;

use crate::ast::*;
use crate::check::*;
use crate::types::*;

impl<'a> Checker<'a> {
    pub(crate) fn task_call(&mut self, e: &Expr, name: &str, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        let span = e.span;
        let out = match name {
            "spawn" => {
                let ok = args.len() == 1 && matches!(&args[0].kind, ExprKind::Function(f) if f.params.is_empty());
                if !ok {
                    self.error(span, "task.spawn expects a function literal without parameters: task.spawn(function() ... end)");
                    for a in args {
                        self.expr(a);
                    }
                } else {
                    let ExprKind::Function(f) = &args[0].kind else { unreachable!() };
                    let ft = self.func_ty_skeleton(f);
                    self.next_fn_is_task = true;
                    self.check_func_body(f, ft);
                    let ftv = self.val(ft);
                    self.info.expr.insert(args[0].id, ftv);
                    if let TyNode::Func(fty) = self.st.node(ft).clone() {
                        let empty = self.st.new_rets(RetsNode::Known(vec![]));
                        if !self.unify_rets(fty.rets, empty, args[0].span) {
                            self.error(args[0].span, "a task function returns no values");
                        }
                    }
                }
                self.info.calls.insert(e.id, CallKind::Task("spawn".into()));
                let t = self.prim(TyNode::Task);
                vec![self.val(t)]
            }
            "wake_through" => {
                // an event loop wakes when a task does (adapter-declared waker protocol)
                let (vals, spans) = self.args_values(args);
                self.info.calls.insert(e.id, CallKind::Task(name.into()));
                if vals.len() != 1 {
                    self.error(span, "task.wake_through expects one native object");
                    return vec![];
                }
                self.need(vals[0], spans[0], "bad argument to task.wake_through (got nil)");
                match self.st.node(vals[0].ty).clone() {
                    TyNode::Native(nt) if self.adapters.task_waker(nt.item).is_some() => {
                        self.info.task_wakers.insert(e.id, nt.item);
                    }
                    _ => {
                        let s = self.show(vals[0].ty);
                        self.error(spans[0], format!("task.wake_through needs a native object with a declared waker protocol (an adapter [[task_waker]]); {s} has none"));
                    }
                }
                vec![]
            }
            "cancel" | "is_pending" => {
                let (vals, spans) = self.args_values(args);
                if vals.len() != 1 {
                    self.error(span, format!("task.{name} expects one task"));
                } else {
                    let t = self.prim(TyNode::Task);
                    self.unify(vals[0].ty, t, spans[0]);
                    self.need(vals[0], spans[0], "bad argument to task function (task expected, got nil)");
                }
                self.info.calls.insert(e.id, CallKind::Task(name.into()));
                vec![self.bool_()]
            }
            "run_ready" | "pending" | "wait_idle" | "polls" => {
                let (vals, _) = self.args_values(args);
                if !vals.is_empty() {
                    self.error(span, format!("task.{name} takes no arguments"));
                }
                self.info.calls.insert(e.id, CallKind::Task(name.into()));
                vec![self.num()]
            }
            _ => {
                for a in args {
                    self.expr(a);
                }
                self.error(span, format!("task.{name} is not a task function (spawn, cancel, is_pending, run_ready, wait_idle, pending, polls)"));
                vec![self.fresh_result()]
            }
        };
        fit(self, out, want)
    }

    pub(crate) fn await_call(&mut self, e: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        let in_task = self.fns.last().map(|f| f.task).unwrap_or(false);
        if !in_task {
            self.error(
                e.span,
                "await can only be used directly inside a task function: task.spawn(function() ... await(f) ... end)",
            );
        }
        let (vals, spans) = self.args_values(args);
        self.info.calls.insert(e.id, CallKind::Await);
        if vals.len() != 1 {
            self.error(e.span, "await expects one future");
            return fit(self, vec![], want);
        }
        self.need(vals[0], spans[0], "attempt to await a nil value");
        let out = match self.st.node(vals[0].ty).clone() {
            TyNode::Future(rets) => rets.iter().map(|s| ETy { ty: s.ty, null: s.null, soft: Soft::No }).collect(),
            TyNode::Native(nt) => match self.native_future_inst(&nt, vals[0].ty, e.span) {
                Ok(inst) => {
                    self.info.await_native.insert(e.id, inst);
                    let TyNode::Future(rets) = self.st.node(self.info.natives[inst].rets[0].ty).clone() else { unreachable!() };
                    rets.iter().map(|s| ETy { ty: s.ty, null: s.null, soft: Soft::No }).collect()
                }
                Err(m) => {
                    self.error(spans[0], m);
                    vec![]
                }
            },
            TyNode::Var => {
                self.error(spans[0], "cannot infer the type of the awaited value; it must be a native future");
                vec![]
            }
            _ => {
                let s = self.show(vals[0].ty);
                self.error(spans[0], format!("await expects a native future, got {s}"));
                vec![]
            }
        };
        fit(self, out, want)
    }

    /// `await(x)` on a native value whose type implements `Future`: the value is
    /// consumed into a future yielding its `Output`.
    fn native_future_inst(&mut self, nt: &NativeTy, ty: TyId, span: crate::diag::Span) -> Result<usize, String> {
        let w = self.world();
        let tname = w.name(nt.item);
        let Some((imp, tr)) = self.toolchain_trait_impl(nt.item, "Future") else {
            return Err(format!("await expects a native future, got {tname} (it does not implement Future)"));
        };
        let env = self.impl_env(imp, nt.item, &nt.args, ty, span).ok_or("the Future impl does not apply to these type arguments")?;
        let (c, out) = env.assoc.get("Output").cloned().ok_or("the Future impl has no Output type")?;
        let ienv = env.in_crate(c);
        let (rs, _) = self.n_rets(&out, &ienv, span).map_err(|m| format!("await on {tname}: {m}"))?;
        let ft = self.future_ty(rs);
        let poll = w.impl_items(imp).into_iter().find(|x| w.name(*x) == "poll").unwrap_or(imp);
        self.info.natives.push(crate::check_native::NativeInst {
            kind: crate::check_native::NKind::AwaitNative,
            item: poll,
            owner: Some((nt.item, nt.args.clone())),
            imp: Some(imp),
            trait_: Some(tr),
            env: ienv,
            span,
            params: vec![],
            rets: vec![self.st.fixed_slot(ft, span, "futures are never nil")],
            recv: Some(ty),
            fallible: false,
            display: format!("await {tname}"),
            deref: 0,
        });
        Ok(self.info.natives.len() - 1)
    }

    /// Source type of a native future yielding `rets`.
    pub(crate) fn future_ty(&mut self, rets: Vec<Slot>) -> TyId {
        self.st.ty(TyNode::Future(Rc::new(rets)))
    }
}

fn fit(ck: &mut Checker, mut out: Vec<ETy>, want: Option<usize>) -> Vec<ETy> {
    if let Some(n) = want {
        out.truncate(n);
        while out.len() < n {
            let x = ck.nil();
            out.push(x);
        }
    }
    out
}
