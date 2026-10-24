//! Coroutine calls use erased values at their boundary; other functions keep the
//! existing static ABI. Every argument is evaluated before the following one.

use super::*;

impl<'a> Gen<'a> {
    pub(super) fn coroutine_source_call(&self, e: &Expr, f: &FuncTy, call: RExpr) -> RExpr {
        let wrapper = self
            .ck
            .info
            .coroutines
            .wrappers
            .iter()
            .any(|r| self.ck.st.rets_root(*r) == self.ck.st.rets_root(f.rets));
        if wrapper {
            rir::at(call, &self.loc(e.span))
        } else {
            rir::try_(call)
        }
    }

    fn coroutine_values(&mut self, args: &[Expr]) -> RExpr {
        let mut pre = Vec::new();
        let mut values = Vec::new();
        let mut tail = None;
        for (i, e) in args.iter().enumerate() {
            if i + 1 == args.len() && self.is_pack(e) {
                let (p, fixed, src, first) = self.pack_src(e);
                pre.extend(p);
                for value in fixed {
                    let name = self.fresh("corov");
                    pre.push(rir::let_(
                        name.clone(),
                        rir::call(
                            "lr::dynamic_fn::IntoDynamic::into_dynamic",
                            vec![value.code],
                        ),
                    ));
                    values.push(rir::atom_e(name));
                }
                tail = Some(rir::call(
                    "lr::dynamic_fn::pack_values",
                    vec![rir::borrow(src), first],
                ));
            } else {
                let (p, vs) = if i + 1 == args.len()
                    && matches!(e.kind, ExprKind::Call(..) | ExprKind::Method(..))
                {
                    self.multi(e, None)
                } else {
                    (vec![], vec![self.expr(e)])
                };
                pre.extend(p);
                for value in vs {
                    let name = self.fresh("corov");
                    pre.push(rir::let_(
                        name.clone(),
                        rir::call(
                            "lr::dynamic_fn::IntoDynamic::into_dynamic",
                            vec![value.code],
                        ),
                    ));
                    values.push(rir::atom_e(name));
                }
            }
        }
        let fixed = RExpr::Macro("vec".into(), values);
        let out = match tail {
            Some(tail) => rir::call("lr::coroutine::join_values", vec![fixed, tail]),
            None => fixed,
        };
        rir::block(pre, out)
    }

    pub(super) fn coroutine_call_code(
        &mut self,
        e: &Expr,
        name: &str,
        args: &[Expr],
    ) -> (RExpr, Vec<(TyId, bool)>) {
        let values = self.coroutine_values(args);
        let argv = self.fresh("coroargs");
        let typ = RType::Apply("Vec".into(), vec![RType::Named("lr::Value".into())]);
        let pre = vec![RStmt::Let(argv.clone(), Some(typ.print()), values)];
        let argv = rir::atom_e(argv);
        let path = match name {
            "create" => "lr::coroutine::create_args",
            "wrap" => "lr::coroutine::wrap_source_args",
            "status" => "lr::coroutine::status_args",
            "close" => "lr::coroutine::close_args",
            "resume" => "lr::coroutine::resume_args",
            "yield" => "lr::coroutine::yield_values",
            "isyieldable" => {
                let code = rir::call("lr::coroutine::isyieldable", vec![]);
                return (
                    rir::block(pre, code),
                    vec![(self.ck.info.expr[&e.id].ty, false)],
                );
            }
            _ => unreachable!("checker rejects unknown coroutine builtin"),
        };
        let arg = if matches!(name, "resume" | "yield") {
            argv
        } else {
            rir::borrow(argv)
        };
        let call = rir::at(rir::call(path, vec![arg]), &self.loc(e.span));
        let (code, outs) = if matches!(name, "resume" | "yield" | "close") {
            (rir::call("lr::coroutine::pack_values", vec![call]), vec![])
        } else {
            (call, vec![(self.ck.info.expr[&e.id].ty, false)])
        };
        (rir::block(pre, code), outs)
    }
}
