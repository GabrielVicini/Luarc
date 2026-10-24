//! Lowering of the dynamic type `any`: boxing into `lr::Value`, casts,
//! dynamic operators and `and`/`or` on dynamic operands. Declared as a child module
//! of `codegen` (it extends `Gen` and uses its private helpers).

use super::*;
use crate::check_dynamic::{CastKind, DynBin, Tag};

impl<'a> Gen<'a> {
    /// A value that flows into `any`: converted to `lr::Value` once evaluated.
    pub(super) fn box_value(&mut self, v: Val) -> Val {
        Val { code: rir::call("lr::dynamic::to_value", vec![v.code]), opt: false }
    }

    /// An `any` value stored in an optional slot reads as `Value::Nil` when absent.
    pub(super) fn any_present(&mut self, v: Val) -> Val {
        if v.opt {
            Val { code: rir::method(v.code, "unwrap_or", vec![rir::atom_e("lr::Value::Nil")]), opt: false }
        } else {
            v
        }
    }

    /// A read of an `any` local inside a `type(x) == "..."` branch: the tag is proven,
    /// the unboxing cannot fail.
    pub(super) fn unboxed_read(&mut self, e: &Expr, tag: Tag) -> Option<Val> {
        let ExprKind::Name(n) = &e.kind else { return None };
        let Some(Res::Local(s)) = self.res.res(n.id) else { return None };
        let slot_opt = self.sym_opt(s);
        let read = self.read_sym(s);
        let v = self.any_present(Val { code: read, opt: slot_opt });
        let m = match tag {
            Tag::Number => "as_num",
            Tag::String => "as_str",
            Tag::Boolean => "as_bool",
            Tag::Table => "as_table",
        };
        Some(Val { code: rir::at(rir::method(v.code, m, vec![]), &self.loc(e.span)), opt: false })
    }

    pub(super) fn is_any_ty(&self, t: TyId) -> bool {
        matches!(self.node(t), TyNode::Any)
    }

    /// `e :: T`.
    pub(super) fn cast_code(&mut self, e: &Expr, inner: &Expr, opt: bool) -> RExpr {
        match self.ck.info.dynamic.casts.get(&e.id).copied().unwrap_or(CastKind::Pass) {
            CastKind::Pass => {
                let v = self.expr(inner);
                self.coerce(v, opt, inner.span, "attempt to use a nil value")
            }
            CastKind::FromAny { opt: accepts_nil } => {
                let v = self.expr_nn(inner, "attempt to use a nil value");
                let ty = self.ck.info.expr[&e.id].ty;
                let target = RType::Named(self.rust_ty(ty));
                let name = self.ck.show(ty);
                let f = if accepts_nil { "lr::dynamic::cast_opt" } else { "lr::dynamic::cast" };
                let call = rir::call_generic(f, &target, vec![rir::borrow(v), rir::atom_e(rust_str_lit(&name))]);
                rir::at(call, &self.loc(e.span))
            }
        }
    }

    /// A binary operator with an `any` operand (both operands are `lr::Value`s).
    pub(super) fn dyn_binary_code(&mut self, e: &Expr, kind: DynBin, a: &Expr, b: &Expr) -> RExpr {
        let loc = self.loc(e.span);
        let what = "attempt to use a nil value";
        let x = self.expr_nn(a, what);
        let y = self.expr_nn(b, what);
        match kind {
            DynBin::Arith(op) => {
                let name = match op {
                    BinOp::Add => "Add",
                    BinOp::Sub => "Sub",
                    BinOp::Mul => "Mul",
                    BinOp::Div => "Div",
                    BinOp::IDiv => "IDiv",
                    BinOp::Mod => "Mod",
                    _ => "Pow",
                };
                let call = rir::call("lr::dynamic::arith", vec![rir::atom_e(format!("lr::dynamic::Arith::{name}")), rir::borrow(x), rir::borrow(y)]);
                rir::at(call, &loc)
            }
            DynBin::Concat => {
                let function = if self.ck.info.runtime_tables.binary.contains(&e.id) { "lr::dynamic::concat_value" } else { "lr::dynamic::concat" };
                rir::at(rir::call(function, vec![rir::borrow(x), rir::borrow(y)]), &loc)
            }
            DynBin::Compare(op) => {
                // `a > b` is `b < a` (as in Luau, including the operand order of its error)
                let (f, swap) = match op {
                    BinOp::Lt => ("lt", false),
                    BinOp::Le => ("le", false),
                    BinOp::Gt => ("lt", true),
                    _ => ("le", true),
                };
                let (l, r) = (self.fresh("l"), self.fresh("r"));
                let (p, q) = if swap { (&r, &l) } else { (&l, &r) };
                let call = rir::call(format!("lr::dynamic::{f}"), vec![rir::borrow(rir::atom_e(p.clone())), rir::borrow(rir::atom_e(q.clone()))]);
                rir::block(vec![rir::let_(l.clone(), x), rir::let_(r.clone(), y)], rir::at(call, &loc))
            }
            DynBin::Eq(eq) => {
                let c = if self.ck.info.runtime_tables.binary.contains(&e.id) {
                    rir::at(rir::call("lr::dynamic::eq", vec![rir::borrow(x), rir::borrow(y)]), &loc)
                } else { rir::call("lr::show::eq", vec![rir::borrow(x), rir::borrow(y)]) };
                if eq {
                    c
                } else {
                    rir::unary("!", c)
                }
            }
        }
    }

    /// `and`/`or` decided at compile time, or with an `any` operand.
    pub(super) fn dyn_logic_code(&mut self, kind: LogicKind, and: bool, a: &Expr, b: &Expr, opt: bool) -> RExpr {
        match kind {
            // `false and x`, `true or x`, `0 or x`: the right operand never runs
            // (the dead operand is still generated, under `if false`, so the names it
            // reads stay used and the generated code stays warning free)
            LogicKind::LeftOnly => {
                let l = self.expr_to(a, opt);
                let dead = self.expr(b);
                let x = self.fresh("l");
                let skipped = RStmt::If(vec![(rir::atom_e("false"), vec![rir::let_("_", dead.code)])], None);
                rir::block(vec![rir::let_(x.clone(), l), skipped], rir::atom_e(x))
            }
            // `true and x`, `false or x`: the left operand is evaluated and dropped
            LogicKind::RightOnly => {
                let l = self.expr(a);
                let r = self.expr_to(b, opt);
                rir::block(vec![rir::let_("_", l.code)], r)
            }
            _ => {
                let what = "attempt to use a nil value";
                let x = self.fresh("a");
                let l = self.expr_nn(a, what);
                let r = self.expr_nn(b, what);
                let xv = || rir::atom_e(x.clone());
                let truthy = rir::call("lr::show::truthy", vec![rir::borrow(xv())]);
                let pick = if and { rir::if_(truthy, r, xv()) } else { rir::if_(truthy, xv(), r) };
                rir::block(vec![rir::let_(x.clone(), l)], pick)
            }
        }
    }
}
