//! First-class builtins: `local log = print`, `fx.for_each_word(s, print)`.
//!
//! * A local bound once to a builtin (`local log = print`, `local insert =
//!   table.insert`) and never reassigned is an **alias**: every call through it is
//!   the builtin call itself, so variadic builtins keep their variadic behaviour
//!   (`log("a")` and `log("a", 1)` both work).
//! * Any other use of a builtin as a value (passed to a function, stored, returned)
//!   is a **function value** with one fixed signature, taken from where the value
//!   flows (a callback parameter, an annotation, its calls). The signature is
//!   validated against what the builtin accepts.

use crate::ast::*;
use crate::check::*;
use crate::diag::Span;
use crate::resolve::{Builtin, Res, SymId};
use crate::types::*;

/// A builtin named by an expression: `print`, `string.upper`.
pub type BuiltinRef = (Builtin, Option<String>);

impl<'a> Checker<'a> {
    /// The builtin an expression names directly (not a call).
    pub(crate) fn builtin_ref(&self, e: &Expr) -> Option<BuiltinRef> {
        match &e.kind {
            ExprKind::Name(n) => match self.res.res(n.id) {
                Some(Res::Builtin(b))
                    if !matches!(b, Builtin::Table | Builtin::StringLib | Builtin::Bit32 | Builtin::Math | Builtin::Arg | Builtin::Require | Builtin::TaskLib | Builtin::CoroutineLib | Builtin::Await) =>
                {
                    Some((b, None))
                }
                Some(Res::Local(s)) => self.info.builtin_aliases.get(&s).cloned(),
                _ => None,
            },
            ExprKind::Field(lib, f) => match is_lib(lib, self.res) {
                Some(b @ (Builtin::Table | Builtin::StringLib | Builtin::Bit32 | Builtin::Math | Builtin::CoroutineLib)) => Some((b, Some(f.text.clone()))),
                _ => None,
            },
            _ => None,
        }
    }

    /// Finds `local x = <builtin>` declarations whose local is never reassigned,
    /// and locals never reassigned after `local p = "<literal>"` (their value is
    /// known: a pattern held in one has known captures).
    pub(crate) fn find_builtin_aliases(&mut self, b: &Block) {
        for s in &b.stats {
            if let StatKind::Local(names, exprs) = &s.kind {
                for ((name, _), x) in names.iter().zip(exprs) {
                    if let ExprKind::Str(lit) = &x.kind {
                        let sym: SymId = self.res.decl(name.id);
                        if !self.res.sym(sym).assigned {
                            self.info.const_strs.insert(sym, lit.clone());
                        }
                    }
                }
            }
            match &s.kind {
                StatKind::Local(names, exprs) if names.len() == 1 && exprs.len() == 1 && names[0].1.is_none() => {
                    if let Some(r) = self.builtin_ref(&exprs[0]) {
                        let sym: SymId = self.res.decl(names[0].0.id);
                        if !self.res.sym(sym).assigned {
                            self.info.builtin_aliases.insert(sym, r);
                            self.info.alias_decls.insert(s.id);
                        }
                    }
                }
                _ => {}
            }
            for_each_block(s, &mut |blk| self.find_builtin_aliases(blk));
        }
    }

    /// A builtin used as a value: a function value whose signature is decided by
    /// its uses.
    pub(crate) fn builtin_value(&mut self, e: &Expr, r: BuiltinRef, span: Span) -> ETy {
        let ty = self.st.var();
        // Static class permissions require a direct call, never an erased function value.
        if r.0 == Builtin::SetMetatable {
            self.error(span, "'setmetatable' cannot be used as a function value (call it directly)");
            return self.val(ty);
        }
        if r.0 == Builtin::CoroutineLib {
            self.error(span, "coroutine builtins require a direct call or an immutable unannotated local alias");
            return self.val(ty);
        }
        self.info.builtin_values.insert(e.id, r.clone());
        self.try_or_defer(Op::BuiltinValue { r, ty, span });
        self.val(ty)
    }

    pub(crate) fn attempt_builtin_value(&mut self, r: &BuiltinRef, ty: TyId, span: Span) -> bool {
        let name = match &r.1 {
            Some(f) => format!("{}.{f}", lib_name(r.0)),
            None => format!("{:?}", r.0).to_lowercase(),
        };
        let f = match self.st.node(ty).clone() {
            TyNode::Var => return false,
            TyNode::Func(f) => f,
            _ => {
                let s = self.show(ty);
                self.error(span, format!("builtin '{name}' is a function, used here as a {s} value"));
                return true;
            }
        };
        let n = f.params.len();
        let num = self.prim(TyNode::Num);
        let st = self.prim(TyNode::Str);
        // (parameter types, results) the builtin takes in this shape
        let sig: Result<(Vec<Option<TyId>>, Vec<(TyId, bool)>), String> = match (r.0, r.1.as_deref()) {
            (Builtin::Print, None) => Ok((vec![None; n], vec![])),
            (Builtin::ToString, None) if n == 1 => Ok((vec![None], vec![(st, false)])),
            (Builtin::Type, None) if n == 1 => Ok((vec![None], vec![(st, false)])),
            (Builtin::Error, None) if n == 1 => Ok((vec![None], vec![])),
            (Builtin::ToNumber, None) if n == 1 => Ok((vec![Some(st)], vec![(num, true)])),
            (Builtin::StringLib, Some("upper" | "lower")) if n == 1 => Ok((vec![Some(st)], vec![(st, false)])),
            (Builtin::StringLib, Some("len")) if n == 1 => Ok((vec![Some(st)], vec![(num, false)])),
            (Builtin::Math, Some("floor" | "ceil" | "abs" | "sqrt")) if n == 1 => Ok((vec![Some(num)], vec![(num, false)])),
            (Builtin::Math, Some("min" | "max")) if n >= 1 => Ok((vec![Some(num); n], vec![(num, false)])),
            (Builtin::Table, Some("insert")) if n == 2 => {
                let (tt, tab) = self.new_table_var(span);
                self.ensure_kind(tab, TKind::Array, span);
                let el = self.elem_slot(tab);
                self.unify(f.params[0].ty, tt, span);
                Ok((vec![Some(tt), Some(el.ty)], vec![]))
            }
            (Builtin::ToString | Builtin::Type | Builtin::Error | Builtin::ToNumber, None) => Err(format!("'{name}' takes one argument, the expected function takes {n}")),
            (Builtin::Pcall | Builtin::Assert | Builtin::CollectGarbage | Builtin::Ipairs | Builtin::Pairs, None) => {
                Err(format!("'{name}' cannot be used as a function value (call it directly)"))
            }
            _ => Err(format!("'{name}' cannot be used as a function value with {n} parameter(s) in this version")),
        };
        let (ps, rets) = match sig {
            Ok(s) => s,
            Err(m) => {
                self.error(span, m);
                return true;
            }
        };
        for (p, want) in f.params.iter().zip(ps) {
            if let Some(w) = want {
                self.unify(p.ty, w, span);
                if self.st.is_null(p.null) {
                    self.error(span, format!("'{name}' does not accept nil arguments"));
                }
            }
        }
        let known: Vec<Slot> = rets
            .iter()
            .map(|(t, opt)| if *opt { self.st.optional_slot(*t, span) } else { self.st.fixed_slot(*t, span, "builtin result") })
            .collect();
        let rk = self.st.new_rets(RetsNode::Known(known));
        self.unify_rets(f.rets, rk, span);
        true
    }
}

fn lib_name(b: Builtin) -> &'static str {
    match b {
        Builtin::Table => "table",
        Builtin::Bit32 => "bit32",
        Builtin::StringLib => "string",
        Builtin::Math => "math",
        Builtin::CoroutineLib => "coroutine",
        _ => "?",
    }
}

/// Calls `f` on every block directly nested in statement `s`.
fn for_each_block(s: &Stat, f: &mut dyn FnMut(&Block)) {
    match &s.kind {
        StatKind::Do(b) | StatKind::While(_, b) | StatKind::Repeat(b, _) => f(b),
        StatKind::If(arms, els) => {
            for (_, b) in arms {
                f(b);
            }
            if let Some(b) = els {
                f(b);
            }
        }
        StatKind::NumFor(_, _, _, _, b) | StatKind::GenFor(_, _, b) => f(b),
        StatKind::LocalFunction(_, fb) | StatKind::Function(_, fb) => f(&fb.body),
        _ => {}
    }
}
