//! The exact `integer` type: arithmetic typing (integer × integer or number ×
//! number, never silently mixed) and integral-literal defaulting.

use crate::ast::BinOp;
use crate::check::*;
use crate::diag::Span;
use crate::types::*;

/// Numeric class of a type during arithmetic checking.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum NumClass {
    Int,
    Num,
    /// An integral literal not yet decided.
    Lit,
    Unknown,
    Other,
}

impl<'a> Checker<'a> {
    pub(crate) fn num_class(&self, t: TyId) -> NumClass {
        match self.st.node(t) {
            TyNode::Int => NumClass::Int,
            TyNode::Num => NumClass::Num,
            TyNode::NumVar => NumClass::Lit,
            TyNode::NPrim(p) if is_int_prim(&p) => NumClass::Int,
            TyNode::NPrim(p) if !matches!(p.as_ref(), "bool" | "char" | "str") => NumClass::Num,
            TyNode::Var => NumClass::Unknown,
            _ => NumClass::Other,
        }
    }

    /// `x op y` (or `-x` when `op` is None).
    pub(crate) fn attempt_arith(&mut self, op: Option<BinOp>, x: ETy, y: ETy, r: TyId, span: Span) -> bool {
        let (cx, cy) = (self.num_class(x.ty), self.num_class(y.ty));
        let float_result = matches!(op, Some(BinOp::Div | BinOp::Pow));
        for (c, v) in [(cx, x), (cy, y)] {
            if c == NumClass::Other {
                let s = self.show(v.ty);
                self.error(span, format!("type mismatch: attempt to perform arithmetic on a {s} value (number or integer expected)"));
                return true;
            }
        }
        match (cx, cy) {
            (NumClass::Int, NumClass::Num) | (NumClass::Num, NumClass::Int) => {
                self.error(
                    span,
                    "cannot mix integer and number operands (integers are exact native values); convert with tonumber(i) or math.tointeger(x)",
                );
                true
            }
            (NumClass::Int, _) | (_, NumClass::Int) => {
                let i = self.prim(TyNode::Int);
                self.unify(x.ty, i, span);
                self.unify(y.ty, i, span);
                let rt = if float_result { self.prim(TyNode::Num) } else { i };
                self.unify(r, rt, span);
                true
            }
            (NumClass::Num, _) | (_, NumClass::Num) => {
                // (number with a literal or unknown operand)
                let n = self.prim(TyNode::Num);
                self.unify(x.ty, n, span);
                self.unify(y.ty, n, span);
                self.unify(r, n, span);
                true
            }
            (NumClass::Lit, _) | (_, NumClass::Lit) => {
                // literal arithmetic stays undecided: `1 + 2` is an integer where one is needed
                self.unify(x.ty, y.ty, span);
                if float_result {
                    let n = self.prim(TyNode::Num);
                    self.unify(x.ty, n, span);
                    self.unify(r, n, span);
                } else {
                    self.unify(r, x.ty, span);
                }
                true
            }
            _ => {
                if self.defaults_round && self.literal_defaults {
                    let n = self.prim(TyNode::Num);
                    self.unify(x.ty, n, span);
                    self.unify(y.ty, n, span);
                    self.unify(r, n, span);
                    true
                } else {
                    false
                }
            }
        }
    }
}
