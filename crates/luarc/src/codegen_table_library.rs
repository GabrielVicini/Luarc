//! Table library lowering for runtime tables and static arrays.
use super::*;

impl<'a> Gen<'a> {
    pub(super) fn runtime_table_library(&mut self, e: &Expr, builtin: BuiltinFn, args: &[Arg]) -> Option<(RExpr, Vec<(TyId, bool)>)> {
        use BuiltinFn::*;
        let name = match builtin {
            TFreeze => "freeze", TIsFrozen => "is_frozen", TMove => "move_",
            TInsert if args.first().is_some_and(|v| self.ck.runtime_type(self.arg_ety(v).ty)) => "insert",
            TConcat if args.first().is_some_and(|v| self.ck.runtime_type(self.arg_ety(v).ty)) => "concat",
            _ => return None,
        };
        let mut pre = Vec::new();
        let mut values = Vec::new();
        for argument in args {
            let value = self.arg_val(argument);
            let value = self.box_value(value);
            let temporary = self.fresh("tablearg");
            pre.push(rir::let_(temporary.clone(), value.code));
            values.push(rir::atom_e(temporary));
        }
        let call = rir::call(format!("lr::table_library::{name}"), vec![rir::borrow(RExpr::Array(values))]);
        let code = rir::block(pre, rir::at(call, &self.loc(e.span)));
        let outputs = self.ck.info.builtin_outs.get(&e.id).into_iter().flatten().map(|v| (v.ty, false)).collect();
        Some((code, outputs))
    }
}
