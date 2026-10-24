//! Table library calls for selectively promoted runtime tables.
use crate::ast::*;
use crate::check::*;
use crate::diag::Span;
use crate::types::*;

impl<'a> Checker<'a> {
    pub(crate) fn table_library_sig(&mut self, b: BuiltinFn, values: &[ETy], spans: &[Span], args: &[Expr], span: Span) -> Option<Vec<ETy>> {
        use BuiltinFn::*;
        let name = match b {
            TFreeze => "freeze", TIsFrozen => "isfrozen", TMove => "move",
            TInsert if values.first().is_some_and(|v| self.runtime_type(v.ty)) => "insert",
            TConcat if values.first().is_some_and(|v| self.runtime_type(v.ty)) => "concat",
            _ => return None,
        };
        let minimum = if b == TMove { 4 } else if b == TInsert { 2 } else { 1 };
        let maximum = if b == TInsert { 3 } else { usize::MAX };
        if !self.arity(span, &format!("table.{name}"), values, minimum, maximum) {
            return Some(match b { TInsert => vec![], TIsFrozen => vec![self.bool_()], TConcat => vec![self.str_()], _ => vec![self.runtime_value(span)] });
        }
        if !self.runtime_type(values[0].ty) {
            self.error(spans[0], format!("table.{name} requires a runtime table (its producer must use the runtime representation)"));
        }
        self.need(values[0], spans[0], &format!("invalid argument #1 to '{name}' (table expected, got nil)"));
        if b == TMove {
            if let Some(destination) = values.get(4) {
                if !matches!(self.st.node(destination.ty), TyNode::Nil) && !self.runtime_type(destination.ty) {
                    self.error(spans[4], "table.move destination requires a runtime table (its producer must use the runtime representation)");
                }
            }
            let destination = values.get(4).filter(|value| !matches!(self.st.node(value.ty), TyNode::Nil)).copied().unwrap_or(values[0]);
            if let TyNode::Table(table) = self.st.node(destination.ty).clone() {
                if let Some(element) = self.st.tab(table).elem.filter(|slot| self.runtime_type(slot.ty)) {
                    let source_element = match self.st.node(values[0].ty).clone() {
                        TyNode::Table(source) => self.st.tab(source).elem,
                        _ => None,
                    };
                    if let Some(source) = source_element.filter(|slot| self.runtime_type(slot.ty)) {
                        self.unify(source.ty, element.ty, span);
                    } else {
                        self.error(span, "table.move into a known table-element array requires a source with known runtime-table elements");
                    }
                }
            }
        }
        // Runtime boundaries perform Luau's argument coercions and error checks.
        for (index, value) in values.iter().enumerate().skip(1) {
            self.boxable(value.ty, spans[index]);
            if b == TInsert && index + 1 == values.len() {
                if args.len() == values.len() {
                    self.runtime_box(&args[index], *value);
                } else if matches!(self.st.node(value.ty), TyNode::Func(_)) {
                    self.error(spans[index], "inserting an expanded function result into a runtime table is not supported yet; bind it to a local first");
                }
            }
        }
        if b == TInsert {
            let raw_position = values.len() == 3 && args.len() == 3 && matches!(args[1].kind, ExprKind::Number(position) if position <= 0.0);
            if !raw_position { self.check_runtime_length(values[0], span, false); }
            if let TyNode::Table(table) = self.st.node(values[0].ty).clone() {
                if let Some(element) = self.st.tab(table).elem.filter(|slot| self.runtime_type(slot.ty)) {
                    let value = *values.last().unwrap();
                    if !self.runtime_type(value.ty) && !matches!(self.st.node(value.ty), TyNode::Nil) {
                        self.error(*spans.last().unwrap(), "table.insert into a known table-element array requires a runtime-table value");
                    } else { self.flow(value, element, *spans.last().unwrap()); }
                }
            }
        }
        if b == TConcat && (values.len() < 4 || values.get(3).is_some_and(|v| self.st.is_null(v.null) || matches!(self.st.node(v.ty), TyNode::Nil))) {
            self.check_runtime_length(values[0], span, false);
        }
        Some(match b {
            TFreeze => vec![self.val(values[0].ty)],
            TIsFrozen => vec![self.bool_()],
            // Source and destination may have different known record fields.
            TMove => vec![self.runtime_value(span)],
            TConcat => vec![self.str_()],
            TInsert => vec![],
            _ => unreachable!(),
        })
    }
}
