//! Protected calls whose handler can return any source value.
use crate::ast::*;
use crate::check::*;
use crate::types::*;

impl<'a> Checker<'a> {
    pub(crate) fn xpcall_call(&mut self, e: &Expr, args: &[Expr], want: Option<usize>) -> Vec<ETy> {
        if args.len() < 2 {
            self.error(e.span, "xpcall expects at least two arguments");
            return vec![self.bool_(), self.any_val()];
        }
        let f = self.expr(&args[0]);
        let h = self.expr(&args[1]);
        self.need(f, args[0].span, "attempt to call a nil value");
        self.need(h, args[1].span, "attempt to call a nil value");
        let (vals, spans) = self.args_values(&args[2..]);
        let mut all = vec![f, h];
        all.extend_from_slice(&vals);
        self.note_multi_tail(e.id, args, &all);
        let count = if let TyNode::Func(ft) = self.st.node(f.ty).clone() {
            for (i, p) in ft.params.iter().enumerate() {
                if let Some(v) = vals.get(i) {
                    if self.is_any(p.ty) {
                        self.boxable(v.ty, spans[i]);
                        self.info.xpcall_boxes.push((v.ty, spans[i]));
                    } else {
                        self.flow_node(args.get(i + 2).map(|a| a.id), *v, *p, spans[i]);
                    }
                } else if !self.is_any(p.ty) { self.st.force(p.null, e.span); }
            }
            if let Some(va) = ft.vararg {
                for (i, v) in vals.iter().enumerate().skip(ft.params.len()) {
                    if self.is_any(va.ty) {
                        self.boxable(v.ty, spans[i]);
                        self.info.xpcall_boxes.push((v.ty, spans[i]));
                    } else {
                        self.flow_node(args.get(i + 2).map(|a| a.id), *v, va, spans[i]);
                    }
                }
            }
            if self.st.rets_tail(ft.rets).is_some() {
                self.error(e.span, "xpcall of a function returning a variable number of values is not supported yet");
            }
            match self.st.rets_known(ft.rets) {
                Some(r) => {
                    let r = r.clone();
                    for s in &r {
                        self.boxable(s.ty, e.span);
                        self.info.xpcall_boxes.push((s.ty, e.span));
                    }
                    r.len()
                },
                None => { self.error(args[0].span, "cannot determine xpcall function results; annotate the return type"); 0 }
            }
        } else {
            self.error(args[0].span, "xpcall expects a function as its first argument"); 0
        };
        if let TyNode::Func(ft) = self.st.node(h.ty).clone() {
            if let Some(p) = ft.params.first() {
                let err = self.str_();
                if !self.is_any(p.ty) { self.flow(err, *p, args[1].span); }
            }
            for p in ft.params.iter().skip(1) { if !self.is_any(p.ty) { self.st.force(p.null, e.span); } }
            if ft.params.is_empty() {
                if let Some(va) = ft.vararg {
                    let err = self.str_();
                    if !self.is_any(va.ty) { self.flow(err, va, args[1].span); }
                }
            }
            if self.st.rets_tail(ft.rets).is_some() {
                self.error(e.span, "xpcall of a handler returning a variable number of values is not supported yet");
            }
            if let Some(r) = self.st.rets_known(ft.rets).cloned() {
                if let Some(s) = r.first() {
                    self.boxable(s.ty, e.span);
                    self.info.xpcall_boxes.push((s.ty, e.span));
                }
            }
            if self.st.rets_known(ft.rets).is_none() {
                self.error(args[1].span, "cannot determine xpcall handler results; annotate the return type");
            }
        } else { self.error(args[1].span, "xpcall expects a function as its second argument"); }
        self.info.calls.insert(e.id, CallKind::Builtin(BuiltinFn::Xpcall));
        if want.is_none() {
            // Success has exactly the body's results; failure has one handler
            // result regardless of the body's normal return count.
            let element = self.any_val();
            self.info.pack_calls.insert(e.id, element);
            self.info.builtin_outs.insert(e.id, vec![]);
            return vec![];
        }
        let mut out = vec![self.bool_()];
        for _ in 0..count.max(1) { out.push(self.any_val()); }
        self.info.builtin_outs.insert(e.id, out.clone());
        if let Some(n) = want {
            out.truncate(n);
            while out.len() < n { out.push(self.nil()); }
        }
        out
    }

    pub(crate) fn validate_xpcall_boxes(&mut self) {
        if !self.info.runtime_tables.enabled { return; }
        for (ty, span) in self.info.xpcall_boxes.clone() {
            let first_error = self.errors.len();
            let erased_function = matches!(self.st.node(ty), TyNode::Func(_));
            self.validate_runtime_manual_box(ty, span, erased_function);
            if erased_function { self.validate_runtime_function(ty, &mut Default::default()); }
            for error in &mut self.errors[first_error..] {
                if error.span == crate::diag::Span::default() { error.span = span; }
            }
        }
    }
}
