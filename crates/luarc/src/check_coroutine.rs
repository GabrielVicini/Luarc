//! Coroutine boundaries use dynamic values; ordinary source functions stay static.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::*;
use crate::check::*;
use crate::diag::Span;
use crate::resolve::{Builtin, Res, Resolution, SymId};
use crate::types::*;

#[derive(Default)]
pub struct CoroutineInfo {
    pub tails: HashMap<NodeId, Slot>,
    pub wrappers: HashSet<RetsId>,
    /// Values crossing the runtime boundary, validated after inference settles.
    pub values: Vec<(ETy, Span, bool)>,
}

#[derive(Default)]
struct Definitions {
    funcs: HashMap<SymId, Vec<NodeId>>,
    aliases: HashMap<SymId, Vec<SymId>>,
    bodies: HashMap<NodeId, FuncBody>,
}

impl Definitions {
    fn value(&mut self, sym: SymId, expr: &Expr, res: &Resolution) {
        match &expr.kind {
            ExprKind::Function(f) => {
                self.funcs.entry(sym).or_default().push(f.id);
            }
            ExprKind::Name(n) => {
                if let Some(Res::Local(s)) = res.res(n.id) {
                    self.aliases.entry(sym).or_default().push(s);
                }
            }
            ExprKind::Paren(e) | ExprKind::Cast(e, _) => self.value(sym, e, res),
            _ => {}
        }
    }
    fn mark(
        &self,
        e: &Expr,
        res: &Resolution,
        out: &mut HashSet<NodeId>,
        seen: &mut HashSet<SymId>,
    ) {
        match &e.kind {
            ExprKind::Function(f) => {
                out.insert(f.id);
            }
            ExprKind::Name(n) => {
                if let Some(Res::Local(s)) = res.res(n.id) {
                    self.mark_sym(s, out, seen);
                }
            }
            ExprKind::Paren(e) | ExprKind::Cast(e, _) => self.mark(e, res, out, seen),
            ExprKind::IfElse(_, a, b) | ExprKind::Binary(BinOp::And | BinOp::Or, a, b) => {
                self.mark(a, res, out, seen);
                self.mark(b, res, out, seen);
            }
            _ => {}
        }
    }
    fn mark_sym(&self, s: SymId, out: &mut HashSet<NodeId>, seen: &mut HashSet<SymId>) {
        if !seen.insert(s) {
            return;
        }
        if let Some(fs) = self.funcs.get(&s) {
            out.extend(fs);
        }
        if let Some(aliases) = self.aliases.get(&s) {
            for s in aliases {
                self.mark_sym(*s, out, seen);
            }
        }
    }
}

impl<'a> Checker<'a> {
    /// Identify runtime-entry functions before their parameter skeletons are made.
    pub(crate) fn prepare_coroutines(&mut self, units: &[ModuleUnit]) {
        let mut defs = Definitions::default();
        for u in units {
            walk_block(
                &u.module.body,
                true,
                &mut |s| match &s.kind {
                    StatKind::LocalFunction(n, f) => {
                        defs.funcs
                            .entry(self.res.decl(n.id))
                            .or_default()
                            .push(f.id);
                    }
                    StatKind::Local(ns, es) => {
                        for ((n, _), e) in ns.iter().zip(es) {
                            defs.value(self.res.decl(n.id), e, self.res);
                        }
                    }
                    StatKind::Assign(ns, es) => {
                        for (n, e) in ns.iter().zip(es) {
                            if let ExprKind::Name(n) = &n.kind {
                                if let Some(Res::Local(s)) = self.res.res(n.id) {
                                    defs.value(s, e, self.res);
                                }
                            }
                        }
                    }
                    StatKind::Function(e, f) => {
                        if let ExprKind::Name(n) = &e.kind {
                            if let Some(Res::Local(s)) = self.res.res(n.id) {
                                defs.funcs.entry(s).or_default().push(f.id);
                            }
                        }
                    }
                    _ => {}
                },
                &mut |_| {},
            );
            walk_block(
                &u.module.body,
                true,
                &mut |s| match &s.kind {
                    StatKind::LocalFunction(_, f) | StatKind::Function(_, f) => {
                        defs.bodies.insert(f.id, (**f).clone());
                    }
                    _ => {}
                },
                &mut |_| {},
            );
            walk_block(&u.module.body, true, &mut |_| {}, &mut |e| {
                if let ExprKind::Function(f) = &e.kind {
                    defs.bodies.insert(f.id, (**f).clone());
                }
            });
        }
        let mut marked = HashSet::new();
        for u in units {
            walk_block(&u.module.body, true, &mut |_| {}, &mut |e| {
                let ExprKind::Call(f, args) = &e.kind else {
                    return;
                };
                let Some((Builtin::CoroutineLib, Some(name))) = self.builtin_ref(f) else {
                    return;
                };
                let args = match name.as_str() {
                    "create" | "wrap" => &args[..args.len().min(1)],
                    "yield" | "resume" => args.as_slice(),
                    _ => return,
                };
                for arg in args {
                    defs.mark(arg, self.res, &mut marked, &mut HashSet::new());
                }
            });
        }
        loop {
            let before = marked.len();
            for id in marked.clone() {
                if let Some(f) = defs.bodies.get(&id) {
                    walk_block(
                        &f.body,
                        false,
                        &mut |s| {
                            if let StatKind::Return(es) = &s.kind {
                                for e in es {
                                    defs.mark(e, self.res, &mut marked, &mut HashSet::new());
                                }
                            }
                        },
                        &mut |_| {},
                    );
                }
            }
            if before == marked.len() {
                break;
            }
        }
        self.info.runtime_functions.extend(marked);
    }

    pub(crate) fn coroutine_call(
        &mut self,
        e: &Expr,
        name: &str,
        args: &[Expr],
        want: Option<usize>,
    ) -> Vec<ETy> {
        if !matches!(
            name,
            "create" | "wrap" | "yield" | "resume" | "status" | "isyieldable" | "close"
        ) {
            for a in args {
                self.expr(a);
            }
            self.error(e.span, format!("coroutine.{name} is unsupported (create, wrap, yield, resume, status, isyieldable, close are supported)"));
            let value = self.any_val();
            return vec![value; want.unwrap_or(1)];
        }
        let (values, tail) = self.pack_items(args);
        for (i, value) in values.iter().enumerate() {
            let span = args
                .get(i)
                .or_else(|| args.last())
                .map(|a| a.span)
                .unwrap_or(e.span);
            self.info.coroutines.values.push((
                *value,
                span,
                i == 0 && matches!(name, "create" | "wrap"),
            ));
        }
        if let Some(tail) = tail {
            self.info.coroutines.values.push((
                tail,
                args.last().map(|a| a.span).unwrap_or(e.span),
                values.is_empty() && matches!(name, "create" | "wrap"),
            ));
        }
        self.info
            .calls
            .insert(e.id, CallKind::Coroutine(name.into()));
        let out = match name {
            "yield" | "resume" | "close" => {
                let any = self.any_val();
                self.info.coroutines.tails.insert(
                    e.id,
                    Slot {
                        ty: any.ty,
                        null: any.null,
                    },
                );
                if let Some(n) = want {
                    let out = vec![any; n];
                    self.info.builtin_outs.insert(e.id, out.clone());
                    return out;
                }
                self.info.pack_calls.insert(e.id, any);
                return vec![];
            }
            "wrap" => {
                let any = self.any_val();
                let slot = Slot {
                    ty: any.ty,
                    null: any.null,
                };
                let rets = self.st.new_rets(RetsNode::Known(vec![]));
                self.st.rets_tail.insert(rets, slot);
                self.info.coroutines.wrappers.insert(rets);
                let ty = self.st.ty(TyNode::Func(Rc::new(FuncTy {
                    params: vec![],
                    rets,
                    vararg: Some(slot),
                })));
                vec![self.val(ty)]
            }
            "status" => vec![self.str_()],
            "isyieldable" => vec![self.bool_()],
            _ => vec![self.any_val()],
        };
        fit(self, out, want)
    }

    pub(crate) fn check_coroutine_boundaries(&mut self) {
        for (value, span, entry) in self.info.coroutines.values.clone() {
            // These bridges erase function ABIs themselves; still check every
            // exposed argument/result for runtime-table representation escapes.
            self.validate_runtime_manual_box(value.ty, span, true);
            if entry && self.is_any(value.ty) {
                self.error(span, "coroutine.create/wrap requires a statically known function value; opaque any functions are unsupported");
            } else if !self.coroutine_value_supported(value.ty, &mut HashSet::new()) {
                self.error(span, "coroutine values require supported dynamic representations; functions need any parameters and at most eight signature slots");
            }
        }
    }

    fn coroutine_value_supported(&self, ty: TyId, seen: &mut HashSet<TyId>) -> bool {
        let ty = self.st.root(ty);
        if !seen.insert(ty) {
            return true;
        }
        match self.st.node(ty) {
            TyNode::Var
            | TyNode::Any
            | TyNode::Num
            | TyNode::NumVar
            | TyNode::Bool
            | TyNode::Str
            | TyNode::Nil
            | TyNode::Table(_)
            | TyNode::Native(_) => true,
            TyNode::FalseOr(t) => self.coroutine_value_supported(*t, seen),
            TyNode::Pcall(s) => self.coroutine_value_supported(s.ty, seen),
            TyNode::Func(f) => {
                let count = f.params.len() + usize::from(f.vararg.is_some());
                if count > 8
                    || f.params.iter().any(|p| !self.is_any(p.ty))
                    || f.vararg.is_some_and(|p| !self.is_any(p.ty))
                {
                    return false;
                }
                let Some(rets) = self.st.rets_known(f.rets) else {
                    return false;
                };
                let tail = self.st.rets_tail(f.rets);
                rets.len() + usize::from(tail.is_some()) <= 8
                    && rets
                        .iter()
                        .all(|s| self.coroutine_value_supported(s.ty, seen))
                    && tail.is_none_or(|s| self.coroutine_value_supported(s.ty, seen))
            }
            _ => false,
        }
    }
}

fn fit(ck: &mut Checker, mut values: Vec<ETy>, want: Option<usize>) -> Vec<ETy> {
    if let Some(n) = want {
        values.truncate(n);
        while values.len() < n {
            values.push(ck.nil());
        }
    }
    values
}

fn walk_block(
    b: &Block,
    functions: bool,
    stat: &mut impl FnMut(&Stat),
    expr: &mut impl FnMut(&Expr),
) {
    for s in &b.stats {
        stat(s);
        match &s.kind {
            StatKind::Local(_, es) | StatKind::Return(es) => {
                for e in es {
                    walk_expr(e, functions, stat, expr);
                }
            }
            StatKind::Assign(a, b) => {
                for e in a.iter().chain(b) {
                    walk_expr(e, functions, stat, expr);
                }
            }
            StatKind::Compound(_, a, b) => {
                walk_expr(a, functions, stat, expr);
                walk_expr(b, functions, stat, expr);
            }
            StatKind::Call(e) => walk_expr(e, functions, stat, expr),
            StatKind::LocalFunction(_, f) => {
                if functions {
                    walk_block(&f.body, functions, stat, expr);
                }
            }
            StatKind::Function(e, f) => {
                walk_expr(e, functions, stat, expr);
                if functions {
                    walk_block(&f.body, functions, stat, expr);
                }
            }
            StatKind::Do(b) => walk_block(b, functions, stat, expr),
            StatKind::While(e, b) | StatKind::Repeat(b, e) => {
                walk_expr(e, functions, stat, expr);
                walk_block(b, functions, stat, expr);
            }
            StatKind::NumFor(_, a, b, c, body) => {
                for e in [Some(a), Some(b), c.as_ref()].into_iter().flatten() {
                    walk_expr(e, functions, stat, expr);
                }
                walk_block(body, functions, stat, expr);
            }
            StatKind::GenFor(_, es, b) => {
                for e in es {
                    walk_expr(e, functions, stat, expr);
                }
                walk_block(b, functions, stat, expr);
            }
            StatKind::If(arms, other) => {
                for (e, b) in arms {
                    walk_expr(e, functions, stat, expr);
                    walk_block(b, functions, stat, expr);
                }
                if let Some(b) = other {
                    walk_block(b, functions, stat, expr);
                }
            }
            _ => {}
        }
    }
}

fn walk_expr(
    e: &Expr,
    functions: bool,
    stat: &mut impl FnMut(&Stat),
    expr: &mut impl FnMut(&Expr),
) {
    expr(e);
    match &e.kind {
        ExprKind::Function(f) => {
            if functions {
                walk_block(&f.body, functions, stat, expr);
            }
        }
        ExprKind::Paren(e)
        | ExprKind::Cast(e, _)
        | ExprKind::Unary(_, e)
        | ExprKind::Field(e, _) => walk_expr(e, functions, stat, expr),
        ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) => {
            walk_expr(a, functions, stat, expr);
            walk_expr(b, functions, stat, expr);
        }
        ExprKind::Call(f, args) | ExprKind::Method(f, _, args) => {
            walk_expr(f, functions, stat, expr);
            for a in args {
                walk_expr(a, functions, stat, expr);
            }
        }
        ExprKind::IfElse(a, b, c) => {
            for e in [a, b, c] {
                walk_expr(e, functions, stat, expr);
            }
        }
        ExprKind::Table(items) => {
            for item in items {
                match item {
                    TableItem::Pos(e) | TableItem::Named(_, e) => {
                        walk_expr(e, functions, stat, expr)
                    }
                    TableItem::Keyed(a, b) => {
                        walk_expr(a, functions, stat, expr);
                        walk_expr(b, functions, stat, expr);
                    }
                }
            }
        }
        ExprKind::Interp(parts) => {
            for part in parts {
                if let InterpPart::Expr(e) = part {
                    walk_expr(e, functions, stat, expr);
                }
            }
        }
        _ => {}
    }
}
