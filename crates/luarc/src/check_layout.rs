//! Luau 0.743 constructor allocation hints observed by `next`.
//! The empty-literal prediction follows Compiler/src/TableShape.cpp: local
//! identity, source preorder, sequential constant indices and small 1..k loops.
use std::collections::{HashMap, HashSet};
use crate::ast::*;
use crate::resolve::{Builtin, Res, Resolution, SymId};
use crate::diag::Span;

#[derive(Default)]
struct Predictor<'a> {
    res: Option<&'a Resolution>,
    optimized_layouts: bool,
    tables: HashMap<SymId, NodeId>,
    constants: HashMap<SymId, Constant>,
    escaped: HashSet<SymId>,
    loops: HashMap<SymId, usize>,
    fields: HashSet<(NodeId, String)>,
    layouts: HashMap<NodeId, (usize, usize)>,
    strings: HashMap<NodeId, Vec<u8>>,
    spans: HashMap<NodeId, Span>,
}

pub struct Analysis {
    pub layouts: HashMap<NodeId, (usize, usize)>,
    pub strings: HashMap<NodeId, Vec<u8>>,
    pub unproven: Vec<(NodeId, Span)>,
}

fn analyze_mode<'a>(block: &Block, res: &'a Resolution, optimized_layouts: bool) -> Predictor<'a> {
    let mut p = Predictor { res: Some(res), optimized_layouts, ..Predictor::default() };
    p.block(block);
    p.tables.clear(); p.loops.clear(); p.fields.clear(); p.layouts.clear(); p.constants.clear(); p.strings.clear(); p.spans.clear();
    p.block(block);
    p
}

pub fn analyze(block: &Block, res: &Resolution, options: ModuleOptions) -> Analysis {
    // Luau Compiler.cpp gates both constant-key promotion and TableShape at O1.
    let p = analyze_mode(block, res, options.oracle_optimization != Some(0));
    let mut unproven = Vec::new();
    if options.oracle_optimization.is_none() {
        let unoptimized = analyze_mode(block, res, false);
        for (&node, shape) in &p.layouts {
            if unoptimized.layouts.get(&node) != Some(shape) {
                if let Some(&span) = p.spans.get(&node) { unproven.push((node, span)); }
            }
        }
    }
    Analysis { layouts: p.layouts, strings: p.strings, unproven }
}

#[derive(Clone)]
enum Constant { Nil, Bool(bool), Number(f64), String(Vec<u8>), Record(NodeId, HashMap<std::string::String, Constant>) }
impl Constant {
    fn truthy(&self) -> bool { !matches!(self, Self::Nil | Self::Bool(false)) }
}
impl Predictor<'_> {
    fn constant(&self, expr: &Expr) -> Option<Constant> {
        use Constant::*;
        Some(match &expr.kind {
            ExprKind::Nil => Nil,
            ExprKind::Bool(v) => Bool(*v),
            ExprKind::Number(v) => Number(*v),
            ExprKind::Str(v) => String(v.clone()),
            ExprKind::Name(_) => self.constants.get(&self.local(expr)?).cloned()?,
            ExprKind::Paren(v) | ExprKind::Cast(v,_) => self.constant(v)?,
            ExprKind::Field(obj,name) => { let Record(_, fields) = self.constant(obj)? else { return None }; fields.get(&name.text).cloned()? }
            ExprKind::Index(obj,index) => {
                let Record(_, fields) = self.constant(obj)? else { return None };
                let String(key) = self.constant(index)? else { return None };
                fields.get(std::str::from_utf8(&key).ok()?).cloned()?
            }
            ExprKind::Table(items) => {
                let mut fields = HashMap::new();
                for item in items {
                    let (key, value) = match item {
                        TableItem::Named(name, value) => (name.text.clone(), self.constant(value)?),
                        TableItem::Keyed(key,value) => {
                            let String(key) = self.constant(key)? else { return None };
                            (std::string::String::from_utf8(key).ok()?, self.constant(value)?)
                        }
                        _ => return None,
                    };
                    if key.is_empty() || matches!(value, Record(..)) { return None; }
                    fields.insert(key, value);
                }
                if fields.len() != items.len() { return None; }
                Record(expr.id, fields)
            }
            ExprKind::Interp(parts) => {
                let mut out = Vec::new();
                for part in parts { match part {
                    InterpPart::Lit(bytes) => out.extend_from_slice(bytes),
                    InterpPart::Expr(expr) => { let String(bytes) = self.constant(expr)? else { return None }; out.extend_from_slice(&bytes); }
                } }
                if out.len() > 4096 { return None; }
                String(out)
            }
            ExprKind::Unary(UnOp::Not,v) => Bool(!self.constant(v)?.truthy()),
            ExprKind::Unary(UnOp::Neg,v) => { let Number(n) = self.constant(v)? else { return None }; Number(-n) }
            ExprKind::Unary(UnOp::Len,v) => { let String(s) = self.constant(v)? else { return None }; Number(s.len() as f64) }
            ExprKind::IfElse(c,a,b) => self.constant(if self.constant(c)?.truthy() { a } else { b })?,
            ExprKind::Binary(op,a,b) => {
                let a = self.constant(a)?;
                if *op == BinOp::And { return if a.truthy() { self.constant(b) } else { Some(a) }; }
                if *op == BinOp::Or { return if a.truthy() { Some(a) } else { self.constant(b) }; }
                let b = self.constant(b)?;
                match (&a,&b) {
                    (Number(x),Number(y)) => match op {
                        BinOp::Add => Number(x+y), BinOp::Sub => Number(x-y), BinOp::Mul => Number(x*y),
                        BinOp::Div => Number(x/y), BinOp::IDiv => Number((x/y).floor()),
                        BinOp::Mod => Number(x - (x/y).floor()*y), BinOp::Pow => Number(x.powf(*y)),
                        BinOp::Eq => Bool(x==y), BinOp::Ne => Bool(x!=y),
                        BinOp::Lt => Bool(x<y), BinOp::Le => Bool(x<=y), BinOp::Gt => Bool(x>y), BinOp::Ge => Bool(x>=y),
                        _ => return None,
                    },
                    (String(x),String(y)) => match op {
                        BinOp::Concat if x.len() + y.len() <= 4096 => { let mut out=x.clone(); out.extend_from_slice(y); String(out) }
                        BinOp::Eq => Bool(x==y), BinOp::Ne => Bool(x!=y),
                        _ => return None,
                    },
                    (Record(x,_),Record(y,_)) => match op { BinOp::Eq => Bool(x==y), BinOp::Ne => Bool(x!=y), _ => return None },
                    (Nil,Nil) | (Bool(false),Bool(false)) | (Bool(true),Bool(true)) => match op { BinOp::Eq => Bool(true), BinOp::Ne => Bool(false), _ => return None },
                    _ => match op { BinOp::Eq => Bool(false), BinOp::Ne => Bool(true), _ => return None },
                }
            }
            _ => return None,
        })
    }
    fn local(&self, expr: &Expr) -> Option<SymId> {
        let ExprKind::Name(name) = &expr.kind else { return None };
        match self.res.unwrap().res(name.id) { Some(Res::Local(sym)) => Some(sym), _ => None }
    }
    fn empty_literal(&self, expr: &Expr) -> Option<NodeId> {
        if !self.optimized_layouts { return None; }
        match &expr.kind {
            ExprKind::Table(items) if items.is_empty() => Some(expr.id),
            ExprKind::Call(func, args) if args.len() == 2 => {
                if let ExprKind::Name(name) = &func.kind {
                    if matches!(self.res.unwrap().res(name.id), Some(Res::Builtin(Builtin::SetMetatable))) {
                        if matches!(&args[0].kind, ExprKind::Table(items) if items.is_empty()) { return Some(args[0].id); }
                    }
                }
                None
            }
            _ => None,
        }
    }
    fn escape(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Name(_) => { if let Some(sym) = self.local(expr) { self.escaped.insert(sym); } }
            ExprKind::Paren(expr) | ExprKind::Cast(expr,_) => self.escape(expr),
            ExprKind::IfElse(_,a,b) | ExprKind::Binary(BinOp::And | BinOp::Or,a,b) => { self.escape(a); self.escape(b); }
            _ => {}
        }
    }
    fn escape_index(&mut self, expr: &Expr) {
        match &expr.kind { ExprKind::Field(obj,_) | ExprKind::Index(obj,_) => self.escape(obj), _ => {} }
    }
    fn assign(&mut self, expr: &Expr) {
        self.escape_index(expr);
        match &expr.kind {
            ExprKind::Field(obj, name) => {
                if let Some(table) = self.local(obj).and_then(|sym| self.tables.get(&sym).copied()) {
                    if self.fields.insert((table, name.text.clone())) { self.layouts.entry(table).or_default().1 += 1; }
                }
            }
            ExprKind::Index(obj, index) => {
                let Some(table) = self.local(obj).and_then(|sym| self.tables.get(&sym).copied()) else { return };
                let bound = self.local(index).and_then(|sym| self.loops.get(&sym).copied());
                let shape = self.layouts.entry(table).or_default();
                if let ExprKind::Number(n) = &index.kind {
                    if *n == (shape.0 + 1) as f64 { shape.0 += 1; }
                } else if let Some(n) = bound { if shape.0 == 0 { shape.0 = n; } }
            }
            _ => {}
        }
    }
    fn block(&mut self, block: &Block) {
        for stat in &block.stats {
            match &stat.kind {
                StatKind::Local(names, values) => {
                    if names.len() == 1 && values.len() == 1 {
                        if let Some(table) = self.empty_literal(&values[0]) { self.tables.insert(self.res.unwrap().decl(names[0].0.id), table); }
                    }
                    for value in values.iter().take(names.len()) { self.escape(value); }
                    self.exprs(values);
                    for (i, (name, _)) in names.iter().enumerate() {
                        let sym = self.res.unwrap().decl(name.id);
                        if !self.res.unwrap().sym(sym).assigned {
                            if let Some(value) = values.get(i).and_then(|value| self.constant(value)) {
                                if !matches!(value, Constant::Record(..)) || !self.escaped.contains(&sym) { self.constants.insert(sym, value); }
                            }
                        }
                    }
                }
                StatKind::Assign(vars, values) => { for var in vars { self.assign(var); } for value in values { self.escape(value); } self.exprs(values); }
                StatKind::Function(name, func) => { self.assign(name); self.block(&func.body); }
                StatKind::LocalFunction(_, func) => self.block(&func.body),
                StatKind::Compound(op, a, b) => { self.escape_index(a); if !matches!(op, BinOp::And | BinOp::Or | BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) { self.escape(a); self.escape(b); } self.expr(a); self.expr(b); }
                StatKind::Call(expr) => self.expr(expr),
                StatKind::Do(body) => self.block(body),
                StatKind::While(expr, body) => { self.expr(expr); self.block(body); }
                StatKind::Repeat(body, expr) => { self.block(body); self.expr(expr); }
                StatKind::If(branches, other) => {
                    for (expr, block) in branches { self.expr(expr); self.block(block); }
                    if let Some(block) = other { self.block(block); }
                }
                StatKind::NumFor(name, from, to, step, body) => {
                    if let (ExprKind::Number(1.0), ExprKind::Number(end), None) = (&from.kind, &to.kind, step) {
                        if *end >= 1.0 && *end <= 16.0 { self.loops.insert(self.res.unwrap().decl(name.id), *end as usize); }
                    }
                    self.expr(from); self.expr(to); if let Some(expr) = step { self.expr(expr); } self.block(body);
                }
                StatKind::GenFor(_, exprs, body) => { for expr in exprs { self.escape(expr); } self.exprs(exprs); self.block(body); }
                StatKind::Return(exprs) => { for expr in exprs { self.escape(expr); } self.exprs(exprs); },
                StatKind::Break | StatKind::Continue | StatKind::TypeAlias(..) => {}
            }
        }
    }
    fn exprs(&mut self, exprs: &[Expr]) { for expr in exprs { self.expr(expr); } }
    fn expr(&mut self, expr: &Expr) {
        if let Some(Constant::String(value)) = self.constant(expr) { self.strings.insert(expr.id, value); }
        match &expr.kind {
            ExprKind::Table(items) => {
                self.spans.insert(expr.id, expr.span);
                if !items.is_empty() {
                    let lists = items.iter().filter(|item| matches!(item, TableItem::Pos(_))).count();
                    let mut hash = items.len() - lists;
                    let records = items.iter().filter(|item| matches!(item, TableItem::Named(..))).count();
                    let mut index = 0;
                    if self.optimized_layouts && lists == 0 {
                        for item in items {
                            if let TableItem::Keyed(key, _) = item {
                                if matches!(self.constant(key), Some(Constant::Number(n)) if n == (index + 1) as f64) { index += 1; }
                            }
                        }
                        if hash == records + index { hash = records; } else { index = 0; }
                    }
                    self.layouts.insert(expr.id, (lists + index, hash));
                } else { self.layouts.entry(expr.id).or_default(); }
                for item in items { match item { TableItem::Pos(v) | TableItem::Named(_, v) => { self.escape(v); self.expr(v); }, TableItem::Keyed(k,v) => { self.escape(k); self.escape(v); self.expr(k); self.expr(v); } } }
            }
            ExprKind::Interp(parts) => { for part in parts { if let InterpPart::Expr(expr) = part { self.expr(expr); } } }
            ExprKind::Index(a,b) => { self.escape(b); self.expr(a); self.expr(b); }
            ExprKind::Binary(op,a,b) => { if !matches!(op, BinOp::And | BinOp::Or | BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) { self.escape(a); self.escape(b); } self.expr(a); self.expr(b); }
            ExprKind::Field(a,_) | ExprKind::Unary(_,a) | ExprKind::Paren(a) | ExprKind::Cast(a,_) => self.expr(a),
            ExprKind::Call(func,args) => { for arg in args { self.escape(arg); } self.expr(func); self.exprs(args); }
            ExprKind::Method(func,_,args) => { self.escape(func); for arg in args { self.escape(arg); } self.expr(func); self.exprs(args); }
            ExprKind::Function(func) => self.block(&func.body),
            ExprKind::IfElse(a,b,c) => { self.expr(a); self.expr(b); self.expr(c); }
            _ => {}
        }
    }
}

impl crate::check::Checker<'_> {
    pub(crate) fn validate_table_layout_options(&mut self) {
        use crate::types::{TKind, TyNode};
        for (node, span) in std::mem::take(&mut self.info.unproven_table_layouts) {
            let Some(value) = self.info.expr.get(&node) else { continue };
            let TyNode::Table(tab) = self.st.node(value.ty) else { continue };
            let root = self.st.tab_root(*tab);
            let table = self.st.tab(*tab);
            let observed = table.runtime
                || (!table.sparse && table.kind == TKind::Array && table.elem.is_some_and(|elem| matches!(self.st.node(elem.ty), TyNode::Any)))
                || (table.kind == TKind::Map && table.key.is_some_and(|key| matches!(self.st.node(key.ty), TyNode::Any)))
                || self.info.next_tables.iter().any(|ty| matches!(self.st.node(*ty), TyNode::Table(tab) if self.st.tab_root(*tab) == root));
            if observed {
                self.error(span, "table allocation depends on an unproven Luau optimization directive; use --!optimize 0, 1, or 2");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_module;
    use crate::resolve::Resolver;
    fn analysis(source: &str) -> Analysis {
        let mut id = 1;
        let module = parse_module(0, source, &mut id).unwrap();
        let mut res = Resolution::default();
        let mut resolver = Resolver::new(&mut res);
        resolver.module(&module, id);
        resolver.finish();
        assert!(resolver.errors.is_empty());
        analyze(&module.body, &res, module.options)
    }
    fn shapes(source: &str) -> Vec<(usize, usize)> {
        let mut shapes: Vec<_> = analysis(source).layouts.into_iter().collect();
        shapes.sort_by_key(|(id, _)| *id);
        shapes.into_iter().map(|(_, shape)| shape).collect()
    }
    #[test]
    fn empty_tables_use_preorder_hints_without_alias_tracking() {
        assert_eq!(shapes("local a = {}; a[1]=1; a[2]=2; a[3]=3; local b={}; for i=1,3 do b[i]=i end; local c={}; local d=c; d[1]=1"), vec![(3,0),(3,0),(0,0)]);
    }
    #[test]
    fn only_empty_single_locals_receive_later_write_hints() {
        assert_eq!(shapes("local a = {1,2,3}; a[4]=4; local b,c={},{}; b[1]=1; local d={}; d.x=1; d.x=2; d.y=3; d[\"z\"]=4"), vec![(3,0),(0,0),(0,0),(0,2)]);
    }
    #[test]
    fn constructor_keys_follow_luau_constant_folding_and_table_escapes() {
        assert_eq!(shapes("local c={x=1}; local k=1; local a={[1+0]=10,[2*1]=20}; local b={[k]=10,[k+1]=20}; local d={[c.x]=10}; local e={[if \"a\"<\"b\" then 1 else 0]=10}; local f={[#(\"a\"..\"\")]=10}"), vec![(0,1),(2,0),(2,0),(1,0),(0,1),(1,0)]);
        assert_eq!(shapes("local c={x=1}; local a={[c.x]=10}; c.x=2"), vec![(0,1),(0,1)]);
    }
    #[test]
    fn sequential_explicit_indices_allocate_an_array_only_if_all_keys_fit() {
        assert_eq!(shapes("local a = {[1]=1,[2]=2}; local b = {[1]=1,[\"1\"]=2,[false]=3}; local c={1,2}"), vec![(2,0),(0,3),(2,0)]);
    }
    #[test]
    fn optimization_zero_disables_prediction_and_all_key_promotion() {
        let body = "local a={}; a[1]=1; a[2]=2; a[3]=3; local b={[1]=1,[2]=2,[3]=3}; local c={[0+1]=1,[1+1]=2,[2+1]=3}; local d={1,2,3}; local e={a=nil,b=2,c=3}";
        assert_eq!(shapes(&format!("--!optimize 0\n{body}")), vec![(0,0),(0,3),(0,3),(3,0),(0,3)]);
        for level in 1..=2 {
            assert_eq!(shapes(&format!("--!optimize {level}\n{body}")), vec![(3,0),(3,0),(3,0),(3,0),(0,3)]);
        }
    }
    #[test]
    fn unknown_optimization_tracks_only_mode_dependent_layouts() {
        let a = analysis("--!optimize 18446744073709551616\nlocal a={}; a[1]=1; local b={[1]=1,[2]=2,[3]=3}; local c={1,2,3}; local d={a=nil,b=2,c=3}");
        assert_eq!(a.unproven.len(), 2);
        let mut uncertain: Vec<_> = a.unproven.iter().map(|(node, _)| a.layouts[node]).collect();
        uncertain.sort();
        assert_eq!(uncertain, vec![(1,0),(3,0)]);
        assert!(analysis("--!optimize 18446744073709551616\nlocal a={1,2,3}; local b={a=nil,b=2,c=3}").unproven.is_empty());
    }
}
