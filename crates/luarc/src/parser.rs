//! Recursive-descent parser following Luau precedence and associativity:
//! `or` < `and` < comparison < `..` (right) < `+ -` < `* / // %` < unary < `^` (right).

use crate::ast::*;
use crate::diag::{err, DResult, Diagnostic, Span};
use crate::lexer::{lex_with_options, InterpPiece, Kw, Tok, Token};

pub struct Parser<'a> {
    toks: Vec<Token>,
    pos: usize,
    next_id: &'a mut NodeId,
    attrs: std::collections::HashMap<NodeId, LocalAttr>,
    depth: u32,
}

/// Nesting limit for expressions, blocks and types to prevent stack overflow.
/// Luau 0.743 accepts 500 nested parentheses and rejects 1000
/// with the same message.
const MAX_DEPTH: u32 = 800;

pub fn parse_module(file: u32, text: &str, next_id: &mut NodeId) -> DResult<Module> {
    let (toks, options) = lex_with_options(file, text)?;
    let mut p = Parser { toks, pos: 0, next_id, attrs: Default::default(), depth: 0 };
    let body = p.block()?;
    if !p.check_eof() {
        let t = p.peek().clone();
        return err(t.span, format!("unexpected {} (expected a statement)", describe(&t.tok)));
    }
    Ok(Module { file, body, options, attrs: p.attrs })
}

fn describe(t: &Tok) -> String {
    match t {
        Tok::Name(n) => format!("'{n}'"),
        Tok::Number(_) | Tok::Int(_) => "number".into(),
        Tok::Str(_) | Tok::Interp(_) => "string".into(),
        Tok::Kw(k) => format!("'{}'", format!("{k:?}").to_lowercase()),
        Tok::Op(o) => format!("'{o}'"),
        Tok::Eof => "end of file".into(),
    }
}

fn binop(t: &Tok) -> Option<(BinOp, u8, u8)> {
    Some(match t {
        Tok::Kw(Kw::Or) => (BinOp::Or, 1, 1),
        Tok::Kw(Kw::And) => (BinOp::And, 2, 2),
        Tok::Op("==") => (BinOp::Eq, 3, 3),
        Tok::Op("~=") => (BinOp::Ne, 3, 3),
        Tok::Op("<") => (BinOp::Lt, 3, 3),
        Tok::Op("<=") => (BinOp::Le, 3, 3),
        Tok::Op(">") => (BinOp::Gt, 3, 3),
        Tok::Op(">=") => (BinOp::Ge, 3, 3),
        Tok::Op("..") => (BinOp::Concat, 5, 4),
        Tok::Op("+") => (BinOp::Add, 6, 6),
        Tok::Op("-") => (BinOp::Sub, 6, 6),
        Tok::Op("*") => (BinOp::Mul, 7, 7),
        Tok::Op("/") => (BinOp::Div, 7, 7),
        Tok::Op("//") => (BinOp::IDiv, 7, 7),
        Tok::Op("%") => (BinOp::Mod, 7, 7),
        Tok::Op("^") => (BinOp::Pow, 10, 9),
        _ => return None,
    })
}
const UNARY_PRIO: u8 = 8;

fn compound_op(t: &Tok) -> Option<BinOp> {
    Some(match t {
        Tok::Op("+=") => BinOp::Add,
        Tok::Op("-=") => BinOp::Sub,
        Tok::Op("*=") => BinOp::Mul,
        Tok::Op("/=") => BinOp::Div,
        Tok::Op("//=") => BinOp::IDiv,
        Tok::Op("%=") => BinOp::Mod,
        Tok::Op("^=") => BinOp::Pow,
        Tok::Op("..=") => BinOp::Concat,
        _ => return None,
    })
}

impl<'a> Parser<'a> {
    fn id(&mut self) -> NodeId {
        let i = *self.next_id;
        *self.next_id += 1;
        i
    }
    fn peek(&self) -> &Token {
        &self.toks[self.pos]
    }
    fn peek_at(&self, k: usize) -> &Tok {
        &self.toks[(self.pos + k).min(self.toks.len() - 1)].tok
    }
    fn span(&self) -> Span {
        self.peek().span
    }
    fn advance(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }
    fn check_eof(&self) -> bool {
        self.peek().tok == Tok::Eof
    }
    fn is_op(&self, op: &str) -> bool {
        matches!(self.peek().tok, Tok::Op(o) if o == op)
    }
    fn is_kw(&self, k: Kw) -> bool {
        self.peek().tok == Tok::Kw(k)
    }
    fn eat_op(&mut self, op: &str) -> bool {
        if self.is_op(op) {
            self.advance();
            true
        } else {
            false
        }
    }
    fn eat_kw(&mut self, k: Kw) -> bool {
        if self.is_kw(k) {
            self.advance();
            true
        } else {
            false
        }
    }
    fn expect_op(&mut self, op: &str, ctx: &str) -> DResult<()> {
        if self.eat_op(op) {
            Ok(())
        } else {
            let t = self.peek().clone();
            err(t.span, format!("expected '{op}' {ctx}, found {}", describe(&t.tok)))
        }
    }
    fn expect_kw(&mut self, k: Kw, ctx: &str) -> DResult<()> {
        if self.eat_kw(k) {
            Ok(())
        } else {
            let t = self.peek().clone();
            err(t.span, format!("expected '{}' {ctx}, found {}", format!("{k:?}").to_lowercase(), describe(&t.tok)))
        }
    }
    fn name(&mut self, ctx: &str) -> DResult<Name> {
        let t = self.peek().clone();
        match t.tok {
            Tok::Name(n) => {
                self.advance();
                Ok(Name { id: self.id(), text: n, span: t.span })
            }
            other => err(t.span, format!("expected a name {ctx}, found {}", describe(&other))),
        }
    }

    fn block_end(&self) -> bool {
        matches!(self.peek().tok, Tok::Eof | Tok::Kw(Kw::End | Kw::Else | Kw::Elseif | Kw::Until))
    }

    pub fn block(&mut self) -> DResult<Block> {
        self.enter("block")?;
        let r = self.block_inner();
        self.depth -= 1;
        r
    }

    /// Counts one nesting level; past [`MAX_DEPTH`] a diagnostic, never a stack overflow.
    fn enter(&mut self, what: &str) -> DResult<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return err(self.span(), format!("Exceeded allowed recursion depth; simplify your {what} to make the code compile"));
        }
        Ok(())
    }

    fn block_inner(&mut self) -> DResult<Block> {
        let span = self.span();
        let mut stats = Vec::new();
        let mut errors: Vec<Diagnostic> = Vec::new();
        while !self.block_end() {
            if self.eat_op(";") {
                continue;
            }
            let st = self.statement()?;
            let terminal = matches!(st.kind, StatKind::Return(_) | StatKind::Break | StatKind::Continue);
            stats.push(st);
            while self.eat_op(";") {}
            if terminal && !self.block_end() {
                let s = self.span();
                errors.push(Diagnostic::new(
                    s,
                    "statement after return/break/continue: it must be the last statement in its block",
                ));
                break;
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(Block { stats, span })
    }

    fn statement(&mut self) -> DResult<Stat> {
        let span = self.span();
        let id = self.id();
        let kind = match self.peek().tok.clone() {
            Tok::Kw(Kw::Local) => {
                self.advance();
                if self.eat_kw(Kw::Function) {
                    let name = self.name("after 'local function'")?;
                    let f = self.func_body(span, name.text.clone(), false)?;
                    StatKind::LocalFunction(name, Box::new(f))
                } else {
                    let mut names = Vec::new();
                    loop {
                        let n = self.name("in local declaration")?;
                        if self.eat_op("<") {
                            let a = self.name("as a local attribute")?;
                            let attr = match a.text.as_str() {
                                "const" => LocalAttr::Const,
                                "close" => LocalAttr::Close,
                                other => return err(a.span, format!("unknown local attribute <{other}> (expected <const> or <close>)")),
                            };
                            self.expect_op(">", "to close the local attribute")?;
                            self.attrs.insert(n.id, attr);
                        }
                        let ty = if self.eat_op(":") { Some(self.type_expr()?) } else { None };
                        names.push((n, ty));
                        if !self.eat_op(",") {
                            break;
                        }
                    }
                    let exprs = if self.eat_op("=") { self.expr_list()? } else { Vec::new() };
                    StatKind::Local(names, exprs)
                }
            }
            Tok::Kw(Kw::Function) => {
                self.advance();
                let first = self.name("after 'function'")?;
                let mut target = Expr { id: self.id(), span: first.span, kind: ExprKind::Name(first.clone()) };
                let mut hint = first.text.clone();
                let mut is_method = false;
                loop {
                    if self.eat_op(".") {
                        let f = self.name("after '.'")?;
                        hint = format!("{hint}.{}", f.text);
                        target = Expr { id: self.id(), span: f.span, kind: ExprKind::Field(Box::new(target), f) };
                    } else if self.eat_op(":") {
                        let f = self.name("after ':'")?;
                        hint = format!("{hint}:{}", f.text);
                        target = Expr { id: self.id(), span: f.span, kind: ExprKind::Field(Box::new(target), f) };
                        is_method = true;
                        break;
                    } else {
                        break;
                    }
                }
                let f = self.func_body(span, hint, is_method)?;
                StatKind::Function(target, Box::new(f))
            }
            Tok::Kw(Kw::Return) => {
                self.advance();
                let exprs = if self.block_end() || self.is_op(";") { Vec::new() } else { self.expr_list()? };
                StatKind::Return(exprs)
            }
            Tok::Kw(Kw::Break) => {
                self.advance();
                StatKind::Break
            }
            Tok::Kw(Kw::Do) => {
                self.advance();
                let b = self.block()?;
                self.expect_kw(Kw::End, "to close 'do'")?;
                StatKind::Do(b)
            }
            Tok::Kw(Kw::While) => {
                self.advance();
                let c = self.expr()?;
                self.expect_kw(Kw::Do, "after 'while' condition")?;
                let b = self.block()?;
                self.expect_kw(Kw::End, "to close 'while'")?;
                StatKind::While(c, b)
            }
            Tok::Kw(Kw::Repeat) => {
                self.advance();
                let b = self.block()?;
                self.expect_kw(Kw::Until, "to close 'repeat'")?;
                let c = self.expr()?;
                StatKind::Repeat(b, c)
            }
            Tok::Kw(Kw::If) => {
                self.advance();
                let mut arms = Vec::new();
                let c = self.expr()?;
                self.expect_kw(Kw::Then, "after 'if' condition")?;
                arms.push((c, self.block()?));
                let mut els = None;
                loop {
                    if self.eat_kw(Kw::Elseif) {
                        let c = self.expr()?;
                        self.expect_kw(Kw::Then, "after 'elseif' condition")?;
                        arms.push((c, self.block()?));
                    } else if self.eat_kw(Kw::Else) {
                        els = Some(self.block()?);
                        self.expect_kw(Kw::End, "to close 'if'")?;
                        break;
                    } else {
                        self.expect_kw(Kw::End, "to close 'if'")?;
                        break;
                    }
                }
                StatKind::If(arms, els)
            }
            Tok::Kw(Kw::For) => {
                self.advance();
                let n1 = self.name("after 'for'")?;
                if self.is_op(":") {
                    return err(self.span(), "type annotations on loop variables are not supported");
                }
                if self.eat_op("=") {
                    let a = self.expr()?;
                    self.expect_op(",", "in numeric for")?;
                    let b = self.expr()?;
                    let c = if self.eat_op(",") { Some(self.expr()?) } else { None };
                    self.expect_kw(Kw::Do, "in numeric for")?;
                    let body = self.block()?;
                    self.expect_kw(Kw::End, "to close 'for'")?;
                    StatKind::NumFor(n1, a, b, c, body)
                } else {
                    let mut names = vec![n1];
                    while self.eat_op(",") {
                        names.push(self.name("in for-in loop")?);
                    }
                    self.expect_kw(Kw::In, "in for-in loop")?;
                    let exprs = self.expr_list()?;
                    self.expect_kw(Kw::Do, "in for-in loop")?;
                    let body = self.block()?;
                    self.expect_kw(Kw::End, "to close 'for'")?;
                    StatKind::GenFor(names, exprs, body)
                }
            }
            Tok::Name(n) if n == "continue" && !matches!(self.peek_at(1), Tok::Op("(" | "." | ":" | "[" | "=" | ",")) => {
                self.advance();
                StatKind::Continue
            }
            Tok::Name(n) if (n == "type" || n == "export") && matches!(self.peek_at(1), Tok::Name(_)) => {
                self.advance();
                if n == "export" {
                    match self.peek().tok.clone() {
                        Tok::Name(t) if t == "type" => {
                            self.advance();
                        }
                        _ => return err(span, "expected 'type' after 'export'"),
                    }
                }
                let name = self.name("in type alias")?;
                let generics = self.generic_names("in type alias parameters")?;
                self.expect_op("=", "in type alias")?;
                let ty = self.type_expr()?;
                StatKind::TypeAlias(name, generics, ty)
            }
            _ => {
                let e = self.suffixed_expr()?;
                if self.is_op("=") || self.is_op(",") {
                    let mut targets = vec![e];
                    while self.eat_op(",") {
                        targets.push(self.suffixed_expr()?);
                    }
                    self.expect_op("=", "in assignment")?;
                    let exprs = self.expr_list()?;
                    for t in &targets {
                        check_assignable(t)?;
                    }
                    StatKind::Assign(targets, exprs)
                } else if let Some(op) = compound_op(&self.peek().tok) {
                    self.advance();
                    check_assignable(&e)?;
                    let rhs = self.expr()?;
                    StatKind::Compound(op, e, rhs)
                } else {
                    match e.kind {
                        ExprKind::Call(..) | ExprKind::Method(..) => StatKind::Call(e),
                        _ => return err(e.span, "syntax error: expression is not a statement (expected a call or assignment)"),
                    }
                }
            }
        };
        Ok(Stat { id, span, kind })
    }

    fn func_body(&mut self, span: Span, hint: String, is_method: bool) -> DResult<FuncBody> {
        let generics = self.generic_names("in function type parameters")?;
        self.expect_op("(", "to start parameter list")?;
        let mut params = Vec::new();
        let mut vararg = None;
        if is_method {
            params.push(Param { name: Name { id: self.id(), text: "self".into(), span }, ty: None });
        }
        if !self.is_op(")") {
            loop {
                if self.is_op("...") {
                    // `...` or `...: T`, always the last parameter
                    let sp = self.span();
                    self.eat_op("...");
                    let ty = if self.eat_op(":") { Some(self.type_expr()?) } else { None };
                    vararg = Some((sp, ty));
                    break;
                }
                let n = self.name("in parameter list")?;
                let ty = if self.eat_op(":") { Some(self.type_expr()?) } else { None };
                params.push(Param { name: n, ty });
                if !self.eat_op(",") {
                    break;
                }
            }
        }
        self.expect_op(")", "to close parameter list")?;
        let rets = if self.eat_op(":") { Some(self.return_types()?) } else { None };
        let body = self.block()?;
        self.expect_kw(Kw::End, "to close function")?;
        Ok(FuncBody { id: self.id(), span, params, rets, vararg, body, name_hint: hint, generics, call_site: None })
    }

    /// `<T, U>` after a function or alias name (empty when there is no `<`).
    fn generic_names(&mut self, ctx: &str) -> DResult<Vec<Name>> {
        let mut out = Vec::new();
        if !self.eat_op("<") {
            return Ok(out);
        }
        loop {
            let n = self.name(ctx)?;
            if self.is_op("...") {
                return err(self.span(), "generic type packs (`T...`) are not supported");
            }
            if out.iter().any(|o: &Name| o.text == n.text) {
                return err(n.span, format!("type parameter '{}' is declared twice", n.text));
            }
            out.push(n);
            if !self.eat_op(",") {
                break;
            }
        }
        self.expect_op(">", ctx)?;
        Ok(out)
    }

    fn return_types(&mut self) -> DResult<Vec<TypeExpr>> {
        // `(a, b)` is a tuple of results unless followed by `->` (a function type).
        if self.is_op("(") {
            let save = self.pos;
            self.advance();
            let mut tys = Vec::new();
            if !self.is_op(")") {
                loop {
                    tys.push(self.type_expr()?);
                    if !self.eat_op(",") {
                        break;
                    }
                }
            }
            self.expect_op(")", "to close return types")?;
            if self.is_op("->") {
                self.pos = save;
                return Ok(vec![self.type_expr()?]);
            }
            if tys.len() == 1 && self.is_op("?") {
                self.pos = save;
                return Ok(vec![self.type_expr()?]);
            }
            Ok(tys)
        } else {
            Ok(vec![self.type_expr()?])
        }
    }

    pub fn type_expr(&mut self) -> DResult<TypeExpr> {
        self.enter("type")?;
        let r = self.type_expr_inner();
        self.depth -= 1;
        r
    }

    fn type_expr_inner(&mut self) -> DResult<TypeExpr> {
        if self.is_op("...") {
            // `...T` ends a parameter or result type list (checked by the checker)
            let sp = self.span();
            self.advance();
            let inner = self.type_expr_inner()?;
            return Ok(TypeExpr::Variadic(Box::new(inner), sp));
        }
        let mut t = self.simple_type()?;
        loop {
            if self.eat_op("?") {
                t = TypeExpr::Optional(Box::new(t));
            } else if self.is_op("|") {
                let sp = self.span();
                self.advance();
                let other = self.simple_type()?;
                match (t, other) {
                    (t0, TypeExpr::Nil(_)) => t = TypeExpr::Optional(Box::new(t0)),
                    (TypeExpr::Nil(_), o) => t = TypeExpr::Optional(Box::new(o)),
                    // `A | B | C` is one flat union (the dynamic type `any`)
                    (TypeExpr::Union(mut ms, usp), o) => {
                        ms.push(o);
                        t = TypeExpr::Union(ms, usp);
                    }
                    (t0, o) => t = TypeExpr::Union(vec![t0, o], sp),
                }
            } else if self.is_op("&") {
                let sp = self.span();
                self.advance();
                self.simple_type()?;
                t = TypeExpr::Unsupported("intersection types".into(), sp);
            } else {
                return Ok(t);
            }
        }
    }

    fn simple_type(&mut self) -> DResult<TypeExpr> {
        let sp = self.span();
        match self.peek().tok.clone() {
            Tok::Kw(Kw::Nil) => {
                self.advance();
                Ok(TypeExpr::Nil(sp))
            }
            Tok::Name(n) => {
                self.advance();
                if n == "typeof" && self.is_op("(") {
                    return err(sp, "typeof(...) types are not supported");
                }
                let mut path = vec![n];
                while self.eat_op(".") {
                    path.push(self.name("in type path")?.text);
                }
                if self.eat_op("<") {
                    if path.len() != 1 {
                        return err(sp, "type arguments are only supported on local type aliases");
                    }
                    let mut args = Vec::new();
                    loop {
                        args.push(self.type_expr()?);
                        if !self.eat_op(",") {
                            break;
                        }
                    }
                    self.expect_op(">", "to close type arguments")?;
                    return Ok(TypeExpr::Applied(path.remove(0), args, sp));
                }
                Ok(TypeExpr::Named(path, sp))
            }
            Tok::Op("{") => {
                self.advance();
                if self.eat_op("[") {
                    let k = self.type_expr()?;
                    self.expect_op("]", "in map type")?;
                    self.expect_op(":", "in map type")?;
                    let v = self.type_expr()?;
                    self.eat_op(",");
                    self.expect_op("}", "to close map type")?;
                    return Ok(TypeExpr::Map(Box::new(k), Box::new(v), sp));
                }
                let is_record = matches!(self.peek().tok, Tok::Name(_)) && matches!(self.peek_at(1), Tok::Op(":"));
                if is_record {
                    let mut fields = Vec::new();
                    while !self.is_op("}") {
                        let n = self.name("in record type")?;
                        self.expect_op(":", "in record type")?;
                        fields.push((n, self.type_expr()?));
                        if !self.eat_op(",") && !self.eat_op(";") {
                            break;
                        }
                    }
                    self.expect_op("}", "to close record type")?;
                    Ok(TypeExpr::Record(fields, sp))
                } else if self.is_op("}") {
                    self.advance();
                    Ok(TypeExpr::Record(Vec::new(), sp))
                } else {
                    let e = self.type_expr()?;
                    self.expect_op("}", "to close array type")?;
                    Ok(TypeExpr::Array(Box::new(e), sp))
                }
            }
            Tok::Op("(") => {
                self.advance();
                let mut params = Vec::new();
                if !self.is_op(")") {
                    loop {
                        // Allow named parameters in function types: `(x: number) -> ()`.
                        if matches!(self.peek().tok, Tok::Name(_)) && matches!(self.peek_at(1), Tok::Op(":")) {
                            self.advance();
                            self.advance();
                        }
                        params.push(self.type_expr()?);
                        if !self.eat_op(",") {
                            break;
                        }
                    }
                }
                self.expect_op(")", "in type")?;
                if self.eat_op("->") {
                    let rets = self.return_types()?;
                    Ok(TypeExpr::Func(params, rets, sp))
                } else if params.len() == 1 {
                    Ok(params.pop().unwrap())
                } else {
                    err(sp, "expected '->' after function type parameters")
                }
            }
            Tok::Str(_) => {
                self.advance();
                Ok(TypeExpr::Unsupported("singleton string types".into(), sp))
            }
            other => err(sp, format!("expected a type, found {}", describe(&other))),
        }
    }

    fn expr_list(&mut self) -> DResult<Vec<Expr>> {
        let mut v = vec![self.expr()?];
        while self.eat_op(",") {
            v.push(self.expr()?);
        }
        Ok(v)
    }

    pub fn expr(&mut self) -> DResult<Expr> {
        self.sub_expr(0)
    }

    fn sub_expr(&mut self, limit: u8) -> DResult<Expr> {
        self.enter("expression")?;
        let r = self.sub_expr_inner(limit);
        self.depth -= 1;
        r
    }

    fn sub_expr_inner(&mut self, limit: u8) -> DResult<Expr> {
        let sp = self.span();
        let mut left = match self.peek().tok {
            Tok::Kw(Kw::Not) | Tok::Op("-") | Tok::Op("#") => {
                let op = match self.advance().tok {
                    Tok::Kw(Kw::Not) => UnOp::Not,
                    Tok::Op("-") => UnOp::Neg,
                    _ => UnOp::Len,
                };
                let e = self.sub_expr(UNARY_PRIO)?;
                Expr { id: self.id(), span: sp, kind: ExprKind::Unary(op, Box::new(e)) }
            }
            _ => {
                let mut e = self.simple_expr()?;
                // `e :: T` binds tighter than every binary operator (Luau)
                while self.is_op("::") {
                    let csp = self.span();
                    self.advance();
                    let ty = self.type_expr()?;
                    e = Expr { id: self.id(), span: csp, kind: ExprKind::Cast(Box::new(e), ty) };
                }
                e
            }
        };
        while let Some((op, lp, rp)) = binop(&self.peek().tok) {
            if lp <= limit {
                break;
            }
            let opspan = self.span();
            self.advance();
            let right = self.sub_expr(rp)?;
            left = Expr { id: self.id(), span: opspan, kind: ExprKind::Binary(op, Box::new(left), Box::new(right)) };
        }
        Ok(left)
    }

    fn simple_expr(&mut self) -> DResult<Expr> {
        let t = self.peek().clone();
        let sp = t.span;
        let kind = match t.tok {
            Tok::Number(n) => {
                self.advance();
                ExprKind::Number(n)
            }
            Tok::Int(i) => {
                self.advance();
                ExprKind::Int(i)
            }
            Tok::Str(s) => {
                self.advance();
                ExprKind::Str(s)
            }
            Tok::Interp(pieces) => {
                self.advance();
                ExprKind::Interp(self.interp(pieces)?)
            }
            Tok::Kw(Kw::Nil) => {
                self.advance();
                ExprKind::Nil
            }
            Tok::Kw(Kw::True) => {
                self.advance();
                ExprKind::Bool(true)
            }
            Tok::Kw(Kw::False) => {
                self.advance();
                ExprKind::Bool(false)
            }
            Tok::Op("...") => {
                self.advance();
                ExprKind::Vararg
            }
            Tok::Op("{") => ExprKind::Table(self.table()?),
            Tok::Kw(Kw::Function) => {
                self.advance();
                ExprKind::Function(Box::new(self.func_body(sp, "anonymous function".into(), false)?))
            }
            Tok::Kw(Kw::If) => {
                self.advance();
                let c = self.expr()?;
                self.expect_kw(Kw::Then, "in if-expression")?;
                let a = self.expr()?;
                let mut elifs = Vec::new();
                while self.eat_kw(Kw::Elseif) {
                    let c2 = self.expr()?;
                    self.expect_kw(Kw::Then, "in if-expression")?;
                    elifs.push((c2, self.expr()?));
                }
                self.expect_kw(Kw::Else, "in if-expression (an else branch is required)")?;
                let mut e = self.expr()?;
                while let Some((c2, a2)) = elifs.pop() {
                    e = Expr { id: self.id(), span: c2.span, kind: ExprKind::IfElse(Box::new(c2), Box::new(a2), Box::new(e)) };
                }
                ExprKind::IfElse(Box::new(c), Box::new(a), Box::new(e))
            }
            _ => return self.suffixed_expr(),
        };
        Ok(Expr { id: self.id(), span: sp, kind })
    }

    fn interp(&mut self, pieces: Vec<InterpPiece>) -> DResult<Vec<InterpPart>> {
        let mut parts = Vec::new();
        for p in pieces {
            match p {
                InterpPiece::Lit(l) => {
                    if !l.is_empty() {
                        parts.push(InterpPart::Lit(l))
                    }
                }
                InterpPiece::Expr(toks) => {
                    let mut sub = Parser { toks, pos: 0, next_id: self.next_id, attrs: Default::default(), depth: self.depth };
                    let e = sub.expr()?;
                    if !sub.check_eof() {
                        return err(sub.span(), "unexpected token in interpolation expression");
                    }
                    parts.push(InterpPart::Expr(e));
                }
            }
        }
        Ok(parts)
    }

    fn table(&mut self) -> DResult<Vec<TableItem>> {
        self.expect_op("{", "")?;
        let mut items = Vec::new();
        while !self.is_op("}") {
            if self.eat_op("[") {
                let k = self.expr()?;
                self.expect_op("]", "in table key")?;
                self.expect_op("=", "in table constructor")?;
                items.push(TableItem::Keyed(k, self.expr()?));
            } else if matches!(self.peek().tok, Tok::Name(_)) && matches!(self.peek_at(1), Tok::Op("=")) {
                let n = self.name("")?;
                self.advance();
                items.push(TableItem::Named(n, self.expr()?));
            } else {
                items.push(TableItem::Pos(self.expr()?));
            }
            if !self.eat_op(",") && !self.eat_op(";") {
                break;
            }
        }
        self.expect_op("}", "to close table constructor")?;
        Ok(items)
    }

    fn primary_expr(&mut self) -> DResult<Expr> {
        let t = self.peek().clone();
        match t.tok {
            Tok::Name(_) => {
                let n = self.name("")?;
                Ok(Expr { id: self.id(), span: n.span, kind: ExprKind::Name(n) })
            }
            Tok::Op("(") => {
                self.advance();
                let e = self.expr()?;
                self.expect_op(")", "to close parenthesis")?;
                Ok(Expr { id: self.id(), span: t.span, kind: ExprKind::Paren(Box::new(e)) })
            }
            other => err(t.span, format!("unexpected {} (expected an expression)", describe(&other))),
        }
    }

    fn call_args(&mut self) -> DResult<Vec<Expr>> {
        let t = self.peek().clone();
        match t.tok {
            Tok::Op("(") => {
                self.advance();
                let args = if self.is_op(")") { Vec::new() } else { self.expr_list()? };
                self.expect_op(")", "to close argument list")?;
                Ok(args)
            }
            Tok::Str(s) => {
                self.advance();
                Ok(vec![Expr { id: self.id(), span: t.span, kind: ExprKind::Str(s) }])
            }
            Tok::Op("{") => {
                let items = self.table()?;
                Ok(vec![Expr { id: self.id(), span: t.span, kind: ExprKind::Table(items) }])
            }
            _ => err(t.span, "expected function arguments"),
        }
    }

    fn suffixed_expr(&mut self) -> DResult<Expr> {
        let mut e = self.primary_expr()?;
        loop {
            let t = self.peek().clone();
            match t.tok {
                Tok::Op(".") => {
                    self.advance();
                    let n = self.name("after '.'")?;
                    e = Expr { id: self.id(), span: n.span, kind: ExprKind::Field(Box::new(e), n) };
                }
                Tok::Op("[") => {
                    self.advance();
                    let k = self.expr()?;
                    self.expect_op("]", "to close index")?;
                    e = Expr { id: self.id(), span: t.span, kind: ExprKind::Index(Box::new(e), Box::new(k)) };
                }
                Tok::Op(":") => {
                    self.advance();
                    let n = self.name("after ':'")?;
                    let args = self.call_args()?;
                    e = Expr { id: self.id(), span: n.span, kind: ExprKind::Method(Box::new(e), n, args) };
                }
                Tok::Op("(") | Tok::Str(_) | Tok::Op("{") => {
                    // A '(' on a new line would be ambiguous in Lua; we accept it.
                    let args = self.call_args()?;
                    let span = e.span;
                    e = Expr { id: self.id(), span, kind: ExprKind::Call(Box::new(e), args) };
                }
                _ => return Ok(e),
            }
        }
    }
}

fn check_assignable(e: &Expr) -> DResult<()> {
    match e.kind {
        ExprKind::Name(_) | ExprKind::Field(..) | ExprKind::Index(..) => Ok(()),
        _ => err(e.span, "cannot assign to this expression"),
    }
}
