//! Abstract syntax tree. Every expression, name and function body carries a
//! `NodeId` (unique across all modules of one compilation) and a source span.

use crate::diag::Span;

pub type NodeId = u32;

#[derive(Clone, Debug)]
pub struct Name {
    pub id: NodeId,
    pub text: String,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: NodeId,
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    Concat,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::IDiv => "//",
            BinOp::Mod => "%",
            BinOp::Pow => "^",
            BinOp::Concat => "..",
            BinOp::Eq => "==",
            BinOp::Ne => "~=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    Len,
}

#[derive(Clone, Debug)]
pub enum InterpPart {
    Lit(Vec<u8>),
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub enum TableItem {
    Pos(Expr),
    Named(Name, Expr),
    Keyed(Expr, Expr),
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Nil,
    Bool(bool),
    Number(f64),
    /// Integer literal above 2^53: always an `integer`.
    Int(i128),
    Str(Vec<u8>),
    Interp(Vec<InterpPart>),
    Name(Name),
    Index(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, Name),
    Call(Box<Expr>, Vec<Expr>),
    Method(Box<Expr>, Name, Vec<Expr>),
    Function(Box<FuncBody>),
    Table(Vec<TableItem>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `(e)`: truncates multiple results to one.
    Paren(Box<Expr>),
    /// `...` (varargs are unsupported; kept for a precise diagnostic).
    Vararg,
    /// `e :: T`: a checked conversion to or from the dynamic type `any`.
    Cast(Box<Expr>, TypeExpr),
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    /// `number`, `Point`, `regex.Regex`
    Named(Vec<String>, Span),
    Nil(Span),
    Optional(Box<TypeExpr>),
    Array(Box<TypeExpr>, Span),
    Map(Box<TypeExpr>, Box<TypeExpr>, Span),
    Record(Vec<(Name, TypeExpr)>, Span),
    Func(Vec<TypeExpr>, Vec<TypeExpr>, Span),
    /// `...T`: the rest of a parameter or result list.
    Variadic(Box<TypeExpr>, Span),
    /// `Pair<number, string>`: a generic alias applied to type arguments.
    Applied(String, Vec<TypeExpr>, Span),
    /// `A | B` (more than one non-nil member): the dynamic type `any`.
    Union(Vec<TypeExpr>, Span),
    /// Unsupported type syntax, kept for a diagnostic.
    Unsupported(String, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named(_, s)
            | TypeExpr::Nil(s)
            | TypeExpr::Array(_, s)
            | TypeExpr::Map(_, _, s)
            | TypeExpr::Record(_, s)
            | TypeExpr::Func(_, _, s)
            | TypeExpr::Applied(_, _, s)
            | TypeExpr::Union(_, s)
            | TypeExpr::Unsupported(_, s)
            | TypeExpr::Variadic(_, s) => *s,
            TypeExpr::Optional(t) => t.span(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: Name,
    pub ty: Option<TypeExpr>,
}

#[derive(Clone, Debug)]
pub struct FuncBody {
    pub id: NodeId,
    pub span: Span,
    /// For methods (`function t:m()`), the implicit `self` is `params[0]`.
    pub params: Vec<Param>,
    pub rets: Option<Vec<TypeExpr>>,
    /// `...` (optionally `...: T`) after the parameters: a variadic function.
    pub vararg: Option<(Span, Option<TypeExpr>)>,
    pub body: Block,
    pub name_hint: String,
    /// Type parameters (`function f<T, U>`); every call site checks its own copy.
    pub generics: Vec<Name>,
    /// For a copy made for one call site (`specialize.rs`): where that call is.
    /// `error(msg, 2)` in the copy reports this position (Luau level 2).
    pub call_site: Option<Span>,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stats: Vec<Stat>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Stat {
    pub id: NodeId,
    pub span: Span,
    pub kind: StatKind,
}

#[derive(Clone, Debug)]
pub enum StatKind {
    Local(Vec<(Name, Option<TypeExpr>)>, Vec<Expr>),
    LocalFunction(Name, Box<FuncBody>),
    /// `function a.b.c()` / `function a:m()` / `function f()` (assignment to an
    /// existing variable). `target` is the assignment target expression.
    Function(Expr, Box<FuncBody>),
    Assign(Vec<Expr>, Vec<Expr>),
    Compound(BinOp, Expr, Expr),
    Call(Expr),
    Do(Block),
    While(Expr, Block),
    Repeat(Block, Expr),
    If(Vec<(Expr, Block)>, Option<Block>),
    NumFor(Name, Expr, Expr, Option<Expr>, Block),
    GenFor(Vec<Name>, Vec<Expr>, Block),
    Return(Vec<Expr>),
    Break,
    Continue,
    /// `type Name<T, U> = ...`: the alias name, its type parameters and its body.
    TypeAlias(Name, Vec<Name>, TypeExpr),
}

/// One parsed source module.
#[derive(Clone, Debug)]
pub struct Module {
    pub file: u32,
    pub body: Block,
    pub options: ModuleOptions,
    /// Attributes of `local x <const>` / `local x <close>` declarations (name node ids).
    pub attrs: std::collections::HashMap<NodeId, LocalAttr>,
}

/// Oracle compilation metadata used to prove GC-stable continuation strings.
#[derive(Clone, Copy, Debug)]
pub struct ModuleOptions {
    /// Pinned Luau defaults to O1; an overflowing directive is not proven.
    pub oracle_optimization: Option<u8>,
}

impl Default for ModuleOptions {
    fn default() -> Self { Self { oracle_optimization: Some(1) } }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalAttr {
    Const,
    Close,
}
