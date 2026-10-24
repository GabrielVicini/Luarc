//! Typed intermediate representation of generated Rust code.
//!
//! Code generation builds [`RExpr`] / [`RStmt`] trees instead of strings; the
//! printer owns parenthesization (operator precedence), so no pass inspects
//! generated text to recover its structure.
//!
//! [`RExpr::Raw`] carries text without structured nodes. Raw operands and
//! expressions use `needs_paren` and `strip` to preserve grouping.
//! `atom` and `strip` accept both strings and nodes.

/// A generated Rust type. Existing type spellings remain opaque named leaves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RType {
    Named(String),
    Apply(String, Vec<RType>),
}

impl RType {
    pub fn print(&self) -> String {
        match self {
            RType::Named(name) => name.clone(),
            RType::Apply(name, args) if args.is_empty() => name.clone(),
            RType::Apply(name, args) => {
                format!("{name}<{}>", args.iter().map(RType::print).collect::<Vec<_>>().join(", "))
            }
        }
    }
}

/// Rust operator precedence, lowest first (the Rust reference, "Expression
/// precedence"). Block-like expressions (`{ }`, `if`, `match`) rank lowest: as an
/// operand they are always parenthesized (at statement start they would end the
/// statement).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Prec {
    Block,
    Or,
    And,
    Cmp,
    BitOr,
    BitXor,
    BitAnd,
    Shift,
    Add,
    Mul,
    Cast,
    Unary,
    Postfix,
    Atom,
}

/// A Rust binary operator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ROp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl ROp {
    pub fn symbol(self) -> &'static str {
        match self {
            ROp::Add => "+",
            ROp::Sub => "-",
            ROp::Mul => "*",
            ROp::Div => "/",
            ROp::Rem => "%",
            ROp::Eq => "==",
            ROp::Ne => "!=",
            ROp::Lt => "<",
            ROp::Le => "<=",
            ROp::Gt => ">",
            ROp::Ge => ">=",
            ROp::And => "&&",
            ROp::Or => "||",
        }
    }

    fn prec(self) -> Prec {
        match self {
            ROp::Add | ROp::Sub => Prec::Add,
            ROp::Mul | ROp::Div | ROp::Rem => Prec::Mul,
            ROp::Eq | ROp::Ne | ROp::Lt | ROp::Le | ROp::Gt | ROp::Ge => Prec::Cmp,
            ROp::And => Prec::And,
            ROp::Or => Prec::Or,
        }
    }
}

/// A structured Rust binding pattern for closures and statements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RPattern {
    Name(String),
    Tuple(Vec<RPattern>),
    Mut(Box<RPattern>),
}

impl RPattern {
    pub fn print(&self) -> String {
        match self {
            Self::Name(name) => name.clone(),
            Self::Tuple(items) => match items.as_slice() {
                [] => "()".into(),
                [item] => format!("({},)", item.print()),
                _ => format!("({})", items.iter().map(Self::print).collect::<Vec<_>>().join(", ")),
            },
            Self::Mut(pattern) => format!("mut {}", pattern.print()),
        }
    }
}

/// A Rust expression.
#[derive(Clone, Debug, PartialEq)]
pub enum RExpr {
    /// Rust code represented as raw text.
    Raw(String),
    /// A token or path that never needs parentheses: literal, identifier, `__str(3)`.
    Atom(String),
    /// A path with expression-position type arguments (`None::<T>`).
    Generic(String, Vec<RType>),
    /// `callee(args)` where the callee is a path (`lr::at`, `Some`, `f64::powf`).
    Call(String, Vec<RExpr>),
    /// `recv.name(args)`.
    Method(Box<RExpr>, String, Vec<RExpr>),
    /// `recv.name` (fields and tuple indices).
    Field(Box<RExpr>, String),
    /// `e?`.
    Try(Box<RExpr>),
    /// Prefix operator: `-`, `!`, `&`, `*`.
    Unary(&'static str, Box<RExpr>),
    Bin(ROp, Box<RExpr>, Box<RExpr>),
    /// `e as T`.
    Cast(Box<RExpr>, String),
    /// `()`, `(a,)`, `(a, b)`.
    Tuple(Vec<RExpr>),
    /// `[a, b]` (borrowed through `Unary("&", ..)` for slices).
    Array(Vec<RExpr>),
    /// `name![args]` (`vec!`).
    Macro(String, Vec<RExpr>),
    /// `{ stmts tail }`.
    Block(Vec<RStmt>, Box<RExpr>),
    /// `if c { a } else { b }`.
    If(Box<RExpr>, Box<RExpr>, Box<RExpr>),
    /// `match e { pat => arm, ... }`.
    Match(Box<RExpr>, Vec<(String, RExpr)>),
    /// `|params| body`.
    Closure(String, Box<RExpr>),
    /// Closure parameters represented as binding patterns.
    ClosurePattern(Vec<RPattern>, Box<RExpr>),
    /// Struct literal `Name { field: value, ... }`.
    Struct(String, Vec<(String, RExpr)>),
    /// `(*e)`: a captured variable bound by reference (always parenthesized).
    Deref(Box<RExpr>),
    /// `let pat = e`, the condition of `while let`.
    LetCond(String, Box<RExpr>),
    /// A source function value: an environment struct holding the captures,
    /// implementing `lr::Callable`.
    Env(Box<EnvFn>),
    /// A task body lowered to a future and spawned (captures moved in).
    Spawn(Box<SpawnFn>),
}

/// A function body: statements, then an optional tail expression.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct FnBody {
    pub stmts: Vec<RStmt>,
    pub tail: Option<RExpr>,
}

impl FnBody {
    pub fn print(&self) -> String {
        let mut s = body(&self.stmts);
        if let Some(t) = &self.tail {
            s.push_str(&t.full());
            s.push('\n');
        }
        s
    }
}

/// Closure environment: `struct Env { captures }` plus `impl lr::Callable`.
#[derive(Clone, Debug, PartialEq)]
pub struct EnvFn {
    pub env: String,
    /// Captured variables: field name and Rust type.
    pub fields: Vec<(String, String)>,
    /// Initial value of each field.
    pub inits: Vec<(String, RExpr)>,
    pub args_ty: String,
    pub rty: String,
    /// Statements run first (argument destructuring, capture bindings), printed on one line.
    pub prologue: Vec<RStmt>,
    pub body: FnBody,
}

/// A spawned task: `captures` are cloned before the `async move` block, `binds`
/// rebind them inside it.
#[derive(Clone, Debug, PartialEq)]
pub struct SpawnFn {
    pub captures: Vec<RStmt>,
    pub binds: Vec<RStmt>,
    pub body: FnBody,
}

/// A Rust statement.
#[derive(Clone, Debug, PartialEq)]
pub enum RStmt {
    /// A zero-argument unit-returning host function.
    Function { name: String, body: Vec<RStmt> },
    /// `let pat = init;` or `let pat: ty = init;`.
    Let(String, Option<String>, RExpr),
    /// A mutable identifier binding; mutability is syntax, not part of its name.
    LetMut(String, Option<String>, RExpr),
    /// `e;` (`let _ = e;` for a block-like `e`, whose value need not be `()`).
    Semi(RExpr),
    /// `place = value;`.
    Assign(RExpr, RExpr),
    /// `place += value;` (the operator is given with its `=`).
    OpAssign(RExpr, &'static str, RExpr),
    /// `let pat = e else { diverge };` (`diverge` is `continue`).
    LetElse(String, RExpr, RExpr),
    /// `'label: for pat in iter { .. }`.
    ForIn { label: Option<String>, pat: String, iter: RExpr, body: Vec<RStmt> },
    /// `return e;`.
    Return(RExpr),
    /// `{ stmts }`.
    Block(Vec<RStmt>),
    /// `if c { .. } else if c2 { .. } else { .. }`.
    If(Vec<(RExpr, Vec<RStmt>)>, Option<Vec<RStmt>>),
    /// `'label: while cond { .. }`, or `loop { .. }` without a condition.
    Loop { label: Option<String>, cond: Option<RExpr>, body: Vec<RStmt> },
    /// `'label: { .. }` (the target of `continue` lowered to `break 'label`).
    Labeled(String, Vec<RStmt>),
    /// `break;` / `break 'label;`.
    Break(Option<String>),
    /// `continue;` / `continue 'label;`.
    Continue(Option<String>),
    /// Unported statement text, printed as is (it carries its own `;`).
    Raw(String),
}

impl From<String> for RExpr {
    fn from(s: String) -> Self {
        RExpr::Raw(s)
    }
}

impl From<&str> for RExpr {
    fn from(s: &str) -> Self {
        RExpr::Raw(s.to_string())
    }
}

// Constructors

pub fn atom_e(s: impl Into<String>) -> RExpr {
    RExpr::Atom(s.into())
}

/// A literal or other token given as text: an atom unless it needs parentheses
/// as an operand (a negative number, `f64::NEG_INFINITY` does not).
pub fn token(s: impl Into<String>) -> RExpr {
    let s = s.into();
    if needs_paren(&s) {
        RExpr::Raw(s)
    } else {
        RExpr::Atom(s)
    }
}

pub fn call(callee: impl Into<String>, args: Vec<RExpr>) -> RExpr {
    RExpr::Call(callee.into(), args)
}

/// `path::<T>(args)`: a call with an explicit type argument.
pub fn call_generic(path: &str, ty: &RType, args: Vec<RExpr>) -> RExpr {
    RExpr::Call(format!("{path}::<{}>", ty.print()), args)
}

pub fn method(recv: impl Into<RExpr>, name: impl Into<String>, args: Vec<RExpr>) -> RExpr {
    RExpr::Method(Box::new(recv.into()), name.into(), args)
}

pub fn field(recv: impl Into<RExpr>, name: impl Into<String>) -> RExpr {
    RExpr::Field(Box::new(recv.into()), name.into())
}

pub fn try_(e: impl Into<RExpr>) -> RExpr {
    RExpr::Try(Box::new(e.into()))
}

pub fn unary(op: &'static str, e: impl Into<RExpr>) -> RExpr {
    RExpr::Unary(op, Box::new(e.into()))
}

pub fn borrow(e: impl Into<RExpr>) -> RExpr {
    unary("&", e)
}

pub fn bin(op: ROp, a: impl Into<RExpr>, b: impl Into<RExpr>) -> RExpr {
    RExpr::Bin(op, Box::new(a.into()), Box::new(b.into()))
}

pub fn cast(e: impl Into<RExpr>, ty: impl Into<String>) -> RExpr {
    RExpr::Cast(Box::new(e.into()), ty.into())
}

pub fn some(e: impl Into<RExpr>) -> RExpr {
    call("Some", vec![e.into()])
}

/// `lr::at(e, loc)?`: a runtime error from `e` gets the source position `loc`.
pub fn at(e: impl Into<RExpr>, loc: &str) -> RExpr {
    try_(call("lr::at", vec![e.into(), atom_e(loc)]))
}

/// `{ stmts tail }`, or just `tail` when there are no statements.
pub fn block(stmts: Vec<RStmt>, tail: impl Into<RExpr>) -> RExpr {
    let tail = tail.into();
    if stmts.is_empty() {
        tail
    } else {
        RExpr::Block(stmts, Box::new(tail))
    }
}

pub fn if_(c: impl Into<RExpr>, a: impl Into<RExpr>, b: impl Into<RExpr>) -> RExpr {
    RExpr::If(Box::new(c.into()), Box::new(a.into()), Box::new(b.into()))
}

pub fn match_(e: impl Into<RExpr>, arms: Vec<(String, RExpr)>) -> RExpr {
    RExpr::Match(Box::new(e.into()), arms)
}

pub fn closure(params: impl Into<String>, body: impl Into<RExpr>) -> RExpr {
    RExpr::Closure(params.into(), Box::new(body.into()))
}

pub fn deref(e: impl Into<RExpr>) -> RExpr {
    RExpr::Deref(Box::new(e.into()))
}

pub fn let_cond(pat: impl Into<String>, e: impl Into<RExpr>) -> RExpr {
    RExpr::LetCond(pat.into(), Box::new(e.into()))
}

pub fn let_(pat: impl Into<String>, init: impl Into<RExpr>) -> RStmt {
    RStmt::Let(pat.into(), None, init.into())
}

// Printing

impl RExpr {
    /// Precedence of the expression's outermost operator.
    pub fn prec(&self) -> Prec {
        match self {
            RExpr::Raw(s) => {
                if needs_paren(s) {
                    Prec::Block
                } else {
                    Prec::Atom
                }
            }
            RExpr::Atom(_) | RExpr::Generic(..) | RExpr::Call(..) | RExpr::Tuple(_) | RExpr::Array(_) | RExpr::Macro(..) | RExpr::Struct(..) | RExpr::Deref(_) => Prec::Atom,
            RExpr::Method(..) | RExpr::Field(..) | RExpr::Try(_) => Prec::Postfix,
            RExpr::Unary(..) => Prec::Unary,
            RExpr::Cast(..) => Prec::Cast,
            RExpr::Bin(op, ..) => op.prec(),
            RExpr::Block(..) | RExpr::If(..) | RExpr::Match(..) | RExpr::Closure(..) | RExpr::ClosurePattern(..) | RExpr::LetCond(..) | RExpr::Env(_) | RExpr::Spawn(_) => Prec::Block,
        }
    }

    /// Code as a complete expression (an argument, an initializer, a block tail):
    /// no parentheses around it.
    pub fn full(&self) -> String {
        match self {
            RExpr::Raw(s) => strip_text(s.clone()),
            _ => self.print(),
        }
    }

    /// Code as the operand of a postfix or prefix operator (`x.f()`, `&x`, `-x`).
    pub fn operand(&self) -> String {
        self.at_least(Prec::Postfix)
    }

    /// Code parenthesized unless its precedence is at least `p`.
    fn at_least(&self, p: Prec) -> String {
        match self {
            RExpr::Raw(s) => {
                if needs_paren(s) {
                    format!("({s})")
                } else {
                    s.clone()
                }
            }
            _ if self.prec() < p => format!("({})", self.print()),
            _ => self.print(),
        }
    }

    fn print(&self) -> String {
        match self {
            RExpr::Raw(s) | RExpr::Atom(s) => s.clone(),
            RExpr::Generic(name, args) => format!("{name}::<{}>", args.iter().map(RType::print).collect::<Vec<_>>().join(", ")),
            RExpr::Call(f, args) => format!("{f}({})", list(args)),
            RExpr::Method(r, m, args) => format!("{}.{m}({})", r.operand(), list(args)),
            RExpr::Field(r, f) => format!("{}.{f}", r.operand()),
            RExpr::Try(e) => format!("{}?", e.operand()),
            RExpr::Unary(op, e) => {
                // `-x` of a literal stays unparenthesized; any operator below a
                // prefix one is wrapped, and so is a nested prefix (`&(-x)`), as the
                // text generator did
                let inner = match &**e {
                    RExpr::Atom(_) | RExpr::Call(..) | RExpr::Method(..) | RExpr::Field(..) | RExpr::Try(_) => e.print(),
                    RExpr::Tuple(_) | RExpr::Array(_) | RExpr::Macro(..) | RExpr::Struct(..) => e.print(),
                    _ => e.at_least(Prec::Atom),
                };
                format!("{op}{inner}")
            }
            RExpr::Bin(op, a, b) => {
                let p = op.prec();
                let left = match (&**a, op) {
                    // `x as T < y` would parse `T<` as generics
                    (RExpr::Cast(..), ROp::Lt) => format!("({})", a.print()),
                    // comparisons do not chain
                    _ if p == Prec::Cmp => a.above(p),
                    _ => a.at_least(p),
                };
                let right = b.above(p);
                format!("{left} {} {right}", op.symbol())
            }
            RExpr::Cast(e, ty) => format!("{} as {ty}", e.at_least(Prec::Cast)),
            RExpr::Tuple(items) => match items.len() {
                0 => "()".into(),
                1 => format!("({},)", items[0].full()),
                _ => format!("({})", list(items)),
            },
            RExpr::Array(items) => format!("[{}]", list(items)),
            RExpr::Macro(name, items) => format!("{name}![{}]", list(items)),
            RExpr::Block(stmts, tail) => {
                let mut s = String::from("{ ");
                for st in stmts {
                    s.push_str(&st.print());
                    s.push(' ');
                }
                s.push_str(&tail.full());
                s.push_str(" }");
                s
            }
            RExpr::If(c, a, b) => {
                let els = match &**b {
                    // `else if` chains stay flat
                    RExpr::If(..) => b.print(),
                    _ => format!("{{ {} }}", b.full()),
                };
                format!("if {} {{ {} }} else {els}", c.full(), a.full())
            }
            RExpr::Match(e, arms) => {
                let arms: Vec<String> = arms.iter().map(|(p, x)| format!("{p} => {}", x.full())).collect();
                format!("match {} {{ {} }}", e.full(), arms.join(", "))
            }
            RExpr::Closure(ps, body) => format!("|{ps}| {}", body.full()),
            RExpr::ClosurePattern(ps, body) => format!("|{}| {}", ps.iter().map(RPattern::print).collect::<Vec<_>>().join(", "), body.full()),
            RExpr::Struct(name, fields) => {
                let fs: Vec<String> = fields.iter().map(|(f, x)| format!("{f}: {}", x.full())).collect();
                format!("{name} {{ {} }}", fs.join(", "))
            }
            RExpr::Deref(e) => format!("(*{})", e.print()),
            RExpr::LetCond(pat, e) => format!("let {pat} = {}", e.full()),
            RExpr::Env(f) => {
                let def = if f.fields.is_empty() {
                    format!("struct {};", f.env)
                } else {
                    let fs: Vec<String> = f.fields.iter().map(|(n, t)| format!("{n}: {t}")).collect();
                    format!("struct {} {{ {} }}", f.env, fs.join(", "))
                };
                let ctor = if f.inits.is_empty() {
                    f.env.clone()
                } else {
                    let is: Vec<String> = f.inits.iter().map(|(n, x)| format!("{n}: {}", x.full())).collect();
                    format!("{} {{ {} }}", f.env, is.join(", "))
                };
                let (env, args_ty, rty) = (&f.env, &f.args_ty, &f.rty);
                format!(
                    "{{\n#[derive(lr::Trace)]\n#[dumpster(crate = lr::gc::dumpster)]\n{def}\nimpl lr::Callable<{args_ty}, {rty}> for {env} {{\nfn call(&self, __this: &lr::LFn<{args_ty}, {rty}>, __args: {args_ty}) -> lr::LResult<{rty}> {{\n{}\n{}}}\n}}\nlr::LFn::new({ctor})\n}}",
                    one_line(&f.prologue),
                    f.body.print()
                )
            }
            RExpr::Spawn(f) => format!(
                "{{ {}lr::task::spawn(async move {{\n// the error type of the task's `?` operators\nif false {{ return Ok::<(), lr::LuaError>(()); }}\n{}\n{}}}) }}",
                one_line(&f.captures),
                one_line(&f.binds),
                f.body.print()
            ),
        }
    }

    /// `{ }`, `if`, `match` (also as raw text): at the start of a statement they
    /// would be parsed as a statement of their own.
    pub fn is_block_like(&self) -> bool {
        match self {
            RExpr::Block(..) | RExpr::If(..) | RExpr::Match(..) | RExpr::Env(_) | RExpr::Spawn(_) => true,
            RExpr::Raw(s) => s.starts_with('{') || s.starts_with("match ") || s.starts_with("if "),
            _ => false,
        }
    }

    /// Code parenthesized unless its precedence is strictly above `p` (the right
    /// operand of a left-associative operator, either side of a comparison).
    fn above(&self, p: Prec) -> String {
        match self {
            RExpr::Raw(_) => self.at_least(Prec::Atom),
            _ if self.prec() <= p => format!("({})", self.print()),
            _ => self.print(),
        }
    }
}

impl RStmt {
    pub fn print(&self) -> String {
        match self {
            RStmt::Function { name, body: b } => format!("fn {name}() {{\n{}}}", body(b)),
            RStmt::Let(p, None, e) => format!("let {p} = {};", e.full()),
            RStmt::Let(p, Some(t), e) => format!("let {p}: {t} = {};", e.full()),
            RStmt::LetMut(p, None, e) => format!("let mut {p} = {};", e.full()),
            RStmt::LetMut(p, Some(t), e) => format!("let mut {p}: {t} = {};", e.full()),
            RStmt::Semi(e) if e.is_block_like() => format!("let _ = {};", e.full()),
            RStmt::Semi(e) => format!("{};", e.full()),
            RStmt::Assign(p, e) => format!("{} = {};", p.full(), e.full()),
            RStmt::OpAssign(p, op, e) => format!("{} {op} {};", p.full(), e.full()),
            RStmt::LetElse(p, e, d) => format!("let {p} = {} else {{ {} }};", e.full(), d.full()),
            RStmt::ForIn { label, pat, iter, body: b } => {
                let label = label.as_ref().map(|l| format!("{l}: ")).unwrap_or_default();
                format!("{label}for {pat} in {} {{\n{}}}", iter.full(), body(b))
            }
            RStmt::Return(e) => format!("return {};", e.full()),
            RStmt::Raw(s) => s.clone(),
            RStmt::Block(b) => format!("{{\n{}}}", body(b)),
            RStmt::If(arms, els) => {
                let mut s = String::new();
                for (i, (c, b)) in arms.iter().enumerate() {
                    let kw = if i == 0 { "if" } else { " else if" };
                    s.push_str(&format!("{kw} {} {{\n{}}}", c.full(), body(b)));
                }
                if let Some(b) = els {
                    s.push_str(&format!(" else {{\n{}}}", body(b)));
                }
                s
            }
            RStmt::Loop { label, cond, body: b } => {
                let label = label.as_ref().map(|l| format!("{l}: ")).unwrap_or_default();
                match cond {
                    Some(c) => format!("{label}while {} {{\n{}}}", c.full(), body(b)),
                    None => format!("{label}loop {{\n{}}}", body(b)),
                }
            }
            RStmt::Labeled(l, b) => format!("{l}: {{\n{}}}", body(b)),
            RStmt::Break(None) => "break;".into(),
            RStmt::Break(Some(l)) => format!("break {l};"),
            RStmt::Continue(None) => "continue;".into(),
            RStmt::Continue(Some(l)) => format!("continue {l};"),
        }
    }
}

/// Statements each followed by a space: a prologue on one line.
fn one_line(stmts: &[RStmt]) -> String {
    stmts.iter().map(|s| s.print() + " ").collect()
}

/// Statements, one per line.
fn body(stmts: &[RStmt]) -> String {
    let mut s = String::new();
    for st in stmts {
        s.push_str(&st.print());
        s.push('\n');
    }
    s
}

impl std::fmt::Display for RExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.full())
    }
}

fn list(items: &[RExpr]) -> String {
    items.iter().map(|x| x.full()).collect::<Vec<_>>().join(", ")
}

/// Code usable as an operand (`x.f()`, `&x`, `-x`): parentheses unless it is atomic.
pub fn atom(code: impl Into<RExpr>) -> String {
    code.into().operand()
}

/// Code as a complete expression, without wrapping parentheses (avoids `unused_parens`).
pub fn strip(code: impl Into<RExpr>) -> String {
    code.into().full()
}

// Legacy text heuristics (raw code only)

/// True if raw `code` needs parentheses to be used as an operand.
fn needs_paren(code: &str) -> bool {
    if code.parse::<f64>().is_ok() && !code.starts_with('-') {
        return false;
    }
    let mut depth = 0i32;
    let mut in_str = false;
    let mut prev = ' ';
    let b: Vec<char> = code.chars().collect();
    for (i, &c) in b.iter().enumerate() {
        if in_str {
            if c == '"' && prev != '\\' {
                in_str = false;
            }
            prev = if prev == '\\' && c == '\\' { ' ' } else { c };
            continue;
        }
        match c {
            '"' => in_str = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ' ' | '+' | '*' | '/' | '%' | '<' | '>' | '=' | '!' | '&' | '|' if depth == 0 => {
                // `::<` turbofish and `->` inside types do not occur at depth 0 here
                return true;
            }
            '-' if depth == 0 => {
                if !(i > 0 && b[i - 1] == 'e') {
                    return true;
                }
            }
            _ => {}
        }
        prev = c;
    }
    code.starts_with('{') || code.starts_with("match ") || code.starts_with("if ")
}

/// Removes one pair of wrapping parentheses from raw code (avoids `unused_parens`).
fn strip_text(code: String) -> String {
    let b = code.as_bytes();
    if b.len() > 2 && b.first() == Some(&b'(') && b.last() == Some(&b')') {
        let mut depth = 0;
        let mut in_str = false;
        let mut esc = false;
        for (i, &c) in b.iter().enumerate() {
            if in_str {
                // `"a\\"` ends at its last quote: an escaped backslash escapes nothing
                if esc {
                    esc = false;
                } else if c == b'\\' {
                    esc = true;
                } else if c == b'"' {
                    in_str = false;
                }
                continue;
            }
            match c {
                b'"' => in_str = true,
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => {
                    depth -= 1;
                    if depth == 0 && i != b.len() - 1 {
                        return code;
                    }
                }
                // `(a, b)` is a tuple, not a parenthesized expression
                b',' if depth == 1 => return code,
                _ => {}
            }
        }
        return code[1..code.len() - 1].to_string();
    }
    code
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]

    fn host_entry_functions_are_structured() {
        let callback = closure("", block(vec![RStmt::Semi(try_(call("m0::require", vec![])))], call("Ok", vec![RExpr::Tuple(vec![])])));
        let entry = RStmt::Function { name: "main".into(), body: vec![RStmt::Semi(call("lr::run_main_coroutine", vec![callback]))] };
        assert_eq!(entry.print(), "fn main() {\nlr::run_main_coroutine(|| { m0::require()?; Ok(()) });\n}");
    }

    #[test]



    fn loop_headers_and_captures_are_structured() {
        assert_eq!(deref(atom_e("captured")).full(), "(*captured)");
        assert_eq!(method(deref(atom_e("captured")), "clone", vec![]).full(), "(*captured).clone()");
        let iter = method(atom_e("t"), "get_at", vec![atom_e("n")]);
        let loop_ = RStmt::Loop { label: Some("'l1".into()), cond: Some(let_cond("Some(v)", iter)), body: vec![RStmt::OpAssign(atom_e("n"), "+=", atom_e("1"))] };
        assert_eq!(loop_.print(), "'l1: while let Some(v) = t.get_at(n) {\nn += 1;\n}");
        let iter = RStmt::ForIn { label: None, pat: "k".into(), iter: method(atom_e("t"), "keys", vec![]), body: vec![RStmt::LetElse("Some(v)".into(), method(atom_e("t"), "get", vec![borrow(atom_e("k"))]), atom_e("continue"))] };
        assert_eq!(iter.print(), "for k in t.keys() {\nlet Some(v) = t.get(&k) else { continue };\n}");
    }

    #[test]
    fn closure_environments_and_tasks_preserve_their_layout() {
        let closure = RExpr::Env(Box::new(EnvFn {
            env: "Env1".into(), fields: vec![("n".into(), "f64".into())], inits: vec![("n".into(), atom_e("outer"))], args_ty: "()".into(), rty: "f64".into(), prologue: vec![let_("()", atom_e("__args")), let_("n", field(atom_e("self"), "n"))], body: FnBody { stmts: vec![RStmt::Return(call("Ok", vec![atom_e("n")]))], tail: None },
        }));
        assert_eq!(closure.full(), "{\n#[derive(lr::Trace)]\n#[dumpster(crate = lr::gc::dumpster)]\nstruct Env1 { n: f64 }\nimpl lr::Callable<(), f64> for Env1 {\nfn call(&self, __this: &lr::LFn<(), f64>, __args: ()) -> lr::LResult<f64> {\nlet () = __args; let n = self.n; \nreturn Ok(n);\n}\n}\nlr::LFn::new(Env1 { n: outer })\n}");
        let task = RExpr::Spawn(Box::new(SpawnFn { captures: vec![let_("cap", atom_e("outer"))], binds: vec![let_("n", atom_e("cap"))], body: FnBody { stmts: vec![], tail: Some(call("Ok", vec![RExpr::Tuple(vec![])])) } }));
        assert_eq!(task.full(), "{ let cap = outer; lr::task::spawn(async move {\n// the error type of the task's `?` operators\nif false { return Ok::<(), lr::LuaError>(()); }\nlet n = cap; \nOk(())\n}) }");
    }

    #[test]
    fn mutable_bindings_print_structurally() {
        assert_eq!(RStmt::LetMut("index".into(), Some("usize".into()), atom_e("0")).print(), "let mut index: usize = 0;");
        assert_eq!(RStmt::LetMut("iter".into(), None, call("iterator", vec![])).print(), "let mut iter = iterator();");
        assert_eq!(RStmt::Let("old".into(), None, atom_e("1")).print(), "let old = 1;");

    }

    #[test]
    fn generic_types_print_structurally_with_opaque_leaves() {
        let class = RType::Apply("lr::Rec".into(), vec![RType::Named("RClass".into())]);
        let record = RType::Apply("lr::MetaRec".into(), vec![RType::Named("RInstance".into()), class]);
        assert_eq!(record.print(), "lr::MetaRec<RInstance, lr::Rec<RClass>>");
        let optional = RType::Apply("Option".into(), vec![record]);
        assert_eq!(optional.print(), "Option<lr::MetaRec<RInstance, lr::Rec<RClass>>>");
        assert_eq!(RType::Named("lr::LFn<(f64,), lr::LResult<()>>".into()).print(), "lr::LFn<(f64,), lr::LResult<()>>");
        assert_eq!(RType::Apply("RPlain".into(), vec![]).print(), "RPlain");
    }

    #[test]
    fn generic_expression_paths_print_structured_type_arguments() {
        let ty = RType::Apply("lr::Rec".into(), vec![RType::Named("RClass".into())]);
        let none = RExpr::Generic("None".into(), vec![ty]);
        assert_eq!(none.full(), "None::<lr::Rec<RClass>>");
        assert_eq!(method(none, "is_none", vec![]).full(), "None::<lr::Rec<RClass>>.is_none()");
    }

    #[test]
    fn calls_with_an_explicit_type_argument() {
        let ty = RType::Apply("lr::Arr".into(), vec![RType::Named("f64".into())]);
        let c = call_generic("lr::dynamic::cast", &ty, vec![borrow(atom_e("v")), atom_e("\"{number}\"")]);
        assert_eq!(c.full(), "lr::dynamic::cast::<lr::Arr<f64>>(&v, \"{number}\")");
        assert_eq!(at(c, "\"m.luarc:3\"").full(), "lr::at(lr::dynamic::cast::<lr::Arr<f64>>(&v, \"{number}\"), \"m.luarc:3\")?");
    }

    fn a(s: &str) -> RExpr {
        atom_e(s)
    }

    #[test]
    fn precedence_parenthesizes_only_where_needed() {
        let sum = bin(ROp::Add, a("x"), a("y"));
        assert_eq!(bin(ROp::Mul, sum.clone(), a("z")).full(), "(x + y) * z");
        assert_eq!(bin(ROp::Add, bin(ROp::Mul, a("x"), a("y")), a("z")).full(), "x * y + z");
        // left associative: a - (b - c) keeps its parentheses, (a - b) - c does not need them
        assert_eq!(bin(ROp::Sub, a("a"), bin(ROp::Sub, a("b"), a("c"))).full(), "a - (b - c)");
        assert_eq!(bin(ROp::Sub, bin(ROp::Sub, a("a"), a("b")), a("c")).full(), "a - b - c");
        // comparisons do not chain
        assert_eq!(bin(ROp::Eq, bin(ROp::Lt, a("a"), a("b")), a("t")).full(), "(a < b) == t");
        assert_eq!(method(sum.clone(), "len", vec![]).full(), "(x + y).len()");
        assert_eq!(unary("-", sum).full(), "-(x + y)");
        assert_eq!(unary("&", unary("-", a("x"))).full(), "&(-x)");
        assert_eq!(bin(ROp::Lt, cast(a("n"), "f64"), a("m")).full(), "(n as f64) < m");
    }

    #[test]
    fn block_like_operands_are_wrapped() {
        let b = block(vec![let_("t", a("1.0"))], a("t"));
        assert_eq!(bin(ROp::Add, b.clone(), a("2.0")).full(), "({ let t = 1.0; t }) + 2.0");
        assert_eq!(b.full(), "{ let t = 1.0; t }");
        assert_eq!(some(b).full(), "Some({ let t = 1.0; t })");
    }

    #[test]
    fn raw_code_keeps_the_text_heuristics() {
        assert_eq!(atom("a + b".to_string()), "(a + b)");
        assert_eq!(atom("x.len()".to_string()), "x.len()");
        assert_eq!(strip("(a + b)".to_string()), "a + b");
        assert_eq!(strip("(a, b)".to_string()), "(a, b)");
        // a string literal containing an operator is one token
        assert_eq!(strip("(\"a\\\\\")".to_string()), "\"a\\\\\"");
        assert_eq!(bin(ROp::Add, RExpr::Raw("a * b".into()), a("c")).full(), "(a * b) + c");
    }
}

#[cfg(test)]
mod pattern_tests {
    use super::*;
    #[test]
    fn structural_closure_patterns_keep_tuple_arity() {
        let name = |s: &str| RPattern::Name(s.into());
        let closure = |patterns| RExpr::ClosurePattern(patterns, Box::new(atom_e("body"))).full();
        assert_eq!(closure(vec![]), "|| body");
        assert_eq!(closure(vec![name("x")]), "|x| body");
        assert_eq!(closure(vec![RPattern::Tuple(vec![])]), "|()| body");
        assert_eq!(closure(vec![RPattern::Tuple(vec![name("x")])]), "|(x,)| body");
        assert_eq!(closure(vec![RPattern::Tuple(vec![name("x"), RPattern::Tuple(vec![name("y")])])]), "|(x, (y,))| body");
        assert_eq!(closure(vec![RPattern::Mut(Box::new(name("x"))), name("y")]), "|mut x, y| body");
    }
}
