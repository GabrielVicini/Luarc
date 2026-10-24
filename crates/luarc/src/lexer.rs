//! Handwritten lexer for the Luau-style source language.

use crate::diag::{err, DResult, Span};
use crate::ast::ModuleOptions;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Name(String),
    Number(f64),
    /// An integer literal above 2^53 (not exactly representable as a number).
    Int(i128),
    Str(Vec<u8>),
    /// Interpolated string: alternating literal pieces and expression source spans.
    Interp(Vec<InterpPiece>),
    Kw(Kw),
    Op(&'static str),
    Eof,
}

#[cfg(test)]
mod source_options_tests {
    use super::*;

    fn optimization(source: &str) -> Option<u8> {
        lex_with_options(0, source).expect("source options fixture").1.oracle_optimization
    }

    #[test]
    fn only_header_line_hotcomments_change_oracle_options() {
        for source in [
            "--!optimize 0\nlocal x=1",
            "\n \t-- ordinary\n--[=[comment]=]\n--!optimize 0\r\nlocal x=1",
        ] { assert_eq!(optimization(source), Some(0), "{source:?}"); }
        for source in [
            "local x=1\n--!optimize 0",
            "-- !optimize 0\nlocal x=1",
            "--! optimize 0\nlocal x=1",
            "--!optimize\t0\nlocal x=1",
            "--[[!optimize 0]]\nlocal x=1",
            "--[=[\n--!optimize 0\n]=]\nlocal x=1",
            "local x='--!optimize 0'",
            "local x=[=[--!optimize 0]=]",
            "local x=`a{1 --!optimize 0\n}`",
        ] { assert_eq!(optimization(source), Some(1), "{source:?}"); }
    }

    #[test]
    fn hotcomments_follow_luau_precedence_and_atoi_prefixes() {
        for (header, expected) in [
            ("--!optimize 0\n--!optimize 1\n", Some(1)),
            ("--!optimize 1\n--!optimize 0\n", Some(0)),
            ("--!optimize 0\n--!native\n", Some(2)),
            ("--!native\n--!optimize 0\n", Some(0)),
            ("--!optimize foo\n", Some(0)),
            ("--!optimize \n", Some(1)),
            ("--!optimize 0\n--!optimize \n", Some(0)),
            ("--!optimize -1\n", Some(0)),
            ("--!optimize 3\n", Some(2)),
            ("--!optimize 0suffix\n", Some(0)),
            ("--!optimize  +2suffix\n", Some(2)),
            ("--!optimize 999999999999999999999\n", None),
            ("--!optimize 999999999999999999999\n--!optimize 1\n", Some(1)),
        ] { assert_eq!(optimization(header), expected, "{header:?}"); }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum InterpPiece {
    Lit(Vec<u8>),
    /// Tokens of an embedded `{expr}`.
    Expr(Vec<Token>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kw {
    And,
    Break,
    Do,
    Else,
    Elseif,
    End,
    False,
    For,
    Function,
    If,
    In,
    Local,
    Nil,
    Not,
    Or,
    Repeat,
    Return,
    Then,
    True,
    Until,
    While,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

const OPS: &[&str] = &[
    "...", "..=", "//=", "==", "~=", "<=", ">=", "//", "..", "::", "->", "+=", "-=", "*=", "/=", "%=", "^=", "+", "-",
    "*", "/", "%", "^", "#", "<", ">", "=", "(", ")", "{", "}", "[", "]", ";", ":", ",", ".", "?", "|", "&",
];

fn keyword(s: &str) -> Option<Kw> {
    Some(match s {
        "and" => Kw::And,
        "break" => Kw::Break,
        "do" => Kw::Do,
        "else" => Kw::Else,
        "elseif" => Kw::Elseif,
        "end" => Kw::End,
        "false" => Kw::False,
        "for" => Kw::For,
        "function" => Kw::Function,
        "if" => Kw::If,
        "in" => Kw::In,
        "local" => Kw::Local,
        "nil" => Kw::Nil,
        "not" => Kw::Not,
        "or" => Kw::Or,
        "repeat" => Kw::Repeat,
        "return" => Kw::Return,
        "then" => Kw::Then,
        "true" => Kw::True,
        "until" => Kw::Until,
        "while" => Kw::While,
        _ => return None,
    })
}

struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    line: u32,
    col: u32,
    file: u32,
    header: bool,
    options: ModuleOptions,
}

pub fn lex(file: u32, text: &str) -> DResult<Vec<Token>> {
    lex_with_options(file, text).map(|(tokens, _)| tokens)
}

pub fn lex_with_options(file: u32, text: &str) -> DResult<(Vec<Token>, ModuleOptions)> {
    let mut lx = Lexer { src: text.as_bytes(), pos: 0, line: 1, col: 1, file, header: true, options: ModuleOptions::default() };
    let mut out = Vec::new();
    loop {
        let t = lx.next_token()?;
        let eof = t.tok == Tok::Eof;
        out.push(t);
        if eof {
            return Ok((out, lx.options));
        }
    }
}

/// Luau 0.743 trims hotcomment tails, applies header directives in source order,
/// and clamps an atoi-style optimize argument to 0..2; native resets it to O2.
fn hotcomment_optimization(comment: &[u8]) -> Option<Option<u8>> {
    let comment = comment.trim_ascii_end();
    if comment == b"native" { return Some(Some(2)); }
    let value = comment.strip_prefix(b"optimize ")?.trim_ascii_start();
    let start = usize::from(matches!(value.first(), Some(b'+' | b'-')));
    let digits = value[start..].iter().take_while(|b| b.is_ascii_digit()).count();
    if digits == 0 { return Some(Some(0)); }
    // C atoi overflow has no portable identity guarantee: keep literal and
    // retained-key proofs, but diagnose computed strings for an unknown level.
    let number = std::str::from_utf8(&value[..start + digits]).ok()?.parse::<i32>().ok();
    Some(number.map(|n| n.clamp(0, 2) as u8))
}

impl<'a> Lexer<'a> {
    fn span(&self) -> Span {
        Span { file: self.file, line: self.line, col: self.col }
    }
    fn peek(&self, k: usize) -> u8 {
        *self.src.get(self.pos + k).unwrap_or(&0)
    }
    fn bump(&mut self) -> u8 {
        let c = self.peek(0);
        self.pos += 1;
        if c == b'\n' {
            self.line += 1;
            self.col = 1;
        } else if c & 0xC0 != 0x80 {
            self.col += 1;
        }
        c
    }
    fn at_end(&self) -> bool {
        self.pos >= self.src.len()
    }

    /// `[[`, `[==[` → level; None if not a long bracket.
    fn long_bracket_level(&self) -> Option<usize> {
        if self.peek(0) != b'[' {
            return None;
        }
        let mut k = 1;
        while self.peek(k) == b'=' {
            k += 1;
        }
        if self.peek(k) == b'[' {
            Some(k - 1)
        } else {
            None
        }
    }

    fn long_string(&mut self, level: usize) -> DResult<Vec<u8>> {
        let start = self.span();
        for _ in 0..level + 2 {
            self.bump();
        }
        // A newline right after the opening bracket is skipped. Like Luau 0.743, a
        // newline is `\n` or `\r\n`; a lone `\r` is content, and `\r\n` inside the
        // string reads as `\n`, so CRLF checkouts keep the same contents.
        if self.peek(0) == b'\r' && self.peek(1) == b'\n' {
            self.bump();
        }
        if self.peek(0) == b'\n' {
            self.bump();
        }
        let mut out = Vec::new();
        loop {
            if self.at_end() {
                return err(start, "unfinished long string/comment");
            }
            if self.peek(0) == b']' {
                let mut k = 1;
                while self.peek(k) == b'=' {
                    k += 1;
                }
                if k - 1 == level && self.peek(k) == b']' {
                    for _ in 0..level + 2 {
                        self.bump();
                    }
                    return Ok(out);
                }
            }
            if self.peek(0) == b'\r' && self.peek(1) == b'\n' {
                self.bump();
            }
            out.push(self.bump());
        }
    }

    fn skip_trivia(&mut self) -> DResult<()> {
        loop {
            let c = self.peek(0);
            if c == b' ' || c == b'\t' || c == b'\r' || c == b'\n' {
                self.bump();
            } else if c == b'-' && self.peek(1) == b'-' {
                self.bump();
                self.bump();
                if let Some(level) = self.long_bracket_level() {
                    self.long_string(level)?;
                } else {
                    let start = self.pos;
                    while !self.at_end() && self.peek(0) != b'\n' {
                        self.bump();
                    }
                    if self.header && self.src.get(start) == Some(&b'!') {
                        if let Some(level) = hotcomment_optimization(&self.src[start + 1..self.pos]) {
                            self.options.oracle_optimization = level;
                        }
                    }
                }
            } else {
                return Ok(());
            }
        }
    }

    fn next_token(&mut self) -> DResult<Token> {
        self.skip_trivia()?;
        let span = self.span();
        if self.at_end() {
            return Ok(Token { tok: Tok::Eof, span });
        }
        self.header = false;
        let c = self.peek(0);
        let tok = if c.is_ascii_alphabetic() || c == b'_' {
            let start = self.pos;
            while self.peek(0).is_ascii_alphanumeric() || self.peek(0) == b'_' {
                self.bump();
            }
            let s = std::str::from_utf8(&self.src[start..self.pos]).unwrap().to_string();
            match keyword(&s) {
                Some(k) => Tok::Kw(k),
                None => Tok::Name(s),
            }
        } else if c.is_ascii_digit() || (c == b'.' && self.peek(1).is_ascii_digit()) {
            match self.number(span)? {
                Ok(f) => Tok::Number(f),
                Err(i) => Tok::Int(i),
            }
        } else if c == b'"' || c == b'\'' {
            Tok::Str(self.short_string(span)?)
        } else if c == b'`' {
            Tok::Interp(self.interp_string(span)?)
        } else if let Some(level) = self.long_bracket_level() {
            Tok::Str(self.long_string(level)?)
        } else {
            let rest = &self.src[self.pos..];
            match OPS.iter().find(|op| rest.starts_with(op.as_bytes())) {
                Some(op) => {
                    for _ in 0..op.len() {
                        self.bump();
                    }
                    Tok::Op(op)
                }
                None => return err(span, format!("unexpected character '{}'", c as char)),
            }
        };
        Ok(Token { tok, span })
    }

    /// A numeric literal: `Ok(number)`, or `Err(integer)` for an integer literal
    /// whose value a number would round (above 2^53).
    fn number(&mut self, span: Span) -> DResult<Result<f64, i128>> {
        let start = self.pos;
        let text = |lx: &Self| -> String {
            std::str::from_utf8(&lx.src[start..lx.pos]).unwrap().chars().filter(|&c| c != '_').collect()
        };
        if self.peek(0) == b'0' && matches!(self.peek(1), b'x' | b'X' | b'b' | b'B') {
            let radix = if matches!(self.peek(1), b'x' | b'X') { 16 } else { 2 };
            self.bump();
            self.bump();
            let ds = self.pos;
            while self.peek(0).is_ascii_alphanumeric() || self.peek(0) == b'_' {
                self.bump();
            }
            let digits: String = std::str::from_utf8(&self.src[ds..self.pos]).unwrap().chars().filter(|&c| c != '_').collect();
            if digits.is_empty() {
                return err(span, "malformed number");
            }
            let mut v = 0f64;
            let mut exact: Option<i128> = Some(0);
            for ch in digits.chars() {
                match ch.to_digit(radix) {
                    Some(d) => {
                        v = v * radix as f64 + d as f64;
                        exact = exact.and_then(|e| e.checked_mul(radix as i128)).and_then(|e| e.checked_add(d as i128));
                    }
                    None => return err(span, format!("malformed number '{}'", text(self))),
                }
            }
            return Ok(match exact {
                Some(i) if i > (1i128 << 53) => Err(i),
                _ => Ok(v),
            });
        }
        while self.peek(0).is_ascii_digit() || self.peek(0) == b'_' {
            self.bump();
        }
        if self.peek(0) == b'.' && self.peek(1) != b'.' {
            self.bump();
            while self.peek(0).is_ascii_digit() || self.peek(0) == b'_' {
                self.bump();
            }
        }
        if matches!(self.peek(0), b'e' | b'E') {
            self.bump();
            if matches!(self.peek(0), b'+' | b'-') {
                self.bump();
            }
            while self.peek(0).is_ascii_digit() {
                self.bump();
            }
        }
        if self.peek(0).is_ascii_alphabetic() || self.peek(0) == b'_' {
            while self.peek(0).is_ascii_alphanumeric() {
                self.bump();
            }
            return err(span, format!("malformed number '{}'", text(self)));
        }
        let t = text(self);
        if t.bytes().all(|b| b.is_ascii_digit()) {
            if let Ok(i) = t.parse::<i128>() {
                if i > (1i128 << 53) {
                    return Ok(Err(i));
                }
            }
        }
        t.parse::<f64>().map(Ok).or_else(|_| err(span, format!("malformed number '{}'", text(self))))
    }

    fn escape(&mut self, span: Span, out: &mut Vec<u8>) -> DResult<()> {
        let c = self.bump();
        match c {
            b'n' => out.push(b'\n'),
            b't' => out.push(b'\t'),
            b'r' => out.push(b'\r'),
            b'a' => out.push(7),
            b'b' => out.push(8),
            b'f' => out.push(12),
            b'v' => out.push(11),
            b'\\' | b'"' | b'\'' | b'`' | b'{' | b'}' => out.push(c),
            b'\n' => out.push(b'\n'),
            b'\r' => {
                if self.peek(0) == b'\n' {
                    self.bump();
                }
                out.push(b'\n')
            }
            b'z' => {
                while matches!(self.peek(0), b' ' | b'\t' | b'\r' | b'\n') {
                    self.bump();
                }
            }
            b'x' => {
                let h = [self.bump(), self.bump()];
                let s = std::str::from_utf8(&h).unwrap_or("");
                match u8::from_str_radix(s, 16) {
                    Ok(v) => out.push(v),
                    Err(_) => return err(span, "invalid \\x escape (expected two hex digits)"),
                }
            }
            b'u' => {
                if self.bump() != b'{' {
                    return err(span, "invalid \\u escape (expected '{')");
                }
                let mut v: u32 = 0;
                while self.peek(0) != b'}' {
                    let d = (self.bump() as char).to_digit(16);
                    match d {
                        Some(d) if v < 0x110000 => v = v * 16 + d,
                        _ => return err(span, "invalid \\u escape"),
                    }
                }
                self.bump();
                match char::from_u32(v) {
                    Some(ch) => out.extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
                    None => return err(span, "invalid \\u escape (not a Unicode scalar value)"),
                }
            }
            b'0'..=b'9' => {
                let mut v = (c - b'0') as u32;
                for _ in 0..2 {
                    if self.peek(0).is_ascii_digit() {
                        v = v * 10 + (self.bump() - b'0') as u32;
                    }
                }
                if v > 255 {
                    return err(span, "decimal escape too large");
                }
                out.push(v as u8);
            }
            _ => return err(span, format!("invalid escape sequence '\\{}'", c as char)),
        }
        Ok(())
    }

    fn short_string(&mut self, span: Span) -> DResult<Vec<u8>> {
        let q = self.bump();
        let mut out = Vec::new();
        loop {
            if self.at_end() || self.peek(0) == b'\n' {
                return err(span, "unfinished string");
            }
            let c = self.bump();
            if c == q {
                return Ok(out);
            }
            if c == b'\\' {
                self.escape(span, &mut out)?;
            } else {
                out.push(c);
            }
        }
    }

    fn interp_string(&mut self, span: Span) -> DResult<Vec<InterpPiece>> {
        self.bump();
        let mut pieces = Vec::new();
        let mut lit = Vec::new();
        loop {
            if self.at_end() {
                return err(span, "unfinished interpolated string");
            }
            let c = self.bump();
            match c {
                b'`' => {
                    pieces.push(InterpPiece::Lit(lit));
                    return Ok(pieces);
                }
                b'\\' => self.escape(span, &mut lit)?,
                b'{' => {
                    pieces.push(InterpPiece::Lit(std::mem::take(&mut lit)));
                    let mut toks = Vec::new();
                    let mut depth = 0;
                    loop {
                        let t = self.next_token()?;
                        match &t.tok {
                            Tok::Eof => return err(span, "unfinished interpolation expression"),
                            Tok::Op("{") => depth += 1,
                            Tok::Op("}") if depth == 0 => break,
                            Tok::Op("}") => depth -= 1,
                            _ => {}
                        }
                        toks.push(t);
                    }
                    if toks.is_empty() {
                        return err(span, "empty interpolation expression");
                    }
                    let end = toks.last().unwrap().span;
                    toks.push(Token { tok: Tok::Eof, span: end });
                    pieces.push(InterpPiece::Expr(toks));
                }
                _ => lit.push(c),
            }
        }
    }
}
