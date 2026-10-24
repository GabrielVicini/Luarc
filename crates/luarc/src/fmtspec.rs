//! Parsing of literal `string.format` strings into directives.
//!
//! The grammar is the reference's: `%` flags (`-+ #0`), a width and a
//! precision of at most two digits each, then one of `c d i o u x X e E f g G
//! q s` or `%%`. The runtime renders the result (`luarc_runtime::fmt`).

/// What a directive formats; decides the argument type and the runtime call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Conv {
    /// `%d %i`
    Signed,
    /// `%u %o %x %X`; the letter selects the base
    Unsigned(u8),
    /// `%c`
    Char,
    /// `%e %E %f %g %G`; the letter selects the form
    Float(u8),
    /// `%s`
    Str,
    /// `%q`
    Quoted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Directive {
    pub conv: Conv,
    /// bit set using the runtime's flag values
    pub flags: u8,
    pub width: u8,
    pub prec: Option<u8>,
}

impl Directive {
    /// The Rust expression for the runtime's `Spec` constant.
    pub fn spec_expr(&self) -> String {
        let names = [(1, "LEFT"), (2, "PLUS"), (4, "SPACE"), (8, "ALT"), (16, "ZERO")];
        let flags: Vec<String> = names.iter().filter(|(b, _)| self.flags & b != 0).map(|(_, n)| format!("lr::fmt::{n}")).collect();
        let flags = if flags.is_empty() { "0".to_string() } else { flags.join(" | ") };
        let prec = self.prec.map_or("None".to_string(), |p| format!("Some({p})"));
        format!("lr::fmt::Spec {{ flags: {flags}, width: {}, prec: {prec} }}", self.width)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FmtPiece {
    Lit(String),
    Arg(Directive),
}

/// Splits a format string into literal text and directives.
pub fn parse(fmt: &str) -> Result<Vec<FmtPiece>, String> {
    let mut pieces = Vec::new();
    let mut lit = String::new();
    let mut chars = fmt.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '%' {
            lit.push(c);
            continue;
        }
        let mut flags = 0u8;
        let mut spec = String::new();
        while let Some(&d) = chars.peek() {
            let bit = match d {
                '-' => 1,
                '+' => 2,
                ' ' => 4,
                '#' => 8,
                '0' => 16,
                _ => break,
            };
            flags |= bit;
            spec.push(d);
            chars.next();
        }
        let number = |chars: &mut std::iter::Peekable<std::str::Chars>, spec: &mut String| -> Result<Option<u8>, String> {
            let mut digits = String::new();
            while let Some(&d) = chars.peek().filter(|d| d.is_ascii_digit()) {
                digits.push(d);
                spec.push(d);
                chars.next();
            }
            match digits.len() {
                0 => Ok(None),
                1 | 2 => Ok(Some(digits.parse().expect("two digits fit in u8"))),
                _ => Err("invalid format (width or precision more than 2 digits)".to_string()),
            }
        };
        let width = number(&mut chars, &mut spec)?;
        let prec = if chars.peek() == Some(&'.') {
            chars.next();
            spec.push('.');
            Some(number(&mut chars, &mut spec)?.unwrap_or(0))
        } else {
            None
        };
        let conv = match chars.next() {
            Some('%') if spec.is_empty() => {
                lit.push('%');
                continue;
            }
            Some('d' | 'i') => Conv::Signed,
            Some(c @ ('u' | 'o' | 'x' | 'X')) => Conv::Unsigned(c as u8),
            Some('c') => Conv::Char,
            Some(c @ ('e' | 'E' | 'f' | 'g' | 'G')) => Conv::Float(c as u8),
            Some('s') => Conv::Str,
            Some('q') => Conv::Quoted,
            other => {
                let shown = other.map(String::from).unwrap_or_default();
                return Err(format!("unsupported format directive '%{spec}{shown}' (supported: %c %d %i %o %u %x %X %e %E %f %g %G %q %s %%)"));
            }
        };
        if !lit.is_empty() {
            pieces.push(FmtPiece::Lit(std::mem::take(&mut lit)));
        }
        pieces.push(FmtPiece::Arg(Directive { conv, flags, width: width.unwrap_or(0), prec }));
    }
    if !lit.is_empty() {
        pieces.push(FmtPiece::Lit(lit));
    }
    Ok(pieces)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dir(s: &str) -> Directive {
        match parse(s).unwrap().as_slice() {
            [FmtPiece::Arg(d)] => d.clone(),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn modifiers() {
        let d = dir("%-08.3e");
        assert_eq!((d.conv, d.flags, d.width, d.prec), (Conv::Float(b'e'), 1 | 16, 8, Some(3)));
        assert_eq!(dir("%.f").prec, Some(0));
        assert_eq!(dir("%5d").prec, None);
        assert_eq!(dir("%x").conv, Conv::Unsigned(b'x'));
        assert_eq!(dir("%i").conv, Conv::Signed);
    }

    #[test]
    fn literals_and_percent() {
        let p = parse("a%%b%sc").unwrap();
        assert_eq!(p.len(), 3);
        assert_eq!(p[0], FmtPiece::Lit("a%b".into()));
        assert_eq!(p[2], FmtPiece::Lit("c".into()));
    }

    #[test]
    fn rejects() {
        assert!(parse("%a").unwrap_err().contains("'%a'"));
        assert!(parse("%5%").unwrap_err().contains("'%5%'"));
        assert!(parse("%").unwrap_err().contains("'%'"));
        assert!(parse("%123d").unwrap_err().contains("2 digits"));
        assert!(parse("%.123f").unwrap_err().contains("2 digits"));
        assert!(parse("%F").is_err());
        assert!(parse("%ld").is_err());
    }

    #[test]
    fn spec_expression() {
        assert_eq!(dir("%-08.3e").spec_expr(), "lr::fmt::Spec { flags: lr::fmt::LEFT | lr::fmt::ZERO, width: 8, prec: Some(3) }");
        assert_eq!(dir("%d").spec_expr(), "lr::fmt::Spec { flags: 0, width: 0, prec: None }");
    }
}
