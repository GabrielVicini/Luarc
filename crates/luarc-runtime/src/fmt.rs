//! `string.format` directives.
//!
//! The compiler parses the literal format string and passes each directive's
//! flags, width and precision as a [`Spec`] constant; this module renders one
//! directive at a time into the output buffer with C `printf` semantics (the
//! reference implementation delegates to `snprintf`). Differences from C are
//! limited to what has no portable answer: NaN prints as `nan` whatever its
//! sign and payload, and `%a` is not offered (Luau 0.743 rejects it too).

use crate::error::{LResult, LuaError};
use crate::show::LuaDisplay;
use crate::value::LStr;
use std::io::Write;

pub const LEFT: u8 = 1;
pub const PLUS: u8 = 2;
pub const SPACE: u8 = 4;
pub const ALT: u8 = 8;
pub const ZERO: u8 = 16;

/// Flags, width and precision of one directive (`%-08.3f`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Spec {
    pub flags: u8,
    pub width: u8,
    pub prec: Option<u8>,
}

impl Spec {
    pub const PLAIN: Spec = Spec { flags: 0, width: 0, prec: None };

    fn has(self, flag: u8) -> bool {
        self.flags & flag != 0
    }
}

/// An argument of an integer directive: a float (truncated toward zero, with
/// the x86-64 "integer indefinite" value for NaN and out-of-range numbers, as
/// the reference prints them) or an exact integer.
pub trait IntArg: Copy {
    fn signed(self) -> i128;
    /// The two's complement 64-bit pattern `%x %o %u %c` print.
    fn bits(self) -> u64;
}

impl IntArg for f64 {
    fn signed(self) -> i128 {
        // `as` saturates and maps NaN to 0, neither of which is what is wanted
        if self.is_finite() && (-9223372036854775808.0..9223372036854775808.0).contains(&self) {
            self as i64 as i128
        } else {
            i64::MIN as i128
        }
    }
    fn bits(self) -> u64 {
        self.signed() as i64 as u64
    }
}

impl IntArg for i128 {
    fn signed(self) -> i128 {
        self
    }
    fn bits(self) -> u64 {
        self as u64
    }
}

/// A numeric string given to a number directive (`string.format("%d", "10")`).
/// `pos` is the argument's position in the call, counting the format string.
pub fn number_arg(s: &LStr, pos: usize) -> LResult<f64> {
    crate::stdlib::tonumber(s).ok_or_else(|| LuaError::new(format!("invalid argument #{pos} to 'format' (number expected, got string)")))
}

/// Appends `prefix`, `body` padded to the directive's width. Zero padding goes
/// between prefix (sign, `0x`) and body, and only where the caller allows it.
fn pad(out: &mut Vec<u8>, spec: Spec, prefix: &[u8], body: &[u8], zero_ok: bool) {
    let len = prefix.len() + body.len();
    let fill = (spec.width as usize).saturating_sub(len);
    if spec.has(LEFT) {
        out.extend_from_slice(prefix);
        out.extend_from_slice(body);
        out.resize(out.len() + fill, b' ');
    } else if spec.has(ZERO) && zero_ok {
        out.extend_from_slice(prefix);
        out.resize(out.len() + fill, b'0');
        out.extend_from_slice(body);
    } else {
        out.resize(out.len() + fill, b' ');
        out.extend_from_slice(prefix);
        out.extend_from_slice(body);
    }
}

/// `%d` and `%i`.
pub fn signed(out: &mut Vec<u8>, spec: Spec, v: impl IntArg) {
    let v = v.signed();
    let digits = digits_of(v.unsigned_abs(), 10, false, spec.prec);
    let sign: &[u8] = if v < 0 {
        b"-"
    } else if spec.has(PLUS) {
        b"+"
    } else if spec.has(SPACE) {
        b" "
    } else {
        b""
    };
    pad(out, spec, sign, &digits, spec.prec.is_none());
}

/// `%u %o %x %X` (`conv` is the directive letter).
pub fn unsigned(out: &mut Vec<u8>, spec: Spec, conv: u8, v: impl IntArg) {
    let v = v.bits();
    let (base, upper) = match conv {
        b'o' => (8, false),
        b'x' => (16, false),
        b'X' => (16, true),
        _ => (10, false),
    };
    let mut digits = digits_of(v as u128, base, upper, spec.prec);
    let mut prefix: &[u8] = b"";
    if spec.has(ALT) {
        match conv {
            b'o' if digits.first() != Some(&b'0') => digits.insert(0, b'0'),
            b'x' if v != 0 => prefix = b"0x",
            b'X' if v != 0 => prefix = b"0X",
            _ => {}
        }
    }
    pad(out, spec, prefix, &digits, spec.prec.is_none());
}

/// Digits of `v` in `base`, zero-extended to the precision. A zero value with
/// precision 0 has no digits, as in C.
fn digits_of(v: u128, base: u32, upper: bool, prec: Option<u8>) -> Vec<u8> {
    let mut d = match (v, base) {
        (0, _) => Vec::new(),
        (_, 10) => v.to_string().into_bytes(),
        (_, 8) => format!("{v:o}").into_bytes(),
        (_, _) if upper => format!("{v:X}").into_bytes(),
        _ => format!("{v:x}").into_bytes(),
    };
    let want = match prec {
        Some(p) => p as usize,
        None => 1,
    };
    if d.len() < want {
        let mut z = vec![b'0'; want - d.len()];
        z.append(&mut d);
        d = z;
    }
    d
}

/// `%c`: the low byte of the value.
pub fn char_(out: &mut Vec<u8>, spec: Spec, v: impl IntArg) {
    pad(out, spec, b"", &[v.bits() as u8], false);
}

/// `%e %E %f %g %G` (`conv` is the directive letter).
pub fn float(out: &mut Vec<u8>, spec: Spec, conv: u8, x: f64) {
    let upper = conv.is_ascii_uppercase();
    let sign: &[u8] = if x.is_nan() {
        // C prints a NaN's sign bit; its value is not portable, so it is dropped
        if spec.has(PLUS) { b"+" } else if spec.has(SPACE) { b" " } else { b"" }
    } else if x.is_sign_negative() {
        b"-"
    } else if spec.has(PLUS) {
        b"+"
    } else if spec.has(SPACE) {
        b" "
    } else {
        b""
    };
    if !x.is_finite() {
        let word: &[u8] = match (x.is_nan(), upper) {
            (true, false) => b"nan",
            (true, true) => b"NAN",
            (false, false) => b"inf",
            (false, true) => b"INF",
        };
        pad(out, spec, sign, word, false);
        return;
    }
    let ax = x.abs();
    let alt = spec.has(ALT);
    let mut body = match conv.to_ascii_lowercase() {
        b'e' => exp_form(ax, spec.prec.unwrap_or(6) as usize, alt),
        b'f' => fixed_form(ax, spec.prec.unwrap_or(6) as usize, alt),
        _ => general_form(ax, spec.prec.unwrap_or(6) as usize, alt),
    };
    if upper {
        body.make_ascii_uppercase();
    }
    pad(out, spec, sign, body.as_bytes(), true);
}

fn fixed_form(ax: f64, prec: usize, alt: bool) -> String {
    let mut s = format!("{ax:.prec$}");
    if alt && prec == 0 {
        s.push('.');
    }
    s
}

/// `d.ddde+XX`: Rust's `{:e}` writes the exponent without sign or padding.
fn exp_form(ax: f64, prec: usize, alt: bool) -> String {
    let s = format!("{ax:.prec$e}");
    let (mant, exp) = s.split_once('e').expect("{:e} always has an exponent");
    let exp: i32 = exp.parse().expect("exponent is an integer");
    let dot = if alt && prec == 0 { "." } else { "" };
    format!("{mant}{dot}e{}{:02}", if exp < 0 { '-' } else { '+' }, exp.abs())
}

/// `%g`: `%e` when the exponent is below -4 or at least the precision, `%f`
/// otherwise, with trailing zeros removed unless `#` is given.
fn general_form(ax: f64, prec: usize, alt: bool) -> String {
    let p = prec.max(1);
    // the exponent after rounding to `p` significant digits decides the style
    let probe = format!("{ax:.*e}", p - 1);
    let exp: i32 = probe.split_once('e').and_then(|(_, e)| e.parse().ok()).expect("exponent");
    let mut s = if exp < -4 || exp >= p as i32 {
        exp_form(ax, p - 1, alt)
    } else {
        fixed_form(ax, (p as i32 - 1 - exp) as usize, alt)
    };
    if !alt {
        s = strip_zeros(&s);
    }
    s
}

/// Removes trailing fractional zeros (and a bare point) before any exponent.
fn strip_zeros(s: &str) -> String {
    let (num, exp) = match s.find('e') {
        Some(i) => s.split_at(i),
        None => (s, ""),
    };
    let num = if num.contains('.') { num.trim_end_matches('0').trim_end_matches('.') } else { num };
    format!("{num}{exp}")
}

/// `%s`. A directive without modifiers copies the value as is; otherwise the
/// value is cut at its first NUL byte (it goes through C's `%s`), truncated to
/// the precision and padded. Like the reference, a modified directive on a
/// string of 100 bytes or more without precision also copies it unchanged.
pub fn string(out: &mut Vec<u8>, spec: Spec, v: &dyn LuaDisplay) {
    if spec == Spec::PLAIN {
        v.fmt_lua(out);
        return;
    }
    let mut buf = Vec::new();
    v.fmt_lua(&mut buf);
    if spec.prec.is_none() && buf.len() >= 100 {
        out.extend_from_slice(&buf);
        return;
    }
    let end = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
    let end = spec.prec.map_or(end, |p| end.min(p as usize));
    pad(out, spec, b"", &buf[..end], true);
}

/// `%q`: a quoted string a program can read back. Modifiers are ignored, as in
/// the reference.
pub fn quoted(out: &mut Vec<u8>, v: &dyn LuaDisplay) {
    let mut buf = Vec::new();
    v.fmt_lua(&mut buf);
    out.push(b'"');
    for &b in &buf {
        match b {
            b'"' | b'\\' | b'\n' => out.extend_from_slice(&[b'\\', b]),
            b'\r' => out.extend_from_slice(b"\\r"),
            0 => out.extend_from_slice(b"\\000"),
            _ => out.push(b),
        }
    }
    out.push(b'"');
}

/// Literal text between directives.
pub fn lit(out: &mut Vec<u8>, s: &str) {
    let _ = out.write_all(s.as_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sp(flags: &str, width: u8, prec: Option<u8>) -> Spec {
        let mut f = 0;
        for c in flags.chars() {
            f |= match c {
                '-' => LEFT,
                '+' => PLUS,
                ' ' => SPACE,
                '#' => ALT,
                '0' => ZERO,
                _ => unreachable!(),
            };
        }
        Spec { flags: f, width, prec }
    }

    fn fl(conv: u8, spec: Spec, x: f64) -> String {
        let mut o = Vec::new();
        float(&mut o, spec, conv, x);
        String::from_utf8(o).unwrap()
    }

    fn un(conv: u8, spec: Spec, x: f64) -> String {
        let mut o = Vec::new();
        unsigned(&mut o, spec, conv, x);
        String::from_utf8(o).unwrap()
    }

    fn sg(spec: Spec, x: f64) -> String {
        let mut o = Vec::new();
        signed(&mut o, spec, x);
        String::from_utf8(o).unwrap()
    }

    // expected values below were produced by Luau 0.743 (see tests/diff/format.luarc)

    #[test]
    fn exponent_form() {
        let p = Spec::PLAIN;
        assert_eq!(fl(b'e', p, 12345.6789), "1.234568e+04");
        assert_eq!(fl(b'E', sp("", 0, None), 0.000123), "1.230000E-04");
        assert_eq!(fl(b'e', sp("", 0, Some(3)), 0.0), "0.000e+00");
        assert_eq!(fl(b'e', sp("", 0, Some(0)), 15.0), "2e+01");
        assert_eq!(fl(b'e', sp("#", 0, Some(0)), 15.0), "2.e+01");
        assert_eq!(fl(b'e', p, -0.0), "-0.000000e+00");
        assert_eq!(fl(b'e', sp("", 10, Some(3)), 1234.5), " 1.234e+03");
        assert_eq!(fl(b'e', sp("+", 0, Some(2)), 1.5), "+1.50e+00");
        assert_eq!(fl(b'e', p, 1e100), "1.000000e+100");
    }

    #[test]
    fn general_form() {
        let p = Spec::PLAIN;
        for (x, want) in [
            (100000.0, "100000"),
            (1e6, "1e+06"),
            (0.0001, "0.0001"),
            (1e-5, "1e-05"),
            (123456.0, "123456"),
            (1234567.0, "1.23457e+06"),
            (123456789.0, "1.23457e+08"),
            (1e100, "1e+100"),
            (0.5, "0.5"),
            (-0.0, "-0"),
            (9.9999995, "10"),
        ] {
            assert_eq!(fl(b'g', p, x), want, "{x}");
        }
        assert_eq!(fl(b'g', sp("", 0, Some(3)), 3.14159), "3.14");
        assert_eq!(fl(b'g', sp("", 0, Some(1)), 0.95), "0.9");
        assert_eq!(fl(b'g', sp("", 0, Some(0)), 123.0), "1e+02");
        assert_eq!(fl(b'g', sp("", 0, Some(10)), 0.1), "0.1");
        assert_eq!(fl(b'g', sp("", 0, Some(17)), 0.1), "0.10000000000000001");
        assert_eq!(fl(b'G', p, 1e-10), "1E-10");
        assert_eq!(fl(b'g', sp("#", 0, None), 1.5), "1.50000");
        assert_eq!(fl(b'g', sp("#", 0, None), 100000.0), "100000.");
        assert_eq!(fl(b'g', sp("-", 12, None), 0.5), "0.5         ");
        assert_eq!(fl(b'g', sp("0", 12, None), -0.5), "-000000000.5");
    }

    #[test]
    fn fixed_form() {
        assert_eq!(fl(b'f', sp("", 5, Some(1)), 2.25), "  2.2");
        assert_eq!(fl(b'f', sp("-", 8, Some(2)), 1.005), "1.00    ");
        assert_eq!(fl(b'f', sp("0", 10, Some(2)), -3.5), "-000003.50");
        assert_eq!(fl(b'f', sp("", 0, Some(0)), 0.5), "0");
        assert_eq!(fl(b'f', sp("", 0, Some(0)), 1.5), "2");
        assert_eq!(fl(b'f', sp("#", 0, Some(0)), 1.0), "1.");
        assert_eq!(fl(b'f', sp("", 0, Some(20)), 0.1), "0.10000000000000000555");
        assert_eq!(fl(b'f', sp("", 0, Some(2)), 2.675), "2.67");
    }

    #[test]
    fn non_finite() {
        assert_eq!(fl(b'g', Spec::PLAIN, f64::INFINITY), "inf");
        assert_eq!(fl(b'g', Spec::PLAIN, f64::NEG_INFINITY), "-inf");
        assert_eq!(fl(b'G', Spec::PLAIN, f64::INFINITY), "INF");
        assert_eq!(fl(b'f', Spec::PLAIN, f64::NAN), "nan");
        assert_eq!(fl(b'g', sp("0", 12, None), f64::INFINITY), "         inf");
        assert_eq!(fl(b'e', sp("+", 0, None), f64::INFINITY), "+inf");
    }

    #[test]
    fn integers() {
        assert_eq!(un(b'x', Spec::PLAIN, 255.0), "ff");
        assert_eq!(un(b'X', Spec::PLAIN, 255.0), "FF");
        assert_eq!(un(b'x', Spec::PLAIN, -1.0), "ffffffffffffffff");
        assert_eq!(un(b'x', Spec::PLAIN, 3.7), "3");
        assert_eq!(un(b'x', Spec::PLAIN, 1e30), "8000000000000000");
        assert_eq!(un(b'x', Spec::PLAIN, f64::NAN), "8000000000000000");
        assert_eq!(un(b'o', Spec::PLAIN, 8.0), "10");
        assert_eq!(un(b'u', Spec::PLAIN, -1.0), "18446744073709551615");
        assert_eq!(un(b'x', sp("#", 0, None), 255.0), "0xff");
        assert_eq!(un(b'X', sp("#", 0, None), 255.0), "0XFF");
        assert_eq!(un(b'x', sp("#", 0, None), 0.0), "0");
        assert_eq!(un(b'o', sp("#", 0, None), 8.0), "010");
        assert_eq!(un(b'o', sp("#", 0, Some(3)), 8.0), "010");
        assert_eq!(un(b'x', sp("+", 0, None), 5.0), "5");
        assert_eq!(un(b'x', sp("#0", 8, None), 255.0), "0x0000ff");
        assert_eq!(sg(sp("+ ", 0, None), 5.0), "+5");
        assert_eq!(sg(sp(" ", 0, None), 5.0), " 5");
        assert_eq!(sg(sp("-+", 5, None), 3.0), "+3   ");
        assert_eq!(sg(sp("0", 5, None), -3.0), "-0003");
        assert_eq!(sg(sp("", 0, Some(3)), 5.0), "005");
        assert_eq!(sg(sp("", 5, Some(3)), 5.0), "  005");
        assert_eq!(sg(sp("0", 5, Some(3)), 5.0), "  005");
        assert_eq!(sg(sp("-0", 5, None), 3.0), "3    ");
        assert_eq!(sg(sp("", 0, Some(0)), 0.0), "");
        assert_eq!(sg(Spec::PLAIN, -0.5), "0");
        assert_eq!(sg(Spec::PLAIN, 1e100), "-9223372036854775808");
        let mut o = Vec::new();
        signed(&mut o, Spec::PLAIN, u64::MAX as i128);
        assert_eq!(o, b"18446744073709551615");
    }

    #[test]
    fn chars() {
        let c = |s: Spec, v: f64| {
            let mut o = Vec::new();
            char_(&mut o, s, v);
            o
        };
        assert_eq!(c(Spec::PLAIN, 65.0), b"A");
        assert_eq!(c(Spec::PLAIN, 321.0), b"A");
        assert_eq!(c(Spec::PLAIN, -1.0), [0xff]);
        assert_eq!(c(sp("", 5, None), 65.0), b"    A");
        assert_eq!(c(sp("-", 5, None), 66.0), b"B    ");
    }

    struct B(&'static [u8]);
    impl LuaDisplay for B {
        fn fmt_lua(&self, out: &mut Vec<u8>) {
            out.extend_from_slice(self.0);
        }
    }

    fn st(spec: Spec, v: &'static [u8]) -> Vec<u8> {
        let mut o = Vec::new();
        string(&mut o, spec, &B(v));
        o
    }

    #[test]
    fn strings() {
        assert_eq!(st(Spec::PLAIN, b"a\0b"), b"a\0b");
        assert_eq!(st(sp("", 5, None), b"ab"), b"   ab");
        assert_eq!(st(sp("-", 5, None), b"ab"), b"ab   ");
        assert_eq!(st(sp("", 0, Some(2)), b"abcdef"), b"ab");
        assert_eq!(st(sp("", 0, Some(0)), b"abc"), b"");
        assert_eq!(st(sp("0", 5, None), b"a"), b"0000a");
        assert_eq!(st(sp("", 5, None), b"a\0b"), b"    a");
        let long = [b'x'; 120];
        let long: &'static [u8] = Box::leak(Box::new(long));
        assert_eq!(st(sp("", 130, None), long), long);
    }

    #[test]
    fn quoting() {
        let mut o = Vec::new();
        quoted(&mut o, &B(b"a\nb\"c\\d\0e\x7f2\r"));
        assert_eq!(o, b"\"a\\\nb\\\"c\\\\d\\000e\x7f2\\r\"");
    }
}
