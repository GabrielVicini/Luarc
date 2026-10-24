//! Builtin library functions (`print`, `string.*`, `math.*`, `table.*`, ...).

use std::cell::RefCell;
use std::io::Write;

use crate::error::{LResult, LuaError};
use crate::show::{fmt_num, LuaDisplay};
use crate::value::{Arr, LStr, PcallVal};

thread_local! {
    static STDOUT: RefCell<std::io::BufWriter<std::io::Stdout>> =
        RefCell::new(std::io::BufWriter::with_capacity(1 << 14, std::io::stdout()));
    // a terminal sees every line as it is printed; pipes and files are flushed
    // at least every FLUSH_EVERY so long-running programs still show progress
    static INTERACTIVE: bool = std::io::IsTerminal::is_terminal(&std::io::stdout());
    static LAST_FLUSH: std::cell::Cell<std::time::Instant> = std::cell::Cell::new(std::time::Instant::now());
}

const FLUSH_EVERY: std::time::Duration = std::time::Duration::from_millis(100);

/// `print(...)`: arguments separated by tabs, followed by a newline.
pub fn print(args: &[&dyn LuaDisplay]) {
    let mut line = Vec::with_capacity(64);
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            line.push(b'\t');
        }
        a.fmt_lua(&mut line);
    }
    line.push(b'\n');
    write_stdout(&line);
}

/// Writes a print fragment, releasing stdout before another source callback runs.
pub fn write_stdout(bytes: &[u8]) {
    STDOUT.with(|s| {
        let mut s = s.borrow_mut();
        let _ = write_stdout_to(&mut *s, bytes);
        let now = std::time::Instant::now();
        if INTERACTIVE.with(|i| *i) || LAST_FLUSH.with(|t| now.duration_since(t.get()) >= FLUSH_EVERY) {
            let _ = s.flush();
            LAST_FLUSH.with(|t| t.set(now));
        }
    });
}

fn write_stdout_to(out: &mut impl Write, bytes: &[u8]) -> std::io::Result<()> {
    // Luau 0.743 uses Windows text-mode stdout: every LF becomes CRLF, even in strings.
    #[cfg(windows)]
    {
        let mut start = 0;
        for (i, &byte) in bytes.iter().enumerate() {
            if byte == b'\n' {
                out.write_all(&bytes[start..i])?;
                out.write_all(b"\r\n")?;
                start = i + 1;
            }
        }
        out.write_all(&bytes[start..])
    }
    #[cfg(not(windows))]
    out.write_all(bytes)
}

pub fn flush_stdout() {
    STDOUT.with(|s| {
        let _ = s.borrow_mut().flush();
    });
}

// Arithmetic

/// Luau `a // b` = floor(a / b).
#[inline]
pub fn floor_div(a: f64, b: f64) -> f64 {
    (a / b).floor()
}

/// Luau `a % b` = a - floor(a / b) * b (sign follows the divisor).
#[inline]
pub fn modulo(a: f64, b: f64) -> f64 {
    a - (a / b).floor() * b
}

// Strings

/// Piece of a `..` chain or interpolated string.
pub trait ConcatPart {
    fn push_to(&self, out: &mut Vec<u8>);
}
impl ConcatPart for LStr {
    fn push_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.as_bytes())
    }
}
impl ConcatPart for f64 {
    fn push_to(&self, out: &mut Vec<u8>) {
        fmt_num(*self, out)
    }
}
impl ConcatPart for &str {
    fn push_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.as_bytes())
    }
}

pub fn concat(parts: &[&dyn ConcatPart]) -> LStr {
    let mut out = Vec::new();
    for p in parts {
        p.push_to(&mut out);
    }
    LStr::from_vec(out)
}

/// String interpolation: every piece goes through `tostring`.
pub fn interp(parts: &[&dyn LuaDisplay]) -> LStr {
    let mut out = Vec::new();
    for p in parts {
        p.fmt_lua(&mut out);
    }
    LStr::from_vec(out)
}

/// Lua's posrelat + clamping for byte offsets (truncating non-integral indices).
pub fn string_sub(s: &LStr, i: f64, j: Option<f64>) -> LStr {
    let len = s.as_bytes().len() as i64;
    let rel = |p: f64| -> i64 {
        let p = if p.is_nan() { 0 } else { p.clamp(-9e15, 9e15) as i64 };
        if p < 0 {
            len + p + 1
        } else {
            p
        }
    };
    let mut a = rel(i);
    let mut b = rel(j.unwrap_or(-1.0));
    if a < 1 {
        a = 1;
    }
    if b > len {
        b = len;
    }
    if a > b {
        LStr::from_bytes(b"")
    } else {
        LStr::from_bytes(&s.as_bytes()[(a - 1) as usize..b as usize])
    }
}

pub fn string_upper(s: &LStr) -> LStr {
    LStr::from_vec(s.as_bytes().to_ascii_uppercase())
}

pub fn string_lower(s: &LStr) -> LStr {
    LStr::from_vec(s.as_bytes().to_ascii_lowercase())
}

/// `string.reverse(s)`: the bytes in reverse order.
pub fn string_reverse(s: &LStr) -> LStr {
    LStr::from_vec(s.as_bytes().iter().rev().copied().collect())
}

/// `string.rep(s, n)`: results too large to allocate raise a language error.
pub fn string_rep(s: &LStr, n: f64) -> LResult<LStr> {
    if !(n >= 1.0) || s.as_bytes().is_empty() {
        return Ok(LStr::from_bytes(b""));
    }
    let len = (s.as_bytes().len() as f64) * n.trunc();
    if len >= isize::MAX as f64 {
        return Err(LuaError::new("bad argument to 'rep' (resulting string too large)"));
    }
    let mut out: Vec<u8> = Vec::new();
    out.try_reserve_exact(len as usize).map_err(|_| LuaError::new("not enough memory"))?;
    for _ in 0..n as usize {
        out.extend_from_slice(s.as_bytes());
    }
    Ok(LStr::from_vec(out))
}

pub fn string_byte(s: &LStr, i: Option<f64>) -> Option<f64> {
    let b = string_sub(s, i.unwrap_or(1.0), Some(i.unwrap_or(1.0)));
    b.as_bytes().first().map(|&c| c as f64)
}

pub fn string_char(codes: &[f64]) -> LResult<LStr> {
    let mut out = Vec::with_capacity(codes.len());
    // Luau 0.743: codes truncate toward zero (`65.9` → `A`,
    // `-0.5` → 0); a truncated code outside 0..=255 is an error.
    for (i, &c) in codes.iter().enumerate() {
        let t = c.trunc();
        if !(0.0..=255.0).contains(&t) {
            return Err(LuaError::new(format!("invalid argument #{} to 'char' (invalid value)", i + 1)));
        }
        out.push(t as u8);
    }
    Ok(LStr::from_vec(out))
}

/// `tonumber(s)` with Luau 0.743's syntax (its `luaO_str2d`, i.e. C `strtod`):
/// optional C whitespace (` \t\n\v\f\r`) around an optionally signed decimal
/// number (fraction, exponent), hexadecimal number (`0x1F`, hex fraction and `p`
/// exponent: `0x1p4`), `inf`/`infinity` or `nan` (case-insensitive). Anything else
/// is nil.
pub fn tonumber(s: &LStr) -> Option<f64> {
    let is_space = |b: &u8| matches!(b, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r');
    // the reference reads a C string: a NUL byte ends it
    let b = s.as_bytes();
    let b = &b[..b.iter().position(|&c| c == 0).unwrap_or(b.len())];
    let start = b.iter().position(|c| !is_space(c))?;
    let end = b.iter().rposition(|c| !is_space(c))? + 1;
    let t = &b[start..end];
    let (neg, body) = match t.first() {
        Some(b'-') => (true, &t[1..]),
        Some(b'+') => (false, &t[1..]),
        _ => (false, t),
    };
    let lower = body.to_ascii_lowercase();
    let v = if lower == b"inf" || lower == b"infinity" {
        f64::INFINITY
    } else if lower == b"nan" || (lower.starts_with(b"nan(") && lower.ends_with(b")") && lower[4..lower.len() - 1].iter().all(|c| c.is_ascii_alphanumeric() || *c == b'_')) {
        f64::NAN
    } else if lower.starts_with(b"0x") {
        hex_float(&lower[2..])?
    } else {
        // digits [. digits] [e [sign] digits], at least one mantissa digit
        let mut i = 0;
        let digits = |i: &mut usize| {
            let s = *i;
            while *i < lower.len() && lower[*i].is_ascii_digit() {
                *i += 1;
            }
            *i - s
        };
        let mut n = digits(&mut i);
        if i < lower.len() && lower[i] == b'.' {
            i += 1;
            n += digits(&mut i);
        }
        if n == 0 {
            return None;
        }
        if i < lower.len() && lower[i] == b'e' {
            i += 1;
            if i < lower.len() && matches!(lower[i], b'+' | b'-') {
                i += 1;
            }
            if digits(&mut i) == 0 {
                return None;
            }
        }
        if i != lower.len() {
            return None;
        }
        std::str::from_utf8(&lower).ok()?.parse::<f64>().ok()?
    };
    Some(if neg { -v } else { v })
}

/// `tonumber(s, base)` of Luau 0.743. The base goes through [`check_int`] and must
/// be 2..=36. Base 10 is plain [`tonumber`]; any other base reads `s` like C
/// `strtoull` reads a C string: it stops at the first NUL byte, skips leading
/// whitespace, takes an optional sign (`-` negates modulo 2^64, so `"-1"` is
/// 2^64 - 1), an optional `0x` for base 16, and saturates at 2^64 - 1 on
/// overflow. At least one digit and nothing but whitespace after the digits,
/// else nil.
pub fn tonumber_base(s: &LStr, base: f64) -> LResult<Option<f64>> {
    let base = check_int(base);
    if base == 10 {
        return Ok(tonumber(s));
    }
    if !(2..=36).contains(&base) {
        return Err(LuaError::new("invalid argument #2 to 'tonumber' (base out of range)"));
    }
    let b = s.as_bytes();
    let b = &b[..b.iter().position(|&c| c == 0).unwrap_or(b.len())];
    let is_space = |c: u8| matches!(c, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r');
    let digit = |c: u8| (c as char).to_digit(36).filter(|&d| d < base as u32);
    let mut i = b.iter().position(|&c| !is_space(c)).unwrap_or(b.len());
    let neg = match b.get(i) {
        Some(b'-') => {
            i += 1;
            true
        }
        Some(b'+') => {
            i += 1;
            false
        }
        _ => false,
    };
    if base == 16 && b.get(i) == Some(&b'0') && matches!(b.get(i + 1), Some(b'x' | b'X')) && b.get(i + 2).and_then(|&c| digit(c)).is_some() {
        i += 2;
    }
    let start = i;
    let mut n = 0u64;
    let mut overflow = false;
    while let Some(d) = b.get(i).and_then(|&c| digit(c)) {
        match n.checked_mul(base as u64).and_then(|n| n.checked_add(d as u64)) {
            Some(v) => n = v,
            None => overflow = true,
        }
        i += 1;
    }
    if i == start || !b[i..].iter().all(|&c| is_space(c)) {
        return Ok(None);
    }
    let n = if overflow {
        u64::MAX
    } else if neg {
        n.wrapping_neg()
    } else {
        n
    };
    Ok(Some(n as f64))
}

/// Hexadecimal significand `h[.h]` with optional binary exponent `p[sign]d`
/// (the part after `0x`), as C `strtod` reads it.
fn hex_float(b: &[u8]) -> Option<f64> {
    let mut i = 0;
    let mut mant = 0f64;
    let mut exp: i64 = 0;
    let mut any = false;
    while i < b.len() && b[i].is_ascii_hexdigit() {
        mant = mant * 16.0 + (b[i] as char).to_digit(16)? as f64;
        any = true;
        i += 1;
    }
    if i < b.len() && b[i] == b'.' {
        i += 1;
        while i < b.len() && b[i].is_ascii_hexdigit() {
            mant = mant * 16.0 + (b[i] as char).to_digit(16)? as f64;
            exp -= 4;
            any = true;
            i += 1;
        }
    }
    if !any {
        return None;
    }
    if i < b.len() && b[i] == b'p' {
        i += 1;
        let neg = match b.get(i) {
            Some(b'-') => {
                i += 1;
                true
            }
            Some(b'+') => {
                i += 1;
                false
            }
            _ => false,
        };
        let s = i;
        let mut e: i64 = 0;
        while i < b.len() && b[i].is_ascii_digit() {
            e = (e * 10 + (b[i] - b'0') as i64).min(100_000);
            i += 1;
        }
        if i == s {
            return None;
        }
        exp += if neg { -e } else { e };
    }
    if i != b.len() {
        return None;
    }
    Some(mant * 2f64.powi(exp.clamp(-100_000, 100_000) as i32))
}

// Math

pub fn math_min(first: f64, rest: &[f64]) -> f64 {
    rest.iter().fold(first, |m, &x| if x < m { x } else { m })
}

pub fn math_max(first: f64, rest: &[f64]) -> f64 {
    rest.iter().fold(first, |m, &x| if x > m { x } else { m })
}

// Table

/// `table.concat(t, sep, i, j)` for arrays of strings or numbers.
pub fn table_concat<T: crate::stdlib::ConcatPart + Clone + dumpster::Trace>(
    t: &Arr<T>,
    sep: Option<&LStr>,
    i: Option<f64>,
    j: Option<f64>,
) -> LResult<LStr> {
    let v = t.borrow();
    let i = i.unwrap_or(1.0);
    let j = j.unwrap_or(v.len() as f64);
    let mut out = Vec::new();
    let mut k = i;
    while k <= j {
        let idx = if k >= 1.0 && k.fract() == 0.0 { Some(k as usize) } else { None };
        match idx.and_then(|p| v.get(p - 1)) {
            Some(e) => e.push_to(&mut out),
            None => {
                return Err(LuaError::new(format!(
                    "invalid value (at index {}) in table for 'concat'",
                    crate::show::num_to_string(k)
                )))
            }
        }
        if k < j {
            if let Some(s) = sep {
                out.extend_from_slice(s.as_bytes());
            }
        }
        k += 1.0;
    }
    Ok(LStr::from_vec(out))
}

// Protected calls

/// Bounded `pcall(f)`: `f` takes no arguments and returns at most one value.
pub fn pcall<T: dumpster::Trace>(f: impl FnOnce() -> LResult<T>) -> (bool, PcallVal<T>) {
    match f() {
        Ok(v) => (true, PcallVal::Ok(v)),
        Err(e) => (false, PcallVal::Err(e.msg)),
    }
}

// Math (expected values checked against Luau 0.743)

/// `math.log(x, base)`: base 2 and 10 use the exact functions, like Luau.
pub fn math_log(x: f64, base: Option<f64>) -> f64 {
    match base {
        None => x.ln(),
        Some(b) if b == 2.0 => x.log2(),
        Some(b) if b == 10.0 => x.log10(),
        Some(b) => x.ln() / b.ln(),
    }
}

/// `math.sign(x)`: -1, 0 or 1 (0 for NaN).
pub fn math_sign(x: f64) -> f64 {
    if x > 0.0 {
        1.0
    } else if x < 0.0 {
        -1.0
    } else {
        0.0
    }
}

/// `math.clamp(x, min, max)`.
pub fn math_clamp(x: f64, lo: f64, hi: f64) -> LResult<f64> {
    if lo > hi {
        return Err(LuaError::new("invalid argument #3 to 'clamp' (max must be greater than or equal to min)"));
    }
    Ok(if x < lo { lo } else if x > hi { hi } else { x })
}

/// `luaL_checkinteger` of Luau 0.743: a C cast of the number to a 32-bit `int`.
/// It truncates toward zero; NaN and values outside the `int` range give the x86
/// "integer indefinite" `i32::MIN`, which is what the reference does.
pub fn check_int(x: f64) -> i32 {
    let t = x.trunc();
    if (-2147483648.0..2147483648.0).contains(&t) { t as i32 } else { i32::MIN }
}

/// `math.frexp(x)`: `(m, e)` with `x = m * 2^e` and `0.5 <= |m| < 1`. Zero keeps
/// its sign with exponent 0; infinities and NaN return exponent -1 like the
/// reference (MSVC's C runtime).
pub fn math_frexp(x: f64) -> (f64, f64) {
    if x == 0.0 {
        return (x, 0.0);
    }
    if !x.is_finite() {
        return (x, -1.0);
    }
    let (x, bias) = if x.abs() < f64::MIN_POSITIVE { (x * 2f64.powi(54), -54) } else { (x, 0) };
    let bits = x.to_bits();
    let e = ((bits >> 52) & 0x7ff) as i32 - 1022;
    let m = f64::from_bits((bits & !(0x7ff << 52)) | (1022 << 52));
    (m, (e + bias) as f64)
}

/// `math.modf(x)`: integer and fractional parts, both with the sign of `x`
/// (`modf(-inf)` is `-inf, -0`; NaN gives NaN twice).
pub fn math_modf(x: f64) -> (f64, f64) {
    let i = x.trunc();
    let f = if x.is_infinite() { 0f64.copysign(x) } else { (x - i).copysign(x) };
    (i, f)
}

/// `math.ldexp(m, e)`: `m * 2^e`, correctly rounded (musl's `scalbn`). The
/// exponent goes through [`check_int`] like the reference.
pub fn math_ldexp(m: f64, e: f64) -> f64 {
    let mut n = check_int(e);
    let mut y = m;
    if n > 1023 {
        y *= 2f64.powi(1023);
        n -= 1023;
        if n > 1023 {
            y *= 2f64.powi(1023);
            n -= 1023;
            n = n.min(1023);
        }
    } else if n < -1022 {
        // scale by 2^-1022 * 2^53 so that the final rounding happens once
        let s = 2f64.powi(-1022 + 53);
        y *= s;
        n += 1022 - 53;
        if n < -1022 {
            y *= s;
            n += 1022 - 53;
            n = n.max(-1022);
        }
    }
    y * f64::from_bits(((0x3ff + n) as u64) << 52)
}

/// `math.lerp(a, b, t)` of Luau 0.743: exact `b` at `t == 1`.
pub fn math_lerp(a: f64, b: f64, t: f64) -> f64 {
    if t == 1.0 { b } else { a + (b - a) * t }
}

// Math.noise
//
// Perlin noise of Luau 0.743 (`lmathlib.cpp`): Ken Perlin's improved noise in
// single precision with the classic permutation table.

const PERLIN: [u8; 256] = [151,160,137,91,90,15,131,13,201,95,96,53,194,233,7,225,140,36,103,30,69,142,8,99,37,240,21,10,23,190,6,148,247,120,234,75,0,26,197,62,94,252,219,203,117,35,11,32,57,177,33,88,237,149,56,87,174,20,125,136,171,168,68,175,74,165,71,134,139,48,27,166,77,146,158,231,83,111,229,122,60,211,133,230,220,105,92,41,55,46,245,40,244,102,143,54,65,25,63,161,1,216,80,73,209,76,132,187,208,89,18,169,200,196,135,130,116,188,159,86,164,100,109,198,173,186,3,64,52,217,226,250,124,123,5,202,38,147,118,126,255,82,85,212,207,206,59,227,47,16,58,17,182,189,28,42,223,183,170,213,119,248,152,2,44,154,163,70,221,153,101,155,167,43,172,9,129,22,39,253,19,98,108,110,79,113,224,232,178,185,112,104,218,246,97,228,251,34,242,193,238,210,144,12,191,179,162,241,81,51,145,235,249,14,239,107,49,192,214,31,181,199,106,157,184,84,204,176,115,121,50,45,127,4,150,254,138,236,205,93,222,114,67,29,24,72,243,141,128,195,78,66,215,61,156,180];

fn perm(i: usize) -> usize {
    PERLIN[i & 255] as usize
}

fn grad(hash: usize, x: f32, y: f32, z: f32) -> f32 {
    let h = hash & 15;
    let u = if h < 8 { x } else { y };
    let v = if h < 4 { y } else if h == 12 || h == 14 { x } else { z };
    (if h & 1 != 0 { -u } else { u }) + (if h & 2 != 0 { -v } else { v })
}

fn nlerp(t: f32, a: f32, b: f32) -> f32 {
    a + t * (b - a)
}

fn fade(t: f32) -> f32 {
    t * t * t * (t * (t * 6.0 - 15.0) + 10.0)
}

/// `math.noise(x, y, z)`: arguments are rounded to `f32` like the reference.
pub fn math_noise(x: f64, y: f64, z: f64) -> f64 {
    let (x, y, z) = (x as f32, y as f32, z as f32);
    let (xf0, yf0, zf0) = (x.floor(), y.floor(), z.floor());
    // C float -> int casts: out of range / NaN is INT_MIN on x86, whose low byte is 0
    let cell = |f: f32| (if f.is_finite() && f.abs() < 2147483648.0 { f as i32 } else { i32::MIN }) as usize & 255;
    let (xi, yi, zi) = (cell(xf0), cell(yf0), cell(zf0));
    let (xf, yf, zf) = (x - xf0, y - yf0, z - zf0);
    let (u, v, w) = (fade(xf), fade(yf), fade(zf));
    let a = perm(xi) + yi;
    let aa = perm(a) + zi;
    let ab = perm(a + 1) + zi;
    let b = perm(xi + 1) + yi;
    let ba = perm(b) + zi;
    let bb = perm(b + 1) + zi;
    let r = nlerp(
        w,
        nlerp(
            v,
            nlerp(u, grad(perm(aa), xf, yf, zf), grad(perm(ba), xf - 1.0, yf, zf)),
            nlerp(u, grad(perm(ab), xf, yf - 1.0, zf), grad(perm(bb), xf - 1.0, yf - 1.0, zf)),
        ),
        nlerp(
            v,
            nlerp(u, grad(perm(aa + 1), xf, yf, zf - 1.0), grad(perm(ba + 1), xf - 1.0, yf, zf - 1.0)),
            nlerp(u, grad(perm(ab + 1), xf, yf - 1.0, zf - 1.0), grad(perm(bb + 1), xf - 1.0, yf - 1.0, zf - 1.0)),
        ),
    );
    r as f64
}

// Math.random
//
// The generator of Luau 0.743 (PCG32, `lmathlib.cpp`), so `math.randomseed(n)`
// gives the same sequence as the reference. The state is per thread and seeded
// from the clock at first use, like Luau seeds each state at creation.

thread_local! {
    static RNG: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
}

fn pcg32(state: &mut u64) -> u32 {
    let old = *state;
    *state = old.wrapping_mul(6364136223846793005).wrapping_add(105);
    let xorshifted = (((old >> 18) ^ old) >> 27) as u32;
    let rot = (old >> 59) as u32;
    xorshifted.rotate_right(rot)
}

fn pcg32_seed(seed: u64) -> u64 {
    let mut s = 0u64;
    pcg32(&mut s);
    s = s.wrapping_add(seed);
    pcg32(&mut s);
    s
}

fn rng_next() -> u32 {
    RNG.with(|c| {
        let mut s = c.get().unwrap_or_else(|| {
            let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos() as u64).unwrap_or(0);
            pcg32_seed(t ^ (c as *const _ as u64))
        });
        let r = pcg32(&mut s);
        c.set(Some(s));
        r
    })
}

/// `math.randomseed(n)`: `n` goes through [`check_int`], then is sign-extended.
pub fn math_randomseed(n: f64) {
    let seed = check_int(n) as i64 as u64;
    RNG.with(|c| c.set(Some(pcg32_seed(seed))));
}

/// `math.random()`: a float in [0, 1) from 64 random bits.
pub fn math_random() -> f64 {
    let lo = rng_next() as u64;
    let hi = rng_next() as u64;
    // ldexp(lo | hi << 32, -64); the u64 → f64 conversion rounds like C's
    (lo | (hi << 32)) as f64 * 2f64.powi(-64)
}

/// `math.random(m)` (`lo` is None: the interval is 1..m) and `math.random(m, n)`.
/// Bounds go through [`check_int`]; errors name the last argument like Luau.
pub fn math_random_range(lo: Option<f64>, hi: f64) -> LResult<f64> {
    let argn = if lo.is_some() { 2 } else { 1 };
    let l = lo.map(check_int).unwrap_or(1);
    let u = check_int(hi);
    if l > u {
        return Err(LuaError::new(format!("invalid argument #{argn} to 'random' (interval is empty)")));
    }
    let ul = (u as u32).wrapping_sub(l as u32);
    if ul == u32::MAX {
        return Err(LuaError::new(format!("invalid argument #{argn} to 'random' (interval is too large)")));
    }
    // Lemire's multiply-shift for a value in [0, ul]
    let x = (ul as u64 + 1) * rng_next() as u64;
    Ok((l as u32).wrapping_add((x >> 32) as u32) as i32 as f64)
}

/// Luau 0.743 prefixes explicit messages with `file:line: msg`,
/// just as it does for the default "assertion failed!".
pub fn assert_failed(msg: Option<LStr>) -> LuaError {
    match msg {
        Some(m) => LuaError::new(m),
        None => LuaError::new("assertion failed!"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stdout_preserves_bytes_with_platform_newlines() {
        let mut output = Vec::new();
        write_stdout_to(&mut output, b"").unwrap();
        write_stdout_to(&mut output, b"\nA\r\nB\rC\0\x80\xff\n").unwrap();
        #[cfg(windows)]
        assert_eq!(output, b"\r\nA\r\r\nB\rC\0\x80\xff\r\n");
        #[cfg(not(windows))]
        assert_eq!(output, b"\nA\r\nB\rC\0\x80\xff\n");
    }

    #[test]
    fn stdout_fragments_preserve_bytes_and_split_crlf() {
        let mut output = Vec::new();
        for fragment in [b"prefix".as_slice(), b"\r", b"\n", b"\0\xff", b"\n", b""] {
            write_stdout_to(&mut output, fragment).unwrap();
        }
        #[cfg(windows)]
        assert_eq!(output, b"prefix\r\r\n\0\xff\r\n");
        #[cfg(not(windows))]
        assert_eq!(output, b"prefix\r\n\0\xff\n");
    }

    #[test]
    fn sub_and_numbers() {
        let s = LStr::from("hello");
        assert_eq!(string_sub(&s, 2.0, Some(3.0)).as_bytes(), b"el");
        assert_eq!(string_sub(&s, -3.0, None).as_bytes(), b"llo");
        assert_eq!(string_sub(&s, 0.0, Some(100.0)).as_bytes(), b"hello");
        assert_eq!(string_sub(&s, 4.0, Some(2.0)).as_bytes(), b"");
        assert_eq!(tonumber(&LStr::from(" 0x10 ")), Some(16.0));
        assert_eq!(tonumber(&LStr::from("1e3")), Some(1000.0));
        assert_eq!(tonumber(&LStr::from("abc")), None);
    }

    /// Expected values observed with Luau 0.743 (`LuaUCompare/luau.exe`), not
    /// derived from this implementation.
    #[test]
    #[cfg_attr(miri, ignore = "Miri perturbs pow/powi results by design; exact digits are checked natively")]
    fn tonumber_matches_luau() {
        let n = |s: &str| tonumber(&LStr::from(s));
        assert_eq!(n("inf"), Some(f64::INFINITY));
        assert_eq!(n("-inf"), Some(f64::NEG_INFINITY));
        assert_eq!(n("infinity"), Some(f64::INFINITY));
        assert!(n("nan").unwrap().is_nan());
        assert_eq!(n("\x0b5"), Some(5.0));
        assert_eq!(n("\x0c5\r"), Some(5.0));
        assert_eq!(n("1e309"), Some(f64::INFINITY));
        assert_eq!(n("0x1p4"), Some(16.0));
        assert_eq!(n("0X1F"), Some(31.0));
        assert_eq!(n("1E2"), Some(100.0));
        assert_eq!(n("+5"), Some(5.0));
        assert_eq!(n(".5"), Some(0.5));
        assert_eq!(n("5."), Some(5.0));
        for bad in ["- 5", "0x-1", "1e", "0b101", "1_000", "", "  ", "0x", ".", "e5", "5 5", "infx"] {
            assert_eq!(n(bad), None, "{bad:?}");
        }
        assert_eq!(tonumber(&LStr::from_bytes(b"\xff5")), None);
        assert_eq!(modulo(-5.0, 3.0), 1.0);
        assert_eq!(floor_div(-5.0, 3.0), -2.0);
        assert_eq!(modulo(5.0, -3.0), -1.0);
    }
}

// Collector

/// `collectgarbage(opt)`:
/// * `"collect"` (default) runs a full collection (cycles included) and returns 0;
/// * `"count"` returns the number of live managed objects on this thread. This
///   differs from Lua, which reports kilobytes: luarc does not track byte sizes
///   of managed objects.
pub fn collectgarbage(opt: Option<&LStr>) -> LResult<f64> {
    match opt.map(|o| o.as_bytes()) {
        None | Some(b"collect") => {
            crate::gc::collect();
            Ok(0.0)
        }
        Some(b"count") => Ok(crate::gc::live_objects() as f64),
        Some(other) => Err(LuaError::new(format!(
            "bad argument #1 to 'collectgarbage' (invalid option '{}'; supported: \"collect\", \"count\")",
            String::from_utf8_lossy(other)
        ))),
    }
}

/// Result of `string.find` / `string.match`.
pub struct Found {
    pub start: Option<f64>,
    pub end: Option<f64>,
    whole: Option<LStr>,
    caps: Vec<crate::pattern::Capture>,
}

impl Found {
    /// A match found by `string.gmatch` (byte offsets, zero based).
    pub(crate) fn matched(start: usize, end: usize, whole: LStr, caps: Vec<crate::pattern::Capture>) -> Found {
        Found { start: Some(start as f64 + 1.0), end: Some(end as f64), whole: Some(whole), caps }
    }

    /// Capture `i` (`string.match` with no captures: the whole match).
    pub fn cap(&self, i: usize) -> Option<LStr> {
        match self.caps.get(i) {
            Some(crate::pattern::Capture::Str(b)) => Some(LStr::from_vec(b.clone())),
            Some(crate::pattern::Capture::Pos(p)) => Some(LStr::from(crate::show::num_to_string(*p))),
            None if i == 0 && self.caps.is_empty() => self.whole.clone(),
            None => None,
        }
    }
    /// Capture `i` of a match whose pattern is known to have it: a string, empty
    /// if absent (the whole match when the pattern has no captures).
    pub fn text(&self, i: usize) -> LStr {
        self.cap(i).unwrap_or_else(|| LStr::from_bytes(b""))
    }
    /// Position capture `i` of a match whose pattern is known to have it.
    pub fn position(&self, i: usize) -> f64 {
        self.pos(i).unwrap_or(f64::NAN)
    }
    /// Position capture `i` (`()` in the pattern): a number, like Luau.
    pub fn pos(&self, i: usize) -> Option<f64> {
        match self.caps.get(i) {
            Some(crate::pattern::Capture::Pos(p)) => Some(*p),
            _ => None,
        }
    }
}

/// `string.find(s, pattern, init, plain)` / `string.match(s, pattern, init)`.
pub fn string_find(s: &LStr, p: &LStr, init: Option<f64>, plain: bool) -> LResult<Found> {
    let b = s.as_bytes();
    Ok(match crate::pattern::find_at(b, p.as_bytes(), init, plain)? {
        Some((st, e, caps)) => Found { start: Some(st as f64 + 1.0), end: Some(e as f64), whole: Some(LStr::from_bytes(&b[st..e])), caps },
        None => Found { start: None, end: None, whole: None, caps: Vec::new() },
    })
}

/// [`string_find`] for a pattern whose value is only known at run time.
/// The call was compiled for a pattern without captures: `find` gives
/// start and end, `match` one string. Where that loses values Luau would give,
/// it is an error instead of a silently shorter result list:
/// * `max_caps`: captures the call site can show (`find`: 0, `match`: 1 when its
///   results are expanded; `usize::MAX` when the site keeps only the fixed ones);
/// * `match_value`: `match`, whose first value is the first capture, typed as a
///   string, so a position capture `()` (a number in Luau) is rejected.
///
/// `plain` patterns have no captures.
pub fn string_find_dyn(s: &LStr, p: &LStr, init: Option<f64>, plain: bool, func: &str, max_caps: usize, match_value: bool) -> LResult<Found> {
    if !plain {
        let caps = crate::pattern::capture_kinds(p.as_bytes());
        let why = if caps.len() > max_caps {
            Some(format!("has {} capture(s), whose values this call would drop", caps.len()))
        } else if match_value && caps.first() == Some(&true) {
            Some("starts with a position capture (a number) where this call gives a string".to_string())
        } else {
            None
        };
        if let Some(why) = why {
            return Err(LuaError::new(format!(
                "bad argument #2 to '{func}' (pattern {:?} {why}; the results of a pattern with captures need a string literal pattern, or a local initialized with one and never reassigned)",
                String::from_utf8_lossy(p.as_bytes())
            )));
        }
    }
    string_find(s, p, init, plain)
}

/// `table.sort(t, lt)`: a stable merge sort with a fallible comparator (an error
/// raised by the comparator leaves the table unchanged).
///
/// The merge sort tolerates comparators that do not define a total order,
/// unlike `slice::sort_by`. Each comparison calls the comparator once.
/// If the result remains out of order, sorting raises Luau's "invalid
/// order function for sorting" error. NaN elements with the default `<`
/// are accepted, as in Luau 0.743.
pub fn table_sort<T: Clone + dumpster::Trace + 'static>(t: &crate::Arr<T>, mut lt: impl FnMut(&T, &T) -> LResult<bool>) -> LResult<()> {
    let mut prefix = t.snapshot();
    prefix.truncate(t.len() as usize);
    // Luau runs comparator callbacks across a non-yielding C boundary.
    let v = crate::coroutine::non_yielding(|| merge_sort(prefix, &mut lt))?;
    for w in v.windows(2) {
        if crate::coroutine::non_yielding(|| lt(&w[1], &w[0]))? {
            return Err(LuaError::new("invalid order function for sorting"));
        }
    }
    t.replace_prefix(v);
    Ok(())
}

fn merge_sort<T: Clone>(v: Vec<T>, lt: &mut impl FnMut(&T, &T) -> LResult<bool>) -> LResult<Vec<T>> {
    if v.len() <= 1 {
        return Ok(v);
    }
    let mut left = v;
    let right = left.split_off(left.len() / 2);
    let left = merge_sort(left, lt)?;
    let right = merge_sort(right, lt)?;
    let mut out = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0, 0);
    while i < left.len() && j < right.len() {
        // stable: take from the right only when it is strictly smaller
        if lt(&right[j], &left[i])? {
            out.push(right[j].clone());
            j += 1;
        } else {
            out.push(left[i].clone());
            i += 1;
        }
    }
    out.extend_from_slice(&left[i..]);
    out.extend_from_slice(&right[j..]);
    Ok(out)
}

impl ConcatPart for i128 {
    fn push_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.to_string().as_bytes())
    }
}

#[cfg(test)]
mod math_tests {
    use super::*;

    /// Deterministic pseudo-random f64 bit patterns covering every exponent,
    /// subnormals, zeros, infinities and NaNs.
    fn samples() -> impl Iterator<Item = f64> {
        let mut s = 0x9e3779b97f4a7c15u64;
        (0..200_000).map(move |_| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            f64::from_bits(s)
        })
    }

    #[test]
    fn frexp_ldexp_round_trip() {
        for x in samples().chain([0.0, -0.0, f64::MIN_POSITIVE, 5e-324, -5e-324, f64::MAX, f64::MIN]) {
            let (m, e) = math_frexp(x);
            if !x.is_finite() {
                assert!(m.is_nan() == x.is_nan() && e == -1.0, "{x:e}");
                continue;
            }
            if x == 0.0 {
                assert!(m.to_bits() == x.to_bits() && e == 0.0);
                continue;
            }
            assert!((0.5..1.0).contains(&m.abs()), "{x:e} -> {m:e}");
            assert_eq!(math_ldexp(m, e).to_bits(), x.to_bits(), "{x:e}");
        }
    }

    #[test]
    fn ldexp_is_correctly_rounded() {
        // half-way cases at the bottom of the subnormal range round to even
        assert_eq!(math_ldexp(1.0, -1075.0), 0.0);
        assert_eq!(math_ldexp(3.0, -1075.0), 1e-323);
        assert_eq!(math_ldexp(1.5, -1074.0), 1e-323);
        assert_eq!(math_ldexp(2.5, -1075.0), 5e-324);
        assert_eq!(math_ldexp(1.0, 1024.0), f64::INFINITY);
        assert_eq!(math_ldexp(5e-324, 2000.0), 5e-324 * 2f64.powi(1000) * 2f64.powi(1000));
        // the exponent goes through a C cast to int
        assert_eq!(math_ldexp(1.0, 1e10), 0.0);
        assert_eq!(math_ldexp(1.0, f64::NAN), 0.0);
        for x in samples().filter(|x| x.is_finite()).take(20_000) {
            for e in [-1100.0, -1074.0, -1022.0, -60.0, -1.0, 0.0, 1.0, 60.0, 1023.0, 2100.0] {
                // exact reference: scale in steps of at most one power of two per
                // multiply only where the intermediate stays normal
                let r = math_ldexp(x, e);
                let back = math_ldexp(r, -e);
                if r.is_finite() && r != 0.0 && r.abs() >= f64::MIN_POSITIVE && x.abs() >= f64::MIN_POSITIVE {
                    assert_eq!(back.to_bits(), x.to_bits(), "{x:e} * 2^{e}");
                }
            }
        }
    }

    #[test]
    fn modf_parts() {
        for x in samples() {
            let (i, f) = math_modf(x);
            if x.is_nan() {
                assert!(i.is_nan() && f.is_nan());
            } else if x.is_infinite() {
                assert!(i == x && f == 0.0 && f.is_sign_negative() == x.is_sign_negative());
            } else {
                assert_eq!(i, x.trunc());
                assert_eq!(i + f, x, "{x:e}");
                assert!(f.abs() < 1.0 && f.is_sign_negative() == x.is_sign_negative());
            }
        }
    }

    #[test]
    fn tonumber_base_cases() {
        let n = |s: &[u8], b: f64| tonumber_base(&LStr::from_bytes(s), b).unwrap();
        assert_eq!(n(b"ff", 16.0), Some(255.0));
        assert_eq!(n(b"-1", 16.0), Some(18446744073709551615u64 as f64));
        assert_eq!(n(b"ffffffffffffffffffffffff", 16.0), Some(u64::MAX as f64));
        assert_eq!(n(b"-ffffffffffffffffffffffff", 16.0), Some(u64::MAX as f64));
        assert_eq!(n(b"1111111111111111111111111111111111111111111111111111111111111111", 2.0), Some(u64::MAX as f64));
        assert_eq!(n(b"0x", 16.0), None);
        assert_eq!(n(b"0x10", 36.0), Some((33 * 36 * 36 + 36) as f64));
        assert_eq!(n(b"12\x002", 3.0), Some(5.0));
        assert_eq!(n(b"1.5", 10.0), Some(1.5));
        assert!(tonumber_base(&LStr::from("1"), 1.0).is_err());
        assert!(tonumber_base(&LStr::from("1"), 37.0).is_err());
        assert!(tonumber_base(&LStr::from("1"), f64::INFINITY).is_err());
    }

    /// Sequences observed with Luau 0.743 (`LuaUCompare/luau.exe`).
    #[test]
    fn random_matches_luau() {
        math_randomseed(42.0);
        assert_eq!(math_random_range(Some(1.0), 100.0).unwrap(), 56.0);
        assert_eq!(math_random_range(Some(1.0), 100.0).unwrap(), 23.0);
        assert_eq!(math_random_range(None, 10.0).unwrap(), 1.0);
        assert_eq!(crate::show::num_to_string(math_random()), "0.53903537823825");
        math_randomseed(-5.0);
        assert_eq!(math_random_range(Some(1.0), 1000000.0).unwrap(), 211518.0);
        assert!(math_random_range(Some(5.0), 1.0).is_err());
        assert!(math_random_range(Some(-2147483648.0), 2147483647.0).is_err());
        assert_eq!(math_random_range(Some(-2147483648.0), -2147483648.0).unwrap(), -2147483648.0);
    }
}
