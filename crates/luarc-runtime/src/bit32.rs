//! The `bit32` library, as in Luau 0.743 (`lbitlib.cpp`).
//!
//! Every operand is a Luau number converted to `u32` the way the reference does it
//! (`luai_num2unsigned`): truncate toward zero to a 64-bit integer, keep the low 32
//! bits. NaN, infinities and values outside the 64-bit range give the x86 "integer
//! indefinite" value, whose low 32 bits are 0. Shift and bit-field counts use
//! `luaL_checkinteger` ([`crate::stdlib::check_int`]).

use crate::error::{LResult, LuaError};
use crate::stdlib::check_int;

/// A Luau number as an unsigned 32-bit operand (`luaL_checkunsigned`).
#[inline]
pub fn u32_of(x: f64) -> u32 {
    let t = x.trunc();
    // x86 `cvttsd2si`: anything outside i64 (and NaN) is i64::MIN, low 32 bits 0
    if t >= -9223372036854775808.0 && t < 9223372036854775808.0 {
        (t as i64) as u32
    } else {
        0
    }
}

#[inline]
fn out(n: u32) -> f64 {
    n as f64
}

/// `bit32.band(...)`: all ones when there are no arguments.
pub fn band(xs: &[f64]) -> f64 {
    out(xs.iter().fold(u32::MAX, |a, &x| a & u32_of(x)))
}

pub fn bor(xs: &[f64]) -> f64 {
    out(xs.iter().fold(0, |a, &x| a | u32_of(x)))
}

pub fn bxor(xs: &[f64]) -> f64 {
    out(xs.iter().fold(0, |a, &x| a ^ u32_of(x)))
}

/// `bit32.btest(...)`: `band(...) ~= 0`.
pub fn btest(xs: &[f64]) -> bool {
    xs.iter().fold(u32::MAX, |a, &x| a & u32_of(x)) != 0
}

pub fn bnot(x: f64) -> f64 {
    out(!u32_of(x))
}

/// Logical shift, left for positive `i`, right for negative; 32 or more empties it.
fn shift_left(n: u32, i: i32) -> u32 {
    // Luau 0.743 preserves the operand for the x86 indefinite count.
    if i == i32::MIN { return n; }
    if i < 0 {
        if i <= -32 {
            0
        } else {
            n >> -i
        }
    } else if i >= 32 {
        0
    } else {
        n << i
    }
}

pub fn lshift(x: f64, disp: f64) -> f64 {
    out(shift_left(u32_of(x), check_int(disp)))
}

pub fn rshift(x: f64, disp: f64) -> f64 {
    out(shift_left(u32_of(x), check_int(disp).wrapping_neg()))
}

pub fn arshift(x: f64, disp: f64) -> f64 {
    let n = u32_of(x);
    let i = check_int(disp);
    // a negative count, or a clear sign bit, is a plain logical shift
    if i == i32::MIN { return out(n); }
    if i < 0 || n & 0x8000_0000 == 0 {
        return out(shift_left(n, i.wrapping_neg()));
    }
    if i >= 32 {
        return out(u32::MAX);
    }
    out((n >> i) | !(u32::MAX >> i))
}

pub fn lrotate(x: f64, disp: f64) -> f64 {
    out(u32_of(x).rotate_left((check_int(disp) & 31) as u32))
}

pub fn rrotate(x: f64, disp: f64) -> f64 {
    out(u32_of(x).rotate_right((check_int(disp) & 31) as u32))
}

pub fn countlz(x: f64) -> f64 {
    u32_of(x).leading_zeros() as f64
}

pub fn countrz(x: f64) -> f64 {
    u32_of(x).trailing_zeros() as f64
}

pub fn byteswap(x: f64) -> f64 {
    out(u32_of(x).swap_bytes())
}

/// The shared range checks of `extract` / `replace`; `arg` is the position of `field`.
fn field_width(field: f64, width: Option<f64>, name: &str, arg: usize) -> LResult<(u32, u32)> {
    let f = check_int(field);
    let w = check_int(width.unwrap_or(1.0));
    if f < 0 {
        return Err(LuaError::new(format!("invalid argument #{arg} to '{name}' (field cannot be negative)")));
    }
    if w <= 0 {
        return Err(LuaError::new(format!("invalid argument #{} to '{name}' (width must be positive)", arg + 1)));
    }
    if f as i64 + w as i64 > 32 {
        return Err(LuaError::new("trying to access non-existent bits"));
    }
    Ok((f as u32, w as u32))
}

fn mask(w: u32) -> u32 {
    if w >= 32 {
        u32::MAX
    } else {
        (1u32 << w) - 1
    }
}

pub fn extract(x: f64, field: f64, width: Option<f64>) -> LResult<f64> {
    let n = u32_of(x);
    let (f, w) = field_width(field, width, "extract", 2)?;
    Ok(out((n >> f) & mask(w)))
}

pub fn replace(x: f64, v: f64, field: f64, width: Option<f64>) -> LResult<f64> {
    let n = u32_of(x);
    let v = u32_of(v);
    let (f, w) = field_width(field, width, "replace", 3)?;
    let m = mask(w);
    Ok(out((n & !(m << f)) | ((v & m) << f)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operands_wrap_like_luau() {
        assert_eq!(band(&[1.5, 3.9]), 1.0);
        assert_eq!(band(&[-1.0, 255.0]), 255.0);
        assert_eq!(band(&[4294967301.0, 7.0]), 5.0);
        assert_eq!(band(&[]), 4294967295.0);
        assert_eq!(bor(&[9223372036854775808.0, 5.0]), 5.0);
        assert_eq!(bor(&[f64::NAN, 5.0]), 5.0);
        assert!(btest(&[]));
        assert!(!btest(&[1.0, 2.0]));
    }

    #[test]
    fn shifts_and_rotates() {
        assert_eq!(lshift(1.0, 32.0), 0.0);
        assert_eq!(lshift(1.0, -1.0), 0.0);
        assert_eq!(lshift(4294967295.0, 4.0), 4294967280.0);
        assert_eq!(rshift(255.0, -4.0), 4080.0);
        assert_eq!(arshift(2147483648.0, 31.0), 4294967295.0);
        assert_eq!(arshift(2147483648.0, 40.0), 4294967295.0);
        assert_eq!(arshift(2147483648.0, -1.0), 0.0);
        assert_eq!(arshift(8.0, -1.0), 16.0);
        assert_eq!(lrotate(1.0, -1.0), 2147483648.0);
        assert_eq!(lrotate(1.0, 33.0), 2.0);
        assert_eq!(rrotate(1.0, -1.0), 2.0);
        assert_eq!(rrotate(1.0, 1.0), 2147483648.0);
    }

    #[test]
    fn fields_and_counts() {
        assert_eq!(extract(305419896.0, 8.0, Some(8.0)).unwrap(), 86.0);
        assert_eq!(extract(255.0, 4.0, Some(4.0)).unwrap(), 15.0);
        assert_eq!(extract(4294967295.0, 0.0, Some(32.0)).unwrap(), 4294967295.0);
        assert_eq!(replace(0.0, 255.0, 8.0, Some(8.0)).unwrap(), 65280.0);
        assert_eq!(replace(0.0, 511.0, 0.0, Some(8.0)).unwrap(), 255.0);
        assert_eq!(extract(1.0, 32.0, None).err().unwrap().msg.to_string_lossy(), "trying to access non-existent bits");
        assert_eq!(extract(1.0, -1.0, None).err().unwrap().msg.to_string_lossy(), "invalid argument #2 to 'extract' (field cannot be negative)");
        assert_eq!(extract(1.0, 0.0, Some(0.0)).err().unwrap().msg.to_string_lossy(), "invalid argument #3 to 'extract' (width must be positive)");
        assert_eq!(replace(1.0, 1.0, 0.0, Some(0.0)).err().unwrap().msg.to_string_lossy(), "invalid argument #4 to 'replace' (width must be positive)");
        assert_eq!((countlz(0.0), countlz(1.0), countrz(0.0), countrz(8.0)), (32.0, 31.0, 32.0, 3.0));
        assert_eq!(byteswap(305419896.0), 2018915346.0);
        assert_eq!(bnot(1.9), 4294967294.0);
    }
}

/// Check numbers using Luau's numeric-string coercion and argument error text.
fn number(args: &[crate::Value], i: usize, name: &str) -> LResult<f64> {
    use crate::{LuaType, Value};
    match args.get(i) {
        Some(Value::Num(n)) => Ok(*n),
        Some(Value::Str(s)) => crate::stdlib::tonumber(s).ok_or_else(|| LuaError::new(format!("invalid argument #{} to '{name}' (number expected, got string)", i + 1))),
        Some(v) => Err(LuaError::new(format!("invalid argument #{} to '{name}' (number expected, got {})", i + 1, v.lua_type()))),
        None => Err(LuaError::new(format!("missing argument #{} to '{name}' (number expected)", i + 1))),
    }
}

/// The bit32 call boundary accepts dynamic values, as Luau does.
pub fn call(name: &str, args: &[crate::Value]) -> LResult<crate::Value> {
    use crate::Value;
    if matches!(name, "band" | "bor" | "bxor" | "btest") {
        let xs: Vec<f64> = (0..args.len()).map(|i| number(args, i, name)).collect::<LResult<_>>()?;
        return Ok(match name {
            "band" => Value::Num(band(&xs)),
            "bor" => Value::Num(bor(&xs)),
            "bxor" => Value::Num(bxor(&xs)),
            _ => Value::Bool(btest(&xs)),
        });
    }
    let n = number(args, 0, name)?;
    let r = match name {
        "bnot" => bnot(n),
        "countlz" => countlz(n),
        "countrz" => countrz(n),
        "byteswap" => byteswap(n),
        "lshift" => lshift(n, number(args, 1, name)?),
        "rshift" => rshift(n, number(args, 1, name)?),
        "arshift" => arshift(n, number(args, 1, name)?),
        "lrotate" => lrotate(n, number(args, 1, name)?),
        "rrotate" => rrotate(n, number(args, 1, name)?),
        "extract" => {
            let f = number(args, 1, name)?;
            let w = match args.get(2) { None | Some(Value::Nil) => None, _ => Some(number(args, 2, name)?) };
            extract(n, f, w)?
        }
        "replace" => {
            let v = number(args, 1, name)?;
            let f = number(args, 2, name)?;
            let w = match args.get(3) { None | Some(Value::Nil) => None, _ => Some(number(args, 3, name)?) };
            replace(n, v, f, w)?
        }
        _ => return Err(LuaError::new("unsupported bit32 function")),
    };
    Ok(Value::Num(r))
}

#[cfg(test)]
mod boundary_tests {
    use super::*;
    use crate::Value;
    #[test]
    fn numeric_strings_and_errors() {
        let x = call("band", &[Value::Str(" 0xff ".into()), Value::Num(7.0)]).unwrap();
        assert!(matches!(x, Value::Num(7.0)));
        assert_eq!(call("bnot", &[]).err().unwrap().msg.to_string_lossy(), "missing argument #1 to 'bnot' (number expected)");
        assert_eq!(call("bxor", &[Value::Bool(false)]).err().unwrap().msg.to_string_lossy(), "invalid argument #1 to 'bxor' (number expected, got boolean)");
        for i in [2147483648.0, -2147483648.0, f64::INFINITY, f64::NAN] {
            assert_eq!(lshift(5.0, i), 5.0);
            assert_eq!(rshift(5.0, i), 5.0);
            assert_eq!(arshift(2147483648.0, i), 2147483648.0);
        }
    }
}

pub fn call_num(name: &str, args: &[crate::Value]) -> LResult<f64> {
    call(name, args)?.as_num()
}
pub fn call_bool(name: &str, args: &[crate::Value]) -> LResult<bool> {
    call(name, args)?.as_bool()
}
