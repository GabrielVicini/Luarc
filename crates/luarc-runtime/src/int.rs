//! The exact `integer` source type (runtime `i128`): the values of native
//! `i64`/`u64`/`i128`/`u128` items, which `number` (f64) cannot hold exactly above
//! 2^53. Arithmetic is checked (overflow is a language error, never wrapping);
//! conversions to and from `number` and native widths are checked and exact.

use crate::error::{LResult, LuaError};

fn overflow(op: &str) -> LuaError {
    LuaError::new(format!("integer overflow in '{op}'"))
}

#[inline]
pub fn add(a: i128, b: i128) -> LResult<i128> {
    a.checked_add(b).ok_or_else(|| overflow("+"))
}
#[inline]
pub fn sub(a: i128, b: i128) -> LResult<i128> {
    a.checked_sub(b).ok_or_else(|| overflow("-"))
}
#[inline]
pub fn mul(a: i128, b: i128) -> LResult<i128> {
    a.checked_mul(b).ok_or_else(|| overflow("*"))
}
#[inline]
pub fn neg(a: i128) -> LResult<i128> {
    a.checked_neg().ok_or_else(|| overflow("-"))
}
/// Floor division (Lua `//`).
pub fn idiv(a: i128, b: i128) -> LResult<i128> {
    if b == 0 {
        return Err(LuaError::new("attempt to perform 'n//0'"));
    }
    let q = a.checked_div(b).ok_or_else(|| overflow("//"))?;
    Ok(if (a % b != 0) && ((a < 0) != (b < 0)) { q - 1 } else { q })
}
/// Floor modulo (Lua `%`): the result has the sign of the divisor.
pub fn modulo(a: i128, b: i128) -> LResult<i128> {
    if b == 0 {
        return Err(LuaError::new("attempt to perform 'n%0'"));
    }
    if b == -1 {
        // `i128::MIN % -1` is 0 (only the quotient overflows)
        return Ok(0);
    }
    let r = a.checked_rem(b).ok_or_else(|| overflow("%"))?;
    Ok(if r != 0 && ((r < 0) != (b < 0)) { r + b } else { r })
}

/// `integer` → `number`, exact (Lua `tonumber(i)` for a value above 2^53 that
/// would round is an error, not a silently different number).
/// 2^127: the first f64 above every i128 (`as i128` saturates there).
const TWO_127: f64 = 170141183460469231731687303715884105728.0;

pub fn to_number(a: i128) -> LResult<f64> {
    let f = a as f64;
    if (-TWO_127..TWO_127).contains(&f) && (f as i128) == a {
        Ok(f)
    } else {
        Err(LuaError::new(format!("integer {a} has no exact number representation")))
    }
}
/// Operand of `/` and `^` (float operations, like Lua): exact conversion.
#[inline]
pub fn float_operand(a: i128) -> LResult<f64> {
    to_number(a)
}
/// `number` → `integer` when it is integral (Lua `math.tointeger`).
pub fn from_number(x: f64) -> Option<i128> {
    if x.fract() == 0.0 && (-TWO_127..TWO_127).contains(&x) {
        Some(x as i128)
    } else {
        None
    }
}

/// Native integer → `integer` (u128 above i128::MAX is an error).
pub fn to_int<T: TryInto<i128> + std::fmt::Display + Copy>(x: T) -> LResult<i128> {
    x.try_into().map_err(|_| LuaError::new(format!("native integer {x} does not fit the integer type")))
}
/// `integer` → native integer of width `T`, checked.
pub fn from_int<T: TryFrom<i128>>(x: i128) -> LResult<T> {
    T::try_from(x).map_err(|_| LuaError::new(format!("integer {x} is out of range for {}", std::any::type_name::<T>())))
}
/// `number` → native 64/128-bit integer, checked (must be integral and in range).
pub fn from_num_int<T: TryFrom<i128>>(x: f64) -> LResult<T> {
    match from_number(x) {
        Some(i) => from_int(i),
        None => Err(LuaError::new(format!("number {} is not an integer", crate::show::num_to_string(x)))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_conversions_and_floor_ops() {
        // i128::MAX rounds to 2^127 as f64: not exact
        assert!(to_number(i128::MAX).is_err());
        assert!(to_number(i128::MAX - 1).is_err());
        assert_eq!(to_number(i128::MIN).ok(), Some(-TWO_127));
        assert_eq!(to_number(1 << 53).ok(), Some(9007199254740992.0));
        assert!(to_number((1 << 53) + 1).is_err());
        assert_eq!(from_number(-TWO_127), Some(i128::MIN));
        assert_eq!(from_number(TWO_127), None);
        assert_eq!(from_number(1.7e38), Some(1.7e38 as i128));
        assert_eq!(from_number(f64::NAN), None);
        assert_eq!(from_number(f64::INFINITY), None);
        assert_eq!(from_number(2.5), None);
        assert_eq!(modulo(i128::MIN, -1).ok(), Some(0));
        assert_eq!(modulo(-7, 3).ok(), Some(2));
        assert_eq!(modulo(7, -3).ok(), Some(-2));
        assert!(idiv(i128::MIN, -1).is_err());
        assert_eq!(idiv(-7, 2).ok(), Some(-4));
        assert_eq!(modulo(1, 0).unwrap_err().msg.as_bytes(), b"attempt to perform 'n%0'");
    }
}
