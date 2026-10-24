//! Checked conversions between source values and native Rust values.
//!
//! * number → integer: must be finite, integral and in range, otherwise a language error.
//! * number → f32: NaN/±inf pass through; finite values beyond `f32::MAX` are an error;
//!   other values round to nearest (ties to even).
//! * integer → number: must be exactly representable (|v| ≤ 2^53), otherwise an error.
//! * string → `&str`/`String`/`char`: validated UTF-8 (no replacement characters).

use crate::error::{LResult, LuaError};
use crate::value::LStr;

pub trait FromNum: Sized {
    fn from_num(x: f64) -> LResult<Self>;
}

pub trait ToNum {
    fn to_num(self) -> LResult<f64>;
}

fn int_err(x: f64, ty: &str) -> LuaError {
    if !x.is_finite() || x.fract() != 0.0 {
        LuaError::new(format!(
            "number {} has no integer representation (expected {ty})",
            crate::show::num_to_string(x)
        ))
    } else {
        LuaError::new(format!("number {} is out of range for {ty}", crate::show::num_to_string(x)))
    }
}

macro_rules! int_conv {
    ($($t:ty: $lo:expr, $hi:expr;)*) => {$(
        impl FromNum for $t {
            #[inline]
            fn from_num(x: f64) -> LResult<$t> {
                // Bounds are exact powers of two: lo <= x < hi.
                if x.is_finite() && x.fract() == 0.0 && x >= $lo && x < $hi {
                    Ok(x as $t)
                } else {
                    Err(int_err(x, stringify!($t)))
                }
            }
        }
        impl ToNum for $t {
            #[inline]
            #[allow(unused_comparisons)]
            fn to_num(self) -> LResult<f64> {
                const LIMIT: i128 = 1i128 << 53;
                let w = self as i128;
                if w <= LIMIT && w >= -LIMIT {
                    Ok(self as f64)
                } else {
                    Err(LuaError::new(format!(
                        "native {} value {} cannot be represented exactly as a number",
                        stringify!($t), self
                    )))
                }
            }
        }
    )*};
}

int_conv! {
    i8: -128.0, 128.0;
    i16: -32768.0, 32768.0;
    i32: -2147483648.0, 2147483648.0;
    i64: -9223372036854775808.0, 9223372036854775808.0;
    isize: -(isize::MAX as f64) - 1.0, (isize::MAX as f64) + 1.0;
    u8: 0.0, 256.0;
    u16: 0.0, 65536.0;
    u32: 0.0, 4294967296.0;
    u64: 0.0, 18446744073709551616.0;
    usize: 0.0, (usize::MAX as f64) + 1.0;
}

impl FromNum for f64 {
    #[inline]
    fn from_num(x: f64) -> LResult<f64> {
        Ok(x)
    }
}
impl ToNum for f64 {
    #[inline]
    fn to_num(self) -> LResult<f64> {
        Ok(self)
    }
}
impl FromNum for f32 {
    fn from_num(x: f64) -> LResult<f32> {
        if x.is_finite() && x.abs() > f32::MAX as f64 {
            Err(LuaError::new(format!("number {} is out of range for f32", crate::show::num_to_string(x))))
        } else {
            Ok(x as f32)
        }
    }
}
impl ToNum for f32 {
    fn to_num(self) -> LResult<f64> {
        Ok(self as f64)
    }
}

#[inline]
pub fn from_num<T: FromNum>(x: f64) -> LResult<T> {
    T::from_num(x)
}
#[inline]
pub fn to_num<T: ToNum>(x: T) -> LResult<f64> {
    x.to_num()
}

pub fn to_char(s: &LStr) -> LResult<char> {
    let st = s.as_str()?;
    let mut it = st.chars();
    match (it.next(), it.next()) {
        (Some(c), None) => Ok(c),
        _ => Err(LuaError::new(format!("expected a single-character string, got {:?}", st))),
    }
}

pub fn from_char(c: char) -> LStr {
    LStr::from(c.encode_utf8(&mut [0u8; 4]) as &str)
}

/// Native fixed-size array argument from a source array snapshot.
pub fn to_fixed_array<T, const N: usize>(v: Vec<T>) -> LResult<[T; N]> {
    let n = v.len();
    v.try_into().map_err(|_| LuaError::new(format!("expected an array of exactly {N} elements, got {n}")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_bounds() {
        assert_eq!(i32::from_num(2147483647.0).unwrap(), i32::MAX);
        assert!(i32::from_num(2147483648.0).is_err());
        assert!(u8::from_num(-1.0).is_err());
        assert!(u8::from_num(1.5).is_err());
        assert!(i64::from_num(f64::NAN).is_err());
        assert!(i64::from_num(9223372036854775808.0).is_err());
        assert_eq!(i64::from_num(-9223372036854775808.0).unwrap(), i64::MIN);
        assert!(u64::MAX.to_num().is_err());
        assert_eq!((1u64 << 53).to_num().unwrap(), 9007199254740992.0);
        assert!(((1u64 << 53) + 1).to_num().is_err());
        assert!(f32::from_num(1e300).is_err());
        assert!(f32::from_num(f64::INFINITY).unwrap().is_infinite());
    }
}

/// A by-value argument from a shared (`Arc`) handle: the object moves out only
/// when no native owner shares it any more (the handle was consumed already).
pub fn unwrap_shared<T>(a: std::sync::Arc<T>, what: &'static str) -> LResult<T> {
    std::sync::Arc::try_unwrap(a).map_err(|_| {
        LuaError::new(format!("{what} object is shared with native code and cannot be moved (it is still in use by another native object)"))
    })
}

/// A native value with no source representation in this position.
pub fn unrepresentable<T>(what: &'static str) -> LResult<T> {
    Err(LuaError::new(what))
}

/// A borrowing native enum given as a record of its variants (`{Buffer = ...}`)
/// must have exactly one variant field set. `set` holds, per
/// variant, whether its field is set.
pub fn one_variant(set: &[bool], enum_name: &str) -> LResult<()> {
    match set.iter().filter(|s| **s).count() {
        1 => Ok(()),
        0 => Err(LuaError::new(format!("{enum_name} value has no variant set (set exactly one field, such as {enum_name}.Variant(...))"))),
        n => Err(LuaError::new(format!("{enum_name} value has {n} variants set; exactly one is allowed"))),
    }
}

/// A variant of a borrowing enum that has no conversion here.
pub fn unsupported_variant<T>(enum_name: &str, variant: &str) -> LResult<T> {
    Err(LuaError::new(format!("variant {enum_name}.{variant} cannot be converted in this position")))
}
