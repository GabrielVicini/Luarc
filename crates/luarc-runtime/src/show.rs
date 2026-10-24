//! `tostring`/`print` formatting, `type()` names and truthiness.

use std::io::Write;

use crate::handle::Handle;
use dumpster::Trace;

use crate::value::{Arr, FalseOr, LFn, LMap, LStr, MetaRec, PcallVal, Rec};

/// Formats a number deterministically:
/// * integral values with magnitude below 1e16 print without a fraction (`42`, `-0`);
/// * `nan`, `inf`, `-inf` for exceptional values;
/// * otherwise the shortest digit string that round-trips, in fixed notation when the
///   decimal exponent is in `-5..17`, else scientific (`1e+20`, `1.5e-07`).
pub fn fmt_num(x: f64, out: &mut Vec<u8>) {
    if x.is_nan() {
        out.extend_from_slice(b"nan");
    } else if x.is_infinite() {
        out.extend_from_slice(if x > 0.0 { b"inf" } else { b"-inf" });
    } else if x == 0.0 {
        out.extend_from_slice(if x.is_sign_negative() { b"-0" } else { b"0" });
    } else if x.fract() == 0.0 && x.abs() < 1e16 {
        let _ = write!(out, "{}", x as i64);
    } else {
        // Shortest round-trip digits come from Rust's `{:e}` formatting.
        let s = format!("{:e}", x);
        let (mant, exp) = s.split_once('e').expect("exponent");
        let exp: i32 = exp.parse().expect("exponent digits");
        let (neg, mant) = match mant.strip_prefix('-') {
            Some(m) => (true, m),
            None => (false, mant),
        };
        let digits: String = mant.chars().filter(|c| *c != '.').collect();
        if neg {
            out.push(b'-');
        }
        if (-5..17).contains(&exp) {
            if exp < 0 {
                out.extend_from_slice(b"0.");
                for _ in 0..(-exp - 1) {
                    out.push(b'0');
                }
                out.extend_from_slice(digits.as_bytes());
            } else {
                let int_len = exp as usize + 1;
                if digits.len() <= int_len {
                    out.extend_from_slice(digits.as_bytes());
                    for _ in digits.len()..int_len {
                        out.push(b'0');
                    }
                } else {
                    out.extend_from_slice(digits[..int_len].as_bytes());
                    out.push(b'.');
                    out.extend_from_slice(digits[int_len..].as_bytes());
                }
            }
        } else {
            out.extend_from_slice(digits[..1].as_bytes());
            if digits.len() > 1 {
                out.push(b'.');
                out.extend_from_slice(digits[1..].as_bytes());
            }
            let _ = write!(out, "e{}{:02}", if exp < 0 { '-' } else { '+' }, exp.abs());
        }
    }
}

pub fn num_to_string(x: f64) -> String {
    let mut v = Vec::new();
    fmt_num(x, &mut v);
    String::from_utf8(v).expect("ascii")
}

pub fn num_to_lstr(x: f64) -> LStr {
    let mut v = Vec::new();
    fmt_num(x, &mut v);
    LStr::from_vec(v)
}

/// The `tostring` conversion for every runtime value.
pub trait LuaDisplay {
    fn fmt_lua(&self, out: &mut Vec<u8>);
}

impl LuaDisplay for f64 {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        fmt_num(*self, out)
    }
}
impl LuaDisplay for LStr {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.as_bytes())
    }
}
impl LuaDisplay for &str {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.as_bytes())
    }
}
impl LuaDisplay for bool {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(if *self { b"true" } else { b"false" })
    }
}
impl LuaDisplay for () {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(b"nil")
    }
}
impl<T: LuaDisplay> LuaDisplay for Option<T> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        match self {
            Some(v) => v.fmt_lua(out),
            None => out.extend_from_slice(b"nil"),
        }
    }
}
impl<T: LuaDisplay + Trace> LuaDisplay for FalseOr<T> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        match self {
            FalseOr::Val(v) => v.fmt_lua(out),
            FalseOr::False => out.extend_from_slice(b"false"),
        }
    }
}
impl<T: LuaDisplay + Trace> LuaDisplay for PcallVal<T> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        match self {
            PcallVal::Ok(v) => v.fmt_lua(out),
            PcallVal::Err(e) => e.fmt_lua(out),
        }
    }
}
pub(crate) fn fmt_addr(kind: &str, p: usize, out: &mut Vec<u8>) {
    let _ = write!(out, "{kind}: 0x{:012x}", p);
}
impl<T: Trace> LuaDisplay for Arr<T> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        fmt_addr("table", self.addr(), out)
    }
}
impl<K: Trace + Eq + std::hash::Hash, V: Trace> LuaDisplay for LMap<K, V> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        fmt_addr("table", self.addr(), out)
    }
}
impl<T: Trace> LuaDisplay for Rec<T> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        fmt_addr("table", self.addr(), out)
    }
}
// Luau 0.743: metatable attachment preserves table display, type, truthiness and identity.
impl<T: Trace, P: Trace> LuaDisplay for MetaRec<T, P> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        fmt_addr("table", self.addr(), out)
    }
}
impl<A, R> LuaDisplay for LFn<A, R> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        fmt_addr("function", self.addr(), out)
    }
}
impl<T: 'static> LuaDisplay for Handle<T> {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        self.fmt_native(out)
    }
}

pub fn tostring(v: &dyn LuaDisplay) -> LStr {
    let mut out = Vec::new();
    v.fmt_lua(&mut out);
    LStr::from_vec(out)
}

/// Result of the `type()` builtin.
pub trait LuaType {
    fn lua_type(&self) -> &'static str;
}

/// Luau tests the represented value, including nil inside internal union wrappers.
#[inline]
pub fn is_nil<T: LuaType + ?Sized>(value: &T) -> bool {
    value.lua_type() == "nil"
}
impl LuaType for f64 {
    fn lua_type(&self) -> &'static str {
        "number"
    }
}
impl LuaType for LStr {
    fn lua_type(&self) -> &'static str {
        "string"
    }
}
impl LuaType for bool {
    fn lua_type(&self) -> &'static str {
        "boolean"
    }
}
impl LuaType for () {
    fn lua_type(&self) -> &'static str {
        "nil"
    }
}
impl<T: LuaType> LuaType for Option<T> {
    fn lua_type(&self) -> &'static str {
        self.as_ref().map_or("nil", |v| v.lua_type())
    }
}
impl<T: LuaType + Trace> LuaType for FalseOr<T> {
    fn lua_type(&self) -> &'static str {
        match self {
            FalseOr::Val(v) => v.lua_type(),
            FalseOr::False => "boolean",
        }
    }
}
impl<T: LuaType + Trace> LuaType for PcallVal<T> {
    fn lua_type(&self) -> &'static str {
        match self {
            PcallVal::Ok(v) => v.lua_type(),
            PcallVal::Err(_) => "string",
        }
    }
}
impl<T: Trace> LuaType for Arr<T> {
    fn lua_type(&self) -> &'static str {
        "table"
    }
}
impl<K: Trace + Eq + std::hash::Hash, V: Trace> LuaType for LMap<K, V> {
    fn lua_type(&self) -> &'static str {
        "table"
    }
}
impl<T: Trace> LuaType for Rec<T> {
    fn lua_type(&self) -> &'static str {
        "table"
    }
}
impl<T: Trace, P: Trace> LuaType for MetaRec<T, P> {
    fn lua_type(&self) -> &'static str {
        "table"
    }
}
impl<A, R> LuaType for LFn<A, R> {
    fn lua_type(&self) -> &'static str {
        "function"
    }
}
impl<T> LuaType for Handle<T> {
    fn lua_type(&self) -> &'static str {
        "userdata"
    }
}

/// Truthiness: only `nil` and `false` are falsey.
pub trait Truthy {
    fn truthy(&self) -> bool;
}
impl Truthy for bool {
    #[inline]
    fn truthy(&self) -> bool {
        *self
    }
}
impl<T: Truthy> Truthy for Option<T> {
    #[inline]
    fn truthy(&self) -> bool {
        self.as_ref().is_some_and(|v| v.truthy())
    }
}
impl<T: Truthy + Trace> Truthy for FalseOr<T> {
    #[inline]
    fn truthy(&self) -> bool {
        match self {
            FalseOr::Val(v) => v.truthy(),
            FalseOr::False => false,
        }
    }
}
impl<T: Truthy + Trace> Truthy for PcallVal<T> {
    fn truthy(&self) -> bool {
        // Luau's protected success value keeps its own nil/false truthiness.
        match self {
            PcallVal::Ok(value) => value.truthy(),
            PcallVal::Err(_) => true,
        }
    }
}
macro_rules! always_truthy {
    ($($t:ty),*) => { $(impl Truthy for $t { #[inline] fn truthy(&self) -> bool { true } })* };
}
always_truthy!(f64, i128, LStr);
impl Truthy for () {
    fn truthy(&self) -> bool {
        false
    }
}
impl<T: Trace> Truthy for Arr<T> {
    fn truthy(&self) -> bool {
        true
    }
}
impl<K: Trace + Eq + std::hash::Hash, V: Trace> Truthy for LMap<K, V> {
    fn truthy(&self) -> bool {
        true
    }
}
impl<T: Trace> Truthy for Rec<T> {
    fn truthy(&self) -> bool {
        true
    }
}
impl<T: Trace, P: Trace> Truthy for MetaRec<T, P> {
    fn truthy(&self) -> bool {
        true
    }
}
impl<A, R> Truthy for LFn<A, R> {
    fn truthy(&self) -> bool {
        true
    }
}
impl<T> Truthy for Handle<T> {
    fn truthy(&self) -> bool {
        true
    }
}

/// `==` for values of one static type (identity for tables, functions and native
/// handles without `PartialEq`).
pub trait LuaEq {
    fn lua_eq(&self, other: &Self) -> bool;
}
impl LuaEq for f64 {
    #[inline]
    fn lua_eq(&self, o: &Self) -> bool {
        self == o
    }
}
impl LuaEq for LStr {
    #[inline]
    fn lua_eq(&self, o: &Self) -> bool {
        self == o
    }
}
impl LuaEq for bool {
    #[inline]
    fn lua_eq(&self, o: &Self) -> bool {
        self == o
    }
}
impl LuaEq for () {
    fn lua_eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T: LuaEq + LuaType> LuaEq for Option<T> {
    fn lua_eq(&self, o: &Self) -> bool {
        match (self, o) {
            (Some(a), Some(b)) => a.lua_eq(b),
            (None, None) => true,
            (Some(value), None) | (None, Some(value)) => is_nil(value),
        }
    }
}
impl<T: LuaEq + Trace> LuaEq for FalseOr<T> {
    fn lua_eq(&self, o: &Self) -> bool {
        match (self, o) {
            (FalseOr::Val(a), FalseOr::Val(b)) => a.lua_eq(b),
            (FalseOr::False, FalseOr::False) => true,
            _ => false,
        }
    }
}
impl<T: LuaEq + Trace> LuaEq for PcallVal<T> {
    fn lua_eq(&self, o: &Self) -> bool {
        match (self, o) {
            (PcallVal::Ok(a), PcallVal::Ok(b)) => a.lua_eq(b),
            (PcallVal::Err(a), PcallVal::Err(b)) => a == b,
            _ => false,
        }
    }
}
impl<T: Trace> LuaEq for Arr<T> {
    fn lua_eq(&self, o: &Self) -> bool {
        self.ptr_eq(o)
    }
}
impl<K: Trace + Eq + std::hash::Hash, V: Trace> LuaEq for LMap<K, V> {
    fn lua_eq(&self, o: &Self) -> bool {
        self.ptr_eq(o)
    }
}
impl<T: Trace> LuaEq for Rec<T> {
    fn lua_eq(&self, o: &Self) -> bool {
        self.ptr_eq(o)
    }
}
impl<T: Trace, P: Trace> LuaEq for MetaRec<T, P> {
    fn lua_eq(&self, o: &Self) -> bool {
        self.ptr_eq(o)
    }
}
impl<A, R> LuaEq for LFn<A, R> {
    fn lua_eq(&self, o: &Self) -> bool {
        self.ptr_eq(o)
    }
}
impl<T: 'static> LuaEq for Handle<T> {
    fn lua_eq(&self, o: &Self) -> bool {
        self.native_eq(o)
    }
}

#[inline]
pub fn truthy<T: Truthy>(v: &T) -> bool {
    v.truthy()
}

#[inline]
pub fn eq<T: LuaEq>(a: &T, b: &T) -> bool {
    a.lua_eq(b)
}

#[cfg(test)]
mod tests {
    use super::num_to_string as s;

    #[test]
    fn protected_nil_and_false_keep_their_value_semantics() {
        use super::*;
        let nil = PcallVal::Ok(None::<f64>);
        assert!(is_nil(&nil));
        assert!(!truthy(&nil));
        assert!(eq(&Some(nil.clone()), &None));
        assert!(eq(&None, &Some(nil.clone())));
        let conditional = FalseOr::Val(nil);
        assert!(is_nil(&Some(conditional.clone())));
        assert!(!truthy(&conditional));
        assert!(eq(&Some(conditional), &None));
        let false_value = PcallVal::Ok(Some(false));
        assert!(!is_nil(&false_value));
        assert!(!truthy(&false_value));
        assert!(!eq(&Some(false_value), &None));
        let false_branch = FalseOr::<PcallVal<Option<f64>>>::False;
        assert!(!is_nil(&false_branch));
        assert!(!truthy(&false_branch));
        let error = PcallVal::<Option<f64>>::Err(LStr::from(""));
        assert!(!is_nil(&error));
        assert!(truthy(&error));
        assert!(truthy(&PcallVal::Ok(Some(0.0))));
        assert!(truthy(&PcallVal::Ok(Some(LStr::from("")))));
        assert!(truthy(&PcallVal::Ok(Some(true))));
        assert!(is_nil(&PcallVal::Ok(())));
        assert!(!truthy(&PcallVal::Ok(())));
    }

    #[test]
    fn nested_dynamic_nil_and_native_integer_need_no_boxing() {
        use super::*;
        let nil = Some(PcallVal::Ok(Some(crate::Value::Nil)));
        assert!(is_nil(&nil));
        assert!(!truthy(&nil));
        assert!(eq(&nil, &None));
        let integer_nil = PcallVal::Ok(None::<i128>);
        assert!(is_nil(&integer_nil));
        assert!(!truthy(&integer_nil));
        assert!(eq(&Some(integer_nil), &None));
        assert!(truthy(&PcallVal::Ok(Some(0_i128))));
        assert!(!is_nil(&PcallVal::Ok(Some(0_i128))));
    }

    #[test]
    fn metarec_keeps_table_identity_and_traits() {
        use super::*;
        let a = MetaRec::<_, Rec<f64>>::new(());
        let alias = a.clone();
        let b = MetaRec::<_, Rec<f64>>::new(());
        let before = tostring(&a);
        a.attach(Rec::new(7.0));
        assert_eq!(a.lua_type(), "table");
        assert!(truthy(&a));
        assert!(eq(&a, &alias));
        assert!(!eq(&a, &b));
        assert_eq!(before, tostring(&alias));
        assert_ne!(tostring(&a), tostring(&b));
    }

    #[test]
    #[cfg_attr(miri, ignore = "Miri perturbs pow/powi results by design; exact digits are checked natively")]
    fn number_formatting() {
        assert_eq!(s(42.0), "42");
        assert_eq!(s(-0.0), "-0");
        assert_eq!(s(0.1), "0.1");
        assert_eq!(s(1.0 / 3.0), "0.3333333333333333");
        assert_eq!(s(1e20), "1e+20");
        assert_eq!(s(1.5e-7), "1.5e-07");
        assert_eq!(s(123.456), "123.456");
        assert_eq!(s(1e16), "10000000000000000");
        assert_eq!(s(2f64.powi(53)), "9007199254740992");
        assert_eq!(s(f64::INFINITY), "inf");
        assert_eq!(s(f64::NAN), "nan");
        assert_eq!(s(0.00001), "0.00001");
        assert_eq!(s(-2.5), "-2.5");
    }
}

impl LuaDisplay for i128 {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.to_string().as_bytes())
    }
}
impl LuaType for i128 {
    fn lua_type(&self) -> &'static str {
        "number"
    }
}
impl LuaEq for i128 {
    #[inline]
    fn lua_eq(&self, o: &Self) -> bool {
        self == o
    }
}
