//! Variadic arguments: a function's `...` is the vector of its extra arguments,
//! `Vec<Option<T>>` (an argument may be nil). The length is known only at run
//! time; every other value list keeps its static count.

use crate::show::LuaDisplay;
use crate::value::Arr;
use crate::{LResult, LuaError, Trace};

/// Value `i` (0-based) of `...`; nil past the end.
pub fn get<T: Clone>(va: &[Option<T>], i: usize) -> Option<T> {
    va.get(i).cloned().flatten()
}

/// The values of `...` from index `i` (0-based) on.
pub fn rest<T: Clone>(va: &[Option<T>], i: usize) -> Vec<Option<T>> {
    va.get(i..).map(|s| s.to_vec()).unwrap_or_default()
}

/// `fixed` followed by the values of `...` from index `i` on (a call's extra
/// arguments ending in `...`).
pub fn with_rest<T: Clone>(mut fixed: Vec<Option<T>>, va: &[Option<T>], i: usize) -> Vec<Option<T>> {
    fixed.extend(rest(va, i));
    fixed
}

/// `select(n, ...)`: the 0-based index of the first selected value. As in Luau
/// 0.743, `n` is truncated to an integer, a negative `n` counts from the end, and
/// `n` past the end selects nothing.
pub fn select(len: usize, n: f64) -> LResult<usize> {
    let n = crate::stdlib::check_int(n) as i64;
    let len = len as i64;
    let first = if n < 0 { len + n } else { n - 1 };
    if n == 0 || first < 0 {
        return Err(LuaError::new("invalid argument #1 to 'select' (index out of range)"));
    }
    Ok(first.min(len) as usize)
}

/// `{a, b, ...}`: an array of the fixed items and the values of `...` from index
/// `i` on. Arrays cannot hold nil (LUARC restriction), so a nil value is an error.
pub fn array<T: Trace + Clone + 'static>(mut fixed: Vec<T>, va: &[Option<T>], i: usize) -> LResult<Arr<T>> {
    for v in va.get(i..).unwrap_or_default() {
        match v {
            Some(x) => fixed.push(x.clone()),
            None => return Err(LuaError::new("arrays cannot contain nil")),
        }
    }
    Ok(Arr::from_vec(fixed))
}

/// `table.unpack(t, i, j)` as in Luau 0.743: `i` defaults to 1 and `j` to `#t`,
/// both truncated like `luaL_checkinteger`; positions outside the array give nil.
/// Luau fails when the results would not fit its 8000-slot C stack frame, which
/// also holds the `nargs` arguments.
pub fn unpack<T: Trace + Clone + 'static>(t: &Arr<T>, i: Option<f64>, j: Option<f64>, nargs: usize) -> LResult<Vec<Option<T>>> {
    let i = i.map(crate::stdlib::check_int).unwrap_or(1) as i64;
    let e = match j {
        Some(j) => crate::stdlib::check_int(j) as i64,
        None => t.len() as i64,
    };
    if i > e {
        return Ok(Vec::new());
    }
    if e - i + 1 > (8000 - nargs) as i64 {
        return Err(LuaError::new("too many results to unpack"));
    }
    Ok((i..=e).map(|k| if k >= 1 { t.get_at((k - 1) as usize) } else { None }).collect())
}

/// `print(a, b, ...)`.
pub fn print<T: LuaDisplay>(fixed: &[&dyn LuaDisplay], va: &[Option<T>], i: usize) {
    let mut all: Vec<&dyn LuaDisplay> = fixed.to_vec();
    for v in va.get(i..).unwrap_or_default() {
        all.push(v);
    }
    crate::stdlib::print(&all);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn select_follows_luau() {
        // select(-1, 1, 2, 3) -> 3; select(2.7, a, b, c) -> b, c; select(5, a) -> nothing
        assert_eq!(select(3, -1.0).unwrap(), 2);
        assert_eq!(select(3, 2.7).unwrap(), 1);
        assert_eq!(select(1, 5.0).unwrap(), 1);
        assert_eq!(select(2, -2.0).unwrap(), 0);
        for bad in [0.0, -2.0, f64::INFINITY, f64::NAN] {
            assert!(select(1, bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn unpack_follows_luau() {
        let t = Arr::from_vec(vec![1.0, 2.0, 3.0]);
        assert_eq!(unpack(&t, None, None, 1).unwrap(), vec![Some(1.0), Some(2.0), Some(3.0)]);
        assert_eq!(unpack(&t, Some(0.0), Some(4.0), 3).unwrap(), vec![None, Some(1.0), Some(2.0), Some(3.0), None]);
        assert_eq!(unpack(&t, Some(2.7), Some(3.9), 3).unwrap(), vec![Some(2.0), Some(3.0)]);
        assert!(unpack(&t, Some(3.0), Some(1.0), 3).unwrap().is_empty());
        // inf truncates to i32::MIN: an empty range
        assert!(unpack(&t, Some(1.0), Some(f64::INFINITY), 3).unwrap().is_empty());
        assert_eq!(unpack(&t, Some(1.0), Some(7997.0), 3).unwrap().len(), 7997);
        assert!(unpack(&t, Some(1.0), Some(7998.0), 3).is_err());
        assert!(unpack(&t, Some(f64::NAN), None, 2).is_err());
    }

    #[test]
    fn get_and_rest_pad_with_nil() {
        let va = vec![Some(1.0), None, Some(3.0)];
        assert_eq!(get(&va, 0), Some(1.0));
        assert_eq!(get(&va, 1), None);
        assert_eq!(get(&va, 7), None);
        assert_eq!(rest(&va, 1), vec![None, Some(3.0)]);
        assert!(rest(&va, 9).is_empty());
        assert_eq!(with_rest(vec![Some(0.0)], &va, 2), vec![Some(0.0), Some(3.0)]);
    }
}
