//! Nil-preserving table.pack storage and dynamic value lists.

use crate::{Arr, LResult, Value};
use crate::dynamic::{to_value, ToValue};

/// A pack's explicit count includes nil slots, including trailing ones.
pub fn table(values: Vec<Option<Value>>) -> Arr<Option<Value>> {
    Arr::from_vec(values.into_iter().map(|v| v.filter(|v| !matches!(v, Value::Nil))).collect())
}

pub fn from_values(values: Vec<Value>) -> Vec<Option<Value>> {
    values.into_iter().map(|v| if matches!(v, Value::Nil) { None } else { Some(v) }).collect()
}

pub fn slot<T: ToValue>(value: T) -> Option<Value> {
    let v = to_value(value);
    if matches!(v, Value::Nil) { None } else { Some(v) }
}

/// Convert a typed result tail without losing its nil positions.
pub fn boxed<T: ToValue + Clone>(values: &[Option<T>], first: usize) -> Vec<Option<Value>> {
    values.get(first..).unwrap_or_default().iter().map(|v| {
        let v = to_value(v.clone());
        if matches!(v, Value::Nil) { None } else { Some(v) }
    }).collect()
}

pub fn unpack(t: &Arr<Option<Value>>, i: Option<f64>, j: Option<f64>, nargs: usize) -> LResult<Vec<Option<Value>>> {
    crate::va::unpack(t, i, j, nargs).map(|values| values.into_iter().map(|v| v.flatten()).collect())
}

/// The protected call returns either true and all results, or false and its error.
pub fn protected(f: impl FnOnce() -> LResult<Vec<Option<Value>>>) -> Vec<Option<Value>> {
    match crate::callback::guard(f).and_then(|r| r) {
        Ok(values) => crate::va::with_rest(vec![Some(Value::Bool(true))], &values, 0),
        Err(e) => vec![Some(Value::Bool(false)), Some(Value::Str(e.msg))],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_retains_nil_positions_and_count() {
        let t = table(vec![Some(Value::Num(1.0)), None, Some(Value::Nil), Some(Value::Bool(false))]);
        assert_eq!(t.len(), 4.0);
        assert!(t.get(2.0).flatten().is_none());
        assert!(t.get(3.0).flatten().is_none());
        let out = unpack(&t, Some(0.0), Some(5.0), 3).unwrap();
        assert_eq!(out.len(), 6);
        assert!(out[0].is_none() && out[2].is_none() && out[3].is_none() && out[5].is_none());
        assert!(matches!(out[4], Some(Value::Bool(false))));
    }

    #[test]
    fn protected_preserves_result_arity_on_success_and_failure() {
        let empty = protected(|| Ok(vec![]));
        assert_eq!(empty.len(), 1);
        assert!(matches!(empty[0], Some(Value::Bool(true))));
        let ok = protected(|| Ok(vec![Some(Value::Num(1.0)), None]));
        assert_eq!(ok.len(), 3);
        assert!(matches!(ok[0], Some(Value::Bool(true))));
        assert!(ok[2].is_none());
        let err = protected(|| Err(crate::LuaError::new("sentinel")));
        assert_eq!(err.len(), 2);
        assert!(matches!(err[0], Some(Value::Bool(false))));
    }
}
