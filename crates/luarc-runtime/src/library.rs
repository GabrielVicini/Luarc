//! Luau library operations that require byte-string or dynamic arguments.
use crate::{Arr, LResult, LStr, LuaError, LuaType, Value};

pub fn string_arg(args: &[Value], i: usize, name: &str) -> LResult<LStr> {
    match args.get(i) {
        Some(Value::Str(s)) => Ok(s.clone()),
        // Luau string library arguments accept numbers through tostring.
        Some(Value::Num(n)) => Ok(crate::show::tostring(n)),
        Some(v) => Err(LuaError::new(format!("invalid argument #{} to '{name}' (string expected, got {})", i + 1, v.lua_type()))),
        None => Err(LuaError::new(format!("missing argument #{} to '{name}' (string expected)", i + 1))),
    }
}

/// Luau split preserves empty fields and splits into individual bytes for "".
pub fn string_split(args: &[Value]) -> LResult<Arr<LStr>> {
    let s = string_arg(args, 0, "split")?;
    let sep = match args.get(1) {
        None | Some(Value::Nil) => LStr::from(","),
        _ => string_arg(args, 1, "split")?,
    };
    let s = s.as_bytes();
    let sep = sep.as_bytes();
    let mut out = Vec::new();
    if sep.is_empty() {
        out.extend(s.iter().map(|b| LStr::from_bytes(&[*b])));
    } else {
        let mut from = 0;
        while let Some(k) = s[from..].windows(sep.len()).position(|p| p == sep) {
            out.push(LStr::from_bytes(&s[from..from + k]));
            from += k + sep.len();
        }
        out.push(LStr::from_bytes(&s[from..]));
    }
    Ok(Arr::from_vec(out))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn split_empty_fields_and_bytes() {
        let s = |x: &str| Value::Str(x.into());
        let xs = string_split(&[s("a,,b"), s(",")]).unwrap().snapshot();
        assert_eq!(xs, vec![LStr::from("a"), LStr::from(""), LStr::from("b")]);
        assert_eq!(string_split(&[s(""), s("")]).unwrap().len(), 0.0);
        assert_eq!(string_split(&[s(""), s(",")]).unwrap().len(), 1.0);
        assert_eq!(string_split(&[Value::Num(123.0), Value::Num(2.0)]).unwrap().snapshot(), vec![LStr::from("1"), LStr::from("3")]);
        assert_eq!(string_split(&[Value::Str(LStr::from_bytes(&[255, 0])), s("")]).unwrap().snapshot(), vec![LStr::from_bytes(&[255]), LStr::from_bytes(&[0])]);
    }
}

/// Luau xpcall uses only the handler's first result, and traps handler failures.
pub fn xpcall(body: impl FnOnce() -> LResult<Vec<Value>>, handler: impl FnOnce(LStr) -> LResult<Value>) -> Vec<Value> {
    match body() {
        Ok(xs) => std::iter::once(Value::Bool(true)).chain(xs).collect(),
        Err(e) => vec![Value::Bool(false), crate::coroutine::non_yielding(|| handler(e.msg)).unwrap_or_else(|_| Value::Str("error in error handling".into()))],
    }
}

/// Nil adjustment for a dynamic library result vector.
pub fn result(xs: &[Value], i: usize) -> Value {
    xs.get(i).cloned().unwrap_or(Value::Nil)
}

#[cfg(test)]
mod xpcall_tests {
    use super::*;
    #[test]
    fn preserves_results_and_handler_value() {
        let xs = xpcall(|| Ok(vec![Value::Num(1.0), Value::Nil, Value::Bool(false)]), |_| Ok(Value::Num(99.0)));
        assert!(matches!(xs.as_slice(), [Value::Bool(true), Value::Num(1.0), Value::Nil, Value::Bool(false)]));
        let xs = xpcall(|| Err(LuaError::new("body")), |e| Ok(Value::Str(e)));
        assert!(matches!(xs.as_slice(), [Value::Bool(false), Value::Str(s)] if s.as_bytes() == b"body"));
        let xs = xpcall(|| Err(LuaError::new("body")), |_| Err(LuaError::new("handler")));
        assert!(matches!(xs.as_slice(), [Value::Bool(false), Value::Str(s)] if s.as_bytes() == b"error in error handling"));
    }
}

/// A missing protected target is an error inside xpcall, without a source prefix.
pub fn protected_callable<T>(value: Option<T>) -> LResult<T> {
    value.ok_or_else(|| LuaError::located("attempt to call a nil value"))
}

#[cfg(test)]
mod protected_callable_tests {
    use super::*;
    #[test]
    fn target_nil_is_an_unlocated_protected_error() {
        assert_eq!(protected_callable(None::<()>).err().unwrap().with_loc("caller").msg.to_string_lossy(), "attempt to call a nil value");
        assert_eq!(protected_callable(Some(7)).unwrap(), 7);
    }
}
