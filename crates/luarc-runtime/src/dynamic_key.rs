//! Raw, hashable identity of a dynamic table key.
use std::hash::{Hash, Hasher};
use super::{Value, ToValue};
use crate::{LResult, LuaError, Trace};
use crate::show::LuaEq;

#[derive(Clone, Trace)]
pub struct Key(Value);

impl Key {
    pub fn new(value: Value) -> LResult<Self> {
        match value {
            Value::Nil => Err(LuaError::new("table index is nil")),
            Value::Num(n) if n.is_nan() => Err(LuaError::new("table index is NaN")),
            Value::Num(n) if n == 0.0 => Ok(Self(Value::Num(0.0))),
            value => Ok(Self(value)),
        }
    }
    pub fn value(&self) -> Value { self.0.clone() }
    pub fn layout_key(&self) -> crate::table_layout::Key {
        crate::table_layout::Key::from_value(&self.0).expect("a validated key is nonnil")
    }
}
impl ToValue for Key { fn to_value(self) -> Value { self.0 } }
impl PartialEq for Key { fn eq(&self, rhs: &Self) -> bool { self.0.lua_eq(&rhs.0) } }
impl Eq for Key {}
impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(&self.0).hash(state);
        match &self.0 {
            Value::Nil => unreachable!("nil is not a table key"),
            Value::Bool(v) => v.hash(state),
            Value::Num(v) => v.to_bits().hash(state),
            Value::Str(v) => v.as_bytes().hash(state),
            Value::Table(v) | Value::Function(v) | Value::Userdata(v) => v.addr.hash(state),
            Value::Thread(thread) => thread.addr().hash(state),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Arr, LFn, LMap};
    #[test]
    fn dynamic_keys_preserve_tags_identity_and_signed_zero() {
        let map = LMap::new();
        map.set(Key::new(1.0.to_value()).unwrap(), "number");
        map.set(Key::new(Value::Str("1".into())).unwrap(), "string");
        map.set(Key::new(false.to_value()).unwrap(), "boolean");
        assert_eq!(map.get(&Key::new(1.0.to_value()).unwrap()), Some("number"));
        assert_eq!(map.get(&Key::new(Value::Str("1".into())).unwrap()), Some("string"));
        assert_eq!(map.get(&Key::new(false.to_value()).unwrap()), Some("boolean"));
        map.set(Key::new((-0.0).to_value()).unwrap(), "zero");
        assert_eq!(map.get(&Key::new(0.0.to_value()).unwrap()), Some("zero"));
        let table = Arr::from_vec(vec![1.0]);
        map.set(Key::new(table.clone().to_value()).unwrap(), "table");
        assert_eq!(map.get(&Key::new(table.to_value()).unwrap()), Some("table"));
        let f = LFn::from_fn(|(): ()| Ok(()));
        map.set(Key::new(f.clone().to_value()).unwrap(), "function");
        assert_eq!(map.get(&Key::new(f.to_value()).unwrap()), Some("function"));
        assert!(Key::new(Value::Nil).is_err());
        assert!(Key::new(f64::NAN.to_value()).is_err());
    }

    #[test]
    fn thread_keys_share_identity_in_storage_and_allocation_layout() {
        let make = || crate::coroutine::Thread::new(crate::dynamic_fn::function(
            LFn::from_fn(|(): ()| Ok(())),
        )).unwrap();
        let first = make();
        let second = make();
        let key = Key::new(first.clone().to_value()).unwrap();
        assert_eq!(key.layout_key(), crate::table_layout::Key::Object(3, first.addr()));
        let map = LMap::new();
        map.set(key, "same");
        assert_eq!(map.get(&Key::new(first.to_value()).unwrap()), Some("same"));
        assert!(map.get(&Key::new(second.to_value()).unwrap()).is_none());
    }
}
