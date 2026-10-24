//! Typed traversal of ordinary arrays and maps.
use std::hash::Hash;
use crate::{Arr, LMap, LResult, LuaError, Trace};
use crate::dynamic::{self, ToValue, Value};
use crate::show::{LuaType, Truthy};
use crate::Table;

/// Preserve typed primitive operands while checking soft-nil compound reads.
/// Both source operands must already have been evaluated, left to right.
pub fn arithmetic_operands<A: LuaType, B: LuaType>(op: dynamic::Arith, left: Option<A>, right: Option<B>) -> LResult<(A, B)> {
    match (left, right) {
        (Some(left), Some(right)) => Ok((left, right)),
        (left, right) => Err(dynamic::arithmetic_error(op, left.lua_type(), right.lua_type())),
    }
}

/// Concatenation's nil error names the actual primitive type on each side.
pub fn concatenation_operands<A: LuaType, B: LuaType>(left: Option<A>, right: Option<B>) -> LResult<(A, B)> {
    match (left, right) {
        (Some(left), Some(right)) => Ok((left, right)),
        (left, right) => Err(dynamic::concatenation_error(left.lua_type(), right.lua_type())),
    }
}

/// Generalized table iteration calls `__iter` once, then passes state/control
/// to its iterator. Plain table traversal keeps keys and reads values live.
pub enum GeneralIterator {
    Array { table: Table, index: usize, stop_at_nil: bool },
    Table { table: Table, keys: std::vec::IntoIter<Value> },
    Function { function: Value, state: Value, control: Value },
}

impl GeneralIterator {
    pub fn new(table: Table) -> LResult<Self> {
        let method = table.metamethod("__iter");
        if method.is_nil() { return Ok(Self::pairs(table)); }
        let mut values = dynamic::call_metamethod(&method, vec![table.to_value()])?.into_iter();
        Ok(Self::Function {
            function: values.next().unwrap_or(Value::Nil),
            state: values.next().unwrap_or(Value::Nil),
            control: values.next().unwrap_or(Value::Nil),
        })
    }

    pub fn pairs(table: Table) -> Self {
        let entries = table.entries();
        // Luau visits array appends without holding a borrow across the body.
        let dense = entries.iter().all(|(key, _)| matches!(key, Value::Num(n) if *n >= 1.0 && n.fract() == 0.0 && *n <= entries.len() as f64));
        if dense { return Self::Array { table, index: 0, stop_at_nil: false }; }
        let keys = entries.into_iter().map(|(k, _)| k).collect::<Vec<_>>().into_iter();
        Self::Table { table, keys }
    }

    pub fn ipairs(table: Table) -> Self { Self::Array { table, index: 0, stop_at_nil: true } }

    pub fn next_values(&mut self) -> LResult<Option<Vec<Value>>> {
        match self {
            Self::Array { table, index, stop_at_nil } => loop {
                *index += 1;
                let key = Value::Num(*index as f64);
                let value = table.raw_get(&key);
                if !value.is_nil() { return Ok(Some(vec![key, value])); }
                if *stop_at_nil { return Ok(None); }
                // Generalized iteration skips holes; ipairs stops at its first nil.
                let later = table.entries().iter().any(|(key, _)| matches!(key, Value::Num(n) if n.fract() == 0.0 && *n > *index as f64));
                if !later { return Ok(None); }
            },
            Self::Table { table, keys } => {
                for key in keys {
                    let value = table.raw_get(&key);
                    if !value.is_nil() { return Ok(Some(vec![key, value])); }
                }
                Ok(None)
            }
            Self::Function { function, state, control } => {
                let values = dynamic::call(function, vec![state.clone(), control.clone()])?;
                *control = values.first().cloned().unwrap_or(Value::Nil);
                Ok((!control.is_nil()).then_some(values))
            }
        }
    }
}

/// Sorting runtime records uses the same guarded sort as typed arrays.
pub fn sort_table(table: &Table, compare: Option<Value>) -> LResult<()> {
    if table.is_frozen() { return Err(LuaError::new("attempt to modify a readonly table")); }
    let count = table.raw_len()? as usize;
    let values = Arr::from_vec((1..=count).map(|i| table.raw_get(&Value::Num(i as f64))).collect());
    crate::stdlib::table_sort(&values, |a, b| match &compare {
        Some(f) if !f.is_nil() => Ok(dynamic::call_first(f, vec![a.clone(), b.clone()])?.truthy()),
        _ => dynamic::lt(a, b),
    })?;
    for (i, value) in values.snapshot().into_iter().enumerate() {
        table.raw_set(Value::Num(i as f64 + 1.0), value)?;
    }
    Ok(())
}

pub fn next_array<T: Trace + Clone + 'static>(t: &Arr<T>, key: Option<f64>) -> LResult<(Option<f64>, Option<T>)> {
    t.next_entry(key)
}

pub fn next_map<K: Trace + Clone + Eq + Hash + 'static, V: Trace + Clone + 'static>(t: &LMap<K, V>, key: Option<K>) -> LResult<(Option<K>, Option<V>)> {
    t.next_entry(key)
}

pub fn next_number_map<V: Trace + Clone + 'static>(t: &LMap<crate::NumKey, V>, key: Option<f64>) -> LResult<(Option<f64>, Option<V>)> {
    let key = key.map(crate::NumKey::new).transpose().map_err(|_| LuaError::new("invalid key to 'next'"))?;
    let (k, v) = t.next_entry(key)?;
    Ok((k.map(crate::NumKey::get), v))
}

pub fn next_dynamic_map<V: Trace + Clone + 'static>(table: &LMap<dynamic::Key, V>, key: Value) -> LResult<(Option<Value>, Option<V>)> {
    let key = if key.is_nil() { None } else {
        Some(dynamic::Key::new(key).map_err(|_| LuaError::new("invalid key to 'next'"))?)
    };
    let (key, value) = table.next_entry(key)?;
    Ok((key.map(|key| key.value()), value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dynamic::DynFunction;
    use crate::LFn;

    #[test]
    fn runtime_arrays_observe_appends_and_dynamic_iterators_stop_on_nil() {
        let table = Table::from_entries(vec![(Value::Num(1.0), Value::Num(3.0))]).unwrap();
        let mut iter = GeneralIterator::new(table.clone()).unwrap();
        assert_eq!(iter.next_values().unwrap().unwrap()[1].as_num().unwrap(), 3.0);
        table.raw_set(Value::Num(2.0), Value::Num(5.0)).unwrap();
        assert_eq!(iter.next_values().unwrap().unwrap()[1].as_num().unwrap(), 5.0);
        assert!(iter.next_values().unwrap().is_none());
        let factory: DynFunction = LFn::from_fn(|_| {
            let step: DynFunction = LFn::from_fn(|args| {
                let n = if args[1].is_nil() { 1.0 } else { args[1].as_num()? + 1.0 };
                Ok(if n <= 4.0 { vec![Value::Num(n), Value::Num(n*n)] } else { vec![] })
            });
            Ok(vec![step.to_value()])
        });
        let meta = Table::from_entries(vec![(Value::Str("__iter".into()), factory.to_value())]).unwrap();
        let table = Table::new().set_metatable(Some(meta)).unwrap();
        let mut iter = GeneralIterator::new(table).unwrap();
        let mut sum = 0.0;
        while let Some(values) = iter.next_values().unwrap() { sum += values[1].as_num().unwrap(); }
        assert_eq!(sum, 30.0);
    }

    #[test]
    fn runtime_sort_and_frozen_error() {
        let table = Table::from_entries(vec![(Value::Num(1.0), Value::Num(3.0)), (Value::Num(2.0), Value::Num(1.0))]).unwrap();
        sort_table(&table, None).unwrap();
        assert_eq!(table.raw_get(&Value::Num(1.0)).as_num().unwrap(), 1.0);
        table.freeze().unwrap();
        assert_eq!(sort_table(&table, None).unwrap_err().msg.to_string_lossy(), "attempt to modify a readonly table");
    }

    #[test]
    fn generalized_arrays_skip_holes_but_ipairs_stops() {
        let table = Table::from_entries((1..=3).map(|i| (Value::Num(i as f64), Value::Num(i as f64))).collect()).unwrap();
        let mut iter = GeneralIterator::new(table.clone()).unwrap();
        assert_eq!(iter.next_values().unwrap().unwrap()[0].as_num().unwrap(), 1.0);
        table.raw_set(Value::Num(2.0), Value::Nil).unwrap();
        assert_eq!(iter.next_values().unwrap().unwrap()[0].as_num().unwrap(), 3.0);
        assert!(iter.next_values().unwrap().is_none());
        let mut iter = GeneralIterator::ipairs(table);
        assert!(iter.next_values().unwrap().is_some());
        assert!(iter.next_values().unwrap().is_none());
    }
    #[test]
    fn arrays_next_and_clear() {
        let a = Arr::from_vec(vec![4.0, 9.0]);
        assert_eq!(next_array(&a, None).unwrap(), (Some(1.0), Some(4.0)));
        assert_eq!(next_array(&a, Some(2.0)).unwrap(), (None, None));
        assert!(next_array(&a, Some(1.5)).is_err());
        a.push(16.0);
        assert_eq!(next_array(&a, Some(4.0)).unwrap(), (None, None));
        assert_eq!(next_array(&a.shallow_clone(), Some(4.0)).unwrap(), (None, None));
        let alias = a.clone();
        a.clear();
        assert_eq!(next_array(&alias, None).unwrap(), (None, None));
    }
    #[test]
    fn maps_next_and_clear() {
        let a = LMap::new();
        a.set(false, 4.0);
        assert_eq!(next_map(&a, None).unwrap(), (Some(false), Some(4.0)));
        assert_eq!(next_map(&a, Some(false)).unwrap(), (None, None));
        assert!(next_map(&a, Some(true)).is_err());
        a.set(true, 8.0);
        a.remove(&false);
        assert_eq!(next_map(&a, Some(false)).unwrap(), (Some(true), Some(8.0)));
        a.clear();
        assert_eq!(a.count(), 0);
    }
    #[test]
    fn compound_operand_guards_keep_integer_types_and_exact_errors() {
        use dynamic::Arith;
        for (op, name) in [(Arith::Add, "add"), (Arith::Sub, "sub"), (Arith::Mul, "mul"), (Arith::Div, "div"), (Arith::IDiv, "idiv"), (Arith::Mod, "mod"), (Arith::Pow, "pow")] {
            for (left, right, tags) in [(None, Some(2i128), "nil and number"), (Some(3i128), None, "number and nil"), (None, None, "nil")] {
                let error = arithmetic_operands(op, left, right).unwrap_err();
                assert_eq!(error.msg.to_string_lossy(), format!("attempt to perform arithmetic ({name}) on {tags}"));
            }
        }
        assert_eq!(arithmetic_operands(Arith::Add, Some(i128::MAX), Some(1i128)).unwrap(), (i128::MAX, 1));
    }

    #[test]
    fn compound_concat_guard_names_both_optional_primitive_types() {
        use crate::LStr;
        let error = concatenation_operands(None::<LStr>, Some(2i128)).unwrap_err();
        assert_eq!(error.msg.to_string_lossy(), "attempt to concatenate nil with number");
        let error = concatenation_operands(Some(LStr::from("x")), None::<LStr>).unwrap_err();
        assert_eq!(error.msg.to_string_lossy(), "attempt to concatenate string with nil");
        let error = concatenation_operands(None::<LStr>, None::<i128>).unwrap_err();
        assert_eq!(error.msg.to_string_lossy(), "attempt to concatenate nil with nil");
        let (left, right) = concatenation_operands(Some(LStr::from("x")), Some(i128::MAX)).unwrap();
        assert_eq!(left.as_bytes(), b"x");
        assert_eq!(right, i128::MAX);
    }
}
