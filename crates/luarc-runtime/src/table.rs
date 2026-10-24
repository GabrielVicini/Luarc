//! Runtime tables for programs requiring dynamic fields or non-index metamethods.
//! Ordinary statically shaped records and arrays retain their existing storage.

use std::cell::RefCell;

use dumpster::Trace;

use crate::dynamic::{self, FromValue, ToValue, Value};
use crate::error::{LResult, LuaError};
use crate::gc::{Gc, Live};
use crate::show::{LuaDisplay, LuaEq, LuaType, Truthy};

#[derive(Trace)]
struct TableData {
    _live: Live,
    entries: RefCell<Vec<(Value, Value)>>,
    metatable: RefCell<Option<Table>>,
    frozen: std::cell::Cell<bool>,
    layout: RefCell<crate::table_layout::Layout>,
}

/// A shared, traced table identity with raw storage, an optional metatable and a
/// readonly flag. No borrow of its storage survives a call into source code.
#[derive(Clone, Trace)]
pub struct Table(Gc<TableData>);

impl Default for Table {
    fn default() -> Self {
        Self::new()
    }
}

impl Table {
    pub fn new() -> Self {
        Self(Gc::new(TableData {
            _live: Live::new(),
            entries: RefCell::new(Vec::new()),
            metatable: RefCell::new(None),
            frozen: std::cell::Cell::new(false),
            layout: RefCell::new(crate::table_layout::Layout::default()),
        }))
    }

    pub fn from_entries(entries: Vec<(Value, Value)>) -> LResult<Self> {
        Self::from_entries_with_layout(entries, 0, 0)
    }
    pub fn from_entries_with_layout(entries: Vec<(Value, Value)>, array: usize, hash: usize) -> LResult<Self> {
        let table = Self::new();
        *table.0.layout.borrow_mut() = crate::table_layout::Layout::new(array, hash);
        for (key, value) in entries {
            table.raw_set(key, value)?;
        }
        Ok(table)
    }
    /// Luau's DUPTABLE templates preseed every named field with a nonnil
    /// placeholder, then clear nil constants, preserving colliding nil keys.
    pub fn from_record_entries(entries: Vec<(Value, Value)>) -> LResult<Self> {
        let mut keys = Vec::new();
        for (key, _) in &entries {
            if let Some(token) = crate::table_layout::Key::from_value(key) {
                if !keys.contains(&token) { keys.push(token); }
            }
        }
        let table = Self::from_entries_with_layout(Vec::new(), 0, keys.len())?;
        for key in keys { table.0.layout.borrow_mut().write(key, true); }
        for (key, value) in entries { table.raw_set(key, value)?; }
        Ok(table)
    }
    pub fn create(size: f64, fill: Value) -> LResult<Self> {
        // Luau's integer argument conversion truncates before checking range.
        let size = crate::table_layout::create_size(size)?;
        let table = Self::from_entries_with_layout(Vec::new(), size, 0)?;
        if !fill.is_nil() {
            for i in 1..=size { table.raw_set(Value::Num(i as f64), fill.clone())?; }
        }
        Ok(table)
    }

    pub fn addr(&self) -> usize {
        Gc::as_ptr(&self.0) as usize
    }

    pub fn ptr_eq(&self, other: &Self) -> bool {
        Gc::ptr_eq(&self.0, &other.0)
    }

    pub fn raw_get(&self, key: &Value) -> Value {
        self.0.entries.borrow().iter().find(|(k, _)| k.lua_eq(key))
            .map_or(Value::Nil, |(_, v)| v.clone())
    }

    pub fn raw_set(&self, key: Value, value: Value) -> LResult<()> {
        self.writable()?;
        // Luau rejects nil and NaN keys even when the assigned value is nil.
        match &key {
            Value::Nil => return Err(LuaError::located("table index is nil")),
            Value::Num(n) if n.is_nan() => return Err(LuaError::located("table index is NaN")),
            _ => {}
        }
        if let Some(token) = crate::table_layout::Key::from_value(&key) {
            self.0.layout.borrow_mut().write(token, !value.is_nil());
        }
        let old = {
            let mut entries = self.0.entries.borrow_mut();
            if let Some(index) = entries.iter().position(|(k, _)| k.lua_eq(&key)) {
                if value.is_nil() { Some(entries.remove(index)) }
                else { Some(std::mem::replace(&mut entries[index], (key, value))) }
            } else if value.is_nil() {
                None
            } else {
                entries.push((key, value));
                None
            }
        };
        drop(old);
        Ok(())
    }

    /// Raw metamethod lookup never invokes the metatable's own `__index`.
    pub fn metamethod(&self, name: &str) -> Value {
        self.0.metatable.borrow().as_ref()
            .map_or(Value::Nil, |meta| meta.raw_get(&Value::Str(name.into())))
    }

    pub fn get(&self, key: &Value) -> LResult<Value> {
        let mut table = self.clone();
        for _ in 0..100 {
            let own = table.raw_get(key);
            if !own.is_nil() {
                return Ok(own);
            }
            let index = table.metamethod("__index");
            if index.is_nil() {
                return Ok(Value::Nil);
            }
            if let Some(parent) = Table::from_value(&index) {
                table = parent;
            } else if matches!(index, Value::Function(_)) {
                return dynamic::call_metamethod_first(&index, vec![table.to_value(), key.clone()]);
            } else {
                return Err(index_error(&index, key));
            }
        }
        Err(LuaError::new("'__index' chain too long; possible loop"))
    }

    pub fn set(&self, key: Value, value: Value) -> LResult<()> {
        let mut table = self.clone();
        for _ in 0..100 {
            let setter = table.metamethod("__newindex");
            if !table.raw_get(&key).is_nil() || setter.is_nil() {
                // VM writes carry their source position; rawset/library writes
                // use the same errors without a source prefix in Luau.
                return table.raw_set(key, value).map_err(|error| LuaError::new(error.msg));
            }
            if let Some(parent) = Table::from_value(&setter) {
                table = parent;
            } else if matches!(setter, Value::Function(_)) {
                dynamic::call_metamethod(&setter, vec![table.to_value(), key, value])?;
                return Ok(());
            } else {
                return Err(index_error(&setter, &key));
            }
        }
        Err(LuaError::new("'__newindex' chain too long; possible loop"))
    }

    pub fn set_metatable(&self, metatable: Option<Table>) -> LResult<Table> {
        // A non-nil __metatable protects attachment, including false.
        if !self.metamethod("__metatable").is_nil() {
            return Err(LuaError::new("cannot change a protected metatable"));
        }
        self.writable()?;
        let old = self.0.metatable.replace(metatable);
        drop(old);
        Ok(self.clone())
    }

    pub fn get_metatable(&self) -> Value {
        let protected = self.metamethod("__metatable");
        if !protected.is_nil() {
            protected
        } else {
            self.0.metatable.borrow().clone().to_value()
        }
    }

    /// Luau's cached boundary search depends on allocated array slots.
    pub fn raw_len(&self) -> LResult<f64> {
        Ok(self.0.layout.borrow_mut().length() as f64)
    }

    pub fn len(&self) -> LResult<f64> {
        let method = self.metamethod("__len");
        if method.is_nil() {
            self.raw_len()
        } else {
            let value = dynamic::call_metamethod_first(&method, vec![self.clone().to_value(), Value::Nil])?;
            f64::from_value(&value).ok_or_else(|| LuaError::new("'__len' must return a number"))
        }
    }

    pub fn freeze(&self) -> LResult<Table> {
        if self.is_frozen() {
            return Err(LuaError::new("invalid argument #1 to 'freeze' (table is already frozen)"));
        }
        if !self.metamethod("__metatable").is_nil() {
            return Err(LuaError::new("invalid argument #1 to 'freeze' (table has a protected metatable)"));
        }
        self.0.frozen.set(true);
        Ok(self.clone())
    }

    pub fn is_frozen(&self) -> bool {
        self.0.frozen.get()
    }

    fn writable(&self) -> LResult<()> {
        if self.is_frozen() {
            Err(LuaError::located("attempt to modify a readonly table"))
        } else {
            Ok(())
        }
    }

    pub fn entries(&self) -> Vec<(Value, Value)> {
        self.0.entries.borrow().iter().filter(|(_, value)| !value.is_nil()).cloned().collect()
    }

    /// `next` validates against allocated array slots and surviving hash keys.
    pub fn next_entry(&self, key: Value) -> LResult<(Value, Value)> {
        let token = crate::table_layout::Key::from_value(&key);
        let next = self.0.layout.borrow().next(token.as_ref()).map_err(|()| LuaError::located("invalid key to 'next'"))?;
        let Some(next) = next else { return Ok((Value::Nil, Value::Nil)); };
        Ok(self.0.entries.borrow().iter().find(|(stored, value)| !value.is_nil() && crate::table_layout::Key::from_value(stored).as_ref() == Some(&next)).cloned().unwrap_or((Value::Nil, Value::Nil)))
    }

    pub fn clear(&self) -> LResult<()> {
        self.writable()?;
        self.0.layout.borrow_mut().clear();
        let old = self.0.entries.replace(Vec::new());
        drop(old);
        Ok(())
    }

    pub fn shallow_clone(&self) -> Table {
        let table = Table::new();
        table.0.entries.replace(self.0.entries.borrow().clone());
        table.0.metatable.replace(self.0.metatable.borrow().clone());
        *table.0.layout.borrow_mut() = self.0.layout.borrow().clone();
        table
    }
    pub fn array_capacity(&self) -> usize { self.0.layout.borrow().array_size() }
    pub fn resize_array(&self, size: usize) -> LResult<()> {
        self.writable()?;
        if size > 1 << 26 { return Err(LuaError::new("table overflow")); }
        self.0.layout.borrow_mut().resize_array(size);
        Ok(())
    }

    pub fn checked_clone(&self) -> LResult<Table> {
        if !self.metamethod("__metatable").is_nil() {
            return Err(LuaError::new("invalid argument #1 to 'clone' (table has a protected metatable)"));
        }
        Ok(self.shallow_clone())
    }
}

pub fn index_error(value: &Value, key: &Value) -> LuaError {
    match key {
        Value::Str(s) => LuaError::new(format!("attempt to index {} with '{}'", value.type_name(), s.to_string_lossy())),
        _ => LuaError::new(format!("attempt to index {} with {}", value.type_name(), key.type_name())),
    }
}

impl LuaDisplay for Table {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(format!("table: 0x{:x}", self.addr()).as_bytes());
    }
}
impl LuaType for Table {
    fn lua_type(&self) -> &'static str { "table" }
}
impl Truthy for Table {
    fn truthy(&self) -> bool { true }
}
impl LuaEq for Table {
    fn lua_eq(&self, other: &Self) -> bool { self.ptr_eq(other) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dynamic::DynFunction;
    use crate::value::LFn;

    fn key(s: &str) -> Value { Value::Str(s.into()) }

    #[test]
    fn deleted_key_metadata_does_not_retain_managed_objects() {
        let base = crate::gc::live_objects();
        let table = Table::new();
        let key_table = Table::new();
        let token = key_table.clone().to_value();
        table.raw_set(token.clone(), Value::Num(1.0)).unwrap();
        table.raw_set(token.clone(), Value::Nil).unwrap();
        assert!(table.next_entry(token.clone()).unwrap().0.is_nil());
        drop(token);
        drop(key_table);
        assert_eq!(crate::gc::live_objects(), base + 1);
        drop(table);
        assert_eq!(crate::gc::live_objects(), base);
    }

    #[test]
    fn raw_storage_and_identity() {
        let table = Table::new();
        table.raw_set(key("x"), Value::Num(1.0)).unwrap();
        assert_eq!(table.raw_get(&key("x")).as_num().unwrap(), 1.0);
        assert!(table.ptr_eq(&table.clone()));
        assert!(!table.ptr_eq(&table.shallow_clone()));
        table.raw_set(key("x"), Value::Nil).unwrap();
        assert!(table.raw_get(&key("x")).is_nil());
        assert_eq!(table.raw_set(Value::Nil, Value::Nil).unwrap_err().msg.to_string_lossy(), "table index is nil");
        assert_eq!(table.raw_set(Value::Num(f64::NAN), Value::Nil).unwrap_err().msg.to_string_lossy(), "table index is NaN");
    }

    #[test]
    fn live_index_and_protection() {
        let table = Table::new();
        let parent = Table::from_entries(vec![(key("x"), Value::Num(7.0))]).unwrap();
        let meta = Table::from_entries(vec![(key("__index"), parent.to_value())]).unwrap();
        table.set_metatable(Some(meta.clone())).unwrap();
        assert_eq!(table.get(&key("x")).unwrap().as_num().unwrap(), 7.0);
        assert!(table.raw_get(&key("x")).is_nil());
        meta.raw_set(key("__index"), Value::Nil).unwrap();
        assert!(table.get(&key("x")).unwrap().is_nil());
        meta.raw_set(key("__metatable"), Value::Bool(false)).unwrap();
        assert!(matches!(table.get_metatable(), Value::Bool(false)));
        assert_eq!(table.set_metatable(None).err().unwrap().msg.to_string_lossy(), "cannot change a protected metatable");
    }

    #[test]
    fn function_newindex_and_existing_fields() {
        let method: DynFunction = LFn::from_fn(|args| {
            let table = Table::from_value(&args[0]).unwrap();
            table.raw_set(args[1].clone(), Value::Num(args[2].as_num()? * 3.0))?;
            Ok(vec![])
        });
        let table = Table::from_entries(vec![(key("x"), Value::Num(1.0))]).unwrap();
        let meta = Table::from_entries(vec![(key("__newindex"), method.to_value())]).unwrap();
        table.set_metatable(Some(meta)).unwrap();
        table.set(key("x"), Value::Num(2.0)).unwrap();
        table.set(key("y"), Value::Num(7.0)).unwrap();
        assert_eq!(table.raw_get(&key("x")).as_num().unwrap(), 2.0);
        assert_eq!(table.raw_get(&key("y")).as_num().unwrap(), 21.0);
    }

    #[test]
    fn frozen_and_clone_storage() {
        let table = Table::from_entries(vec![(key("x"), Value::Num(1.0))]).unwrap();
        table.freeze().unwrap();
        assert!(table.is_frozen());
        assert_eq!(table.set(key("x"), Value::Num(2.0)).unwrap_err().msg.to_string_lossy(), "attempt to modify a readonly table");
        let copy = table.shallow_clone();
        assert!(!copy.is_frozen());
        copy.set(key("x"), Value::Num(3.0)).unwrap();
        assert_eq!(table.raw_get(&key("x")).as_num().unwrap(), 1.0);
        assert_eq!(copy.raw_get(&key("x")).as_num().unwrap(), 3.0);
    }

    #[test]
    fn frozen_setter_and_raw_error_locations() {
        let method = crate::dynamic_fn::function(LFn::from_fn(|(): ()| Ok(())));
        let meta = Table::from_entries(vec![(key("__newindex"), method)]).unwrap();
        let table = Table::new();
        table.set_metatable(Some(meta)).unwrap();
        table.freeze().unwrap();
        table.set(key("absent"), Value::Num(1.0)).unwrap();
        let raw = table.raw_set(key("x"), Value::Num(1.0)).unwrap_err().with_loc("source:1");
        assert_eq!(raw.msg.to_string_lossy(), "attempt to modify a readonly table");
        let plain = Table::new();
        plain.freeze().unwrap();
        let source = plain.set(key("x"), Value::Num(1.0)).unwrap_err().with_loc("source:1");
        assert_eq!(source.msg.to_string_lossy(), "source:1: attempt to modify a readonly table");
        let meta = Table::new();
        let protected = Table::new();
        protected.set_metatable(Some(meta.clone())).unwrap();
        protected.freeze().unwrap();
        meta.raw_set(key("__metatable"), key("lock")).unwrap();
        assert_eq!(protected.set_metatable(None).err().unwrap().msg.to_string_lossy(), "cannot change a protected metatable");
    }

    #[test]
    fn next_retains_deleted_keys_until_clear() {
        let table = Table::from_entries(vec![(key("a"), Value::Num(1.0)), (key("b"), Value::Num(2.0))]).unwrap();
        table.raw_set(key("a"), Value::Nil).unwrap();
        assert!(table.next_entry(key("a")).unwrap().0.lua_eq(&key("b")));
        table.clear().unwrap();
        assert!(table.next_entry(key("a")).is_err());
        table.raw_set(Value::Num(1.0), Value::Num(1.0)).unwrap();
        table.raw_set(Value::Num(2.0), Value::Num(2.0)).unwrap();
        table.clear().unwrap();
        assert!(table.next_entry(Value::Num(2.0)).unwrap().0.is_nil());
    }

    #[test]
    fn mixed_keys_and_sequence_length() {
        let table = Table::from_entries(vec![
            (Value::Num(1.0), key("number")), (key("1"), key("string")),
            (Value::Bool(false), key("boolean")),
        ]).unwrap();
        assert_eq!(table.entries().len(), 3);
        assert_eq!(table.raw_len().unwrap(), 1.0);
        assert_eq!(table.raw_get(&Value::Bool(false)).as_str().unwrap().to_string_lossy(), "boolean");
    }

    #[test]
    fn operator_methods_and_errors() {
        let add = crate::dynamic_fn::function(LFn::from_fn(|(a, b): (Value, Value)| {
            let number = |v: Value| match Table::from_value(&v) {
                Some(t) => t.raw_get(&key("value")).as_num(),
                None => v.as_num(),
            };
            Ok(number(a)? + number(b)?)
        }));
        let meta = Table::from_entries(vec![(key("__add"), add)]).unwrap();
        let table = Table::from_entries(vec![(key("value"), Value::Num(13.0))]).unwrap();
        table.set_metatable(Some(meta.clone())).unwrap();
        let v = table.to_value();
        assert_eq!(dynamic::arith(dynamic::Arith::Add, &v, &Value::Num(5.0)).unwrap().as_num().unwrap(), 18.0);
        assert_eq!(dynamic::arith(dynamic::Arith::Add, &Value::Num(5.0), &v).unwrap().as_num().unwrap(), 18.0);
        let equal = crate::dynamic_fn::function(LFn::from_fn(|_: (Value, Value)| Ok(true)));
        meta.raw_set(key("__eq"), equal.clone()).unwrap();
        meta.raw_set(key("__lt"), equal).unwrap();
        let other = Table::new();
        other.set_metatable(Some(meta)).unwrap();
        let other = other.to_value();
        assert!(dynamic::eq(&v, &other).unwrap());
        assert!(!v.lua_eq(&other));
        assert!(dynamic::lt(&v, &other).unwrap());
        assert!(dynamic::lt(&v, &Table::new().to_value()).is_err());
    }

    #[test]
    fn callable_length_and_display_methods() {
        let meta = Table::from_entries(vec![
            (key("__call"), crate::dynamic_fn::function(LFn::from_fn(|(_, x, y): (Value, Value, Value)| Ok(x.as_num()? * 7.0 + y.as_num()?)))),
            (key("__len"), crate::dynamic_fn::function(LFn::from_fn(|(): ()| Ok(137.0)))),
            (key("__tostring"), crate::dynamic_fn::function(LFn::from_fn(|(): ()| Ok(crate::LStr::from("<core>"))))),
            (key("__concat"), crate::dynamic_fn::function(LFn::from_fn(|(): ()| Ok(12.0)))),
        ]).unwrap();
        let table = Table::new();
        table.set_metatable(Some(meta)).unwrap();
        assert_eq!(table.len().unwrap(), 137.0);
        let value = table.to_value();
        assert_eq!(dynamic::call_first(&value, vec![Value::Num(6.0), Value::Num(1.0)]).unwrap().as_num().unwrap(), 43.0);
        assert_eq!(dynamic::tostring(&value).unwrap().to_string_lossy(), "<core>");
        assert_eq!(dynamic::concat_value(&value, &key("x")).unwrap().as_num().unwrap(), 12.0);
        let nested_meta = Table::from_entries(vec![(key("__call"), value)]).unwrap();
        let nested = Table::new();
        nested.set_metatable(Some(nested_meta)).unwrap();
        assert_eq!(dynamic::call(&nested.to_value(), vec![]).unwrap_err().msg.to_string_lossy(), "attempt to call a table value");
    }
}
