//! The dynamic type `any`: one tagged run-time value.
//!
//! A source value converts into a [`Value`] when it flows into an `any` slot
//! ([`ToValue`]) and comes back out only through a checked cast ([`FromValue`]) or
//! a `type(x) == "..."` test. Operators on `Value`s follow Luau, including its error
//! messages (`attempt to perform arithmetic (add) on table and number`).

use std::any::Any;

#[path = "dynamic_key.rs"]
mod key;
pub use key::Key;

use dumpster::Trace;

use crate::error::{LResult, LuaError};
use crate::gc::{Gc, Live, TraceWith, Visitor};
use crate::handle::Handle;
use crate::show::{fmt_num, LuaDisplay, LuaEq, LuaType, Truthy};
use crate::value::{Arr, LFn, LMap, LStr, MetaRec, Rec};

/// A type-erased managed object (table, function or native handle) held by a [`Value`].
pub trait DynObj: Trace {
    fn as_any(&self) -> &dyn Any;
    fn alternate_any(&self) -> Option<&dyn Any> {
        None
    }
    fn fmt_obj(&self, out: &mut Vec<u8>);
}

#[derive(Trace)]
struct Holder<T: Trace + LuaDisplay + 'static> {
    _live: Live,
    v: T,
}

impl<T: Trace + LuaDisplay + 'static> DynObj for Holder<T> {
    fn as_any(&self) -> &dyn Any {
        &self.v
    }
    fn fmt_obj(&self, out: &mut Vec<u8>) {
        self.v.fmt_lua(out)
    }
}

#[derive(Trace)]
struct DualHolder<T: Trace + LuaDisplay + 'static, O: Trace + 'static> {
    _live: Live,
    v: T,
    original: O,
}

impl<T: Trace + LuaDisplay + 'static, O: Trace + 'static> DynObj for DualHolder<T, O> {
    fn as_any(&self) -> &dyn Any {
        &self.v
    }
    fn alternate_any(&self) -> Option<&dyn Any> {
        Some(&self.original)
    }
    fn fmt_obj(&self, out: &mut Vec<u8>) {
        self.v.fmt_lua(out)
    }
}

/// A managed object behind a [`Value`]: identity is the address of the original table,
/// function or handle, so boxing the same object twice gives equal values.
pub struct Obj {
    inner: Gc<dyn DynObj>,
    addr: usize,
}

impl Clone for Obj {
    fn clone(&self) -> Self {
        Obj { inner: self.inner.clone(), addr: self.addr }
    }
}

// SAFETY: visits the only managed pointer the object holds.
unsafe impl<V: Visitor> TraceWith<V> for Obj {
    #[inline]
    fn accept(&self, v: &mut V) -> Result<(), ()> {
        self.inner.accept(v)
    }
}

impl Obj {
    pub(crate) fn identity(&self) -> usize { self.addr }
    pub(crate) fn new<T: Trace + LuaDisplay + 'static>(v: T, addr: usize) -> Obj {
        let g: Gc<Holder<T>> = Gc::new(Holder { _live: Live::new(), v });
        Obj { inner: dumpster::unsync::coerce_gc!(g), addr }
    }
    pub(crate) fn with_original<T: Trace + LuaDisplay + 'static, O: Trace + 'static>(v: T, original: O, addr: usize) -> Obj {
        let g: Gc<DualHolder<T, O>> = Gc::new(DualHolder { _live: Live::new(), v, original });
        Obj { inner: dumpster::unsync::coerce_gc!(g), addr }
    }
    fn downcast<T: Clone + 'static>(&self) -> Option<T> {
        // Luau preserves the original callable's identity even when it already
        // uses the erased ABI, so prefer that view when both signatures match.
        self.inner.alternate_any().and_then(|value| value.downcast_ref::<T>())
            .or_else(|| self.inner.as_any().downcast_ref::<T>()).cloned()
    }
}

/// A value of the dynamic type `any`.
#[derive(Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Num(f64),
    Str(LStr),
    Table(Obj),
    Function(Obj),
    Userdata(Obj),
    /// A real same-thread coroutine handle (Luau's `thread` tag).
    Thread(crate::coroutine::Thread),
}

// SAFETY: only the object variants hold managed pointers.
unsafe impl<V: Visitor> TraceWith<V> for Value {
    #[inline]
    fn accept(&self, v: &mut V) -> Result<(), ()> {
        match self {
            Value::Table(o) | Value::Function(o) | Value::Userdata(o) => o.accept(v),
            Value::Thread(t) => t.accept(v),
            _ => Ok(()),
        }
    }
}

// Conversion into `any`

/// A static value that can flow into `any`.
pub trait ToValue {
    fn to_value(self) -> Value;
}

#[inline]
pub fn to_value<T: ToValue>(x: T) -> Value {
    x.to_value()
}

impl ToValue for Value {
    fn to_value(self) -> Value {
        self
    }
}
impl ToValue for crate::Table {
    fn to_value(self) -> Value {
        let addr = self.addr();
        Value::Table(Obj::new(self, addr))
    }
}
impl ToValue for () {
    fn to_value(self) -> Value {
        Value::Nil
    }
}
impl ToValue for bool {
    fn to_value(self) -> Value {
        Value::Bool(self)
    }
}
impl ToValue for f64 {
    fn to_value(self) -> Value {
        Value::Num(self)
    }
}
impl ToValue for LStr {
    fn to_value(self) -> Value {
        Value::Str(self)
    }
}
impl<T: ToValue + Trace + 'static> ToValue for crate::value::FalseOr<T> {
    fn to_value(self) -> Value {
        match self {
            crate::value::FalseOr::False => Value::Bool(false),
            crate::value::FalseOr::Val(v) => v.to_value(),
        }
    }
}
impl<T: ToValue> ToValue for Option<T> {
    fn to_value(self) -> Value {
        match self {
            Some(v) => v.to_value(),
            None => Value::Nil,
        }
    }
}
impl<T: Trace + Clone + 'static> ToValue for Arr<T> {
    fn to_value(self) -> Value {
        let a = self.addr();
        Value::Table(Obj::new(self, a))
    }
}
impl<K: Trace + Clone + Eq + std::hash::Hash + 'static, V: Trace + Clone + 'static> ToValue for LMap<K, V> {
    fn to_value(self) -> Value {
        let a = self.addr();
        Value::Table(Obj::new(self, a))
    }
}
impl<T: Trace + 'static> ToValue for Rec<T> {
    fn to_value(self) -> Value {
        let a = self.addr();
        Value::Table(Obj::new(self, a))
    }
}
impl<T: Trace + 'static, P: Trace + 'static> ToValue for MetaRec<T, P> {
    fn to_value(self) -> Value {
        let a = self.addr();
        Value::Table(Obj::new(self, a))
    }
}
impl<A: 'static, R: 'static> ToValue for LFn<A, R> {
    fn to_value(self) -> Value {
        let a = self.addr();
        Value::Function(Obj::new(self, a))
    }
}
impl<T: 'static> ToValue for Handle<T> {
    fn to_value(self) -> Value {
        let a = self.addr();
        Value::Userdata(Obj::new(self, a))
    }
}

// Conversion out of `any`

/// A static type a [`Value`] can be cast to (`v :: T`).
pub trait FromValue: Sized {
    fn from_value(v: &Value) -> Option<Self>;
}

impl FromValue for Value {
    fn from_value(v: &Value) -> Option<Self> {
        Some(v.clone())
    }
}
impl FromValue for () {
    fn from_value(value: &Value) -> Option<Self> {
        value.is_nil().then_some(())
    }
}
impl<T: FromValue> FromValue for Option<T> {
    fn from_value(v: &Value) -> Option<Self> {
        if v.is_nil() { Some(None) } else { T::from_value(v).map(Some) }
    }
}
impl FromValue for crate::Table {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Table(o) => o.downcast::<Self>(),
            _ => None,
        }
    }
}

/// Erased source-call ABI used by runtime-table metamethods and dynamic iteration.
pub type DynFunction = LFn<Vec<Value>, Vec<Value>>;

/// Calls an erased function, or a runtime table's `__call`, preserving all values.
pub fn call(value: &Value, args: Vec<Value>) -> LResult<Vec<Value>> {
    if let Value::Function(object) = value {
        if let Some(function) = object.downcast::<DynFunction>() {
            return function.call(args);
        }
    }
    if let Some(table) = crate::Table::from_value(value) {
        let method = table.metamethod("__call");
        // Luau's __call slot must contain an actual function; a recursively
        // callable table is not accepted here (other operator slots may use one).
        if matches!(method, Value::Function(_)) {
            let mut with_self = Vec::with_capacity(args.len() + 1);
            with_self.push(value.clone());
            with_self.extend(args);
            return call(&method, with_self);
        }
    }
    Err(LuaError::new(format!("attempt to call a {} value", value.type_name())))
}

pub fn call_first(value: &Value, args: Vec<Value>) -> LResult<Value> {
    Ok(call(value, args)?.into_iter().next().unwrap_or(Value::Nil))
}

/// Metamethod and iterator-factory callbacks are non-yielding C boundaries.
/// Ordinary calls (including __call) keep the yieldable `call` path.
pub fn call_metamethod(value: &Value, args: Vec<Value>) -> LResult<Vec<Value>> {
    crate::coroutine::non_yielding(|| call(value, args))
}

pub fn call_metamethod_first(value: &Value, args: Vec<Value>) -> LResult<Value> {
    Ok(call_metamethod(value, args)?.into_iter().next().unwrap_or(Value::Nil))
}

/// A raw metamethod lookup, including on the right operand of arithmetic.
pub fn metamethod(value: &Value, name: &str) -> Value {
    crate::Table::from_value(value).map_or(Value::Nil, |table| table.metamethod(name))
}

fn binary_method(name: &str, a: &Value, b: &Value) -> Option<Value> {
    let left = metamethod(a, name);
    let method = if left.is_nil() { metamethod(b, name) } else { left };
    (!method.is_nil()).then_some(method)
}

/// Source equality: tables share an __eq only when both raw metamethod values
/// are equal. Raw equality remains available through `LuaEq` / `rawequal`.
pub fn eq(a: &Value, b: &Value) -> LResult<bool> {
    if a.lua_eq(b) {
        return Ok(true);
    }
    if matches!((a, b), (Value::Table(_), Value::Table(_))) {
        let left = metamethod(a, "__eq");
        let right = metamethod(b, "__eq");
        if !left.is_nil() && left.lua_eq(&right) {
            return call_metamethod_first(&left, vec![a.clone(), b.clone()]).map(|v| v.truthy());
        }
    }
    Ok(false)
}

/// Fallible tostring, needed because __tostring is source code and can raise.
pub fn print_tail<T: ToValue + Clone>(mut values: Vec<Value>, tail: &[Option<T>], first: usize) -> LResult<()> {
    values.extend(tail.get(first..).unwrap_or(&[]).iter().cloned().map(ToValue::to_value));
    print(values)
}

pub fn result_pack(values: Vec<Value>) -> Vec<Option<Value>> {
    values.into_iter().map(|value| if value.is_nil() { None } else { Some(value) }).collect()
}

impl<T: ToValue + crate::Trace + 'static> ToValue for crate::PcallVal<T> {
    fn to_value(self) -> Value {
        match self {
            crate::PcallVal::Ok(value) => value.to_value(),
            crate::PcallVal::Err(error) => error.to_value(),
        }
    }
}

pub fn print(values: Vec<Value>) -> LResult<()> {
    for (index, value) in values.iter().enumerate() {
        let text = tostring(value)?;
        if index > 0 { crate::stdlib::write_stdout(b"\t"); }
        crate::stdlib::write_stdout(text.as_bytes());
    }
    crate::stdlib::write_stdout(b"\n");
    Ok(())
}

pub fn tostring(value: &Value) -> LResult<LStr> {
    let method = metamethod(value, "__tostring");
    if method.is_nil() {
        Ok(crate::show::tostring(value))
    } else {
        let result = call_metamethod_first(&method, vec![value.clone()])?;
        // Luau accepts a numeric result, but rejects other non-string kinds.
        match result {
            Value::Str(s) => Ok(s),
            Value::Num(_) => Ok(crate::show::tostring(&result)),
            _ => Err(LuaError::new("'__tostring' must return a string")),
        }
    }
}

pub fn index(value: &Value, key: &Value) -> LResult<Value> {
    crate::Table::from_value(value).map_or_else(
        || Err(crate::table::index_error(value, key)),
        |table| table.get(key),
    )
}

pub fn set_index(value: &Value, key: Value, assigned: Value) -> LResult<()> {
    crate::Table::from_value(value).map_or_else(
        || Err(crate::table::index_error(value, &key)),
        |table| table.set(key.clone(), assigned),
    )
}
impl FromValue for bool {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }
}
impl FromValue for f64 {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Num(n) => Some(*n),
            _ => None,
        }
    }
}
impl FromValue for LStr {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Str(s) => Some(s.clone()),
            _ => None,
        }
    }
}
impl<T: Trace + Clone + 'static> FromValue for Arr<T> {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Table(o) => o.downcast::<Self>(),
            _ => None,
        }
    }
}
impl<K: Trace + Clone + Eq + std::hash::Hash + 'static, V: Trace + Clone + 'static> FromValue for LMap<K, V> {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Table(o) => o.downcast::<Self>(),
            _ => None,
        }
    }
}
impl<T: Trace + 'static> FromValue for Rec<T> {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Table(o) => o.downcast::<Self>(),
            _ => None,
        }
    }
}
impl<T: Trace + 'static, P: Trace + 'static> FromValue for MetaRec<T, P> {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Table(o) => o.downcast::<Self>(),
            _ => None,
        }
    }
}
impl<A: 'static, R: 'static> FromValue for LFn<A, R> {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Function(o) => o.downcast::<Self>(),
            _ => None,
        }
    }
}
impl<T: 'static> FromValue for Handle<T> {
    fn from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Userdata(o) => o.downcast::<Self>(),
            _ => None,
        }
    }
}

/// `v :: T` for a non-optional target: the value must have the target's type.
pub fn cast<T: FromValue>(v: &Value, target: &str) -> LResult<T> {
    T::from_value(v).ok_or_else(|| LuaError::new(format!("invalid cast: expected {target}, got {}", v.type_name())))
}

/// `v :: T?`: nil is accepted too.
pub fn cast_opt<T: FromValue>(v: &Value, target: &str) -> LResult<Option<T>> {
    match v {
        Value::Nil => Ok(None),
        _ => cast::<T>(v, target).map(Some),
    }
}

// The Value itself

impl Value {
    /// Result of `type(v)`.
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Nil => "nil",
            Value::Bool(_) => "boolean",
            Value::Num(_) => "number",
            Value::Str(_) => "string",
            Value::Table(_) => "table",
            Value::Function(_) => "function",
            Value::Userdata(_) => "userdata",
            Value::Thread(_) => "thread",
        }
    }
    pub fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }
    /// Unboxing after `type(v) == "number"` (the checker proved the tag).
    pub fn as_num(&self) -> LResult<f64> {
        f64::from_value(self).ok_or_else(|| LuaError::new("invalid cast: expected number"))
    }
    pub fn as_str(&self) -> LResult<LStr> {
        LStr::from_value(self).ok_or_else(|| LuaError::new("invalid cast: expected string"))
    }
    pub fn as_bool(&self) -> LResult<bool> {
        bool::from_value(self).ok_or_else(|| LuaError::new("invalid cast: expected boolean"))
    }
    pub fn as_table(&self) -> LResult<crate::Table> {
        crate::Table::from_value(self).ok_or_else(|| LuaError::new("invalid cast: expected table"))
    }
}

impl LuaDisplay for Value {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        match self {
            Value::Nil => out.extend_from_slice(b"nil"),
            Value::Bool(b) => b.fmt_lua(out),
            Value::Num(n) => fmt_num(*n, out),
            Value::Str(s) => out.extend_from_slice(s.as_bytes()),
            // Luau 0.743: boxing the same function preserves its tostring identity.
            Value::Function(o) => crate::show::fmt_addr("function", o.addr, out),
            Value::Table(o) | Value::Userdata(o) => o.inner.fmt_obj(out),
            Value::Thread(t) => t.fmt_lua(out),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut b = Vec::new();
        self.fmt_lua(&mut b);
        write!(f, "{}({})", self.type_name(), String::from_utf8_lossy(&b))
    }
}

impl LuaType for Value {
    fn lua_type(&self) -> &'static str {
        self.type_name()
    }
}

impl Truthy for Value {
    fn truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }
}

impl LuaEq for Value {
    fn lua_eq(&self, o: &Self) -> bool {
        match (self, o) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Num(a), Value::Num(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Table(a), Value::Table(b)) | (Value::Function(a), Value::Function(b)) | (Value::Userdata(a), Value::Userdata(b)) => {
                a.addr == b.addr
            }
            (Value::Thread(a), Value::Thread(b)) => a.lua_eq(b),
            _ => false,
        }
    }
}

// Operators

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
}

impl Arith {
    fn name(self) -> &'static str {
        match self {
            Arith::Add => "add",
            Arith::Sub => "sub",
            Arith::Mul => "mul",
            Arith::Div => "div",
            Arith::IDiv => "idiv",
            Arith::Mod => "mod",
            Arith::Pow => "pow",
        }
    }
}

/// A number, or a string that reads as one (Luau coerces strings in arithmetic).
fn to_number(v: &Value) -> Option<f64> {
    match v {
        Value::Num(n) => Some(*n),
        Value::Str(s) => parse_number(s.as_bytes()),
        _ => None,
    }
}

fn parse_number(b: &[u8]) -> Option<f64> {
    let s = std::str::from_utf8(b).ok()?.trim_matches(|c: char| c == ' ' || ('\t'..='\r').contains(&c));
    if s.is_empty() {
        return None;
    }
    let (neg, body) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    if let Some(h) = body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
        let n = u64::from_str_radix(h, 16).ok()? as f64;
        return Some(if neg { -n } else { n });
    }
    // Rust accepts "inf"/"nan"/"infinity"; Luau's reader does not
    if body.chars().any(|c| c.is_ascii_alphabetic() && c != 'e' && c != 'E') {
        return None;
    }
    body.parse::<f64>().ok().map(|n| if neg { -n } else { n })
}

/// The shared Luau error for nonnumeric primitive operands.
pub fn arithmetic_error(op: Arith, left: &str, right: &str) -> LuaError {
    if left == right {
        LuaError::new(format!("attempt to perform arithmetic ({}) on {}", op.name(), left))
    } else {
        LuaError::new(format!("attempt to perform arithmetic ({}) on {} and {}", op.name(), left, right))
    }
}

/// `a <op> b`, including numeric string coercion and metamethod dispatch.
pub fn arith(op: Arith, a: &Value, b: &Value) -> LResult<Value> {
    let (Some(x), Some(y)) = (to_number(a), to_number(b)) else {
        let name = match op {
            Arith::Add => "__add", Arith::Sub => "__sub", Arith::Mul => "__mul",
            Arith::Div => "__div", Arith::IDiv => "__idiv", Arith::Mod => "__mod", Arith::Pow => "__pow",
        };
        if let Some(method) = binary_method(name, a, b) {
            return call_metamethod_first(&method, vec![a.clone(), b.clone()]);
        }
        return Err(arithmetic_error(op, a.type_name(), b.type_name()));
    };
    Ok(Value::Num(match op {
        Arith::Add => x + y,
        Arith::Sub => x - y,
        Arith::Mul => x * y,
        Arith::Div => x / y,
        Arith::IDiv => crate::stdlib::floor_div(x, y),
        Arith::Mod => crate::stdlib::modulo(x, y),
        Arith::Pow => x.powf(y),
    }))
}

/// `-a`.
pub fn neg(a: &Value) -> LResult<Value> {
    match to_number(a) {
        Some(x) => Ok(Value::Num(-x)),
        None => {
            let method = metamethod(a, "__unm");
            if method.is_nil() {
                Err(LuaError::new(format!("attempt to perform arithmetic (unm) on {}", a.type_name())))
            } else {
                call_metamethod_first(&method, vec![a.clone(), a.clone()])
            }
        }
    }
}

/// The shared Luau error for a primitive that cannot be concatenated.
pub fn concatenation_error(left: &str, right: &str) -> LuaError {
    LuaError::new(format!("attempt to concatenate {} with {}", left, right))
}

/// `a .. b` (strings and numbers only).
pub fn concat(a: &Value, b: &Value) -> LResult<LStr> {
    fn part(v: &Value, out: &mut Vec<u8>) -> bool {
        match v {
            Value::Str(s) => out.extend_from_slice(s.as_bytes()),
            Value::Num(n) => fmt_num(*n, out),
            _ => return false,
        }
        true
    }
    let mut out = Vec::new();
    if part(a, &mut out) && part(b, &mut out) {
        Ok(LStr::from_vec(out))
    } else {
        Err(concatenation_error(a.type_name(), b.type_name()))
    }
}

/// Concatenation through a runtime table can return any metamethod result.
pub fn concat_value(a: &Value, b: &Value) -> LResult<Value> {
    if matches!(a, Value::Str(_) | Value::Num(_)) && matches!(b, Value::Str(_) | Value::Num(_)) {
        return concat(a, b).map(Value::Str);
    }
    match binary_method("__concat", a, b) {
        Some(method) => call_metamethod_first(&method, vec![a.clone(), b.clone()]),
        None => concat(a, b).map(Value::Str),
    }
}

fn compare_method(name: &str, a: &Value, b: &Value) -> Option<Value> {
    let left = metamethod(a, name);
    let right = metamethod(b, name);
    (!left.is_nil() && left.lua_eq(&right)).then_some(left)
}

/// `a .. b` where only one side is an `any` value and the other a string.
pub fn concat_str_left(a: &LStr, b: &Value) -> LResult<LStr> {
    concat(&Value::Str(a.clone()), b)
}

fn compare(a: &Value, b: &Value, sym: &str, ord: fn(std::cmp::Ordering) -> bool, num: fn(f64, f64) -> bool) -> LResult<bool> {
    match (a, b) {
        (Value::Num(x), Value::Num(y)) => Ok(num(*x, *y)),
        (Value::Str(x), Value::Str(y)) => Ok(ord(x.as_bytes().cmp(y.as_bytes()))),
        _ => Err(LuaError::new(format!("attempt to compare {} {sym} {}", a.type_name(), b.type_name()))),
    }
}

/// `a < b`. `a > b` is `lt(b, a)` (Luau reports the swapped operands too).
pub fn lt(a: &Value, b: &Value) -> LResult<bool> {
    if let Some(method) = compare_method("__lt", a, b) {
        return call_metamethod_first(&method, vec![a.clone(), b.clone()]).map(|v| v.truthy());
    }
    compare(a, b, "<", |o| o.is_lt(), |x, y| x < y)
}

/// `a <= b`. `a >= b` is `le(b, a)`.
pub fn le(a: &Value, b: &Value) -> LResult<bool> {
    if let Some(method) = compare_method("__le", a, b) {
        return call_metamethod_first(&method, vec![a.clone(), b.clone()]).map(|v| v.truthy());
    }
    if let Some(method) = compare_method("__lt", b, a) {
        return call_metamethod_first(&method, vec![b.clone(), a.clone()]).map(|v| !v.truthy());
    }
    compare(a, b, "<=", |o| o.is_le(), |x, y| x <= y)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::show::{eq, tostring, truthy};

    fn s(x: &str) -> Value {
        Value::Str(LStr::from(x))
    }

    #[test]
    fn display_type_truthiness() {
        assert_eq!(tostring(&Value::Nil).to_string_lossy(), "nil");
        assert_eq!(tostring(&Value::Bool(true)).to_string_lossy(), "true");
        assert_eq!(tostring(&Value::Num(1.5)).to_string_lossy(), "1.5");
        assert_eq!(tostring(&s("x")).to_string_lossy(), "x");
        assert_eq!(Value::Num(0.0).type_name(), "number");
        assert!(truthy(&Value::Num(0.0)) && truthy(&s("")));
        assert!(!truthy(&Value::Nil) && !truthy(&Value::Bool(false)));
    }

    #[test]
    fn equality_is_by_kind_and_identity() {
        assert!(eq(&Value::Num(1.0), &Value::Num(1.0)));
        assert!(!eq(&Value::Num(1.0), &s("1")));
        assert!(!eq(&Value::Nil, &Value::Bool(false)));
        let t = Arr::from_vec(vec![1.0f64]);
        let u = Arr::from_vec(vec![1.0f64]);
        assert!(eq(&to_value(t.clone()), &to_value(t.clone())));
        assert!(!eq(&to_value(t), &to_value(u)));
    }

    #[test]
    fn casts_check_the_tag_and_the_type() {
        assert_eq!(cast::<f64>(&Value::Num(2.0), "number").unwrap(), 2.0);
        let e = cast::<f64>(&s("x"), "number").unwrap_err();
        assert_eq!(e.msg.to_string_lossy(), "invalid cast: expected number, got string");
        assert!(cast_opt::<f64>(&Value::Nil, "number").unwrap().is_none());
        let t = to_value(Arr::from_vec(vec![1.0f64, 2.0]));
        assert_eq!(cast::<Arr<f64>>(&t, "{number}").unwrap().len(), 2.0);
        assert!(cast::<Arr<LStr>>(&t, "{string}").is_err());
    }

    #[test]
    fn protected_result_boxing_preserves_success_nil_and_error_values() {
        assert!(matches!(to_value(crate::PcallVal::Ok(Some(7.0))), Value::Num(7.0)));
        assert!(matches!(to_value(crate::PcallVal::Ok(None::<f64>)), Value::Nil));
        assert!(matches!(to_value(crate::PcallVal::Ok(false)), Value::Bool(false)));
        let error: crate::PcallVal<Option<f64>> = crate::PcallVal::Err(LStr::from("sentinel-failure"));
        assert!(eq(&to_value(error), &s("sentinel-failure")));
    }

    #[test]
    fn arithmetic_and_messages_match_luau() {
        let r = |op, a: &Value, b: &Value| arith(op, a, b).map(|v| tostring(&v).to_string_lossy()).map_err(|e| e.msg.to_string_lossy());
        assert_eq!(r(Arith::Add, &Value::Num(1.0), &Value::Num(2.0)).unwrap(), "3");
        assert_eq!(r(Arith::Add, &s("10"), &Value::Num(1.0)).unwrap(), "11");
        assert_eq!(r(Arith::Add, &Value::Num(1.0), &s("x")).unwrap_err(), "attempt to perform arithmetic (add) on number and string");
        assert_eq!(r(Arith::Div, &Value::Num(1.0), &Value::Nil).unwrap_err(), "attempt to perform arithmetic (div) on number and nil");
        assert_eq!(r(Arith::Add, &Value::Nil, &Value::Nil).unwrap_err(), "attempt to perform arithmetic (add) on nil");
        assert_eq!(r(Arith::Add, &s("x"), &s("y")).unwrap_err(), "attempt to perform arithmetic (add) on string");
        assert_eq!(r(Arith::Add, &Value::Bool(true), &Value::Bool(false)).unwrap_err(), "attempt to perform arithmetic (add) on boolean");
        assert_eq!(r(Arith::Mod, &Value::Num(7.0), &s("2")).unwrap(), "1");
        assert_eq!(neg(&Value::Nil).unwrap_err().msg.to_string_lossy(), "attempt to perform arithmetic (unm) on nil");
        assert_eq!(tostring(&neg(&s("5")).unwrap()).to_string_lossy(), "-5");
    }

    #[test]
    fn concat_and_compare_messages_match_luau() {
        assert_eq!(concat(&Value::Num(1.5), &s("x")).unwrap().to_string_lossy(), "1.5x");
        let e = concat(&Value::Nil, &s("x")).unwrap_err();
        assert_eq!(e.msg.to_string_lossy(), "attempt to concatenate nil with string");
        assert!(lt(&Value::Num(1.0), &Value::Num(2.0)).unwrap());
        assert!(le(&s("a"), &s("b")).unwrap());
        let e = lt(&Value::Num(1.0), &s("x")).unwrap_err();
        assert_eq!(e.msg.to_string_lossy(), "attempt to compare number < string");
        let e = le(&Value::Nil, &Value::Num(1.0)).unwrap_err();
        assert_eq!(e.msg.to_string_lossy(), "attempt to compare nil <= number");
    }
}
