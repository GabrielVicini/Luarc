//! Typed-to-erased closure adapters. They retain the original callable identity
//! and trace its environment; missing arguments are nil, extra ones are dropped.

use crate::dynamic::{FromValue, Obj, ToValue, Value};
use crate::gc::{TraceWith, Visitor};
use crate::{Callable, LFn, LResult, LuaError};

pub trait FromValues: Sized {
    fn from_values(values: &[Value]) -> LResult<Self>;
}

pub trait IntoValues {
    fn into_values(self) -> Vec<Value>;
}

/// One erased result, including a callable occurring inside a result tuple.
pub trait IntoDynamic {
    fn into_dynamic(self) -> Value;
}

impl FromValues for () {
    fn from_values(_: &[Value]) -> LResult<Self> {
        Ok(())
    }
}
impl FromValues for Vec<Value> {
    fn from_values(values: &[Value]) -> LResult<Self> {
        Ok(values.to_vec())
    }
}
impl FromValues for Vec<Option<Value>> {
    fn from_values(values: &[Value]) -> LResult<Self> {
        Ok(values
            .iter()
            .map(|value| {
                if value.is_nil() {
                    None
                } else {
                    Some(value.clone())
                }
            })
            .collect())
    }
}
impl IntoValues for () {
    fn into_values(self) -> Vec<Value> {
        vec![]
    }
}
impl IntoValues for Vec<Value> {
    fn into_values(self) -> Vec<Value> {
        self
    }
}
impl<T: IntoDynamic> IntoValues for Vec<Option<T>> {
    fn into_values(self) -> Vec<Value> {
        self.into_iter().map(IntoDynamic::into_dynamic).collect()
    }
}
impl<T: IntoDynamic> IntoValues for Option<T> {
    fn into_values(self) -> Vec<Value> {
        vec![self.into_dynamic()]
    }
}
impl<T: IntoDynamic> IntoDynamic for Option<T> {
    fn into_dynamic(self) -> Value {
        self.map_or(Value::Nil, IntoDynamic::into_dynamic)
    }
}
impl<A: FromValues + 'static, R: IntoValues + 'static> IntoValues for LFn<A, R> {
    fn into_values(self) -> Vec<Value> {
        vec![function(self)]
    }
}
impl<A: FromValues + 'static, R: IntoValues + 'static> IntoDynamic for LFn<A, R> {
    fn into_dynamic(self) -> Value {
        function(self)
    }
}

macro_rules! values {
    ($($ty:ty),* $(,)?) => {$(
        impl IntoValues for $ty {
            fn into_values(self) -> Vec<Value> { vec![self.to_value()] }
        }
        impl IntoDynamic for $ty {
            fn into_dynamic(self) -> Value { self.to_value() }
        }
    )*};
}
values!(
    Value,
    f64,
    bool,
    crate::LStr,
    crate::Table,
    crate::coroutine::Thread
);
impl IntoDynamic for () {
    fn into_dynamic(self) -> Value {
        Value::Nil
    }
}

impl<T: dumpster::Trace + Clone + 'static> IntoDynamic for crate::Arr<T> {
    fn into_dynamic(self) -> Value {
        self.to_value()
    }
}
impl<T: dumpster::Trace + Clone + 'static> IntoValues for crate::Arr<T> {
    fn into_values(self) -> Vec<Value> {
        vec![self.to_value()]
    }
}

macro_rules! opaque_values {
    ($name:ident<$($param:ident:$bound:path),+>) => {
        impl<$($param: $bound + 'static),+> IntoDynamic for crate::$name<$($param),+> {
            fn into_dynamic(self) -> Value { self.to_value() }
        }
        impl<$($param: $bound + 'static),+> IntoValues for crate::$name<$($param),+> {
            fn into_values(self) -> Vec<Value> { vec![self.to_value()] }
        }
    };
}
opaque_values!(Rec<T:dumpster::Trace>);
opaque_values!(MetaRec<T:dumpster::Trace, P:dumpster::Trace>);
impl<
        K: dumpster::Trace + Clone + Eq + std::hash::Hash + 'static,
        V: dumpster::Trace + Clone + 'static,
    > IntoDynamic for crate::LMap<K, V>
{
    fn into_dynamic(self) -> Value {
        self.to_value()
    }
}
impl<
        K: dumpster::Trace + Clone + Eq + std::hash::Hash + 'static,
        V: dumpster::Trace + Clone + 'static,
    > IntoValues for crate::LMap<K, V>
{
    fn into_values(self) -> Vec<Value> {
        vec![self.to_value()]
    }
}
impl<T: 'static> IntoDynamic for crate::Handle<T> {
    fn into_dynamic(self) -> Value {
        self.to_value()
    }
}
impl<T: 'static> IntoValues for crate::Handle<T> {
    fn into_values(self) -> Vec<Value> {
        vec![self.to_value()]
    }
}
impl<T: dumpster::Trace + IntoDynamic + 'static> IntoDynamic for crate::value::FalseOr<T> {
    fn into_dynamic(self) -> Value {
        match self {
            crate::value::FalseOr::False => Value::Bool(false),
            crate::value::FalseOr::Val(v) => v.into_dynamic(),
        }
    }
}
impl<T: dumpster::Trace + IntoDynamic + 'static> IntoValues for crate::value::FalseOr<T> {
    fn into_values(self) -> Vec<Value> {
        vec![self.into_dynamic()]
    }
}
impl<T: dumpster::Trace + IntoDynamic + 'static> IntoDynamic for crate::value::PcallVal<T> {
    fn into_dynamic(self) -> Value {
        match self {
            crate::value::PcallVal::Ok(v) => v.into_dynamic(),
            crate::value::PcallVal::Err(e) => Value::Str(e),
        }
    }
}
impl<T: dumpster::Trace + IntoDynamic + 'static> IntoValues for crate::value::PcallVal<T> {
    fn into_values(self) -> Vec<Value> {
        vec![self.into_dynamic()]
    }
}

macro_rules! tuple {
    ($($ty:ident:$index:tt),+) => {
        impl<$($ty: FromValue),+> FromValues for ($($ty,)+) {
            fn from_values(values: &[Value]) -> LResult<Self> {
                Ok(($({
                    let value = values.get($index).unwrap_or(&Value::Nil);
                    $ty::from_value(value).ok_or_else(|| LuaError::new(format!(
                        "invalid argument #{} (incompatible {} value)", $index + 1, value.type_name()
                    )))?
                },)+))
            }
        }
        impl<$($ty: IntoDynamic),+> IntoValues for ($($ty,)+) {
            fn into_values(self) -> Vec<Value> {
                vec![$(self.$index.into_dynamic()),+]
            }
        }
    };
}
tuple!(A:0);
tuple!(A:0, B:1);
tuple!(A:0, B:1, C:2);
tuple!(A:0, B:1, C:2, D:3);
tuple!(A:0, B:1, C:2, D:3, E:4);
tuple!(A:0, B:1, C:2, D:3, E:4, F:5);
tuple!(A:0, B:1, C:2, D:3, E:4, F:5, G:6);
tuple!(A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7);

macro_rules! tuple_pack {
    ($count:tt; $($ty:ident:$index:tt),+) => {
        impl<$($ty: FromValue),+> FromValues for ($($ty,)+ Vec<Option<Value>>) {
            fn from_values(values: &[Value]) -> LResult<Self> {
                Ok(($({
                    let value = values.get($index).unwrap_or(&Value::Nil);
                    $ty::from_value(value).ok_or_else(|| LuaError::new(format!(
                        "invalid argument #{} (incompatible {} value)", $index + 1, value.type_name()
                    )))?
                },)+ Vec::<Option<Value>>::from_values(values.get($count..).unwrap_or(&[]))?))
            }
        }
        impl<T: IntoDynamic, $($ty: IntoDynamic),+> IntoValues for ($($ty,)+ Vec<Option<T>>) {
            fn into_values(self) -> Vec<Value> {
                let mut values = vec![$(self.$index.into_dynamic()),+];
                values.extend(self.$count.into_values());
                values
            }
        }
    };
}
impl FromValues for (Vec<Option<Value>>,) {
    fn from_values(values: &[Value]) -> LResult<Self> {
        Ok((Vec::<Option<Value>>::from_values(values)?,))
    }
}
impl<T: IntoDynamic> IntoValues for (Vec<Option<T>>,) {
    fn into_values(self) -> Vec<Value> {
        self.0.into_values()
    }
}
tuple_pack!(1; A:0);
tuple_pack!(2; A:0, B:1);
tuple_pack!(3; A:0, B:1, C:2);
tuple_pack!(4; A:0, B:1, C:2, D:3);
tuple_pack!(5; A:0, B:1, C:2, D:3, E:4);
tuple_pack!(6; A:0, B:1, C:2, D:3, E:4, F:5);
tuple_pack!(7; A:0, B:1, C:2, D:3, E:4, F:5, G:6);

/// Erase a source pack, preserving nil slots, callable identities, and arity.
pub fn pack_values<T: Clone + IntoDynamic>(values: &[Option<T>], first: usize) -> Vec<Value> {
    values
        .get(first..)
        .unwrap_or(&[])
        .iter()
        .cloned()
        .map(IntoDynamic::into_dynamic)
        .collect()
}

struct Adapter<A: 'static, R: 'static> {
    function: LFn<A, R>,
}

// SAFETY: the callable is the only managed edge; signature types are not stored.
unsafe impl<V: Visitor, A: 'static, R: 'static> TraceWith<V> for Adapter<A, R> {
    fn accept(&self, visitor: &mut V) -> Result<(), ()> {
        self.function.accept(visitor)
    }
}

impl<A: FromValues + 'static, R: IntoValues + 'static> Callable<Vec<Value>, Vec<Value>>
    for Adapter<A, R>
{
    fn call(&self, _: &LFn<Vec<Value>, Vec<Value>>, values: Vec<Value>) -> LResult<Vec<Value>> {
        self.function
            .call(A::from_values(&values)?)
            .map(IntoValues::into_values)
    }
}

/// Box a callable using the erased ABI while retaining raw equality with another
/// boxing of the same callable (especially shared __eq/__lt metamethods).
pub fn function<A: FromValues + 'static, R: IntoValues + 'static>(function: LFn<A, R>) -> Value {
    let addr = function.addr();
    let erased = LFn::<Vec<Value>, Vec<Value>>::new(Adapter { function: function.clone() });
    Value::Function(Obj::with_original(erased, function, addr))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dynamic;
    use crate::show::LuaEq;

    #[test]
    fn erased_function_display_uses_original_identity() {
        let typed = LFn::from_fn(|(): ()| Ok(7.0));
        let expected = crate::show::tostring(&typed);
        let plain = typed.clone().to_value();
        let a = function(typed.clone());
        let b = function(typed);
        assert!(a.lua_eq(&b));
        assert!(a.lua_eq(&plain));
        assert_eq!(crate::show::tostring(&a), expected);
        assert_eq!(crate::show::tostring(&b), expected);
        assert_eq!(crate::show::tostring(&plain), expected);
    }

    #[test]
    fn adapter_keeps_identity_and_all_results() {
        let typed = LFn::from_fn(|(a, b): (Value, Value)| Ok((a, b)));
        let a = function(typed.clone());
        let b = function(typed);
        assert!(a.lua_eq(&b));
        let results = dynamic::call(&a, vec![Value::Num(7.0)]).unwrap();
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].as_num().unwrap(), 7.0);
        assert!(results[1].is_nil());
    }

    #[test]
    fn tuple_results_erase_nested_callables() {
        let typed =
            LFn::from_fn(|(): ()| Ok((LFn::from_fn(|(): ()| Ok(7.0)), Value::Nil, Value::Nil)));
        let values = dynamic::call(&function(typed), vec![]).unwrap();
        assert_eq!(values.len(), 3);
        assert_eq!(
            dynamic::call_first(&values[0], vec![])
                .unwrap()
                .as_num()
                .unwrap(),
            7.0
        );
    }

    #[test]
    fn erased_function_retains_its_matching_typed_view() {
        let typed = LFn::from_fn(|(): ()| Ok(7.0));
        let erased = function(typed.clone());
        let recovered = LFn::<(), f64>::from_value(&erased).expect("matching typed callable");
        assert!(recovered.ptr_eq(&typed));
        assert_eq!(recovered.call(()).unwrap(), 7.0);
        assert_eq!(dynamic::call_first(&erased, vec![]).unwrap().as_num().unwrap(), 7.0);
        assert!(erased.lua_eq(&recovered.to_value()));
        assert!(erased.lua_eq(&function(typed)));

        // Reject mismatched signatures instead of reinterpreting them.
        assert!(LFn::<(f64,), f64>::from_value(&erased).is_none());
        let mismatch = dynamic::cast::<LFn<(), crate::LStr>>(&erased, "() -> string");
        assert_eq!(mismatch.err().unwrap().msg.as_bytes(), b"invalid cast: expected () -> string, got function");
        assert!(LFn::<(), f64>::from_value(&Value::Nil).is_none());
        assert!(LFn::<(), f64>::from_value(&Value::Num(7.0)).is_none());
    }

    #[test]
    fn an_already_erased_signature_retains_original_identity_and_calls() {
        let typed = LFn::from_fn(|values: Vec<Value>| Ok(values));
        let erased = function(typed.clone());
        let recovered = LFn::<Vec<Value>, Vec<Value>>::from_value(&erased).expect("original erased signature");
        assert!(recovered.ptr_eq(&typed));
        assert!(erased.lua_eq(&recovered.clone().to_value()));
        let arguments = vec![Value::Num(8.0), Value::Nil, Value::Str("tail".into())];
        for results in [dynamic::call(&erased, arguments.clone()).unwrap(), recovered.call(arguments.clone()).unwrap()] {
            assert_eq!(results.len(), arguments.len());
            assert!(results.iter().zip(&arguments).all(|(actual, expected)| actual.lua_eq(expected)));
        }
    }

    #[derive(dumpster::Trace)]
    struct CapturedFunctionCycle {
        value: crate::Cell<Option<Value>>,
    }

    impl Callable<(), f64> for CapturedFunctionCycle {
        fn call(&self, _: &LFn<(), f64>, (): ()) -> LResult<f64> {
            Ok(if self.value.get().is_some() { 7.0 } else { 0.0 })
        }
    }

    #[test]
    fn both_function_views_trace_cycles_and_recovered_roots() {
        crate::gc::collect();
        let baseline = crate::gc::live_objects();
        {
            let captured = crate::Cell::new(None);
            let typed = LFn::new(CapturedFunctionCycle { value: captured.clone() });
            let erased = function(typed.clone());
            captured.set(Some(erased.clone()));
            let recovered = LFn::<(), f64>::from_value(&erased).expect("captured typed callable");
            assert!(recovered.ptr_eq(&typed));
            drop(typed);
            drop(captured);
            drop(erased);
            crate::gc::collect();
            assert_eq!(crate::gc::live_objects(), baseline + 4);
            assert_eq!(recovered.call(()).unwrap(), 7.0);
        }
        crate::gc::collect();
        assert_eq!(crate::gc::live_objects(), baseline);
    }

    #[test]
    fn pack_adapters_preserve_nil_and_all_values() {
        let typed = LFn::from_fn(|(first, rest): (Value, Vec<Option<Value>>)| Ok((first, rest)));
        let values = vec![
            Value::Str("first".into()),
            Value::Nil,
            Value::Num(3.0),
            Value::Nil,
        ];
        let result = dynamic::call(&function(typed), values).unwrap();
        assert_eq!(result.len(), 4);
        assert!(result[1].is_nil());
        assert_eq!(result[2].as_num().unwrap(), 3.0);
        assert!(result[3].is_nil());
    }

    #[test]
    fn typed_pack_results_are_erased_without_losing_nil() {
        let typed = LFn::from_fn(|(): ()| {
            Ok((crate::LStr::from("fixed"), vec![Some(7.0), None, Some(9.0)]))
        });
        let result = dynamic::call(&function(typed), vec![]).unwrap();
        assert_eq!(result.len(), 4);
        assert_eq!(result[1].as_num().unwrap(), 7.0);
        assert!(result[2].is_nil());
        assert_eq!(result[3].as_num().unwrap(), 9.0);
    }
}
