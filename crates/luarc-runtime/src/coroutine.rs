//! Same-thread stackful coroutines. Managed values never cross OS threads.
//!
//! `corosensei` owns the guarded stack and unwinds suspended frames on close/drop.
//! The live stack's managed handles are external roots, as in opaque native
//! storage. Stack memory is not traced.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use corosensei::{Coroutine as Stack, CoroutineResult, Yielder};

use crate::dynamic::{FromValue, ToValue, Value};
use crate::error::{LResult, LuaError};
use crate::gc::{TraceWith, Visitor};
use crate::show::{LuaDisplay, LuaEq, LuaType};
use crate::{Callable, LFn, LStr};

type Values = Vec<Value>;
type Engine = Stack<Values, Values, LResult<Values>>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Suspended,
    Running,
    Dead,
}

struct State {
    engine: RefCell<Option<Engine>>,
    phase: Cell<Phase>,
    error: RefCell<Option<LuaError>>,
}

/// A coroutine handle: clone preserves thread identity and suspended stack.
#[derive(Clone)]
pub struct Thread(Rc<State>);

// SAFETY: opaque stacks hold independently counted managed roots, not traced
// edges. As with native futures, cycles through these roots can leak;
// marking their contents as traced without a real stack map would be unsound.
unsafe impl<V: Visitor> TraceWith<V> for Thread {
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

struct Active {
    id: usize,
    yielder: *const Yielder<Values, Values>,
    blocked: usize,
}

thread_local! {
    static ACTIVE: RefCell<Vec<Active>> = const { RefCell::new(Vec::new()) };
    static MAIN_BLOCKED: Cell<usize> = const { Cell::new(0) };
}

/// The resumer owns context restoration after each switch. Keeping this guard
/// off suspended stacks also avoids the optimized Windows forced-unwind crash
/// exercised by the close/drop regressions; no TLS cleanup runs in those frames.
struct ActiveGuard(usize);

impl Drop for ActiveGuard {
    fn drop(&mut self) {
        ACTIVE.with(|a| {
            let mut a = a.borrow_mut();
            a.truncate(self.0);
        });
    }
}

impl Thread {
    pub fn new(f: Value) -> LResult<Self> {
        if !matches!(f, Value::Function(_)) {
            return Err(LuaError::new(format!(
                "invalid argument #1 to 'create' (function expected, got {})",
                f.type_name()
            )));
        }
        let state = Rc::new(State {
            engine: RefCell::new(None),
            phase: Cell::new(Phase::Suspended),
            error: RefCell::new(None),
        });
        let id = Rc::as_ptr(&state) as usize;
        let engine = Stack::new(move |yielder, args| {
            ACTIVE.with(|a| {
                a.borrow_mut().push(Active {
                    id,
                    yielder,
                    blocked: 0,
                })
            });
            // Retained native callbacks use the existing callback unwind
            // bridge. Catch that language channel inside this thread, so resume
            // reports false/message; unrelated panics still propagate fatally.
            crate::callback::guard(|| match LFn::<Values, Values>::from_value(&f) {
                Some(f) => f.call(args),
                None => Err(LuaError::new(
                    "coroutine function has an incompatible calling convention",
                )),
            })
            .and_then(|result| result)
        });
        *state.engine.borrow_mut() = Some(engine);
        Ok(Thread(state))
    }

    pub fn addr(&self) -> usize {
        Rc::as_ptr(&self.0) as usize
    }

    pub fn status(&self) -> &'static str {
        match self.0.phase.get() {
            Phase::Suspended => "suspended",
            Phase::Dead => "dead",
            Phase::Running => {
                if ACTIVE.with(|a| a.borrow().last().map(|a| a.id)) == Some(self.addr()) {
                    "running"
                } else {
                    "normal"
                }
            }
        }
    }

    fn run(&self, args: Values) -> LResult<Values> {
        match self.0.phase.get() {
            Phase::Dead => return Err(LuaError::new("cannot resume dead coroutine")),
            Phase::Running => {
                return Err(LuaError::new(format!(
                    "cannot resume {} coroutine",
                    self.status()
                )))
            }
            Phase::Suspended => {}
        }
        let Some(mut engine) = self.0.engine.borrow_mut().take() else {
            return Err(LuaError::new("cannot resume dead coroutine"));
        };
        self.0.phase.set(Phase::Running);
        let _active = ActiveGuard(ACTIVE.with(|a| a.borrow().len()));
        match engine.resume(args) {
            CoroutineResult::Yield(values) => {
                self.0.phase.set(Phase::Suspended);
                *self.0.engine.borrow_mut() = Some(engine);
                Ok(values)
            }
            CoroutineResult::Return(result) => {
                self.0.phase.set(Phase::Dead);
                if let Err(e) = &result {
                    *self.0.error.borrow_mut() = Some(e.clone());
                }
                result
            }
        }
    }

    pub fn resume(&self, args: Values) -> Values {
        protected(self.run(args))
    }

    pub fn close(&self) -> LResult<Values> {
        if self.0.phase.get() == Phase::Running {
            return Err(LuaError::new(format!(
                "cannot close {} coroutine",
                self.status()
            )));
        }
        self.0.phase.set(Phase::Dead);
        // Drop outside the RefCell borrow: unwinding can drop source objects.
        let engine = self.0.engine.borrow_mut().take();
        drop(engine);
        Ok(protected(match self.0.error.borrow_mut().take() {
            Some(e) => Err(e),
            None => Ok(vec![]),
        }))
    }
}

fn protected(result: LResult<Values>) -> Values {
    match result {
        Ok(mut values) => {
            values.insert(0, Value::Bool(true));
            values
        }
        Err(e) => vec![Value::Bool(false), Value::Str(e.msg)],
    }
}

fn thread(value: &Value, name: &str) -> LResult<Thread> {
    Thread::from_value(value).ok_or_else(|| {
        LuaError::new(format!(
            "invalid argument #1 to '{name}' (thread expected, got {})",
            value.type_name()
        ))
    })
}

pub fn create(f: Value) -> LResult<Value> {
    Ok(Thread::new(f)?.to_value())
}
pub fn resume(value: &Value, args: Values) -> LResult<Values> {
    Ok(thread(value, "resume")?.resume(args))
}
pub fn status(value: &Value) -> LResult<LStr> {
    Ok(LStr::from(thread(value, "status")?.status()))
}
pub fn close(value: &Value) -> LResult<Values> {
    thread(value, "close")?.close()
}

fn first<'a>(values: &'a [Value], name: &str, expected: &str) -> LResult<&'a Value> {
    values.first().ok_or_else(|| {
        LuaError::new(format!(
            "missing argument #1 to '{name}' ({expected} expected)"
        ))
    })
}

pub fn create_args(values: &[Value]) -> LResult<Value> {
    create(first(values, "create", "function")?.clone())
}
pub fn status_args(values: &[Value]) -> LResult<LStr> {
    status(first(values, "status", "thread")?)
}
pub fn close_args(values: &[Value]) -> LResult<Values> {
    close(first(values, "close", "thread")?)
}
pub fn resume_args(mut values: Values) -> LResult<Values> {
    first(&values, "resume", "thread")?;
    let value = values.remove(0);
    resume(&value, values)
}

/// Source result packs keep nil as an empty element, without losing arity.
pub fn pack_values(values: Values) -> Vec<Option<Value>> {
    values
        .into_iter()
        .map(|v| if v.is_nil() { None } else { Some(v) })
        .collect()
}

pub fn join_values(mut values: Values, tail: Values) -> Values {
    values.extend(tail);
    values
}

/// Luau's standalone CLI executes its entry chunk in a yieldable coroutine too.
pub fn isyieldable() -> bool {
    ACTIVE
        .with(|a| a.borrow().last().map(|a| a.blocked == 0))
        .unwrap_or_else(|| MAIN_BLOCKED.with(|b| b.get() == 0))
}

pub fn yield_values(values: Values) -> LResult<Values> {
    if !isyieldable() {
        return Err(LuaError::located(
            "attempt to yield across metamethod/C-call boundary",
        ));
    }
    let active = ACTIVE.with(|a| a.borrow_mut().pop());
    let Some(active) = active else {
        // Compiled coroutine programs enter through `drive_entry`; this reports
        // Rust API misuse without panicking when no source execution is active.
        return Err(LuaError::new(
            "coroutine.yield requires the coroutine entry driver",
        ));
    };
    // SAFETY: the pointer came from this coroutine's `Stack::new` callback and
    // stays on its guarded stack until that callback returns. ACTIVE only holds
    // the executing coroutine; the entry is removed before suspension and
    // restored only after resumption on the same thread. No pointer escapes to
    // another stack or thread; forced unwind drops `active` without restoring it.
    let values = unsafe { (&*active.yielder).suspend(values) };
    ACTIVE.with(|a| a.borrow_mut().push(active));
    Ok(values)
}

/// Host outcome of a source entry chunk, including a yield escaping the chunk.
pub enum Entry {
    Returned(LResult<()>),
    Yielded,
}

/// Luau CLI runs its entry chunk as a yieldable coroutine. A yielded chunk
/// returns to the host, outside every source pcall; dropping the root unwinds
/// all suspended frames before the executable reports the host error.
pub fn drive_entry(body: impl FnOnce() -> LResult<()> + 'static) -> Entry {
    let mut root = Stack::new(move |yielder: &Yielder<Values, Values>, _: Values| {
        let id = yielder as *const Yielder<Values, Values> as usize;
        ACTIVE.with(|a| {
            a.borrow_mut().push(Active {
                id,
                yielder,
                blocked: 0,
            })
        });
        body()
    });
    let _active = ActiveGuard(ACTIVE.with(|a| a.borrow().len()));
    match root.resume(vec![]) {
        CoroutineResult::Yield(_) => Entry::Yielded,
        CoroutineResult::Return(result) => Entry::Returned(result),
    }
}

struct Boundary(Option<usize>);

impl Drop for Boundary {
    fn drop(&mut self) {
        ACTIVE.with(|a| {
            if let Some(id) = self.0 {
                if let Some(active) = a.borrow_mut().last_mut().filter(|a| a.id == id) {
                    active.blocked -= 1;
                }
            } else {
                MAIN_BLOCKED.with(|b| b.set(b.get() - 1));
            }
        });
    }
}

/// Luau forbids yielding through library/metamethod/native callback boundaries.
pub fn non_yielding<T>(f: impl FnOnce() -> T) -> T {
    let id = ACTIVE.with(|a| {
        let mut a = a.borrow_mut();
        if let Some(active) = a.last_mut() {
            active.blocked += 1;
            Some(active.id)
        } else {
            MAIN_BLOCKED.with(|b| b.set(b.get() + 1));
            None
        }
    });
    let _guard = Boundary(id);
    f()
}

struct Wrapped(Thread);

// SAFETY: visits the only field (its opaque stack keeps external GC roots).
unsafe impl<V: Visitor> TraceWith<V> for Wrapped {
    fn accept(&self, v: &mut V) -> Result<(), ()> {
        self.0.accept(v)
    }
}

impl Callable<Values, Values> for Wrapped {
    fn call(&self, _: &LFn<Values, Values>, args: Values) -> LResult<Values> {
        // Luau adds the wrapper call's location even to an already located error.
        self.0.run(args).map_err(|e| LuaError::new(e.msg))
    }
}

pub fn wrap(f: Value) -> LResult<Value> {
    if !matches!(f, Value::Function(_)) {
        return Err(LuaError::new(format!(
            "invalid argument #1 to 'wrap' (function expected, got {})",
            f.type_name()
        )));
    }
    Ok(LFn::new(Wrapped(Thread::new(f)?)).to_value())
}

type SourceValues = Vec<Option<Value>>;
struct SourceWrapped(Thread);

// SAFETY: the coroutine handle is the only field.
unsafe impl<V: Visitor> TraceWith<V> for SourceWrapped {
    fn accept(&self, v: &mut V) -> Result<(), ()> {
        self.0.accept(v)
    }
}

impl Callable<(SourceValues,), SourceValues> for SourceWrapped {
    fn call(
        &self,
        _: &LFn<(SourceValues,), SourceValues>,
        (args,): (SourceValues,),
    ) -> LResult<SourceValues> {
        self.0
            .run(args.into_iter().map(|v| v.unwrap_or(Value::Nil)).collect())
            .map(pack_values)
            .map_err(|e| LuaError::new(e.msg))
    }
}

pub fn wrap_source_args(values: &[Value]) -> LResult<LFn<(SourceValues,), SourceValues>> {
    let f = first(values, "wrap", "function")?;
    if !matches!(f, Value::Function(_)) {
        return Err(LuaError::new(format!(
            "invalid argument #1 to 'wrap' (function expected, got {})",
            f.type_name()
        )));
    }
    Ok(LFn::new(SourceWrapped(Thread::new(f.clone())?)))
}

impl LuaDisplay for Thread {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(format!("thread: 0x{:x}", self.addr()).as_bytes());
    }
}
impl LuaType for Thread {
    fn lua_type(&self) -> &'static str {
        "thread"
    }
}
impl LuaEq for Thread {
    fn lua_eq(&self, other: &Self) -> bool {
        self.addr() == other.addr()
    }
}
impl ToValue for Thread {
    fn to_value(self) -> Value {
        Value::Thread(self)
    }
}
impl FromValue for Thread {
    fn from_value(v: &Value) -> Option<Self> {
        if let Value::Thread(t) = v {
            Some(t.clone())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestFn<F>(F);
    // SAFETY: test callbacks keep any managed handles as external roots.
    unsafe impl<V: Visitor, F> TraceWith<V> for TestFn<F> {
        fn accept(&self, _: &mut V) -> Result<(), ()> {
            Ok(())
        }
    }
    impl<F: Fn(Values) -> LResult<Values> + 'static> Callable<Values, Values> for TestFn<F> {
        fn call(&self, _: &LFn<Values, Values>, args: Values) -> LResult<Values> {
            (self.0)(args)
        }
    }
    fn function(f: impl Fn(Values) -> LResult<Values> + 'static) -> Value {
        LFn::new(TestFn(f)).to_value()
    }
    fn s(s: &str) -> Value {
        Value::Str(LStr::from(s))
    }
    fn assert_values(got: Values, want: Values) {
        assert_eq!(got.len(), want.len(), "{got:?} != {want:?}");
        for (a, b) in got.iter().zip(&want) {
            assert!(a.lua_eq(b), "{got:?} != {want:?}");
        }
    }

    #[test]
    fn yields_and_resumes_with_all_results_and_nil() {
        let t = Thread::new(function(|args| {
            let Value::Num(start) = args[0] else {
                return Err(LuaError::new("number expected"));
            };
            let args = yield_values(vec![s("phase1"), Value::Num(start + 1.0), Value::Nil])?;
            let Value::Num(a) = args[0] else {
                return Err(LuaError::new("number expected"));
            };
            Ok(vec![s("phase2"), Value::Num(a * 2.0), args[1].clone()])
        }))
        .unwrap();
        assert_eq!(t.status(), "suspended");
        assert_values(
            t.resume(vec![Value::Num(10.0)]),
            vec![Value::Bool(true), s("phase1"), Value::Num(11.0), Value::Nil],
        );
        assert_eq!(t.status(), "suspended");
        assert_values(
            t.resume(vec![Value::Num(7.0), s("ok")]),
            vec![Value::Bool(true), s("phase2"), Value::Num(14.0), s("ok")],
        );
        assert_eq!(t.status(), "dead");
        assert_values(
            t.resume(vec![]),
            vec![Value::Bool(false), s("cannot resume dead coroutine")],
        );
    }

    #[test]
    fn wrap_preserves_nil_and_repeated_suspensions() {
        let wrapped = wrap(function(|_| {
            yield_values(vec![s("one"), Value::Nil])?;
            yield_values(vec![s("two"), Value::Num(2.0)])?;
            Ok(vec![s("done"), Value::Num(3.0)])
        }))
        .unwrap();
        let f = LFn::<Values, Values>::from_value(&wrapped).unwrap();
        assert_values(f.call(vec![]).unwrap(), vec![s("one"), Value::Nil]);
        assert_values(f.call(vec![]).unwrap(), vec![s("two"), Value::Num(2.0)]);
        assert_values(f.call(vec![]).unwrap(), vec![s("done"), Value::Num(3.0)]);
        assert_eq!(
            f.call(vec![]).unwrap_err().msg.to_string_lossy(),
            "cannot resume dead coroutine"
        );
    }

    #[test]
    fn error_is_reported_by_resume_then_close_and_close_resets_error() {
        let t = Thread::new(function(|_| Err(LuaError::located("bad")))).unwrap();
        assert_values(t.resume(vec![]), vec![Value::Bool(false), s("bad")]);
        assert_eq!(t.status(), "dead");
        assert_values(t.close().unwrap(), vec![Value::Bool(false), s("bad")]);
        assert_values(t.close().unwrap(), vec![Value::Bool(true)]);
    }

    #[test]
    fn direct_stack_close_unwinds_frames() {
        struct Dropped(Rc<Cell<usize>>);
        impl Drop for Dropped {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let count = Rc::new(Cell::new(0));
        let copied = count.clone();
        let mut stack: Engine = Stack::new(move |y: &Yielder<Values, Values>, _: Values| {
            ACTIVE.with(|a| {
                a.borrow_mut().push(Active {
                    id: 17,
                    yielder: y,
                    blocked: 0,
                })
            });
            let _d = Dropped(copied);
            yield_values(vec![])?;
            Ok(vec![])
        });
        assert!(matches!(stack.resume(vec![]), CoroutineResult::Yield(_)));
        drop(stack);
        assert_eq!(count.get(), 1);
    }

    #[test]
    fn closing_a_suspended_stack_runs_destructors() {
        struct Dropped(Rc<Cell<usize>>);
        impl Drop for Dropped {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let count = Rc::new(Cell::new(0));
        let cloned = count.clone();
        let t = Thread::new(function(move |_| {
            let _dropped = Dropped(cloned.clone());
            yield_values(vec![])?;
            Ok(vec![])
        }))
        .unwrap();
        assert_values(t.resume(vec![]), vec![Value::Bool(true)]);
        assert_eq!(count.get(), 0);
        assert_values(t.close().unwrap(), vec![Value::Bool(true)]);
        assert_eq!(count.get(), 1);
        assert_eq!(t.status(), "dead");
        assert!(isyieldable());
    }

    #[test]
    fn dropping_a_suspended_stack_unwinds_and_restores_parent_context() {
        let t = Thread::new(function(|_| {
            yield_values(vec![Value::Nil])?;
            Ok(vec![])
        }))
        .unwrap();
        assert_values(t.resume(vec![]), vec![Value::Bool(true), Value::Nil]);
        drop(t);
        assert!(ACTIVE.with(|a| a.borrow().is_empty()));
        assert!(isyieldable());
    }

    #[test]
    fn acyclic_threads_release_captures_on_completion_or_drop() {
        let captured = Rc::new(());
        let copied = captured.clone();
        let completed = Thread::new(function(move |_| {
            let _keep = &copied;
            Ok(vec![])
        }))
        .unwrap();
        assert_eq!(Rc::strong_count(&captured), 2);
        assert_values(completed.resume(vec![]), vec![Value::Bool(true)]);
        assert_eq!(Rc::strong_count(&captured), 1);
        let copied = captured.clone();
        let never_started = Thread::new(function(move |_| {
            let _keep = &copied;
            Ok(vec![])
        }))
        .unwrap();
        assert_eq!(Rc::strong_count(&captured), 2);
        drop(never_started);
        assert_eq!(Rc::strong_count(&captured), 1);
        let copied = captured.clone();
        let suspended = Thread::new(function(move |_| {
            let _keep = &copied;
            yield_values(vec![])?;
            Ok(vec![])
        }))
        .unwrap();
        suspended.resume(vec![]);
        assert_eq!(Rc::strong_count(&captured), 2);
        drop(suspended);
        assert_eq!(Rc::strong_count(&captured), 1);
    }

    #[test]
    fn boundaries_forbid_yields_but_nested_coroutines_are_yieldable() {
        assert!(isyieldable());
        non_yielding(|| {
            assert!(!isyieldable());
            assert_eq!(
                yield_values(vec![]).unwrap_err().msg.to_string_lossy(),
                "attempt to yield across metamethod/C-call boundary"
            );
            let child = Thread::new(function(|_| {
                assert!(isyieldable());
                yield_values(vec![s("child")])?;
                Ok(vec![])
            }))
            .unwrap();
            assert_values(child.resume(vec![]), vec![Value::Bool(true), s("child")]);
            assert!(!isyieldable());
            child.close().unwrap();
        });
        assert!(isyieldable());
    }

    #[test]
    fn nested_resume_distinguishes_running_and_normal_and_restores_parent() {
        let holder: Rc<RefCell<Option<Thread>>> = Rc::new(RefCell::new(None));
        let own = holder.clone();
        let parent = Thread::new(function(move |_| {
            let parent = own
                .borrow()
                .as_ref()
                .cloned()
                .ok_or_else(|| LuaError::new("missing parent"))?;
            assert_eq!(parent.status(), "running");
            assert_values(
                parent.resume(vec![]),
                vec![Value::Bool(false), s("cannot resume running coroutine")],
            );
            assert_eq!(
                parent.close().unwrap_err().msg.to_string_lossy(),
                "cannot close running coroutine"
            );
            let ancestor = own.clone();
            let child = Thread::new(function(move |_| {
                let parent = ancestor
                    .borrow()
                    .as_ref()
                    .cloned()
                    .ok_or_else(|| LuaError::new("missing parent"))?;
                assert_eq!(parent.status(), "normal");
                assert_values(
                    parent.resume(vec![]),
                    vec![Value::Bool(false), s("cannot resume normal coroutine")],
                );
                assert_eq!(
                    parent.close().unwrap_err().msg.to_string_lossy(),
                    "cannot close normal coroutine"
                );
                yield_values(vec![s("child")])?;
                Ok(vec![])
            }))?;
            assert_values(child.resume(vec![]), vec![Value::Bool(true), s("child")]);
            drop(child);
            assert_eq!(parent.status(), "running");
            yield_values(vec![s("parent")])?;
            Ok(vec![])
        }))
        .unwrap();
        *holder.borrow_mut() = Some(parent.clone());
        assert_values(parent.resume(vec![]), vec![Value::Bool(true), s("parent")]);
        assert_values(parent.resume(vec![]), vec![Value::Bool(true)]);
        *holder.borrow_mut() = None;
        assert!(ACTIVE.with(|a| a.borrow().is_empty()));
    }

    #[test]
    fn identity_and_dynamic_thread_tag_are_preserved() {
        let t = Thread::new(function(|_| Ok(vec![]))).unwrap();
        let a = t.clone().to_value();
        let b = t.clone().to_value();
        assert_eq!(a.type_name(), "thread");
        assert!(a.lua_eq(&b));
        assert_eq!(Thread::from_value(&a).unwrap().addr(), t.addr());
        assert!(Thread::from_value(&Value::Nil).is_none());
    }

    #[test]
    fn entry_yield_reaches_the_host_and_unwinds_without_a_lua_error() {
        let reached = Rc::new(Cell::new(false));
        let copied = reached.clone();
        let result = drive_entry(move || {
            assert!(isyieldable());
            yield_values(vec![s("main")])?;
            copied.set(true);
            Ok(())
        });
        assert!(matches!(result, Entry::Yielded));
        assert!(!reached.get());
        assert!(ACTIVE.with(|a| a.borrow().is_empty()));
        assert!(matches!(drive_entry(|| Ok(())), Entry::Returned(Ok(()))));
    }

    #[test]
    fn nested_entry_drop_preserves_its_parent_context() {
        let result = drive_entry(|| {
            let id = ACTIVE.with(|a| a.borrow().last().unwrap().id);
            assert!(matches!(
                drive_entry(|| {
                    yield_values(vec![])?;
                    Ok(())
                }),
                Entry::Yielded
            ));
            assert_eq!(ACTIVE.with(|a| a.borrow().last().unwrap().id), id);
            assert!(isyieldable());
            Ok(())
        });
        assert!(matches!(result, Entry::Returned(Ok(()))));
        assert!(ACTIVE.with(|a| a.borrow().is_empty()));
    }

    #[test]
    fn source_wrapper_abi_retains_nil_arity_and_identity() {
        let entry = function(|values| {
            let resumed = yield_values(values)?;
            Ok(resumed)
        });
        let wrapped = wrap_source_args(&[entry]).unwrap();
        let erased = crate::dynamic_fn::function(wrapped.clone());
        assert!(erased.lua_eq(&crate::dynamic_fn::function(wrapped.clone())));
        let first = wrapped
            .call((vec![None, Some(Value::Bool(false)), None],))
            .unwrap();
        assert_eq!(first.len(), 3);
        assert!(first[0].is_none() && first[2].is_none());
        assert!(matches!(first[1], Some(Value::Bool(false))));
        assert_values(
            crate::dynamic::call(&erased, vec![s("done"), Value::Nil]).unwrap(),
            vec![s("done"), Value::Nil],
        );
        assert_eq!(
            wrapped.call((vec![],)).unwrap_err().msg.to_string_lossy(),
            "cannot resume dead coroutine"
        );
    }

    #[test]
    fn source_argument_checks_distinguish_absence_from_nil() {
        assert_eq!(
            create_args(&[]).unwrap_err().msg.to_string_lossy(),
            "missing argument #1 to 'create' (function expected)"
        );
        assert_eq!(
            create_args(&[Value::Nil])
                .unwrap_err()
                .msg
                .to_string_lossy(),
            "invalid argument #1 to 'create' (function expected, got nil)"
        );
        assert_eq!(
            resume_args(vec![]).unwrap_err().msg.to_string_lossy(),
            "missing argument #1 to 'resume' (thread expected)"
        );
        assert_eq!(
            close_args(&[Value::Nil]).unwrap_err().msg.to_string_lossy(),
            "invalid argument #1 to 'close' (thread expected, got nil)"
        );
        assert_eq!(
            status_args(&[]).unwrap_err().msg.to_string_lossy(),
            "missing argument #1 to 'status' (thread expected)"
        );
    }

    #[test]
    fn erased_metamethod_boundary_blocks_only_that_invocation() {
        let callback = function(|_| yield_values(vec![s("yielded")]));
        let method = callback.clone();
        let blocked = Thread::new(function(move |_| {
            crate::dynamic::call_metamethod(&method, vec![])
        }))
        .unwrap();
        assert_values(
            blocked.resume(vec![]),
            vec![
                Value::Bool(false),
                s("attempt to yield across metamethod/C-call boundary"),
            ],
        );
        let regular =
            Thread::new(function(move |_| crate::dynamic::call(&callback, vec![]))).unwrap();
        assert_values(
            regular.resume(vec![]),
            vec![Value::Bool(true), s("yielded")],
        );
        assert_values(
            regular.resume(vec![Value::Nil]),
            vec![Value::Bool(true), Value::Nil],
        );
    }
}
