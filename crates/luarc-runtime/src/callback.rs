//! Source closures passed to native code as synchronous `Fn`/`FnMut` callbacks.
//!
//! A native function cannot return our `Result` from inside its own callback, so an
//! error raised by a source callback travels as a dedicated unwind payload through
//! the (Rust, unwind-compatible) native frames and is converted back into a
//! [`LuaError`] by the generated wrapper's [`guard`]. Any other panic is not
//! converted: it stays a fatal panic.

use std::cell::RefCell;
use std::panic::{self, AssertUnwindSafe};
use std::sync::Once;

use crate::error::{LResult, LuaError};

/// Unwind payload marking a language error raised inside a source callback. The
/// error itself (which holds non-`Send` `Rc` data) waits in a thread-local slot.
pub struct CallbackUnwind;

thread_local! {
    static PENDING: RefCell<Option<LuaError>> = const { RefCell::new(None) };
}

/// Called inside the Rust closure handed to native code.
#[inline]
pub fn unwrap_or_unwind<T>(r: LResult<T>) -> T {
    match r {
        Ok(v) => v,
        Err(e) => {
            PENDING.with(|p| *p.borrow_mut() = Some(e));
            panic::resume_unwind(Box::new(CallbackUnwind))
        }
    }
}

/// Runs a native call that received source callbacks; converts a callback error
/// payload back into a language error. Native state is left as the native code
/// left it (no rollback).
pub fn guard<T>(f: impl FnOnce() -> T) -> LResult<T> {
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(v) => Ok(v),
        Err(payload) => match payload.downcast::<CallbackUnwind>() {
            Ok(_) => Err(PENDING
                .with(|p| p.borrow_mut().take())
                .unwrap_or_else(|| LuaError::new("callback error lost while unwinding"))),
            Err(other) => panic::resume_unwind(other),
        },
    }
}

/// Keeps the default panic message for real panics while staying silent for the
/// callback payload (which `resume_unwind` does not report anyway).
pub fn install_panic_hook() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let default = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            if info.payload().downcast_ref::<CallbackUnwind>().is_none() {
                default(info);
            }
        }));
    });
}

/// Error channel of a native trait implemented by a source table, for methods
/// that cannot return an error to their native caller: the first source error is
/// stored, later callbacks are suppressed (the source state may be inconsistent),
/// and the native call that received the implementation reports the error when
/// it returns. No unwinding crosses the native code.
#[derive(Clone, Default)]
pub struct ErrorSlot(std::rc::Rc<RefCell<Option<LuaError>>>);

impl ErrorSlot {
    pub fn is_set(&self) -> bool {
        self.0.borrow().is_some()
    }
    /// Stores `e` unless an earlier error is already stored.
    pub fn set(&self, e: LuaError) {
        let mut s = self.0.borrow_mut();
        if s.is_none() {
            *s = Some(e);
        }
    }
    /// The stored error, reported at the owning call.
    pub fn take(&self) -> LResult<()> {
        match self.0.borrow_mut().take() {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }
}

/// Runs a source call inside a generated native callback (pins the error type).
#[inline]
pub fn protect<T>(f: impl FnOnce() -> LResult<T>) -> LResult<T> {
    // A synchronous native callback is a non-yielding C boundary in Luau.
    crate::coroutine::non_yielding(f)
}
