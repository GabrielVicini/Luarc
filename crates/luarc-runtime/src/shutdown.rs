//! Deterministic program shutdown.
//!
//! When the entry module finishes (normally or with an uncaught error), module
//! values are released in reverse initialization order, then a final collection
//! reclaims every remaining managed object, so native destructors (windows, GPU
//! resources, files) run on the owning thread before the process exits. The
//! process then exits explicitly, without relying on thread-local destructors.

use std::cell::RefCell;

thread_local! {
    static AT_EXIT: RefCell<Vec<fn()>> = const { RefCell::new(Vec::new()) };
}

/// Registers a release function (called by a module after its first initialization).
pub fn at_exit(f: fn()) {
    AT_EXIT.with(|a| a.borrow_mut().push(f));
}

/// Releases module values (last initialized first) and collects all cycles.
pub fn release_all() {
    loop {
        let next = AT_EXIT.with(|a| a.borrow_mut().pop());
        match next {
            Some(f) => f(),
            None => break,
        }
    }
    crate::gc::collect();
}
