//! Managed heap: a cycle-tracking reference-counted collector (`dumpster`'s
//! thread-local `Gc`).
//!
//! * Acyclic objects are freed as soon as their last reference disappears, exactly
//!   as with `Rc`.
//! * Unreachable cycles are reclaimed by a collection. Collections run
//!   automatically (amortized, from `Gc` drops) and explicitly through
//!   [`collect`] (`collectgarbage("collect")` in source programs).
//! * Every managed object kind (tables, records, upvalue cells, closures, native
//!   handles) carries a [`Live`] token, so [`live_objects`] counts managed
//!   allocations independently of the collector's internals.
//!
//! Native objects are never traced. Managed values that native memory holds
//! (retained callbacks, pending native futures, view owners) are clones that act
//! as roots: a cycle through them is not collected.

use std::cell::Cell as StdCell;

pub use dumpster::unsync::Gc;
pub use dumpster;
pub use dumpster::{TraceWith, Visitor};

thread_local! {
    static LIVE: StdCell<usize> = const { StdCell::new(0) };
    static PEAK: StdCell<usize> = const { StdCell::new(0) };
    static COLLECTIONS: StdCell<usize> = const { StdCell::new(0) };
}

/// Allocation counter carried by every managed object (zero-sized).
pub struct Live(());

impl Live {
    #[inline]
    pub fn new() -> Live {
        LIVE.with(|l| {
            let n = l.get() + 1;
            l.set(n);
            PEAK.with(|p| {
                if n > p.get() {
                    p.set(n)
                }
            });
        });
        Live(())
    }
}

impl Default for Live {
    fn default() -> Self {
        Live::new()
    }
}

impl Clone for Live {
    /// A cloned object is a new allocation.
    fn clone(&self) -> Self {
        Live::new()
    }
}

impl Drop for Live {
    #[inline]
    fn drop(&mut self) {
        // `try_with`: thread-local destructors may already have run at thread exit.
        let _ = LIVE.try_with(|l| l.set(l.get().saturating_sub(1)));
    }
}

// SAFETY: `Live` contains no `Gc` pointers.
unsafe impl<V: Visitor> TraceWith<V> for Live {
    #[inline]
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

/// Number of managed objects currently allocated on this thread.
pub fn live_objects() -> usize {
    LIVE.with(|l| l.get())
}

/// Highest value [`live_objects`] has reached on this thread.
pub fn peak_objects() -> usize {
    PEAK.with(|p| p.get())
}

/// Number of explicit collections run on this thread.
pub fn collections() -> usize {
    COLLECTIONS.with(|c| c.get())
}

/// Initializes the collector before source execution creates any managed TLS roots.
///
/// A failed module initializer does not register its function-cache cleanup. The
/// collector must therefore outlive those caches during native TLS teardown too.
/// This empty startup collection does not count as a source-requested collection.
pub(crate) fn initialize() {
    dumpster::unsync::collect();
}

/// Reclaims every unreachable managed object (including cycles) on this thread.
///
/// Native destructors of reclaimed handles run here, on the owning thread. No
/// source code runs during a collection (the language has no finalizers), and a
/// collection never frees an object that is borrowed by an active call: such an
/// object is referenced from that call's frame and therefore reachable.
pub fn collect() {
    COLLECTIONS.with(|c| c.set(c.get() + 1));
    dumpster::unsync::collect();
}

#[cfg(test)]
mod tests {
    #[test]
    fn initialization_preserves_allocation_and_explicit_collection_counters() {
        std::thread::spawn(|| {
            let before = (super::live_objects(), super::peak_objects(), super::collections());
            assert_eq!(before, (0, 0, 0));
            super::initialize();
            super::initialize();
            assert_eq!((super::live_objects(), super::peak_objects(), super::collections()), before);
            super::collect();
            assert_eq!(super::collections(), 1);
        }).join().expect("fresh collector thread");
    }
}
