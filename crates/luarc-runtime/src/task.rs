//! Cooperative tasks and native futures.
//!
//! * A **native future** (`impl Future` / `async fn` of an imported crate) is a
//!   first-class value [`Fut`]: it does nothing until a task awaits it, it can be
//!   awaited once (a second `await` is an error), and dropping it cancels it.
//! * A **task** (`task.spawn(function() ... end)`) is a source function lowered
//!   to a Rust future. Tasks run on the program's thread only (managed values
//!   never cross threads); they are polled by [`run_ready`] when woken.
//! * Wakers are ordinary `std::task::Waker`s (`Send + Sync`): waking marks the
//!   task ready, signals a condition variable and calls the optional wake hook
//!   (installed by an event loop integration, e.g. a winit `EventLoopProxy`), so a
//!   sleeping event loop or `wait_idle` resumes. Nothing spins.
//! * Executor independence: futures that need a specific runtime (a tokio
//!   reactor) are not supported by this executor; they typically panic when
//!   polled, which surfaces as a native panic at the `await`.

use std::cell::RefCell;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Condvar, Mutex};
use std::task::{Context, Poll, Wake, Waker};

use crate::error::{LResult, LuaError};

type BoxFut<R> = Pin<Box<dyn Future<Output = LResult<R>>>>;

// Native futures

/// A native computation producing `R` (already converted to source values).
pub struct Fut<R: 'static>(std::rc::Rc<RefCell<Option<BoxFut<R>>>>);

impl<R: 'static> Clone for Fut<R> {
    fn clone(&self) -> Self {
        Fut(self.0.clone())
    }
}

// SAFETY: a native future holds no managed pointers: wrappers convert native
// results into source values only when the future completes.
unsafe impl<V: crate::gc::Visitor, R: 'static> crate::gc::TraceWith<V> for Fut<R> {
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

impl<R: 'static> Fut<R> {
    pub fn new(f: impl Future<Output = LResult<R>> + 'static) -> Self {
        Fut(std::rc::Rc::new(RefCell::new(Some(Box::pin(f)))))
    }
    fn take(&self) -> LResult<BoxFut<R>> {
        self.0.borrow_mut().take().ok_or_else(|| LuaError::new("this future was already awaited (a future can be awaited once)"))
    }
}

/// `await(f)` inside a task.
pub async fn wait<R: 'static>(f: Fut<R>) -> LResult<R> {
    let fut = f.take()?;
    fut.await
}

// Executor

struct Ready {
    queue: Mutex<Vec<usize>>,
    cv: Condvar,
    hook: Mutex<Option<Arc<dyn Fn() + Send + Sync>>>,
}

impl Ready {
    fn push(&self, id: usize) {
        {
            let mut q = self.queue.lock().unwrap_or_else(|e| e.into_inner());
            if !q.contains(&id) {
                q.push(id);
            }
        }
        self.cv.notify_all();
        let hook = self.hook.lock().unwrap_or_else(|e| e.into_inner()).clone();
        if let Some(h) = hook {
            h();
        }
    }
}

struct TaskWaker {
    id: usize,
    ready: Arc<Ready>,
}

impl Wake for TaskWaker {
    fn wake(self: Arc<Self>) {
        self.ready.push(self.id);
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.ready.push(self.id);
    }
}

struct Slot {
    gen: u64,
    fut: Option<BoxFut<()>>,
    /// The task's future is being polled (it is temporarily out of the slot).
    running: bool,
    /// Cancelled while running: drop the future as soon as the poll returns.
    cancel_requested: bool,
    /// The waker given to the last poll. When the executor holds its only
    /// reference, nothing can wake the task any more.
    waker: Option<Arc<TaskWaker>>,
}

#[derive(Default)]
struct Exec {
    slots: Vec<Slot>,
    next_gen: u64,
    live: usize,
}

thread_local! {
    static POLLS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static EXEC: RefCell<Exec> = RefCell::new(Exec::default());
    static READY: Arc<Ready> = Arc::new(Ready { queue: Mutex::new(Vec::new()), cv: Condvar::new(), hook: Mutex::new(None) });
}

/// A spawned task (source value). Cancelling or finishing releases everything
/// the task's function retained.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Task {
    id: usize,
    gen: u64,
}

// SAFETY: a task id holds no managed pointers.
unsafe impl<V: crate::gc::Visitor> crate::gc::TraceWith<V> for Task {
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

impl crate::show::LuaDisplay for Task {
    fn fmt_lua(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(format!("task: {}", self.id).as_bytes())
    }
}

/// Starts a task; it first runs at the next [`run_ready`].
pub fn spawn(f: impl Future<Output = LResult<()>> + 'static) -> Task {
    let t = EXEC.with(|e| {
        let mut e = e.borrow_mut();
        e.next_gen += 1;
        let gen = e.next_gen;
        e.live += 1;
        let slot = Slot { gen, fut: Some(Box::pin(f)), running: false, cancel_requested: false, waker: None };
        match e.slots.iter().position(|s| s.fut.is_none() && !s.running) {
            Some(i) => {
                e.slots[i] = slot;
                Task { id: i, gen }
            }
            None => {
                e.slots.push(slot);
                Task { id: e.slots.len() - 1, gen }
            }
        }
    });
    READY.with(|r| r.push(t.id));
    t
}

/// Cancels a task: its future (and every value it retained) is dropped. Returns
/// whether the task was still pending.
pub fn cancel(t: Task) -> bool {
    let dropped = EXEC.with(|e| {
        let mut e = e.borrow_mut();
        let Some(s) = e.slots.get_mut(t.id) else { return None };
        if s.gen != t.gen {
            return None;
        }
        if s.running {
            s.cancel_requested = true;
            return Some(None);
        }
        let f = s.fut.take()?;
        e.live -= 1;
        Some(Some(f))
    });
    // dropped outside the executor borrow: destructors may touch the executor
    match dropped {
        Some(Some(f)) => {
            drop(f);
            true
        }
        Some(None) => true,
        None => false,
    }
}

/// Whether a task is still pending.
pub fn is_pending(t: Task) -> bool {
    EXEC.with(|e| e.borrow().slots.get(t.id).map(|s| s.gen == t.gen && (s.fut.is_some() || s.running)).unwrap_or(false))
}

/// Number of pending tasks.
pub fn pending() -> usize {
    EXEC.with(|e| e.borrow().live)
}

/// Polls every woken task once. A task's error is returned to the caller of
/// `run_ready` (the source boundary that drives the tasks); remaining ready
/// tasks stay queued.
pub fn run_ready() -> LResult<usize> {
    let ready = READY.with(|r| r.clone());
    let ids: Vec<usize> = std::mem::take(&mut *ready.queue.lock().unwrap_or_else(|e| e.into_inner()));
    let mut ran = 0;
    // wakeups of tasks being polled by an outer `run_ready` (this call is nested in
    // a task body): kept for the next round instead of being lost
    let mut busy = Vec::new();
    for (k, id) in ids.iter().enumerate() {
        let taken = EXEC.with(|e| {
            let mut e = e.borrow_mut();
            let s = e.slots.get_mut(*id)?;
            if s.running {
                busy.push(*id);
                return None;
            }
            let f = s.fut.take()?;
            s.running = true;
            Some((f, s.gen))
        });
        let Some((mut f, gen)) = taken else { continue };
        let tw = Arc::new(TaskWaker { id: *id, ready: ready.clone() });
        let waker = Waker::from(tw.clone());
        let mut cx = Context::from_waker(&waker);
        let r = f.as_mut().poll(&mut cx);
        drop(waker);
        ran += 1;
        POLLS.with(|p| p.set(p.get() + 1));
        let finished = !matches!(r, Poll::Pending);
        let to_drop = EXEC.with(|e| {
            let mut e = e.borrow_mut();
            let s = &mut e.slots[*id];
            s.running = false;
            if finished || s.cancel_requested || s.gen != gen {
                s.cancel_requested = false;
                e.live -= 1;
                Some(f)
            } else {
                s.fut = Some(f);
                s.waker = Some(tw);
                None
            }
        });
        drop(to_drop);
        if let Poll::Ready(Err(err)) = r {
            // requeue the ids not processed yet, then report
            let rest: Vec<usize> = ids[k + 1..].to_vec();
            let mut q = ready.queue.lock().unwrap_or_else(|e| e.into_inner());
            q.extend(busy);
            q.extend(rest);
            return Err(err);
        }
    }
    if !busy.is_empty() {
        ready.queue.lock().unwrap_or_else(|e| e.into_inner()).extend(busy);
    }
    Ok(ran)
}

/// Runs tasks until none is pending, sleeping (not spinning) while every
/// pending task waits for an external wakeup.
///
/// Errors instead of hanging: inside a task (it would wait for
/// itself), and when every pending task is waiting but no waker for any of them
/// exists any more (nothing can resume them).
pub fn wait_idle() -> LResult<()> {
    if EXEC.with(|e| e.borrow().slots.iter().any(|s| s.running)) {
        return Err(LuaError::new("task.wait_idle cannot be called inside a task (the task would wait for itself)"));
    }
    let ready = READY.with(|r| r.clone());
    while pending() > 0 {
        run_ready()?;
        if pending() == 0 {
            break;
        }
        let q = ready.queue.lock().unwrap_or_else(|e| e.into_inner());
        if q.is_empty() && stuck() {
            drop(q);
            let n = pending();
            return Err(LuaError::new(format!(
                "{n} pending task(s) can never resume: nothing holds a waker for them (a future that never wakes its task)"
            )));
        }
        if q.is_empty() {
            drop(ready.cv.wait_while(q, |q| q.is_empty()).unwrap_or_else(|e| e.into_inner()));
        }
    }
    Ok(())
}

/// Every pending task was polled and dropped its waker: no thread, timer or
/// native object can wake it (the executor holds the only reference).
fn stuck() -> bool {
    EXEC.with(|e| {
        let e = e.borrow();
        e.slots.iter().filter(|s| s.fut.is_some()).all(|s| s.waker.as_ref().map(|w| Arc::strong_count(w) == 1).unwrap_or(false))
    })
}

/// Installs the hook called (from any thread) whenever a task is woken: an event
/// loop integration uses it to wake the loop so it calls `run_ready`.
pub fn set_wake_hook(h: Option<Arc<dyn Fn() + Send + Sync>>) {
    READY.with(|r| *r.hook.lock().unwrap_or_else(|e| e.into_inner()) = h);
}

/// Drops every pending task (program shutdown).
pub fn cancel_all() {
    let futs: Vec<BoxFut<()>> = EXEC.with(|e| {
        let mut e = e.borrow_mut();
        e.live = 0;
        e.slots.iter_mut().filter_map(|s| s.fut.take()).collect()
    });
    drop(futs);
    set_wake_hook(None);
}

/// Number of task polls so far (tests use it to show the executor does not spin).
pub fn polls() -> u64 {
    POLLS.with(|p| p.get())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A task that wakes itself and then drives the executor from inside its own
    /// poll (`task.run_ready()` in a task body). Its wakeup must not be consumed
    /// by the nested call while the task is running.
    #[test]
    fn nested_run_ready_keeps_running_task_wakeup() {
        struct SelfWake(u32);
        impl Future for SelfWake {
            type Output = LResult<()>;
            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<LResult<()>> {
                self.0 += 1;
                if self.0 > 1 {
                    return Poll::Ready(Ok(()));
                }
                cx.waker().wake_by_ref();
                run_ready().unwrap();
                Poll::Pending
            }
        }
        spawn(SelfWake(0));
        assert_eq!(run_ready().unwrap(), 1);
        assert_eq!(pending(), 1);
        // the self-wake is still queued: the task completes on the next round
        assert_eq!(run_ready().unwrap(), 1);
        assert_eq!(pending(), 0);
    }

    /// Reject waits that cannot make progress instead of hanging.
    #[test]
    fn wait_idle_reports_deadlocks() {
        // a future that never wakes its task
        spawn(async { std::future::pending::<LResult<()>>().await });
        let e = wait_idle().unwrap_err();
        assert!(e.msg.to_string_lossy().contains("can never resume"), "{}", e.msg.to_string_lossy());
        cancel_all();
        // wait_idle from inside a task
        let seen = std::rc::Rc::new(std::cell::RefCell::new(None));
        let s2 = seen.clone();
        spawn(async move {
            *s2.borrow_mut() = Some(wait_idle().is_err());
            Ok(())
        });
        wait_idle().unwrap();
        assert_eq!(*seen.borrow(), Some(true));
        // a task woken later by another thread is not a deadlock
        let (tx, rx) = std::sync::mpsc::channel::<Waker>();
        let h = std::thread::spawn(move || {
            let w = rx.recv().unwrap();
            std::thread::sleep(std::time::Duration::from_millis(20));
            w.wake();
        });
        let mut sent = Some(tx);
        spawn(std::future::poll_fn(move |cx| match sent.take() {
            Some(tx) => {
                tx.send(cx.waker().clone()).unwrap();
                Poll::Pending
            }
            None => Poll::Ready(Ok(())),
        }));
        wait_idle().unwrap();
        h.join().unwrap();
    }
}
