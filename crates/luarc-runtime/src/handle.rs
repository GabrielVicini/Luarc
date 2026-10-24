//! Managed handles for native Rust objects.
//!
//! A handle is a managed pointer shared by every source alias; assignment copies
//! the handle, never the native value. A handle is either
//!
//! * **owned**: it holds the native value in an explicit state machine
//!   (live → consumed | closed). Access is a checked `RefCell` borrow held only
//!   for one native call, so reentrant conflicting access becomes a language
//!   error instead of a borrow panic. Every alias observes a transition.
//! * a **view**: a borrowed projection into another handle (a public field, an
//!   enum payload, a `&T` result). A view retains its owner, re-projects on every
//!   access and is valid only while the owner is unchanged: each exclusive access,
//!   consumption or close of the owner advances the owner's *generation*, and a
//!   view created at an older generation raises a language error instead of
//!   observing a mutated, moved or freed value. No raw pointers are kept.
//!
//! Native values are not traced (they cannot contain managed pointers); the
//! owners a handle retains are.

use std::cell::{Cell as StdCell, Ref, RefCell, RefMut};



use dumpster::Trace;

use crate::error::{LResult, LuaError};
use crate::gc::{Gc, Live, TraceWith, Visitor};

pub enum HState<T> {
    Live(T),
    Consumed(&'static str),
    Closed,
}

/// Per-type behaviour of a handle (formatting and equality).
pub struct HandleMeta<T: 'static> {
    pub type_name: &'static str,
    pub show: fn(&T, &mut Vec<u8>),
    /// `Some(a == b)` when the type implements `PartialEq`, `None` otherwise.
    pub eq: fn(&T, &T) -> Option<bool>,
}

/// Shared access to a handle's value: a shared borrow, or (for a view whose native
/// accessor takes `&mut self`) an exclusive borrow of its owner.
pub enum HRef<'a, T> {
    Shared(Ref<'a, T>),
    Excl(HMut<'a, T>),
    /// A lent value (see [`lend`]): the reference plus the shared borrow flag.
    Lent(&'a T, Ref<'a, ()>),
}

impl<T> std::ops::Deref for HRef<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        match self {
            HRef::Shared(r) => r,
            HRef::Excl(r) => r,
            HRef::Lent(r, _) => r,
        }
    }
}

/// Exclusive access to a handle's value.
pub enum HMut<'a, T> {
    Cell(RefMut<'a, T>),
    /// A mutably lent value: the reference plus the exclusive borrow flag.
    Lent(&'a mut T, RefMut<'a, ()>),
}

impl<T> std::ops::Deref for HMut<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        match self {
            HMut::Cell(r) => r,
            HMut::Lent(r, _) => r,
        }
    }
}

impl<T> std::ops::DerefMut for HMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        match self {
            HMut::Cell(r) => r,
            HMut::Lent(r, _) => r,
        }
    }
}

impl<'a, T> HMut<'a, T> {
    /// Projects to a part (`None`: absent), keeping the borrow.
    pub fn filter_map<U>(self, f: impl FnOnce(&mut T) -> Option<&mut U>) -> Result<HMut<'a, U>, ()> {
        match self {
            HMut::Cell(r) => RefMut::filter_map(r, f).map(HMut::Cell).map_err(|_| ()),
            HMut::Lent(p, g) => f(p).map(|u| HMut::Lent(u, g)).ok_or(()),
        }
    }
}

/// A projection from an owner handle to a borrowed part of it.
pub trait Project<T: 'static> {
    fn get(&self) -> LResult<HRef<'_, T>>;
    fn get_mut(&self) -> LResult<HMut<'_, T>>;
    /// Moves the projected value out (consumes the owner).
    fn take(&self, method: &'static str) -> LResult<T>;
    fn generation(&self) -> u64;
    fn is_live(&self) -> bool;
}

enum Kind<T: 'static> {
    Owned { state: RefCell<HState<T>>, gen: StdCell<u64> },
    /// `owner` is the projected handle, kept here so the collector traces it.
    View { proj: Box<dyn Project<T>>, owner: Gc<dyn Owner> },
    /// A value lent by native code for the duration of a callback (see [`lend`]).
    Lent { ptr: *mut T, mutable: bool, live: StdCell<bool>, flag: RefCell<()> },
}

pub struct HandleBox<T: 'static> {
    _live: Live,
    kind: Kind<T>,
    meta: &'static HandleMeta<T>,
    /// Objects kept alive for as long as this handle lives (owner retention).
    owners: Vec<Gc<dyn Owner>>,
    /// Set while a dependent native object borrows this one (an open
    /// `RenderPass` locks its `CommandEncoder`): every access is refused.
    lock: std::rc::Rc<StdCell<Option<&'static str>>>,
    /// The lock this object holds on another one (released when this object's
    /// native value is dropped, closed or consumed).
    unlock: Option<std::rc::Rc<StdCell<Option<&'static str>>>>,
}

impl<T: 'static> HandleBox<T> {
    fn release_lock(&self) {
        if let Some(l) = &self.unlock {
            l.set(None);
        }
    }
}

impl<T: 'static> Drop for HandleBox<T> {
    fn drop(&mut self) {
        // the native value goes first (a render pass ends), then the lock it held
        if let Kind::Owned { state, .. } = &mut self.kind {
            let old = std::mem::replace(state.get_mut(), HState::Closed);
            drop(old);
        }
        self.release_lock();
    }
}

/// Type-erased handle used to retain an owner.
pub trait Owner: Trace {
    /// The object is (or is a view of) a reference lent to a running callback.
    fn lent(&self) -> bool;
}
impl<T: 'static> Owner for HandleBox<T> {
    fn lent(&self) -> bool {
        match &self.kind {
            Kind::Lent { .. } => true,
            Kind::View { owner, .. } => owner.lent(),
            Kind::Owned { .. } => false,
        }
    }
}

// SAFETY: the native value is not traced: native memory never contains managed
// pointers (source callbacks retained by native code go through the registry,
// which roots them explicitly). Owners and view sources are traced.
unsafe impl<V: Visitor, T: 'static> TraceWith<V> for HandleBox<T> {
    fn accept(&self, v: &mut V) -> Result<(), ()> {
        for o in &self.owners {
            o.accept(v)?;
        }
        if let Kind::View { owner, .. } = &self.kind {
            owner.accept(v)?;
        }
        Ok(())
    }
}

pub struct Handle<T: 'static>(Gc<HandleBox<T>>);

impl<T: 'static> Clone for Handle<T> {
    fn clone(&self) -> Self {
        Handle(self.0.clone())
    }
}

// SAFETY: visits the handle's only managed pointer.
unsafe impl<V: Visitor, T: 'static> TraceWith<V> for Handle<T> {
    #[inline]
    fn accept(&self, v: &mut V) -> Result<(), ()> {
        self.0.accept(v)
    }
}

impl<T: 'static> Handle<T> {
    pub fn new(v: T, meta: &'static HandleMeta<T>) -> Self {
        Self::with_owners(v, meta, Vec::new())
    }

    /// Like [`Handle::new`] but retains `owner` until this handle is released.
    pub fn with_owner(v: T, meta: &'static HandleMeta<T>, owner: Gc<dyn Owner>) -> Self {
        Self::with_owners(v, meta, vec![owner])
    }

    fn with_owners(v: T, meta: &'static HandleMeta<T>, owners: Vec<Gc<dyn Owner>>) -> Self {
        Handle(Gc::new(HandleBox {
            _live: Live::new(),
            kind: Kind::Owned { state: RefCell::new(HState::Live(v)), gen: StdCell::new(0) },
            meta,
            owners,
            lock: Default::default(),
            unlock: None,
        }))
    }

    /// A view projecting into `owner` (see [`ViewOf`]).
    pub fn view<O: 'static>(
        owner: &Handle<O>,
        what: &'static str,
        get: for<'a> fn(&'a O) -> Option<&'a T>,
        get_mut: Option<for<'a> fn(&'a mut O) -> Option<&'a mut T>>,
        take: Option<ProjMove<O, T>>,
        meta: &'static HandleMeta<T>,
    ) -> Self {
        let get: ProjRef<O, T> = Box::new(get);
        let get_mut: Option<ProjMut<O, T>> = get_mut.map(|f| Box::new(f) as ProjMut<O, T>);
        Self::view_with(owner, what, Some(get), get_mut, take, meta)
    }

    /// A view whose projections are closures (a method's borrowed result: the
    /// accessor is re-applied, with its captured arguments, on every use).
    pub fn view_with<O: 'static>(
        owner: &Handle<O>,
        what: &'static str,
        get: Option<ProjRef<O, T>>,
        get_mut: Option<ProjMut<O, T>>,
        take: Option<ProjMove<O, T>>,
        meta: &'static HandleMeta<T>,
    ) -> Self {
        let proj: Box<dyn Project<T>> =
            Box::new(ViewOf { owner: owner.clone(), gen: StdCell::new(owner.generation()), what, get, get_mut, take });
        Handle(Gc::new(HandleBox {
            _live: Live::new(),
            kind: Kind::View { proj, owner: owner.as_owner() },
            meta,
            owners: Vec::new(),
            lock: Default::default(),
            unlock: None,
        }))
    }

    pub fn type_name(&self) -> &'static str {
        self.0.meta.type_name
    }

    pub fn is_view(&self) -> bool {
        matches!(self.0.kind, Kind::View { .. })
    }

    fn terminal_error(&self, s: &HState<T>) -> LuaError {
        match s {
            HState::Consumed(m) => LuaError::new(format!(
                "{} object was consumed by '{}' and can no longer be used",
                self.0.meta.type_name, m
            )),
            HState::Closed => LuaError::new(format!("{} object has been closed", self.0.meta.type_name)),
            HState::Live(_) => unreachable!(),
        }
    }

    fn in_use(&self) -> LuaError {
        LuaError::new(format!(
            "{} object is already in use by an active native call (reentrant access from a callback)",
            self.0.meta.type_name
        ))
    }

    /// Current generation: advances on every exclusive access, consumption and close.
    pub fn generation(&self) -> u64 {
        match &self.0.kind {
            Kind::Owned { gen, .. } => gen.get(),
            Kind::View { proj: p, .. } => p.generation(),
            Kind::Lent { .. } => 0,
        }
    }

    /// Shared access for `&self` methods and `&T` arguments.
    pub fn get(&self) -> LResult<HRef<'_, T>> {
        self.check_lock()?;
        match &self.0.kind {
            Kind::Owned { state, .. } => {
                let r = state.try_borrow().map_err(|_| self.in_use())?;
                Ref::filter_map(r, |s| match s {
                    HState::Live(v) => Some(v),
                    _ => None,
                })
                .map(HRef::Shared)
                .map_err(|r| self.terminal_error(&r))
            }
            Kind::View { proj: p, .. } => p.get(),
            Kind::Lent { ptr, live, flag, .. } => {
                if !live.get() {
                    return Err(self.expired());
                }
                let g = flag.try_borrow().map_err(|_| self.in_use())?;
                // SAFETY: `live` is true only inside the `lend` scope, while the
                // reference this pointer came from is alive; the flag tracks the
                // shared/exclusive borrows made through this handle, and `lend`
                // verifies none is outstanding when the scope ends.
                Ok(HRef::Lent(unsafe { &**ptr }, g))
            }
        }
    }

    /// Exclusive access for `&mut self` methods and `&mut T` arguments. Invalidates
    /// views of this object.
    pub fn get_mut(&self) -> LResult<HMut<'_, T>> {
        self.check_lock()?;
        match &self.0.kind {
            Kind::Owned { state, gen } => {
                let r = state.try_borrow_mut().map_err(|_| self.in_use())?;
                let r = RefMut::filter_map(r, |s| match s {
                    HState::Live(v) => Some(v),
                    _ => None,
                })
                .map_err(|r| self.terminal_error(&r))?;
                gen.set(gen.get() + 1);
                Ok(HMut::Cell(r))
            }
            Kind::View { proj: p, .. } => p.get_mut(),
            Kind::Lent { ptr, mutable, live, flag } => {
                if !live.get() {
                    return Err(self.expired());
                }
                if !*mutable {
                    return Err(LuaError::new(format!(
                        "{} was lent as a shared reference and cannot be mutated",
                        self.0.meta.type_name
                    )));
                }
                let g = flag.try_borrow_mut().map_err(|_| self.in_use())?;
                // SAFETY: as in `get`; the exclusive flag borrow guarantees this is
                // the only reference derived from the pointer, and the lender
                // passed a `&mut T`.
                Ok(HMut::Lent(unsafe { &mut **ptr }, g))
            }
        }
    }

    fn check_lock(&self) -> LResult<()> {
        match self.0.lock.get() {
            None => Ok(()),
            Some(by) => Err(LuaError::new(format!(
                "{} is locked by an open {by}; finish or close the {by} first",
                self.0.meta.type_name
            ))),
        }
    }

    /// Locks this object while a dependent native object borrows it.
    pub fn lock_by(&self, by: &'static str) -> LResult<()> {
        self.check_lock()?;
        self.0.lock.set(Some(by));
        Ok(())
    }

    /// A handle for `v` that locks `owner` until `v` is dropped, closed or
    /// consumed (an open render pass locks its encoder).
    pub fn new_locking<O: 'static>(v: T, meta: &'static HandleMeta<T>, owner: &Handle<O>, by: &'static str) -> LResult<Self> {
        owner.lock_by(by)?;
        Ok(Handle(Gc::new(HandleBox {
            _live: Live::new(),
            kind: Kind::Owned { state: RefCell::new(HState::Live(v)), gen: StdCell::new(0) },
            meta,
            owners: Vec::new(),
            lock: Default::default(),
            unlock: Some(owner.0.lock.clone()),
        })))
    }

    /// Ends a lock taken with [`Handle::lock_by`].
    pub fn unlock(&self) {
        self.0.lock.set(None);
    }

    fn expired(&self) -> LuaError {
        LuaError::new(format!(
            "{} was lent to a callback and is only valid while that callback runs",
            self.0.meta.type_name
        ))
    }

    /// Moves the native value out for a consuming (`self`) method; every alias then
    /// observes the consumed state.
    pub fn take(&self, method: &'static str) -> LResult<T> {
        self.check_lock()?;
        match &self.0.kind {
            Kind::Owned { state, gen } => {
                let mut r = state.try_borrow_mut().map_err(|_| self.in_use())?;
                match std::mem::replace(&mut *r, HState::Consumed(method)) {
                    HState::Live(v) => {
                        gen.set(gen.get() + 1);
                        self.0.release_lock();
                        Ok(v)
                    }
                    other => {
                        let e = self.terminal_error(&other);
                        *r = other;
                        Err(e)
                    }
                }
            }
            Kind::View { proj: p, .. } => p.take(method),
            Kind::Lent { .. } => Err(LuaError::new(format!(
                "'{method}' needs to own {}, but it is only lent to this callback",
                self.0.meta.type_name
            ))),
        }
    }

    /// Deterministic release: drops the native value now. Closing twice is allowed.
    pub fn close(&self) -> LResult<()> {
        self.check_lock()?;
        let Kind::Owned { state, gen } = &self.0.kind else {
            return Err(LuaError::new(format!(
                "{} is a borrowed view; close the object that owns it",
                self.0.meta.type_name
            )));
        };
        let old = {
            let mut r = state.try_borrow_mut().map_err(|_| self.in_use())?;
            match &*r {
                HState::Live(_) => std::mem::replace(&mut *r, HState::Closed),
                _ => return Ok(()),
            }
        };
        gen.set(gen.get() + 1);
        drop(old); // runs the native destructor outside the borrow
        self.0.release_lock();
        Ok(())
    }

    pub fn is_live(&self) -> bool {
        match &self.0.kind {
            Kind::Owned { state, .. } => matches!(state.try_borrow().as_deref(), Ok(HState::Live(_)) | Err(_)),
            Kind::View { proj: p, .. } => p.is_live(),
            Kind::Lent { live, .. } => live.get(),
        }
    }

    pub fn ptr_eq(&self, o: &Self) -> bool {
        Gc::ptr_eq(&self.0, &o.0)
    }

    pub fn addr(&self) -> usize {
        Gc::as_ptr(&self.0) as *const u8 as usize
    }

    /// Value equality when the native type implements `PartialEq`, identity otherwise.
    pub fn native_eq(&self, o: &Self) -> bool {
        if self.ptr_eq(o) {
            return true;
        }
        match (self.get(), o.get()) {
            (Ok(a), Ok(b)) => (self.0.meta.eq)(&a, &b) == Some(true),
            _ => false,
        }
    }

    /// Type-erased strong reference, used for owner retention.
    pub fn as_owner(&self) -> Gc<dyn Owner> {
        let g: Gc<HandleBox<T>> = self.0.clone();
        dumpster::unsync::coerce_gc!(g)
    }

    pub fn fmt_native(&self, out: &mut Vec<u8>) {
        let name = self.0.meta.type_name;
        match &self.0.kind {
            Kind::Owned { state, .. } => match state.try_borrow() {
                Ok(s) => match &*s {
                    HState::Live(v) => (self.0.meta.show)(v, out),
                    HState::Consumed(m) => out.extend_from_slice(format!("{name} (consumed by {m})").as_bytes()),
                    HState::Closed => out.extend_from_slice(format!("{name} (closed)").as_bytes()),
                },
                Err(_) => out.extend_from_slice(format!("{name} (in use)").as_bytes()),
            },
            Kind::View { proj: p, .. } => match p.get() {
                Ok(v) => (self.0.meta.show)(&v, out),
                Err(e) => out.extend_from_slice(format!("{name} (invalid view: {})", e.msg.to_string_lossy()).as_bytes()),
            },
            Kind::Lent { .. } => match self.get() {
                Ok(v) => (self.0.meta.show)(&v, out),
                Err(_) => out.extend_from_slice(format!("{name} (expired loan)").as_bytes()),
            },
        }
    }

    /// Number of live source references to this handle (diagnostics/tests).
    pub fn ref_count(&self) -> usize {
        Gc::ref_count(&self.0).get()
    }
}

// Views

/// Shared projection `&O -> Option<&T>` (`None`: the part is absent, e.g. another
/// enum variant).
pub type ProjRef<O, T> = Box<dyn for<'a> Fn(&'a O) -> Option<&'a T>>;
/// Exclusive projection.
pub type ProjMut<O, T> = Box<dyn for<'a> Fn(&'a mut O) -> Option<&'a mut T>>;
/// Moving projection (consumes the owner value).
pub type ProjMove<O, T> = fn(O) -> Option<T>;

/// A view into handle `O`, valid while the owner's generation is unchanged.
pub struct ViewOf<O: 'static, T: 'static> {
    owner: Handle<O>,
    gen: StdCell<u64>,
    what: &'static str,
    /// None: the native accessor needs `&mut` (reads borrow the owner exclusively).
    get: Option<ProjRef<O, T>>,
    get_mut: Option<ProjMut<O, T>>,
    take: Option<ProjMove<O, T>>,
}

impl<O: 'static, T: 'static> ViewOf<O, T> {
    fn check(&self) -> LResult<()> {
        if self.owner.generation() != self.gen.get() {
            return Err(LuaError::new(format!(
                "borrowed view '{}' of {} is no longer valid: its owner was mutated, consumed or closed after the view was created",
                self.what,
                self.owner.type_name()
            )));
        }
        Ok(())
    }

    fn absent(&self) -> LuaError {
        LuaError::new(format!("borrowed view '{}' of {} does not refer to a value", self.what, self.owner.type_name()))
    }
}

impl<O: 'static, T: 'static> Project<T> for ViewOf<O, T> {
    fn get(&self) -> LResult<HRef<'_, T>> {
        self.check()?;
        let Some(proj) = &self.get else {
            // an exclusive accessor (`fn child_mut(&mut self) -> &mut T`): reading
            // borrows the owner exclusively, as the native call does
            return self.get_mut().map(HRef::Excl);
        };
        match self.owner.get()? {
            HRef::Shared(r) => Ref::filter_map(r, |o| proj(o)).map(HRef::Shared).map_err(|_| self.absent()),
            HRef::Lent(r, g) => match proj(r) {
                Some(x) => Ok(HRef::Lent(x, g)),
                None => Err(self.absent()),
            },
            HRef::Excl(r) => match &self.get_mut {
                Some(pm) => r.filter_map(|o| pm(o)).map(HRef::Excl).map_err(|_| self.absent()),
                None => Err(LuaError::new(format!(
                    "borrowed view '{}' cannot be read while its owner is exclusively borrowed",
                    self.what
                ))),
            },
        }
    }

    fn get_mut(&self) -> LResult<HMut<'_, T>> {
        self.check()?;
        let Some(proj) = &self.get_mut else {
            return Err(LuaError::new(format!(
                "borrowed view '{}' of {} is read-only (the native API lends it as a shared reference)",
                self.what,
                self.owner.type_name()
            )));
        };
        let r = self.owner.get_mut()?;
        // Mutating through this view keeps it valid and invalidates all others.
        self.gen.set(self.owner.generation());
        r.filter_map(|o| proj(o)).map_err(|_| self.absent())
    }

    fn take(&self, method: &'static str) -> LResult<T> {
        self.check()?;
        let Some(proj) = self.take else {
            return Err(LuaError::new(format!(
                "'{method}' needs to own '{}', but it is borrowed from {}",
                self.what,
                self.owner.type_name()
            )));
        };
        // Probe first so a mismatch does not consume the owner.
        if self.get().is_err() {
            return Err(self.absent());
        }
        let o = self.owner.take(method)?;
        proj(o).ok_or_else(|| self.absent())
    }

    fn generation(&self) -> u64 {
        self.owner.generation()
    }

    fn is_live(&self) -> bool {
        self.check().is_ok() && self.owner.is_live()
    }
}

/// Fallback formatter for native types without `Display`/`Debug`.
pub fn show_opaque<T>(v: &T, out: &mut Vec<u8>) {
    out.extend_from_slice(format!("userdata: 0x{:012x}", v as *const T as usize).as_bytes());
}

// Formatting and equality chosen per concrete native type (autoref dispatch):
// `Display` if implemented, else `Debug`, else an opaque address; `PartialEq`
// if implemented, else identity.

pub struct ShowProbe<'a, T>(pub &'a T);

pub trait ShowViaDisplay {
    fn show_into(&self, out: &mut Vec<u8>);
}
impl<T: std::fmt::Display> ShowViaDisplay for &&ShowProbe<'_, T> {
    fn show_into(&self, out: &mut Vec<u8>) {
        use std::io::Write;
        let _ = write!(out, "{}", self.0);
    }
}
pub trait ShowViaDebug {
    fn show_into(&self, out: &mut Vec<u8>);
}
impl<T: std::fmt::Debug> ShowViaDebug for &ShowProbe<'_, T> {
    fn show_into(&self, out: &mut Vec<u8>) {
        use std::io::Write;
        let _ = write!(out, "{:?}", self.0);
    }
}
pub trait ShowOpaque {
    fn show_into(&self, out: &mut Vec<u8>);
}
impl<T> ShowOpaque for ShowProbe<'_, T> {
    fn show_into(&self, out: &mut Vec<u8>) {
        show_opaque(self.0, out)
    }
}

/// `lr::show_native!(value_ref, out)`.
#[macro_export]
macro_rules! show_native {
    ($v:expr, $out:expr) => {{
        #[allow(unused_imports)]
        use $crate::handle::{ShowOpaque as _, ShowViaDebug as _, ShowViaDisplay as _};
        (&&&$crate::handle::ShowProbe($v)).show_into($out)
    }};
}

pub struct EqProbe<'a, T>(pub &'a T, pub &'a T);

pub trait EqViaPartialEq {
    fn native_eq(&self) -> Option<bool>;
}
impl<T: PartialEq> EqViaPartialEq for &EqProbe<'_, T> {
    fn native_eq(&self) -> Option<bool> {
        Some(self.0 == self.1)
    }
}
pub trait EqNone {
    fn native_eq(&self) -> Option<bool>;
}
impl<T> EqNone for EqProbe<'_, T> {
    fn native_eq(&self) -> Option<bool> {
        None
    }
}

/// `lr::eq_native!(a_ref, b_ref)`: `Some(a == b)` or `None` without `PartialEq`.
#[macro_export]
macro_rules! eq_native {
    ($a:expr, $b:expr) => {{
        #[allow(unused_imports)]
        use $crate::handle::{EqNone as _, EqViaPartialEq as _};
        (&&$crate::handle::EqProbe($a, $b)).native_eq()
    }};
}

/// Checks that every handle a call will consume can be consumed (live, not
/// borrowed, not passed twice), so a call never consumes some of its arguments
/// and then fails on another.
pub fn check_consumable(hs: &[(&dyn Consumable, &'static str)]) -> LResult<()> {
    for (i, (h, what)) in hs.iter().enumerate() {
        h.consumable(what)?;
        for (o, _) in &hs[..i] {
            if h.identity() == o.identity() {
                return Err(LuaError::new(format!("the same object is passed twice to '{what}', which consumes it")));
            }
        }
    }
    Ok(())
}

pub trait Consumable {
    fn consumable(&self, what: &'static str) -> LResult<()>;
    fn identity(&self) -> usize;
}

impl<T: 'static> Consumable for Handle<T> {
    fn consumable(&self, what: &'static str) -> LResult<()> {
        self.check_lock()?;
        match &self.0.kind {
            Kind::Owned { state, .. } => match state.try_borrow_mut() {
                Err(_) => Err(self.in_use()),
                Ok(s) => match &*s {
                    HState::Live(_) => Ok(()),
                    other => Err(self.terminal_error(other)),
                },
            },
            Kind::View { proj, .. } => {
                let _ = what;
                self.check_lock()?;
                proj.get().map(|_| ())
            }
            Kind::Lent { .. } => Err(LuaError::new(format!("{} is only lent to this callback and cannot be consumed", self.0.meta.type_name))),
        }
    }
    fn identity(&self) -> usize {
        self.addr()
    }
}

impl<T: 'static> Consumable for &Handle<T> {
    fn consumable(&self, what: &'static str) -> LResult<()> {
        (**self).consumable(what)
    }
    fn identity(&self) -> usize {
        (**self).identity()
    }
}

/// Scope guard of a `local x <close> = ...` variable: closes the handle (drops
/// the native value) when the scope exits by any path — fallthrough, `break`,
/// `return` or an error. Variables close in reverse declaration order (Rust drop
/// order), like Lua's to-be-closed variables. A handle already consumed or closed
/// is left as it is.
pub struct CloseOnExit<T: 'static>(Option<Handle<T>>);

impl<T: 'static> CloseOnExit<T> {
    pub fn new(h: &Handle<T>) -> Self {
        CloseOnExit(Some(h.clone()))
    }
    pub fn opt(h: &Option<Handle<T>>) -> Self {
        CloseOnExit(h.clone())
    }
}

impl<T: 'static> Drop for CloseOnExit<T> {
    fn drop(&mut self) {
        if let Some(h) = self.0.take() {
            // in use: an active native call holds it (cannot happen at scope exit
            // of straight-line code); views cannot be closed: nothing to release
            let _ = h.close();
        }
    }
}

/// A shared projection closure (the signature is fixed by this function, so the
/// closure's lifetimes are inferred as higher-ranked).
pub fn proj_ref<O: 'static, T: 'static>(f: impl for<'a> Fn(&'a O) -> Option<&'a T> + 'static) -> ProjRef<O, T> {
    Box::new(f)
}

/// An exclusive projection closure.
pub fn proj_mut<O: 'static, T: 'static>(f: impl for<'a> Fn(&'a mut O) -> Option<&'a mut T> + 'static) -> ProjMut<O, T> {
    Box::new(f)
}

// Lending: `&T` / `&mut T` arguments of callbacks

/// Ends a loan when the callback scope exits (normally or by unwinding).
struct EndLoan<'h, T: 'static>(&'h Handle<T>);

impl<T: 'static> Drop for EndLoan<'_, T> {
    fn drop(&mut self) {
        if let Kind::Lent { live, flag, .. } = &self.0 .0.kind {
            // Every borrow made through the handle is a guard local to one
            // wrapper call inside the callback, so none can be outstanding here.
            // If one were, ending the loan would leave a dangling reference:
            // abort instead of continuing.
            if flag.try_borrow_mut().is_err() {
                eprintln!("luarc: internal error: a lent native reference outlived its callback");
                std::process::abort();
            }
            live.set(false);
        }
    }
}

impl<T: 'static> Handle<T> {
    fn lent(ptr: *mut T, mutable: bool, meta: &'static HandleMeta<T>) -> Self {
        Handle(Gc::new(HandleBox {
            _live: Live::new(),
            kind: Kind::Lent { ptr, mutable, live: StdCell::new(true), flag: RefCell::new(()) },
            meta,
            owners: Vec::new(),
            lock: Default::default(),
            unlock: None,
        }))
    }
}

/// Lends `r` to source code for the duration of `f`: the handle passed to `f`
/// reaches `r` only while `f` runs. Afterwards (a source closure kept the handle)
/// every access raises "only valid while that callback runs". This is the one
/// place a raw pointer is kept; the invariants are documented on `Kind::Lent`
/// accessors and enforced by `EndLoan`.
pub fn lend<T: 'static, R>(r: &T, meta: &'static HandleMeta<T>, f: impl FnOnce(&Handle<T>) -> R) -> R {
    let h = Handle::lent(r as *const T as *mut T, false, meta);
    let _end = EndLoan(&h);
    f(&h)
}

/// Lends `r` mutably for the duration of `f` (see [`lend`]).
pub fn lend_mut<T: 'static, R>(r: &mut T, meta: &'static HandleMeta<T>, f: impl FnOnce(&Handle<T>) -> R) -> R {
    let h = Handle::lent(r as *mut T, true, meta);
    let _end = EndLoan(&h);
    f(&h)
}

impl<T: 'static> Handle<std::sync::Arc<T>> {
    /// A by-value argument moves the object out of its `Arc`, which is only
    /// possible while no native object shares it. Checked before any argument of
    /// the call is consumed, so a refused call consumes nothing.
    /// Race-free: with a strong count of 1 and no weak references, no other thread
    /// can create a new reference before the take.
    pub fn check_unshared(&self, what: &'static str) -> LResult<()> {
        let r = self.get()?;
        if std::sync::Arc::strong_count(&r) == 1 && std::sync::Arc::weak_count(&r) == 0 {
            Ok(())
        } else {
            Err(LuaError::new(format!(
                "{what} object is shared with native code and cannot be moved (it is still in use by another native object)"
            )))
        }
    }
}

impl<T: 'static> Handle<T> {
    /// A native future borrows its receiver and arguments until it completes.
    /// Reject lent objects when creating the future because their callback loan
    /// may end before the future releases its borrow.
    pub fn check_not_lent(&self, what: &'static str) -> LResult<()> {
        if self.0.lent() {
            Err(LuaError::new(format!(
                "'{what}' returns a future that borrows {}, which is only lent to the running callback; the future could outlive the loan",
                self.0.meta.type_name
            )))
        } else {
            Ok(())
        }
    }
}

/// These tests exist for the unsafe code in `lend`/`lend_mut`: they are meant to
/// run under Miri (`cargo +<nightly> miri test -p luarc-runtime handle::`).
#[cfg(test)]
mod tests {
    use super::*;

    static META: HandleMeta<Vec<i32>> = HandleMeta { type_name: "Vec", show: |_, _| {}, eq: |_, _| None };

    #[test]
    fn shared_loan_reads_and_refuses_mutation() {
        let v = vec![1, 2, 3];
        lend(&v, &META, |h| {
            assert_eq!(h.get().unwrap().len(), 3);
            // several shared guards at once are fine
            let (a, b) = (h.get().unwrap(), h.get().unwrap());
            assert_eq!(a[0] + b[2], 4);
            drop((a, b));
            assert!(h.get_mut().is_err());
        });
        assert_eq!(v, [1, 2, 3]);
    }

    #[test]
    fn mutable_loan_writes_through() {
        let mut v = vec![1, 2, 3];
        lend_mut(&mut v, &META, |h| {
            h.get_mut().unwrap().push(4);
            {
                let mut g = h.get_mut().unwrap();
                g[0] = 10;
                // an exclusive guard excludes every other access
                assert!(h.get().is_err());
                assert!(h.get_mut().is_err());
            }
            assert_eq!(h.get().unwrap().iter().sum::<i32>(), 19);
        });
        assert_eq!(v, [10, 2, 3, 4]);
    }

    #[test]
    fn handle_kept_past_the_loan_is_expired() {
        let mut v = vec![1];
        let mut kept = None;
        lend_mut(&mut v, &META, |h| kept = Some(h.clone()));
        let h = kept.unwrap();
        let e = h.get().err().expect("expired").msg.to_string_lossy().to_string();
        assert!(e.contains("only valid while that callback runs"), "{e}");
        assert!(h.get_mut().is_err());
        // the owner can be used again, and the stale handle still cannot reach it
        v.push(2);
        assert!(h.get().is_err());
        assert_eq!(v, [1, 2]);
    }

    #[test]
    fn loan_ends_when_the_callback_unwinds() {
        let mut v = vec![1];
        let mut kept = None;
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            lend_mut(&mut v, &META, |h| {
                kept = Some(h.clone());
                panic!("callback failed");
            })
        }));
        assert!(r.is_err());
        assert!(kept.unwrap().get().is_err());
        v.push(2);
        assert_eq!(v, [1, 2]);
    }

    #[test]
    fn owned_handle_borrow_rules() {
        let h = Handle::new(vec![1], &META);
        let g = h.get().unwrap();
        assert!(h.get_mut().is_err(), "a shared guard excludes exclusive access");
        drop(g);
        let before = h.generation();
        h.get_mut().unwrap().push(2);
        assert_eq!(h.generation(), before + 1);
        assert_eq!(h.take("into_inner").unwrap(), [1, 2]);
        assert!(h.get().is_err(), "consumed");
    }

    #[test]
    fn view_is_invalidated_by_exclusive_access_to_its_owner() {
        let owner = Handle::new(vec![5, 6], &META);
        static ELEM: HandleMeta<i32> = HandleMeta { type_name: "i32", show: |_, _| {}, eq: |a, b| Some(a == b) };
        let view = Handle::view(&owner, "first", |v: &Vec<i32>| v.first(), Some(|v: &mut Vec<i32>| v.first_mut()), None, &ELEM);
        assert_eq!(*view.get().unwrap(), 5);
        *view.get_mut().unwrap() = 7;
        assert_eq!(owner.get().unwrap()[0], 7);
        owner.get_mut().unwrap().push(8);
        assert!(view.get().is_err(), "the owner changed since the view was made");
    }
}
