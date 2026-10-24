//! Managed value representations used by generated code.
//!
//! Tables, records, mutable upvalue cells and closures live on the managed heap
//! ([`crate::gc`]): acyclic objects are freed as soon as their last reference
//! disappears, unreachable cycles at the next collection.

use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use dumpster::Trace;

use crate::error::{LResult, LuaError};
use crate::gc::{Gc, Live, TraceWith, Visitor};

// Strings: immutable byte strings with cheap clones.

/// A source-language string: immutable bytes (may contain NUL or invalid UTF-8).
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LStr(pub Rc<[u8]>);

// SAFETY: a string is a leaf: it holds no managed pointers.
unsafe impl<V: Visitor> TraceWith<V> for LStr {
    #[inline]
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

impl LStr {
    pub fn from_bytes(b: &[u8]) -> LStr {
        LStr(Rc::from(b))
    }
    pub fn from_vec(v: Vec<u8>) -> LStr {
        LStr(Rc::from(v.into_boxed_slice()))
    }
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
    pub fn len(&self) -> f64 {
        self.0.len() as f64
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Validating UTF-8 view, used for native `&str` parameters.
    pub fn as_str(&self) -> LResult<&str> {
        std::str::from_utf8(&self.0).map_err(|e| {
            LuaError::new(format!("string is not valid UTF-8 (invalid byte at offset {})", e.valid_up_to()))
        })
    }
    /// Validating conversion, used for native `String` parameters.
    pub fn to_utf8_string(&self) -> LResult<String> {
        self.as_str().map(str::to_owned)
    }
    pub fn to_string_lossy(&self) -> String {
        String::from_utf8_lossy(&self.0).into_owned()
    }
}

impl From<&str> for LStr {
    fn from(s: &str) -> LStr {
        LStr::from_bytes(s.as_bytes())
    }
}
impl From<String> for LStr {
    fn from(s: String) -> LStr {
        LStr::from_vec(s.into_bytes())
    }
}
impl std::fmt::Debug for LStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", String::from_utf8_lossy(&self.0))
    }
}

// Mutable upvalue cells.

#[derive(Trace)]
pub struct CellBox<T: Trace + 'static> {
    _live: Live,
    v: RefCell<T>,
}

/// A mutable local captured by one or more closures. Every closure capturing the
/// same local shares this cell. Borrows never outlive a single read or write.
#[derive(Trace)]
pub struct Cell<T: Trace + 'static>(Gc<CellBox<T>>);

impl<T: Trace + 'static> Clone for Cell<T> {
    fn clone(&self) -> Self {
        Cell(self.0.clone())
    }
}
impl<T: Trace + Clone + 'static> Cell<T> {
    pub fn new(v: T) -> Self {
        Cell(Gc::new(CellBox { _live: Live::new(), v: RefCell::new(v) }))
    }
    #[inline]
    pub fn get(&self) -> T {
        self.0.v.borrow().clone()
    }
    #[inline]
    pub fn set(&self, v: T) {
        // The old value is dropped after the borrow ends (its drop may run a collection).
        let old = std::mem::replace(&mut *self.0.v.borrow_mut(), v);
        drop(old);
    }
}

// Arrays: dense, 1-based, shared identity.

#[derive(Trace)]
pub struct ArrBox<T: Trace + 'static> {
    _live: Live,
    v: RefCell<Vec<T>>,
    layout: RefCell<crate::table_layout::Layout>,
}

/// A dense array table `{T}`.
#[derive(Trace)]
pub struct Arr<T: Trace + 'static>(pub Gc<ArrBox<T>>);

impl<T: Trace + 'static> Clone for Arr<T> {
    fn clone(&self) -> Self {
        Arr(self.0.clone())
    }
}

/// Converts a source number to a 1-based array position, if it is a positive integer.
#[inline]
fn position(i: f64) -> Option<usize> {
    if i >= 1.0 && i.fract() == 0.0 && i <= usize::MAX as f64 {
        Some(i as usize)
    } else {
        None
    }
}

fn dynamic_element<T: 'static>() -> bool {
    std::any::TypeId::of::<T>() == std::any::TypeId::of::<crate::dynamic::Value>()
}
fn element_is_nil<T: 'static>(value: &T) -> bool {
    (value as &dyn std::any::Any).downcast_ref::<crate::dynamic::Value>().is_some_and(crate::dynamic::Value::is_nil)
}
fn nil_element<T: 'static>() -> Option<T> {
    let value: Box<dyn std::any::Any> = Box::new(crate::dynamic::Value::Nil);
    value.downcast::<T>().ok().map(|value| *value)
}

impl<T: Trace + Clone + 'static> Arr<T> {
    pub fn new() -> Self {
        Arr::from_vec(Vec::new())
    }
    pub fn from_vec(v: Vec<T>) -> Self {
        let n = v.len();
        Self::from_vec_with_layout(v, n, 0)
    }
    pub fn from_vec_with_layout(v: Vec<T>, array: usize, hash: usize) -> Self {
        let mut layout = crate::table_layout::Layout::new(array, hash);
        for (i, value) in v.iter().enumerate() { layout.write(crate::table_layout::Key::number((i+1) as f64), !element_is_nil(value)); }
        Arr(Gc::new(ArrBox { _live: Live::new(), v: RefCell::new(v), layout: RefCell::new(layout) }))
    }
    pub fn with_layout(array: usize, hash: usize) -> Self {
        Self::from_vec_with_layout(Vec::new(), array, hash)
    }
    /// `table.create(n)`: reserves capacity, length stays zero.
    pub fn with_capacity(n: f64) -> LResult<Self> {
        Ok(Self::with_layout(crate::table_layout::create_size(n)?, 0))
    }
    /// `table.create(n, v)`: n copies of `v` (a table value repeats its shared identity).
    pub fn filled(n: f64, v: T) -> LResult<Self> {
        let n = crate::table_layout::create_size(n)?;
        // Luau 0.743 rejects sizes beyond its limit with this message; an
        // allocation failure is an error too, not an abort
        let mut out: Vec<T> = Vec::new();
        out.try_reserve_exact(n).map_err(|_| LuaError::new("not enough memory"))?;
        out.resize(n, v);
        Ok(Arr::from_vec(out))
    }
    /// Replaces every element (the old elements are dropped after the borrow ends).
    pub fn replace_all(&self, v: Vec<T>) {
        let old_len = self.0.v.borrow().len();
        let mut layout = self.0.layout.borrow_mut();
        // Sorting rewrites values without clearing hash tombstones or capacity.
        for (i, value) in v.iter().enumerate() { layout.write(crate::table_layout::Key::number((i+1) as f64), !element_is_nil(value)); }
        for i in v.len()+1..=old_len { layout.write(crate::table_layout::Key::number(i as f64), false); }
        drop(layout);
        let old = std::mem::replace(&mut *self.0.v.borrow_mut(), v);
        release(old);
    }
    /// Sort writes only the `1..#t` prefix; values beyond a sparse boundary keep
    /// their source indices and hash tombstones survive.
    pub fn replace_prefix(&self, values: Vec<T>) {
        let old = {
            let mut storage = self.0.v.borrow_mut();
            let mut layout = self.0.layout.borrow_mut();
            let mut old = Vec::new();
            for (i, value) in values.into_iter().enumerate() {
                layout.write(crate::table_layout::Key::number((i+1) as f64), !element_is_nil(&value));
                if i < storage.len() { old.push(std::mem::replace(&mut storage[i], value)); }
                else { storage.push(value); }
            }
            old
        };
        release(old);
    }
    /// Shared access to the elements (never held across a call into user code).
    #[inline]
    pub fn borrow(&self) -> Ref<'_, Vec<T>> {
        self.0.v.borrow()
    }
    #[inline]
    pub fn len(&self) -> f64 {
        if dynamic_element::<T>() { self.0.layout.borrow_mut().length() as f64 }
        else { self.0.v.borrow().len() as f64 }
    }
    pub fn slot_count(&self) -> usize { self.0.v.borrow().len() }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0.0
    }
    /// `t[i]`: missing positions read as nil.
    #[inline]
    pub fn get(&self, i: f64) -> Option<T> {
        let v = self.0.v.borrow();
        position(i).and_then(|p| v.get(p - 1).filter(|value| !element_is_nil(*value)).cloned())
    }
    /// 0-based read used by `ipairs`/numeric iteration; no borrow is retained.
    #[inline]
    pub fn get_at(&self, k: usize) -> Option<T> {
        self.0.v.borrow().get(k).filter(|value| !element_is_nil(*value)).cloned()
    }
    /// `t[i] = v`: updates an existing slot or appends at `#t + 1`.
    pub fn set(&self, i: f64, val: T) -> LResult<()> {
        let old = {
            let mut v = self.0.v.borrow_mut();
            match position(i) {
                Some(p) if p <= v.len() => {
                    self.0.layout.borrow_mut().write(crate::table_layout::Key::number(i), !element_is_nil(&val));
                    std::mem::replace(&mut v[p - 1], val)
                }
                Some(p) if p == v.len() + 1 => {
                    self.0.layout.borrow_mut().write(crate::table_layout::Key::number(i), !element_is_nil(&val));
                    v.push(val);
                    return Ok(());
                }
                _ => {
                    return Err(LuaError::new(format!(
                        "array index {} out of range for write (length {}); arrays must stay dense (holes are unsupported)",
                        crate::show::num_to_string(i),
                        v.len()
                    )))
                }
            }
        };
        drop(old);
        Ok(())
    }
    /// `t[i] = v` where `v` may be nil: nil at the last slot removes it; nil past the
    /// end is a no-op; nil inside the array would create a hole and is rejected.
    pub fn set_opt(&self, i: f64, val: Option<T>) -> LResult<()> {
        match val {
            Some(x) => self.set(i, x),
            None => {
                if dynamic_element::<T>() && position(i).is_some_and(|p| p <= self.0.v.borrow().len()) {
                    if let Some(nil) = nil_element::<T>() { return self.set(i, nil); }
                }
                let old = {
                    let mut v = self.0.v.borrow_mut();
                    match position(i) {
                        Some(p) if p == v.len() => {
                            self.0.layout.borrow_mut().write(crate::table_layout::Key::number(i), false);
                            v.pop()
                        }
                        Some(p) if p > v.len() => {
                            self.0.layout.borrow_mut().write(crate::table_layout::Key::number(i), false);
                            None
                        }
                        _ => {
                            return Err(LuaError::new(format!(
                                "cannot assign nil to array index {} (length {}): interior holes are unsupported",
                                crate::show::num_to_string(i),
                                v.len()
                            )))
                        }
                    }
                };
                drop(old);
                Ok(())
            }
        }
    }
    /// `table.insert(t, v)`.
    pub fn push(&self, val: T) {
        let n = self.len() as usize + 1;
        self.0.layout.borrow_mut().write(crate::table_layout::Key::number(n as f64), !element_is_nil(&val));
        let old = {
            let mut storage = self.0.v.borrow_mut();
            if n <= storage.len() { Some(std::mem::replace(&mut storage[n-1], val)) }
            else { storage.push(val); None }
        };
        drop(old);
    }
    /// `table.insert(t, pos, v)`.
    pub fn insert_at(&self, pos: f64, val: T) -> LResult<()> {
        // Luau 0.743 truncates a fractional position
        let pos = pos.trunc();
        let logical = self.len() as usize;
        let mut v = self.0.v.borrow_mut();
        if dynamic_element::<T>() {
            return match position(pos) {
                Some(p) if p <= logical+1 => {
                    v.insert(p-1, val);
                    let old = if logical+1 < v.len() { Some(v.remove(logical+1)) } else { None };
                    for i in p..=logical+1 { self.0.layout.borrow_mut().write(crate::table_layout::Key::number(i as f64), !element_is_nil(&v[i-1])); }
                    drop(v); drop(old); Ok(())
                }
                _ => Err(LuaError::new("bad argument #2 to 'insert' (position out of bounds)")),
            };
        }
        match position(pos) {
            Some(p) if p <= v.len() + 1 => {
                self.0.layout.borrow_mut().write(crate::table_layout::Key::number((v.len()+1) as f64), true);
                v.insert(p - 1, val);
                Ok(())
            }
            _ => Err(LuaError::new("bad argument #2 to 'insert' (position out of bounds)")),
        }
    }
    /// `table.remove(t)`.
    pub fn pop(&self) -> Option<T> {
        if dynamic_element::<T>() {
            let n = self.len() as usize;
            if n == 0 { return None; }
            if let Some(nil) = nil_element::<T>() {
                self.0.layout.borrow_mut().write(crate::table_layout::Key::number(n as f64), false);
                return self.0.v.borrow_mut().get_mut(n-1).map(|value| std::mem::replace(value, nil));
            }
        }
        let n = self.0.v.borrow().len();
        if n > 0 { self.0.layout.borrow_mut().write(crate::table_layout::Key::number(n as f64), false); }
        self.0.v.borrow_mut().pop()
    }
    /// `table.remove(t, pos)`.
    pub fn remove_at(&self, pos: f64) -> LResult<Option<T>> {
        let pos = pos.trunc();
        if dynamic_element::<T>() {
            let n = self.len() as usize;
            return match position(pos) {
                Some(p) if p <= n => {
                    if let Some(nil) = nil_element::<T>() {
                        let mut v = self.0.v.borrow_mut();
                        let old = v.remove(p-1);
                        v.insert(n-1, nil);
                        for i in p..=n { self.0.layout.borrow_mut().write(crate::table_layout::Key::number(i as f64), !element_is_nil(&v[i-1])); }
                        Ok(Some(old))
                    } else { Ok(None) }
                }
                // Luau returns nil without mutation outside the logical prefix,
                // including non-finite positions after integer coercion.
                _ => Ok(None),
            };
        }
        let mut v = self.0.v.borrow_mut();
        let n = v.len();
        match position(pos) {
            Some(p) if p <= n => {
                self.0.layout.borrow_mut().write(crate::table_layout::Key::number(n as f64), false);
                Ok(Some(v.remove(p - 1)))
            }
            Some(p) if p == n + 1 => Ok(None),
            _ if n == 0 && pos == 0.0 => Ok(None),
            _ => Err(LuaError::new("bad argument #2 to 'remove' (position out of bounds)")),
        }
    }
    /// `table.clone(t)`: shallow copy with a new identity.
    pub fn shallow_clone(&self) -> Self {
        let copy = Arr::from_vec(self.0.v.borrow().clone());
        *copy.0.layout.borrow_mut() = self.0.layout.borrow().clone();
        copy
    }
    pub fn clear(&self) {
        self.0.layout.borrow_mut().clear();
        let old = std::mem::take(&mut *self.0.v.borrow_mut());
        release(old);
    }
    pub fn reserve_layout_array(&self, size: usize) {
        self.0.layout.borrow_mut().resize_array(size);
    }
    pub fn array_capacity(&self) -> usize { self.0.layout.borrow().array_size() }
    pub fn next_entry(&self, key: Option<f64>) -> LResult<(Option<f64>, Option<T>)> {
        let token = key.map(crate::table_layout::Key::number);
        let next = self.0.layout.borrow().next(token.as_ref()).map_err(|()| LuaError::located("invalid key to 'next'"))?;
        match next {
            Some(crate::table_layout::Key::Number(bits)) => {
                let n = f64::from_bits(bits);
                Ok((Some(n), self.get(n)))
            }
            _ => Ok((None, None)),
        }
    }
    /// Snapshot used for native `Vec<T>`/slice conversion.
    pub fn snapshot(&self) -> Vec<T> {
        self.0.v.borrow().clone()
    }
}

impl<T: Trace + 'static> Arr<T> {
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Gc::ptr_eq(&self.0, &other.0)
    }
    pub fn addr(&self) -> usize {
        Gc::as_ptr(&self.0) as *const u8 as usize
    }
}

impl<T: Trace + Clone + 'static> Default for Arr<T> {
    fn default() -> Self {
        Arr::new()
    }
}

// Maps: insertion-ordered hash maps with shared identity.

/// Hashable wrapper for number keys. `-0` and `0` are the same key (they are
/// equal numbers), and NaN is rejected (it is not equal to itself), so key
/// identity always agrees with `==`.
#[derive(Clone, Copy, Debug)]
pub struct NumKey(u64);

// SAFETY: a number key holds no managed pointers.
unsafe impl<V: Visitor> TraceWith<V> for NumKey {
    #[inline]
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

impl NumKey {
    pub fn new(x: f64) -> LResult<NumKey> {
        if x.is_nan() {
            return Err(LuaError::new("table index is NaN"));
        }
        let x = if x == 0.0 { 0.0 } else { x };
        Ok(NumKey(x.to_bits()))
    }
    pub fn get(self) -> f64 {
        f64::from_bits(self.0)
    }
}
impl PartialEq for NumKey {
    fn eq(&self, o: &Self) -> bool {
        self.0 == o.0
    }
}
impl Eq for NumKey {}
impl Hash for NumKey {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.0.hash(h)
    }
}

struct MapKeyLayout<K>(fn(&K) -> crate::table_layout::Key);
// SAFETY: a function pointer contains no managed pointers.
unsafe impl<K, V: Visitor> TraceWith<V> for MapKeyLayout<K> {
    fn accept(&self, _: &mut V) -> Result<(), ()> { Ok(()) }
}

#[derive(Trace)]
pub struct MapInner<K: Trace + Eq + Hash + 'static, V: Trace + 'static> {
    _live: Live,
    slots: Vec<Option<(K, V)>>,
    index: HashMap<K, usize>,
    layout: crate::table_layout::Layout,
    key_layout: MapKeyLayout<K>,
}

/// A map table `{[K]: V}`. Iteration order is insertion order of live keys; programs
/// must not rely on any particular order.
#[derive(Trace)]
pub struct LMap<K: Trace + Eq + Hash + 'static, V: Trace + 'static>(pub Gc<RefCellMap<K, V>>);

/// The mutable map body behind an [`LMap`] handle.
#[derive(Trace)]
pub struct RefCellMap<K: Trace + Eq + Hash + 'static, V: Trace + 'static>(RefCell<MapInner<K, V>>);

impl<K: Trace + Eq + Hash + 'static, V: Trace + 'static> Clone for LMap<K, V> {
    fn clone(&self) -> Self {
        LMap(self.0.clone())
    }
}

impl<K: Trace + Clone + Eq + Hash + 'static, V: Trace + Clone + 'static> LMap<K, V> {
    pub fn new() -> Self {
        Self::with_layout(0, 0)
    }
    pub fn with_layout(array: usize, hash: usize) -> Self {
        Self::with_key_layout(array, hash, crate::table_layout::static_key::<K>)
    }
    pub fn with_key_layout(array: usize, hash: usize, key_layout: fn(&K) -> crate::table_layout::Key) -> Self {
        LMap(Gc::new(RefCellMap(RefCell::new(MapInner { _live: Live::new(), slots: Vec::new(), index: HashMap::new(), layout: crate::table_layout::Layout::new(array, hash), key_layout: MapKeyLayout(key_layout) }))))
    }
    pub fn get(&self, k: &K) -> Option<V> {
        let m = self.0 .0.borrow();
        m.index.get(k).and_then(|&i| m.slots[i].as_ref().map(|(_, v)| v.clone()))
    }
    pub fn set(&self, k: K, v: V) {
        if element_is_nil(&v) { self.remove(&k); return; }
        let old = {
            let mut m = self.0 .0.borrow_mut();
            let token = (m.key_layout.0)(&k);
            m.layout.write(token, true);
            if let Some(&i) = m.index.get(&k) {
                if let Some(slot) = m.slots[i].as_mut() {
                    Some(std::mem::replace(&mut slot.1, v))
                } else {
                    None
                }
            } else {
                let i = m.slots.len();
                m.slots.push(Some((k.clone(), v)));
                m.index.insert(k, i);
                None
            }
        };
        drop(old);
    }
    /// `m[k] = v` where `v` may be nil (nil deletes the key).
    pub fn set_opt(&self, k: K, v: Option<V>) {
        match v {
            Some(v) => self.set(k, v),
            None => self.remove(&k),
        }
    }
    pub fn remove(&self, k: &K) {
        let removed = {
            let mut m = self.0 .0.borrow_mut();
            let token = (m.key_layout.0)(k);
            m.layout.write(token, false);
            match m.index.remove(k) {
                Some(i) => {
                    let old = m.slots[i].take();
                    let live = m.index.len();
                    if m.slots.len() > 32 && m.slots.len() > 2 * live {
                        // Compact tombstones; iteration snapshots hold keys, not slot indexes.
                        let old_slots = std::mem::take(&mut m.slots);
                        let mut idx = HashMap::with_capacity(live);
                        let mut slots = Vec::with_capacity(live);
                        for (k, v) in old_slots.into_iter().flatten() {
                            idx.insert(k.clone(), slots.len());
                            slots.push(Some((k, v)));
                        }
                        m.slots = slots;
                        m.index = idx;
                    }
                    old
                }
                None => None,
            }
        };
        drop(removed);
    }
    /// Snapshot of the live keys at the start of a `pairs` loop.
    pub fn keys(&self) -> Vec<K> {
        self.0 .0.borrow().slots.iter().flatten().map(|(k, _)| k.clone()).collect()
    }
    pub fn count(&self) -> usize {
        self.0 .0.borrow().index.len()
    }
    pub fn shallow_clone(&self) -> Self {
        let key_layout = self.0 .0.borrow().key_layout.0;
        let n = LMap::with_key_layout(0, 0, key_layout);
        for k in self.keys() {
            if let Some(v) = self.get(&k) {
                n.set(k, v);
            }
        }
        n.0 .0.borrow_mut().layout = self.0 .0.borrow().layout.clone();
        n
    }
    pub fn clear(&self) {
        let old = {
            let mut m = self.0 .0.borrow_mut();
            m.layout.clear();
            (std::mem::take(&mut m.slots), std::mem::take(&mut m.index))
        };
        drop(old);
    }
    pub fn next_entry(&self, key: Option<K>) -> LResult<(Option<K>, Option<V>)> {
        let m = self.0 .0.borrow();
        let token = key.as_ref().map(m.key_layout.0);
        let next = m.layout.next(token.as_ref()).map_err(|()| LuaError::located("invalid key to 'next'"))?;
        if let Some(next) = next {
            for (k, v) in m.slots.iter().flatten() {
                if (m.key_layout.0)(k) == next { return Ok((Some(k.clone()), Some(v.clone()))); }
            }
        }
        Ok((None, None))
    }
}

impl<K: Trace + Eq + Hash + 'static, V: Trace + 'static> LMap<K, V> {
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Gc::ptr_eq(&self.0, &other.0)
    }
    pub fn addr(&self) -> usize {
        Gc::as_ptr(&self.0) as *const u8 as usize
    }
}

impl<K: Trace + Clone + Eq + Hash + 'static, V: Trace + Clone + 'static> Default for LMap<K, V> {
    fn default() -> Self {
        LMap::new()
    }
}

// Records: generated structs behind a shared handle.

#[derive(Trace)]
pub struct RecBox<T: Trace + 'static> {
    _live: Live,
    v: RefCell<T>,
}

/// A record table; `T` is a struct generated for one structural record type.
#[derive(Trace)]
pub struct Rec<T: Trace + 'static>(pub Gc<RecBox<T>>);

impl<T: Trace + 'static> Clone for Rec<T> {
    fn clone(&self) -> Self {
        Rec(self.0.clone())
    }
}
impl<T: Trace + 'static> Rec<T> {
    pub fn new(v: T) -> Self {
        Rec(Gc::new(RecBox { _live: Live::new(), v: RefCell::new(v) }))
    }
    /// Shared borrow for runtime helpers. Generated field reads use [`Rec::read`]:
    /// a `Ref` temporary inside a larger expression lives to the end of the
    /// enclosing statement, so a later call in that statement writing the record
    /// would hit `BorrowMutError`.
    #[inline]
    pub fn borrow(&self) -> Ref<'_, T> {
        self.0.v.borrow()
    }
    /// Field read: the borrow ends before `read` returns.
    #[inline]
    pub fn read<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        f(&self.0.v.borrow())
    }
    /// Field writes: callers drop the replaced value after the borrow ends.
    #[inline]
    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        self.0.v.borrow_mut()
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Gc::ptr_eq(&self.0, &other.0)
    }
    pub fn addr(&self) -> usize {
        Gc::as_ptr(&self.0) as *const u8 as usize
    }
}
impl<T: Trace + Clone + 'static> Rec<T> {
    pub fn shallow_clone(&self) -> Self {
        Rec::new(self.0.v.borrow().clone())
    }
}

#[derive(Trace)]
struct MetaRecBox<T: Trace + 'static, P: Trace + 'static> {
    _live: Live,
    v: RefCell<T>,
    parent: RefCell<Option<P>>,
}

/// A record whose static type permits attachment; the handle belongs to each object.
/// `P` is the class in the class subset, or the actual metatable for general lookup.
#[derive(Trace)]
pub struct MetaRec<T: Trace + 'static, P: Trace + 'static>(Gc<MetaRecBox<T, P>>);

impl<T: Trace + 'static, P: Trace + 'static> Clone for MetaRec<T, P> {
    fn clone(&self) -> Self {
        MetaRec(self.0.clone())
    }
}
impl<T: Trace + 'static, P: Trace + 'static> MetaRec<T, P> {
    pub fn new(v: T) -> Self {
        MetaRec(Gc::new(MetaRecBox { _live: Live::new(), v: RefCell::new(v), parent: RefCell::new(None) }))
    }
    /// Own storage only; generated field reads use `read` to end the borrow promptly.
    #[inline]
    pub fn borrow(&self) -> Ref<'_, T> {
        self.0.v.borrow()
    }
    #[inline]
    pub fn read<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        f(&self.0.v.borrow())
    }
    /// Own writes never modify the parent. Drop replaced values after this borrow ends.
    #[inline]
    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        self.0.v.borrow_mut()
    }
    /// Luau 0.743: setmetatable replaces attachment and returns the same table identity.
    pub fn attach(&self, parent: P) -> Self {
        let old = self.0.parent.replace(Some(parent));
        drop(old);
        self.clone()
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Gc::ptr_eq(&self.0, &other.0)
    }
    pub fn addr(&self) -> usize {
        Gc::as_ptr(&self.0) as *const u8 as usize
    }
}
impl<T: Trace + 'static, P: Trace + Clone + 'static> MetaRec<T, P> {
    /// Luau 0.743: snapshot the attached handle, releasing the borrow before live lookup.
    pub fn parent(&self) -> Option<P> {
        self.0.parent.borrow().clone()
    }
}

impl<T: Trace + Clone + 'static, P: Trace + Clone + 'static> MetaRec<T, P> {
    /// Luau 0.743: table.clone copies own storage and shares the live metatable handle.
    pub fn shallow_clone(&self) -> Self {
        let v = self.read(Clone::clone);
        let parent = self.parent();
        MetaRec(Gc::new(MetaRecBox { _live: Live::new(), v: RefCell::new(v), parent: RefCell::new(parent) }))
    }
}

// Functions.

/// A callable function body. Generated closures implement it on an environment
/// struct holding their captured values (so every captured edge is traced).
/// `this` is the function value being called, which gives recursive closures a
/// reference to themselves without a stored (cyclic) self pointer.
pub trait Callable<A: 'static, R: 'static>: Trace {
    fn call(&self, this: &LFn<A, R>, args: A) -> LResult<R>;
}

/// A function value taking the argument tuple `A` and returning `R`.
/// Identity is pointer identity.
pub struct LFn<A: 'static, R: 'static>(pub Gc<dyn Callable<A, R>>);

impl<A: 'static, R: 'static> Clone for LFn<A, R> {
    fn clone(&self) -> Self {
        LFn(self.0.clone())
    }
}

// SAFETY: visits the only managed pointer the value holds.
unsafe impl<V: Visitor, A: 'static, R: 'static> TraceWith<V> for LFn<A, R> {
    #[inline]
    fn accept(&self, v: &mut V) -> Result<(), ()> {
        self.0.accept(v)
    }
}

/// Allocation of a closure environment (adds the live-object token).
#[derive(Trace)]
struct ClosureBox<E: Trace + 'static> {
    _live: Live,
    env: E,
}

impl<A: 'static, R: 'static, E: Callable<A, R> + 'static> Callable<A, R> for ClosureBox<E> {
    #[inline]
    fn call(&self, this: &LFn<A, R>, args: A) -> LResult<R> {
        self.env.call(this, args)
    }
}

/// A plain function pointer used as a function value (static functions, builtins).
struct FnPtr<A: 'static, R: 'static> {
    _live: Live,
    f: fn(A) -> LResult<R>,
}

// SAFETY: a function pointer holds no managed pointers.
unsafe impl<V: Visitor, A: 'static, R: 'static> TraceWith<V> for FnPtr<A, R> {
    #[inline]
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

impl<A: 'static, R: 'static> Callable<A, R> for FnPtr<A, R> {
    #[inline]
    fn call(&self, _this: &LFn<A, R>, args: A) -> LResult<R> {
        (self.f)(args)
    }
}

impl<A: 'static, R: 'static> LFn<A, R> {
    /// Allocates a closure from its environment.
    pub fn new<E: Callable<A, R> + 'static>(env: E) -> Self {
        let g: Gc<ClosureBox<E>> = Gc::new(ClosureBox { _live: Live::new(), env });
        LFn(dumpster::unsync::coerce_gc!(g))
    }
    /// A function value for a plain function (no captures).
    pub fn from_fn(f: fn(A) -> LResult<R>) -> Self {
        let g: Gc<FnPtr<A, R>> = Gc::new(FnPtr { _live: Live::new(), f });
        LFn(dumpster::unsync::coerce_gc!(g))
    }
    #[inline]
    pub fn call(&self, args: A) -> LResult<R> {
        self.0.call(self, args)
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Gc::ptr_eq(&self.0, &other.0)
    }
    pub fn addr(&self) -> usize {
        Gc::as_ptr(&self.0) as *const u8 as usize
    }
}

// Internal finite unions.

/// Result of `a and b` where `a` is a boolean and `b` is not: `false` or `b`.
#[derive(Clone, Trace)]
pub enum FalseOr<T: Trace + 'static> {
    False,
    Val(T),
}

/// Second result of `pcall`: the value on success or the error message on failure.
#[derive(Clone, Trace)]
pub enum PcallVal<T: Trace + 'static> {
    Ok(T),
    Err(LStr),
}

impl<T: Trace + 'static> PcallVal<T> {
    /// Used only where the checker proved the success branch.
    #[inline]
    pub fn ok_value(self) -> T {
        match self {
            PcallVal::Ok(v) => v,
            PcallVal::Err(_) => unreachable!("luarc: pcall narrowing violated"),
        }
    }
    /// Used only where the checker proved the failure branch.
    #[inline]
    pub fn err_value(self) -> LStr {
        match self {
            PcallVal::Err(e) => e,
            PcallVal::Ok(_) => unreachable!("luarc: pcall narrowing violated"),
        }
    }
}

/// Unwraps a value the checker proved non-nil (narrowed optional).
#[inline]
pub fn narrowed<T>(v: Option<T>) -> T {
    match v {
        Some(v) => v,
        None => unreachable!("luarc: nil narrowing violated"),
    }
}

/// Uses a value that may be nil at runtime (a table read) where a value is required,
/// raising the language error Lua would raise.
#[inline]
pub fn present<T>(v: Option<T>, what: &'static str) -> LResult<T> {
    match v {
        Some(v) => Ok(v),
        None => Err(LuaError::new(what)),
    }
}

/// Drops a value replaced by a write, after the write's borrow has ended (the
/// argument is evaluated first, so the borrow is already released here).
#[inline]
pub fn release<T>(_old: T) {}

#[cfg(test)]
mod metarec_tests {
    use super::*;

    #[test]
    fn attachment_preserves_identity_and_is_per_instance() {
        let a = MetaRec::<_, Rec<f64>>::new(None::<f64>);
        let b = MetaRec::<_, Rec<f64>>::new(None::<f64>);
        let alias = a.clone();
        assert!(a.parent().is_none());
        let class = Rec::new(7.0);
        let result = a.attach(class.clone());
        assert!(result.ptr_eq(&a));
        assert!(alias.ptr_eq(&a));
        assert_eq!(alias.addr(), result.addr());
        assert!(!b.ptr_eq(&a));
        assert!(b.parent().is_none());
        assert!(alias.parent().is_some_and(|p| p.ptr_eq(&class)));
        *class.borrow_mut() = 8.0;
        assert_eq!(alias.parent().map(|p| p.read(|x| *x)), Some(8.0));
        *a.borrow_mut() = Some(0.0);
        assert_eq!(*alias.borrow(), Some(0.0));
        assert_eq!(class.read(|x| *x), 8.0);
        let other = Rec::new(9.0);
        assert!(a.attach(other.clone()).ptr_eq(&a));
        assert!(alias.parent().is_some_and(|p| p.ptr_eq(&other)));
        assert_eq!(class.read(|x| *x), 8.0);
    }

    #[test]
    fn read_and_parent_snapshots_release_borrows_before_later_calls() {
        let child = MetaRec::new(Some(1.0));
        let class = Rec::new(7.0);
        child.attach(class.clone());
        let own = child.read(|x| *x);
        *child.borrow_mut() = Some(2.0);
        let parent = child.parent();
        child.attach(Rec::new(9.0));
        let inherited = parent.map(|p| p.read(|x| *x));
        *class.borrow_mut() = 8.0;
        assert_eq!(own, Some(1.0));
        assert_eq!(inherited, Some(7.0));
        assert_eq!(child.read(|x| *x), Some(2.0));
        assert_eq!(child.parent().map(|p| p.read(|x| *x)), Some(9.0));
    }

    #[test]
    fn shallow_clone_shares_live_metadata_with_independent_storage_and_attachment() {
        let p = Rec::new(1.0);
        let q = Rec::new(2.0);
        let mt = Rec::new(Some(p.clone()));
        let child = MetaRec::new(3.0);
        child.attach(mt.clone());
        let copy = child.shallow_clone();
        assert!(!copy.ptr_eq(&child));
        assert_ne!(copy.addr(), child.addr());
        assert_eq!(copy.read(|x| *x), 3.0);
        assert!(copy.parent().is_some_and(|m| m.ptr_eq(&mt)));
        *copy.borrow_mut() = 4.0;
        assert_eq!(child.read(|x| *x), 3.0);
        assert_eq!(copy.read(|x| *x), 4.0);
        *mt.borrow_mut() = Some(q);
        let lookup = |t: &MetaRec<f64, Rec<Option<Rec<f64>>>>| {
            t.parent().and_then(|m| m.read(Clone::clone)).map(|p| p.read(|x| *x))
        };
        assert_eq!(lookup(&child), Some(2.0));
        assert_eq!(lookup(&copy), Some(2.0));
        *mt.borrow_mut() = None;
        assert_eq!(lookup(&child), None);
        assert_eq!(lookup(&copy), None);
        *mt.borrow_mut() = Some(p.clone());
        copy.attach(Rec::new(Some(Rec::new(9.0))));
        *p.borrow_mut() = 5.0;
        assert_eq!(lookup(&child), Some(5.0));
        assert_eq!(lookup(&copy), Some(9.0));
    }

    #[test]
    fn shallow_clone_of_unattached_storage_keeps_nested_table_identity() {
        let nested = Rec::new(7.0);
        let plain = MetaRec::<_, Rec<f64>>::new((None::<f64>, nested.clone()));
        let copy = plain.shallow_clone();
        assert!(!copy.ptr_eq(&plain));
        assert_eq!(copy.read(|v| v.0), None);
        assert!(copy.read(|v| v.1.ptr_eq(&nested)));
        plain.attach(Rec::new(8.0));
        assert!(copy.parent().is_none());
        let own = copy.read(|v| v.1.clone());
        *own.borrow_mut() = 9.0;
        assert_eq!(plain.read(|v| v.1.read(|x| *x)), 9.0);
        copy.borrow_mut().0 = Some(0.0);
        assert_eq!(plain.read(|v| v.0), None);
        assert_eq!(copy.read(|v| v.0), Some(0.0));
        assert!(copy.parent().is_none());
    }

    #[derive(Trace)]
    struct CloneMetadata {
        owner: Option<MetaRec<(), Rec<CloneMetadata>>>,
    }

    impl Drop for CloneMetadata {
        fn drop(&mut self) {
            if let Some(owner) = &self.owner {
                assert!(owner.0.v.try_borrow_mut().is_ok());
                assert!(owner.0.parent.try_borrow_mut().is_ok());
                crate::gc::collect();
            }
        }
    }

    #[test]
    fn cloned_metadata_destruction_can_reenter_after_reattachment() {
        let child = MetaRec::new(());
        child.attach(Rec::new(CloneMetadata { owner: Some(child.clone()) }));
        let copy = child.shallow_clone();
        child.attach(Rec::new(CloneMetadata { owner: None }));
        copy.attach(Rec::new(CloneMetadata { owner: None }));
    }

    #[derive(Trace)]
    struct ReentrantParent {
        owner: Option<MetaRec<(), ReentrantParent>>,
    }

    impl Drop for ReentrantParent {
        fn drop(&mut self) {
            if let Some(owner) = &self.owner {
                assert!(owner.0.parent.try_borrow_mut().is_ok());
                crate::gc::collect();
            }
        }
    }

    #[test]
    fn replaced_parent_is_dropped_after_attachment_borrow_ends() {
        let child = MetaRec::new(());
        child.attach(ReentrantParent { owner: Some(child.clone()) });
        child.attach(ReentrantParent { owner: None });
    }

    #[derive(Trace)]
    struct Class {
        index: Option<Rec<Class>>,
        x: f64,
    }

    #[test]
    fn parent_and_own_edges_trace_a_class_data_cycle() {
        crate::gc::collect();
        let baseline = crate::gc::live_objects();
        {
            let class = Rec::new(Class { index: None, x: 7.0 });
            class.borrow_mut().index = Some(class.clone());
            let child = MetaRec::new(None::<Rec<Class>>);
            child.attach(class);
            crate::gc::collect();
            assert_eq!(crate::gc::live_objects(), baseline + 2);
            assert_eq!(child.parent().map(|p| p.read(|c| c.x)), Some(7.0));
            // An own edge keeps Class alive after replacing the attachment edge.
            *child.borrow_mut() = child.parent();
            child.attach(Rec::new(Class { index: None, x: 9.0 }));
            crate::gc::collect();
            assert_eq!(crate::gc::live_objects(), baseline + 3);
            assert_eq!(child.read(|v| v.as_ref().map(|p| p.read(|c| c.x))), Some(7.0));
            let old = child.borrow_mut().take();
            drop(old);
            crate::gc::collect();
            assert_eq!(crate::gc::live_objects(), baseline + 2);
        }
        crate::gc::collect();
        assert_eq!(crate::gc::live_objects(), baseline);
    }

    #[test]
    fn cloned_attachment_keeps_a_metadata_cycle_live_then_reclaims_it() {
        crate::gc::collect();
        let baseline = crate::gc::live_objects();
        {
            let parent = Rec::new(Parent { child: None });
            let child = MetaRec::new(());
            child.attach(parent.clone());
            parent.borrow_mut().child = Some(child.clone());
            let copy = child.shallow_clone();
            drop(child);
            drop(parent);
            crate::gc::collect();
            assert_eq!(crate::gc::live_objects(), baseline + 3);
            assert!(copy.parent().is_some_and(|p| p.read(|p| p.child.is_some())));
            copy.attach(Rec::new(Parent { child: None }));
            crate::gc::collect();
            assert_eq!(crate::gc::live_objects(), baseline + 2);
        }
        crate::gc::collect();
        assert_eq!(crate::gc::live_objects(), baseline);
    }

    #[derive(Trace)]
    struct Parent {
        child: Option<MetaRec<(), Rec<Parent>>>,
    }

    #[test]
    fn cycle_through_attachment_is_reclaimed() {
        crate::gc::collect();
        let baseline = crate::gc::live_objects();
        {
            let parent = Rec::new(Parent { child: None });
            let child = MetaRec::new(());
            child.attach(parent.clone());
            parent.borrow_mut().child = Some(child);
        }
        crate::gc::collect();
        assert_eq!(crate::gc::live_objects(), baseline);
    }
}
