//! Luau 0.743 array/hash allocation history, independent of value storage.
//!
//! Mirrors VM/src/ltable.cpp (MIT), including dead hash keys, Brent chains,
//! density rehashing and the array-boundary invariant. Rust allocation capacity
//! is deliberately irrelevant to source table allocation.

// Upstream: https://github.com/luau-lang/luau/tree/0.743/VM/src
// Allocation/chains and hashing adapted from ltable.cpp and lstring.cpp.
// MIT License
// Copyright (c) 2019-2026 Roblox Corporation
// Copyright (c) 1994–2019 Lua.org, PUC-Rio.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of
// this software and associated documentation files (the "Software"), to deal in
// the Software without restriction, including without limitation the rights to
// use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is furnished to do
// so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use crate::gc::{TraceWith, Visitor};
use crate::value::{LStr, NumKey};
use std::any::Any;

pub fn create_size(n: f64) -> crate::LResult<usize> {
    let n = n.trunc();
    if !n.is_finite() || n < 0.0 || n > i32::MAX as f64 {
        return Err(crate::LuaError::new(
            "invalid argument #1 to 'create' (size out of range)",
        ));
    }
    if n > (1 << 26) as f64 {
        return Err(crate::LuaError::located("table overflow"));
    }
    Ok(n as usize)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Key {
    Number(u64),
    String(Vec<u8>),
    Boolean(bool),
    Integer(i128),
    Object(u8, usize),
}

// SAFETY: layout keys contain owned bytes and scalar identities only.
unsafe impl<V: Visitor> TraceWith<V> for Key {
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

impl Key {
    pub fn from_value(value: &crate::dynamic::Value) -> Option<Self> {
        use crate::dynamic::Value;
        match value {
            Value::Nil => None,
            Value::Bool(v) => Some(Self::Boolean(*v)),
            Value::Num(v) => Some(Self::number(*v)),
            Value::Str(v) => Some(Self::String(v.as_bytes().to_vec())),
            Value::Table(v) => Some(Self::Object(0, v.identity())),
            Value::Function(v) => Some(Self::Object(1, v.identity())),
            Value::Userdata(v) => Some(Self::Object(2, v.identity())),
            Value::Thread(thread) => Some(Self::Object(3, thread.addr())),
        }
    }
    pub fn number(n: f64) -> Self {
        Self::Number(if n == 0.0 { 0 } else { n.to_bits() })
    }
    pub fn array_index(&self) -> Option<usize> {
        match self {
            Self::Number(bits) => {
                let n = f64::from_bits(*bits);
                (n >= 1.0 && n <= (1u32 << 26) as f64 && n.fract() == 0.0).then_some(n as usize)
            }
            Self::Integer(n) => (*n >= 1 && *n <= 1 << 26).then_some(*n as usize),
            _ => None,
        }
    }
    fn hash(&self) -> u32 {
        match self {
            Self::Boolean(v) => u32::from(*v),
            Self::Integer(v) => Self::number(*v as f64).hash(),
            Self::Number(bits) => {
                let mut h1 = *bits as u32;
                let mut h2 = (*bits >> 32) as u32 & 0x7fff_ffff;
                h1 ^= h2 >> 18;
                h1 = h1.wrapping_mul(0x5bd1_e995);
                h2 ^= h1 >> 22;
                h2 = h2.wrapping_mul(0x5bd1_e995);
                h1 ^= h2 >> 17;
                h1 = h1.wrapping_mul(0x5bd1_e995);
                h2 ^= h1 >> 19;
                h2.wrapping_mul(0x5bd1_e995)
            }
            Self::String(bytes) => {
                let mut bytes = bytes.as_slice();
                let (mut a, mut b, mut h) = (0u32, 0u32, bytes.len() as u32);
                while bytes.len() >= 32 {
                    let word = |i| {
                        u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]])
                    };
                    a = a.wrapping_add(word(0));
                    b = b.wrapping_add(word(4));
                    h = h.wrapping_add(word(8));
                    a ^= h;
                    a = a.wrapping_sub(h.rotate_right(14));
                    b ^= a;
                    b = b.wrapping_sub(a.rotate_right(11));
                    h ^= b;
                    h = h.wrapping_sub(b.rotate_right(25));
                    bytes = &bytes[12..];
                }
                for &v in bytes.iter().rev() {
                    h ^= (h << 5).wrapping_add(h >> 2).wrapping_add(u32::from(v));
                }
                h
            }
            Self::Object(_, addr) => {
                let mut h = *addr as u32;
                h ^= h >> 16;
                h = h.wrapping_mul(0x85eb_ca6b);
                h ^= h >> 13;
                h = h.wrapping_mul(0xc2b2_ae35);
                h ^ (h >> 16)
            }
        }
    }
}

/// Static key types need no new trait bound. Mixed keys provide their extractor
/// explicitly to `LMap::with_key_layout`.
pub fn static_key<K: 'static>(key: &K) -> Key {
    let key = key as &dyn Any;
    if let Some(v) = key.downcast_ref::<NumKey>() {
        Key::number(v.get())
    } else if let Some(v) = key.downcast_ref::<LStr>() {
        Key::String(v.as_bytes().to_vec())
    } else if let Some(v) = key.downcast_ref::<bool>() {
        Key::Boolean(*v)
    } else if let Some(v) = key.downcast_ref::<i64>() {
        Key::number(*v as f64)
    } else if let Some(v) = key.downcast_ref::<i128>() {
        Key::Integer(*v)
    } else if let Some(v) = key.downcast_ref::<f64>() {
        Key::number(*v)
    } else {
        Key::Object(0, key as *const dyn Any as *const () as usize)
    }
}

#[derive(Clone, Default)]
struct Node {
    key: Option<Key>,
    live: bool,
    next: Option<usize>,
}

#[derive(Clone, Default)]
pub struct Layout {
    array: Vec<bool>,
    nodes: Vec<Node>,
    last_free: usize,
    boundary: Option<usize>,
}

// SAFETY: layout contains no managed pointers.
unsafe impl<V: Visitor> TraceWith<V> for Layout {
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

impl Layout {
    pub fn new(array: usize, hash: usize) -> Self {
        let size = if hash == 0 {
            0
        } else {
            hash.next_power_of_two()
        };
        Self {
            array: vec![false; array],
            nodes: vec![Node::default(); size],
            last_free: size,
            boundary: None,
        }
    }
    pub fn array_size(&self) -> usize {
        self.array.len()
    }
    fn main(&self, key: &Key) -> usize {
        key.hash() as usize & (self.nodes.len() - 1)
    }
    fn find_hash(&self, key: &Key) -> Option<usize> {
        if self.nodes.is_empty() {
            return None;
        }
        let mut i = self.main(key);
        loop {
            if self.nodes[i].key.as_ref() == Some(key) {
                return Some(i);
            }
            i = self.nodes[i].next?;
        }
    }
    fn live(&self, key: &Key) -> bool {
        if let Some(i) = key.array_index().filter(|&i| i <= self.array.len()) {
            self.array[i - 1]
        } else {
            self.find_hash(key).is_some_and(|i| self.nodes[i].live)
        }
    }
    fn adjust_array(&self, mut size: usize, extra: Option<usize>) -> usize {
        let bound = !self.nodes.is_empty() || size < self.array.len();
        while extra == Some(size + 1) || (bound && self.live(&Key::number((size + 1) as f64))) {
            size += 1;
        }
        size
    }
    fn rehash(&mut self, key: &Key) {
        let integer = match key {
            Key::Number(bits) => {
                let n = f64::from_bits(*bits);
                n >= i32::MIN as f64 && n <= i32::MAX as f64 && n.fract() == 0.0
            }
            Key::Integer(_) => true,
            _ => false,
        };
        // The pinned oracle enables LuauSplitTableLookups: noninteger-key
        // insertion grows the hash without rebalancing the existing array.
        if !integer {
            let hash = self.nodes.iter().filter(|n| n.live).count() + 1;
            self.resize(self.array.len(), hash);
            return;
        }
        let mut nums = [0usize; 27];
        let mut total = 1;
        let mut count = |key: &Key| {
            if let Some(i) = key.array_index() {
                nums[(usize::BITS - (i - 1).leading_zeros()) as usize] += 1;
            }
        };
        for (i, live) in self.array.iter().enumerate() {
            if *live {
                total += 1;
                count(&Key::number((i + 1) as f64));
            }
        }
        for node in &self.nodes {
            if node.live {
                total += 1;
                if let Some(key) = &node.key {
                    count(key);
                }
            }
        }
        count(key);
        let (mut used, mut array, mut array_used) = (0, 0, 0);
        for (log, n) in nums.iter().enumerate() {
            used += n;
            let size = 1usize << log;
            if *n > 0 && used > size / 2 {
                array = size;
                array_used = used;
            }
        }
        let mut hash = total - array_used;
        let adjusted = self.adjust_array(array, key.array_index());
        let extra = adjusted - array;
        if extra > 0 {
            hash = hash.saturating_sub(extra);
            array = self.adjust_array(adjusted + extra, key.array_index());
        }
        self.resize(array, hash);
    }
    fn resize(&mut self, array: usize, hash: usize) {
        let old = std::mem::replace(self, Self::new(array, hash));
        for i in 0..old.array.len().min(array) {
            self.array[i] = old.array[i];
        }
        for i in array..old.array.len() {
            if old.array[i] {
                self.write(Key::number((i + 1) as f64), true);
            }
        }
        for node in old.nodes.into_iter().rev() {
            if node.live {
                if let Some(key) = node.key {
                    self.write(key, true);
                }
            }
        }
    }
    pub fn resize_array(&mut self, size: usize) {
        let size = self.adjust_array(size, None);
        self.resize(size, self.nodes.len());
    }
    pub fn write(&mut self, key: Key, live: bool) {
        loop {
            if let Some(i) = key.array_index().filter(|&i| i <= self.array.len()) {
                self.array[i - 1] = live;
                return;
            }
            if let Some(i) = self.find_hash(&key) {
                self.nodes[i].live = live;
                return;
            }
            if key.array_index() == Some(self.array.len() + 1) || self.nodes.is_empty() {
                self.rehash(&key);
                continue;
            }
            let mut mp = self.main(&key);
            if self.nodes[mp].live {
                let free = loop {
                    if self.last_free == 0 {
                        break None;
                    }
                    self.last_free -= 1;
                    if self.nodes[self.last_free].key.is_none() {
                        break Some(self.last_free);
                    }
                };
                let Some(free) = free else {
                    self.rehash(&key);
                    continue;
                };
                if let Some(old_key) = &self.nodes[mp].key {
                    let other = self.main(old_key);
                    if other != mp {
                        let mut prev = other;
                        while let Some(next) = self.nodes[prev].next {
                            if next == mp {
                                break;
                            }
                            prev = next;
                        }
                        self.nodes[prev].next = Some(free);
                        self.nodes[free] = self.nodes[mp].clone();
                        self.nodes[mp].next = None;
                    } else {
                        self.nodes[free].next = self.nodes[mp].next;
                        self.nodes[mp].next = Some(free);
                        mp = free;
                    }
                }
            }
            self.nodes[mp].key = Some(key);
            self.nodes[mp].live = live;
            return;
        }
    }
    pub fn clear(&mut self) {
        self.array.fill(false);
        self.nodes.fill(Node::default());
        self.last_free = self.nodes.len();
        self.boundary = None;
    }
    pub fn next(&self, key: Option<&Key>) -> Result<Option<Key>, ()> {
        let start = match key {
            None => 0,
            Some(key) => {
                if let Some(i) = key.array_index().filter(|&i| i <= self.array.len()) {
                    i
                } else {
                    self.array.len() + self.find_hash(key).ok_or(())? + 1
                }
            }
        };
        for i in start..self.array.len() {
            if self.array[i] {
                return Ok(Some(Key::number((i + 1) as f64)));
            }
        }
        for node in self
            .nodes
            .iter()
            .skip(start.saturating_sub(self.array.len()))
        {
            if node.live {
                return Ok(node.key.clone());
            }
        }
        Ok(None)
    }
    pub fn length(&mut self) -> usize {
        let size = self.array.len();
        let at = |i: usize| i > 0 && self.array.get(i - 1).copied().unwrap_or(false);
        // Luau overlays lastfree and the negated cached boundary in one union.
        let b = if self.last_free == 0 {
            self.boundary.unwrap_or(size)
        } else {
            size
        };
        if b > 0 {
            if at(size) && self.nodes.is_empty() {
                return size;
            }
            if b < size && at(b) && !at(b + 1) {
                return b;
            }
            if b < size && !at(b) && b >= 2 && at(b - 1) {
                if self.last_free == 0 {
                    self.boundary = Some(b - 1);
                }
                return b - 1;
            }
            if b + 1 < size && at(b + 1) && !at(b + 2) {
                if self.last_free == 0 {
                    self.boundary = Some(b + 1);
                }
                return b + 1;
            }
        }
        if size > 0 && !at(size) {
            let (mut base, mut rest) = (0usize, size);
            while rest >> 1 > 0 {
                let half = rest >> 1;
                if at(base + half + 1) {
                    base += half;
                }
                rest -= half;
            }
            let result = base + usize::from(at(base + 1));
            if self.last_free == 0 {
                self.boundary = (result > 0).then_some(result);
            }
            result
        } else {
            size
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allocated_nil_slots_are_continuation_keys() {
        let mut layout = Layout::new(3, 0);
        assert_eq!(layout.next(Some(&Key::number(3.0))), Ok(None));
        assert!(layout.next(Some(&Key::number(4.0))).is_err());
        layout.write(Key::number(1.0), true);
        layout.clear();
        assert_eq!(layout.next(Some(&Key::number(3.0))), Ok(None));
        let mut empty = Layout::default();
        empty.write(Key::number(1.0), false);
        empty.clear();
        assert_eq!(empty.next(Some(&Key::number(1.0))), Ok(None));
    }

    #[test]
    fn deletion_survives_until_hash_reuse_or_rehash() {
        let a = Key::String(b"a".to_vec());
        let b = Key::String(b"b".to_vec());
        let mut layout = Layout::new(0, 1);
        layout.write(a.clone(), true);
        layout.write(a.clone(), false);
        assert_eq!(layout.next(Some(&a)), Ok(None));
        layout.write(b, true);
        assert!(layout.next(Some(&a)).is_err());
    }

    #[test]
    fn growth_and_clone_preserve_physical_allocation() {
        let mut layout = Layout::new(3, 0);
        for i in 1..=5 {
            layout.write(Key::number(i as f64), true);
        }
        assert_eq!(layout.array_size(), 8);
        let mut copy = layout.clone();
        copy.clear();
        assert_eq!(copy.next(Some(&Key::number(8.0))), Ok(None));
        assert_eq!(
            layout.next(Some(&Key::number(4.0))),
            Ok(Some(Key::number(5.0)))
        );
    }

    #[test]
    fn create_sizes_match_truncation_and_limits() {
        assert_eq!(create_size(3.8).unwrap(), 3);
        assert_eq!(create_size(-0.5).unwrap(), 0);
        for n in [-1.0, f64::INFINITY, f64::NAN, 1e30] {
            assert!(create_size(n).is_err());
        }
        assert_eq!(
            create_size(67108865.0).unwrap_err().msg.to_string_lossy(),
            "table overflow"
        );
    }

    #[test]
    fn dynamic_array_nil_slots_use_the_luau_boundary_and_iteration_order() {
        use crate::{Arr, Value};
        let a = Arr::from_vec(vec![
            Value::Num(1.0),
            Value::Nil,
            Value::Num(3.0),
            Value::Nil,
            Value::Num(5.0),
            Value::Nil,
        ]);
        assert_eq!(a.len(), 1.0);
        assert_eq!(a.slot_count(), 6);
        assert!(a.get_at(1).is_none());
        assert_eq!(a.next_entry(Some(1.0)).unwrap().0, Some(3.0));
        crate::stdlib::table_sort(&a, |x, y| Ok(x.as_num()? < y.as_num()?)).unwrap();
        assert_eq!(a.get(3.0).unwrap().as_num().unwrap(), 3.0);
        a.set(5.0, Value::Nil).unwrap();
        a.push(Value::Num(9.0));
        a.push(Value::Nil);
        a.push(Value::Num(7.0));
        assert_eq!(a.len(), 4.0);
        a.insert_at(2.0, Value::Num(8.0)).unwrap();
        assert_eq!(a.len(), 5.0);
        assert_eq!(a.remove_at(3.0).unwrap().unwrap().as_num().unwrap(), 9.0);
        assert_eq!(a.pop().unwrap().as_num().unwrap(), 7.0);
        assert_eq!(a.len(), 3.0);
        crate::stdlib::table_sort(&a, |x, y| Ok(x.as_num()? < y.as_num()?)).unwrap();
        assert_eq!(a.get(3.0).unwrap().as_num().unwrap(), 8.0);
        let b = a.shallow_clone();
        b.set_opt(3.0, None).unwrap();
        assert_eq!(b.len(), 2.0);
        assert_eq!(a.len(), 3.0);
        b.clear();
        assert_eq!(b.len(), 0.0);
        assert!(b.next_entry(Some(6.0)).unwrap().0.is_none());
        let filled = Arr::filled(3.0, Value::Nil).unwrap();
        assert_eq!(filled.len(), 0.0);
        assert_eq!(filled.slot_count(), 3);
        assert!(filled.next_entry(Some(3.0)).unwrap().0.is_none());
        let pack = Arr::from_vec(vec![Some(Value::Num(1.0)), None]);
        assert_eq!(pack.len(), 2.0);
        assert!(matches!(pack.get_at(1), Some(None)));
        let outside = Arr::from_vec(vec![Value::Num(1.0), Value::Nil, Value::Num(3.0)]);
        for position in [0.0, -1.0, 0.9, -0.9, 99.0, 99.9, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert!(outside.remove_at(position).unwrap().is_none());
            assert_eq!(outside.len(), 3.0);
            assert_eq!(outside.get(3.0).unwrap().as_num().unwrap(), 3.0);
        }
        assert_eq!(outside.remove_at(1.9).unwrap().unwrap().as_num().unwrap(), 1.0);
        assert!(outside.get(1.0).is_none());
        assert_eq!(outside.get(2.0).unwrap().as_num().unwrap(), 3.0);
    }

    #[test]
    fn dynamic_map_nil_deletes_values_without_forgetting_key_slots() {
        use crate::{LMap, LStr, Value};
        let map: LMap<LStr, Value> = LMap::with_layout(0, 2);
        map.set("a".into(), Value::Num(1.0));
        map.set("b".into(), Value::Nil);
        assert_eq!(map.count(), 1);
        assert!(map.get(&"b".into()).is_none());
        assert!(map.next_entry(Some("b".into())).is_ok());
        map.set("a".into(), Value::Nil);
        assert!(map.keys().is_empty());
        let copy = map.shallow_clone();
        assert!(copy.next_entry(Some("a".into())).is_ok());
        copy.clear();
        assert!(copy.next_entry(Some("a".into())).is_err());
    }
}
