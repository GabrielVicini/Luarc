//! Allocation-history differential coverage against pinned Luau 0.743.
//! This directly exercises runtime storage, independently of source lowering.

use luarc_runtime::{dynamic::Value, table::Table, table_layout::Key, Arr, LMap, NumKey};
use std::{fmt::Write, path::PathBuf, process::Command};

fn value(v: &Value) -> String {
    match v {
        Value::Nil => "nil".into(),
        Value::Bool(v) => v.to_string(),
        Value::Num(v) => luarc_runtime::show::num_to_string(*v),
        Value::Str(v) => v.to_string_lossy(),
        _ => "object".into(),
    }
}
fn literal(v: &Value) -> String {
    match v {
        Value::Str(v) => format!("{:?}", v.to_string_lossy()),
        _ => value(v),
    }
}
fn keys() -> Vec<Value> {
    let mut keys = vec![
        Value::Nil,
        Value::Num(-1.0),
        Value::Num(0.0),
        Value::Num(-0.0),
        Value::Num(0.5),
    ];
    keys.extend((1..=20).map(|i| Value::Num(i as f64)));
    keys.extend([
        Value::Str("a".into()),
        Value::Str("b".into()),
        Value::Str("c".into()),
        Value::Str("d".into()),
        Value::Bool(false),
        Value::Bool(true),
    ]);
    keys
}
struct Probe {
    lua: String,
    expected: String,
    table: Table,
}
impl Probe {
    fn new() -> Self {
        Self {
            lua: "local t\nlocal function show(k) local ok,a,b=pcall(next,t,k); if ok then print('next',k,a,b) else print('next',k,'invalid') end end\n".into(),
            expected: String::new(), table: Table::new(),
        }
    }
    fn create(&mut self, n: usize) {
        writeln!(self.lua, "t=table.create({n})").unwrap();
        self.table = Table::create(n as f64, Value::Nil).unwrap();
    }
    fn set(&mut self, key: Value, val: Value) {
        writeln!(self.lua, "rawset(t,{},{})", literal(&key), literal(&val)).unwrap();
        self.table.raw_set(key, val).unwrap();
    }
    fn snapshot(&mut self) {
        self.lua.push_str("print('len',#t)\n");
        writeln!(self.expected, "len\t{}", self.table.raw_len().unwrap()).unwrap();
        for key in keys() {
            writeln!(self.lua, "show({})", literal(&key)).unwrap();
            match self.table.next_entry(key.clone()) {
                Ok((k, v)) => writeln!(
                    self.expected,
                    "next\t{}\t{}\t{}",
                    value(&key),
                    value(&k),
                    value(&v)
                )
                .unwrap(),
                Err(_) => writeln!(self.expected, "next\t{}\tinvalid", value(&key)).unwrap(),
            }
        }
    }
    fn clear(&mut self) {
        self.lua.push_str("table.clear(t)\n");
        self.table.clear().unwrap();
    }
    fn clone_(&mut self) {
        self.lua.push_str("t=table.clone(t)\n");
        self.table = self.table.shallow_clone();
    }
    fn insert(&mut self, n: usize) {
        writeln!(self.lua, "table.insert(t,{n})").unwrap();
        let at = self.table.raw_len().unwrap() + 1.0;
        self.table
            .raw_set(Value::Num(at), Value::Num(n as f64))
            .unwrap();
    }
    fn remove(&mut self) {
        self.lua.push_str("table.remove(t)\n");
        let at = self.table.raw_len().unwrap();
        if at >= 1.0 {
            self.table.raw_set(Value::Num(at), Value::Nil).unwrap();
        }
    }
    fn move_(&mut self, from: usize, to: usize, count: usize) {
        writeln!(self.lua, "table.move(t,{from},{},{to})", from + count - 1).unwrap();
        if to + count - 1 > self.table.array_capacity() && to <= self.table.array_capacity() + 1 {
            self.table.resize_array(to + count - 1).unwrap();
        }
        let values: Vec<_> = (from..from + count)
            .map(|i| self.table.raw_get(&Value::Num(i as f64)))
            .collect();
        for (offset, v) in values.into_iter().enumerate() {
            self.table
                .raw_set(Value::Num((to + offset) as f64), v)
                .unwrap();
        }
    }
}

#[test]
fn allocation_history_matches_luau() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let exe = std::env::var_os("LUARC_LUAU_REF")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            root.join("LuaUCompare")
                .join(format!("luau{}", std::env::consts::EXE_SUFFIX))
        });
    if !exe.is_file() {
        eprintln!("SKIP allocation_history_matches_luau: Luau 0.743 unavailable");
        return;
    }
    let mut p = Probe::new();
    for values in [
        [None, None, None, None, None, None],
        [Some(1), None, Some(3), None, Some(5), None],
    ] {
        let entries: Vec<_> = (b'a'..=b'f')
            .zip(values)
            .map(|(k, v)| {
                (
                    Value::Str(char::from(k).to_string().into()),
                    v.map_or(Value::Nil, |v| Value::Num(v as f64)),
                )
            })
            .collect();
        p.lua.push_str("t={");
        for (key, value) in &entries {
            write!(
                p.lua,
                "{}={},",
                match key {
                    Value::Str(s) => s.to_string_lossy(),
                    _ => unreachable!(),
                },
                literal(value)
            )
            .unwrap();
        }
        p.lua.push_str("}\n");
        p.table = Table::from_record_entries(entries).unwrap();
        p.snapshot();
        p.clone_();
        p.snapshot();
        p.clear();
        p.snapshot();
    }
    for size in [0, 1, 2, 3, 5, 8, 13] {
        p.create(size);
        p.snapshot();
        p.set(Value::Num(1.0), Value::Nil);
        p.snapshot();
        p.clear();
        p.snapshot();
        for i in 1..=11 {
            p.set(Value::Num(i as f64), Value::Num(i as f64));
            if i <= 5 || i == 11 {
                p.snapshot();
            }
        }
        p.clone_();
        p.snapshot();
        p.remove();
        p.snapshot();
        p.clear();
        p.snapshot();
        for i in 1..=7 {
            p.insert(i);
            p.snapshot();
        }
        p.move_(2, 6, 3);
        p.snapshot();
        p.move_(1, 2, 5);
        p.snapshot();
        p.clear();
        p.snapshot();
    }
    // Deleted and nil-only hash keys may survive collisions, but rehash drops them.
    p.create(0);
    for (key, val) in [
        (Value::Str("a".into()), Value::Num(1.0)),
        (Value::Str("b".into()), Value::Num(2.0)),
        (Value::Str("a".into()), Value::Nil),
        (Value::Str("c".into()), Value::Num(3.0)),
        (Value::Bool(false), Value::Num(4.0)),
        (Value::Str("d".into()), Value::Nil),
        (Value::Num(17.0), Value::Num(17.0)),
        (Value::Num(0.5), Value::Num(9.0)),
        (Value::Bool(true), Value::Num(5.0)),
        (Value::Str("b".into()), Value::Nil),
    ] {
        p.set(key, val);
        p.snapshot();
    }
    p.clone_();
    p.snapshot();
    p.clear();
    p.snapshot();
    let mut seed = 0x7634_1u32;
    for size in [0, 3, 13] {
        p.create(size);
        for i in 0..200 {
            seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
            let key = match seed % 7 {
                0 => Value::Bool(seed & 8 != 0),
                1 => Value::Str(format!("field{}", seed % 17).into()),
                2 => Value::Str(
                    format!("long_field_abcdefghijklmnopqrstuvwxyz_{}", seed % 17).into(),
                ),
                _ => Value::Num((seed % 35) as f64 - 3.0),
            };
            p.set(
                key,
                if seed & 16 != 0 {
                    Value::Nil
                } else {
                    Value::Num(i as f64)
                },
            );
            if i % 17 == 0 {
                p.clone_();
            }
            if i % 37 == 0 {
                p.clear();
            }
            p.snapshot();
        }
    }
    // Dense wrappers retain allocation after removal/clear/clone independently of Vec capacity.
    let a = Arr::with_layout(3, 0);
    for i in 1..=3 {
        a.set(i as f64, i).unwrap();
    }
    assert!(a.next_entry(Some(4.0)).is_err());
    a.push(4);
    a.push(5);
    assert!(a.next_entry(Some(8.0)).unwrap().0.is_none());
    a.pop();
    let a = a.shallow_clone();
    a.clear();
    assert!(a.next_entry(Some(8.0)).unwrap().0.is_none());
    let empty: Arr<f64> = Arr::new();
    empty.set_opt(100.0, None).unwrap();
    empty.replace_all(Vec::new());
    assert!(empty.next_entry(Some(100.0)).unwrap().0.is_none());
    p.lua
        .push_str("t=table.create(0); t[100]=nil; table.sort(t); show(100)\n");
    p.expected.push_str("next\t100\tnil\tnil\n");
    let map: LMap<NumKey, i32> = LMap::with_layout(3, 0);
    for i in 1..=3 {
        map.set(NumKey::new(i as f64).unwrap(), i);
    }
    assert!(map.next_entry(Some(NumKey::new(4.0).unwrap())).is_err());
    map.remove(&NumKey::new(3.0).unwrap());
    map.clear();
    assert!(map
        .next_entry(Some(NumKey::new(3.0).unwrap()))
        .unwrap()
        .0
        .is_none());
    assert!(Table::new().next_entry(Value::Num(f64::NAN)).is_err());
    assert_eq!(Key::number(-0.0), Key::number(0.0));
    let scratch = root.join("target/table-layout-oracle");
    std::fs::create_dir_all(&scratch).unwrap();
    let file = scratch.join("layout.luau");
    std::fs::write(&file, &p.lua).unwrap();
    std::fs::write(scratch.join("runtime.out"), &p.expected).unwrap();
    let output = Command::new(exe).arg(&file).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n");
    std::fs::write(scratch.join("oracle.out"), &actual).unwrap();
    if actual != p.expected {
        let a: Vec<_> = actual.lines().collect();
        let b: Vec<_> = p.expected.lines().collect();
        let i = a
            .iter()
            .zip(&b)
            .position(|(a, b)| a != b)
            .unwrap_or(a.len().min(b.len()));
        panic!("allocation history differs at line {}: oracle {:?}, runtime {:?}; inspect target/table-layout-oracle",i+1,a.get(i),b.get(i));
    }
}
