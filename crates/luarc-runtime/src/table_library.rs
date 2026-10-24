//! Runtime table libraries for selectively promoted tables.
use crate::dynamic::FromValue;
use crate::{LResult, LStr, LuaError, LuaType, Table, Value};

fn table_arg(args: &[Value], i: usize, name: &str) -> LResult<Table> {
    match args.get(i) {
        Some(v) => Table::from_value(v).ok_or_else(|| LuaError::new(format!("invalid argument #{} to '{name}' (table expected, got {})", i + 1, v.lua_type()))),
        None => Err(LuaError::new(format!("missing argument #{} to '{name}' (table expected)", i + 1))),
    }
}

fn number_arg(args: &[Value], i: usize, name: &str) -> LResult<f64> {
    match args.get(i) {
        Some(Value::Num(n)) => Ok(*n),
        Some(Value::Str(s)) => crate::stdlib::tonumber(s).ok_or_else(|| LuaError::new(format!("invalid argument #{} to '{name}' (number expected, got string)", i + 1))),
        Some(v) => Err(LuaError::new(format!("invalid argument #{} to '{name}' (number expected, got {})", i + 1, v.lua_type()))),
        None => Err(LuaError::new(format!("missing argument #{} to '{name}' (number expected)", i + 1))),
    }
}

pub fn freeze(args: &[Value]) -> LResult<Table> {
    table_arg(args, 0, "freeze")?.freeze()
}
pub fn is_frozen(args: &[Value]) -> LResult<bool> {
    Ok(table_arg(args, 0, "isfrozen")?.is_frozen())
}

/// Luau move is a raw copy; overlap chooses the direction and nil deletes slots.
pub fn move_(args: &[Value]) -> LResult<Table> {
    let source = table_arg(args, 0, "move")?;
    let first = crate::stdlib::check_int(number_arg(args, 1, "move")?) as i64;
    let last = crate::stdlib::check_int(number_arg(args, 2, "move")?) as i64;
    let target = crate::stdlib::check_int(number_arg(args, 3, "move")?) as i64;
    let destination = match args.get(4) {
        None | Some(Value::Nil) => source.clone(),
        _ => table_arg(args, 4, "move")?,
    };
    if last < first { return Ok(destination); }
    let count = last - first + 1;
    if count > i32::MAX as i64 {
        return Err(LuaError::new("invalid argument #3 to 'move' (too many elements to move)"));
    }
    if target + count - 1 > i32::MAX as i64 {
        return Err(LuaError::new("invalid argument #4 to 'move' (destination wrap around)"));
    }
    // Luau's library reserves the whole contiguous destination range first.
    // This affects later length/next operations even when copied slots are nil.
    let end = target + count - 1;
    let capacity = destination.array_capacity() as i64;
    if end > capacity && target <= capacity + 1 {
        destination.resize_array(end as usize)?;
    }
    if source.ptr_eq(&destination) && target > first && target <= last {
        for offset in (0..count).rev() {
            let value = source.raw_get(&Value::Num((first + offset) as f64));
            destination.raw_set(Value::Num((target + offset) as f64), value)?;
        }
    } else {
        for offset in 0..count {
            let value = source.raw_get(&Value::Num((first + offset) as f64));
            destination.raw_set(Value::Num((target + offset) as f64), value)?;
        }
    }
    Ok(destination)
}

/// Luau insert shifts only positive positions within the current sequence.
pub fn insert(args: &[Value]) -> LResult<()> {
    let table = table_arg(args, 0, "insert")?;
    if table.is_frozen() {
        return Err(LuaError::located("attempt to modify a readonly table"));
    }
    let (position, value) = match args.len() {
        2 => (table.raw_len()? as i64 + 1, args[1].clone()),
        3 => (crate::stdlib::check_int(number_arg(args, 1, "insert")?) as i64, args[2].clone()),
        _ => return Err(LuaError::new("wrong number of arguments to 'insert'")),
    };
    if position > 0 {
        let length = table.raw_len()? as i64;
        for i in (position..=length).rev() {
            let value = table.raw_get(&Value::Num(i as f64));
            table.raw_set(Value::Num((i + 1) as f64), value)?;
        }
    }
    table.raw_set(Value::Num(position as f64), value)
}

/// Concat reads raw values; explicit bounds require no length of a sparse table.
pub fn concat(args: &[Value]) -> LResult<LStr> {
    let table = table_arg(args, 0, "concat")?;
    let separator = match args.get(1) {
        None | Some(Value::Nil) => LStr::from(""),
        _ => crate::library::string_arg(args, 1, "concat")?,
    };
    let first = match args.get(2) {
        None | Some(Value::Nil) => 1,
        _ => crate::stdlib::check_int(number_arg(args, 2, "concat")?) as i64,
    };
    let last = match args.get(3) {
        None | Some(Value::Nil) => table.raw_len()? as i64,
        _ => crate::stdlib::check_int(number_arg(args, 3, "concat")?) as i64,
    };
    let mut out = Vec::new();
    for i in first..=last {
        let value = table.raw_get(&Value::Num(i as f64));
        let part = match value {
            Value::Str(s) => s,
            Value::Num(n) => crate::show::tostring(&n),
            value => return Err(LuaError::new(format!("invalid value ({}) at index {i} in table for 'concat'", value.lua_type()))),
        };
        let extra = if i == first { 0 } else { separator.as_bytes().len() };
        out.try_reserve(extra + part.as_bytes().len()).map_err(|_| LuaError::new("not enough memory"))?;
        if i != first { out.extend_from_slice(separator.as_bytes()); }
        out.extend_from_slice(part.as_bytes());
    }
    Ok(LStr::from_vec(out))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dynamic::ToValue;
    fn n(x: f64) -> Value { Value::Num(x) }
    fn array(xs: &[f64]) -> Table {
        Table::from_entries(xs.iter().enumerate().map(|(i, v)| (n((i + 1) as f64), n(*v))).collect()).unwrap()
    }
    #[test]
    fn move_overlaps_and_preserves_sparse_nil_slots() {
        let t = array(&[10.0, 20.0, 30.0]);
        let moved = move_(&[t.clone().to_value(), n(1.0), n(2.0), n(2.0)]).unwrap();
        assert!(moved.ptr_eq(&t));
        assert_eq!(t.raw_get(&n(2.0)).as_num().unwrap(), 10.0);
        assert_eq!(t.raw_get(&n(3.0)).as_num().unwrap(), 20.0);
        let destination = Table::new();
        move_(&[t.clone().to_value(), n(1.0), n(3.0), n(-2.0), destination.clone().to_value()]).unwrap();
        assert_eq!(destination.raw_get(&n(-2.0)).as_num().unwrap(), 10.0);
        assert_eq!(destination.raw_get(&n(0.0)).as_num().unwrap(), 20.0);
        t.raw_set(n(2.0), Value::Nil).unwrap();
        move_(&[t.to_value(), n(1.0), n(3.0), n(1.0), destination.clone().to_value()]).unwrap();
        assert!(destination.raw_get(&n(2.0)).is_nil());
        assert_eq!(destination.raw_get(&n(3.0)).as_num().unwrap(), 20.0);
    }
    #[test]
    fn move_reserves_nil_slots_before_raw_copy() {
        let source = Table::create(3.0, Value::Nil).unwrap();
        source.raw_set(n(3.0), n(33.0)).unwrap();
        let target = Table::new();
        move_(&[source.clone().to_value(), n(1.0), n(3.0), n(1.0), target.clone().to_value()]).unwrap();
        assert_eq!(target.array_capacity(), 3);
        assert_eq!(target.raw_len().unwrap(), 3.0);
        let (key, value) = target.next_entry(n(2.0)).unwrap();
        assert_eq!(key.as_num().unwrap(), 3.0);
        assert_eq!(value.as_num().unwrap(), 33.0);
        let empty = Table::new();
        move_(&[source.to_value(), n(1.0), n(2.0), n(1.0), empty.clone().to_value()]).unwrap();
        assert_eq!(empty.array_capacity(), 2);
        assert_eq!(empty.raw_len().unwrap(), 0.0);
        assert!(empty.next_entry(n(1.0)).unwrap().0.is_nil());
    }
    #[test]
    fn frozen_tables_and_move_validation_order() {
        let t = array(&[4.0, 5.0]);
        let args = [t.clone().to_value()];
        assert!(!is_frozen(&args).unwrap());
        assert!(freeze(&args).unwrap().ptr_eq(&t));
        assert!(is_frozen(&args).unwrap());
        assert_eq!(freeze(&args).err().unwrap().msg.to_string_lossy(), "invalid argument #1 to 'freeze' (table is already frozen)");
        assert!(move_(&[t.clone().to_value(), n(2.0), n(1.0), n(1.0)]).is_ok());
        assert_eq!(move_(&[t.clone().to_value(), n(1.0), n(2.0), n(2147483647.0)]).err().unwrap().msg.to_string_lossy(), "invalid argument #4 to 'move' (destination wrap around)");
        assert_eq!(move_(&[t.clone().to_value(), n(-2147483648.0), n(2147483647.0), n(1.0)]).err().unwrap().msg.to_string_lossy(), "invalid argument #3 to 'move' (too many elements to move)");
        assert_eq!(move_(&[t.to_value(), n(1.0), n(1.0), n(1.0)]).err().unwrap().with_loc("caller").msg.to_string_lossy(), "attempt to modify a readonly table");
    }
    #[test]
    fn insert_and_explicit_concat_follow_raw_storage() {
        let t = array(&[10.0, 20.0]);
        insert(&[t.clone().to_value(), n(1.0), n(30.0)]).unwrap();
        let text = concat(&[t.clone().to_value(), Value::Str(",".into()), n(1.0), n(3.0)]).unwrap();
        assert_eq!(text.to_string_lossy(), "30,10,20");
        insert(&[t.clone().to_value(), n(0.0), n(40.0)]).unwrap();
        assert_eq!(t.raw_get(&n(0.0)).as_num().unwrap(), 40.0);
        insert(&[t.clone().to_value(), n(5.0), n(50.0)]).unwrap();
        assert!(t.raw_get(&n(4.0)).is_nil());
        assert_eq!(t.raw_get(&n(5.0)).as_num().unwrap(), 50.0);
        assert_eq!(concat(&[t.clone().to_value(), Value::Str(",".into()), n(1.0), n(5.0)]).err().unwrap().msg.to_string_lossy(), "invalid value (nil) at index 4 in table for 'concat'");
        t.freeze().unwrap();
        assert_eq!(insert(&[t.to_value(), Value::Bool(false), n(7.0)]).err().unwrap().msg.to_string_lossy(), "attempt to modify a readonly table");
    }
}
