//! Differential tests against the pinned Luau reference implementation.
//!
//! Reference: Luau 0.743 standalone `luau.exe` (`LuaUCompare/luau.exe`; override
//! with `LUARC_LUAU_REF=<path>`). The binaries are
//! not checked in: when the reference is missing these tests print `SKIP` and pass,
//! so a green run without it proves nothing about Luau compatibility.
//!
//! * `luau_differential`: every program in `tests/diff/` uses only semantics LUARC
//!   shares with Luau. It runs under luarc (debug and release builds) and under
//!   Luau; stdout and exit status must be identical.
//! * `luau_differential_generated`: seeded random expression programs (numbers,
//!   comparisons, logic, strings, side-effect traces). Seeds come from
//!   `tests/diff/seeds.txt` plus `LUARC_DIFF_SEED` when set; a failing seed is
//!   printed so it can be added there and minimized into `tests/diff/`.
//!
//! Normalization (host differences, not semantics): Luau names a chunk `./file`
//! where luarc uses `file`. Number printing is a documented divergence (LUARC
//! prints decimal exponents outside −5…16 in scientific form, Luau does not), so
//! generated programs print numbers through `show`, which only uses `tostring`
//! inside the range both agree on.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn repo() -> PathBuf {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..");
    let c = fs::canonicalize(&p).unwrap();
    let s = c.to_string_lossy().to_string();
    match s.strip_prefix(r"\\?\") {
        Some(r) => PathBuf::from(r),
        None => c,
    }
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).replace("\r\n", "\n")
}

fn luau_ref() -> Option<PathBuf> {
    let p = match std::env::var_os("LUARC_LUAU_REF") {
        Some(p) => PathBuf::from(p),
        None => repo().join("LuaUCompare").join(format!("luau{}", std::env::consts::EXE_SUFFIX)),
    };
    p.is_file().then_some(p)
}

fn luarc(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_luarc")).args(args).current_dir(dir).output().expect("run luarc")
}

struct Run {
    stdout: String,
    stderr: String,
    exit: Option<i32>,
}

fn run_luau(exe: &Path, file: &Path) -> Run {
    let dir = file.parent().unwrap();
    let name = file.file_name().unwrap().to_string_lossy().to_string();
    let out = Command::new(exe).arg(&name).current_dir(dir).output().expect("run luau");
    Run {
        stdout: text(&out.stdout).replace(&format!("./{name}:"), &format!("{name}:")),
        stderr: text(&out.stderr),
        exit: out.status.code(),
    }
}

fn run_luarc(file: &Path, release: bool) -> Run {
    let dir = file.parent().unwrap();
    let name = file.file_name().unwrap().to_string_lossy().to_string();
    let mut args = vec!["run", name.as_str()];
    if release {
        args.push("--release");
    }
    let out = luarc(dir, &args);
    Run { stdout: text(&out.stdout), stderr: text(&out.stderr), exit: out.status.code() }
}

/// Compares one program; returns a readable report on mismatch.
fn compare(exe: &Path, file: &Path, release: bool) -> Result<(), String> {
    let r = run_luau(exe, file);
    let l = run_luarc(file, release);
    let name = file.file_name().unwrap().to_string_lossy();
    let mode = if release { "release" } else { "debug" };
    // Generated Rust must compile without warnings.
    if l.stderr.contains("warning in generated code") {
        return Err(format!("{name} ({mode}): generated Rust produced warnings\n{}", l.stderr.trim_end()));
    }
    if r.stdout == l.stdout && r.exit == l.exit {
        return Ok(());
    }
    let (ra, la): (Vec<&str>, Vec<&str>) = (r.stdout.lines().collect(), l.stdout.lines().collect());
    let first = (0..ra.len().max(la.len())).find(|&i| ra.get(i) != la.get(i)).unwrap_or(0);
    Err(format!(
        "{name} ({mode}): luau exit {:?}, luarc exit {:?}\nfirst differing line {}:\n  luau : {:?}\n  luarc: {:?}\n--- luarc stderr\n{}\n--- luau stderr\n{}",
        r.exit,
        l.exit,
        first + 1,
        ra.get(first),
        la.get(first),
        l.stderr.trim_end(),
        r.stderr.trim_end()
    ))
}

fn collect(results: Vec<Result<(), String>>) {
    let failures: Vec<String> = results.into_iter().filter_map(|r| r.err()).collect();
    if !failures.is_empty() {
        panic!("{} failure(s):\n\n{}", failures.len(), failures.join("\n\n"));
    }
}

#[test]
fn luau_differential() {
    let Some(exe) = luau_ref() else {
        eprintln!("SKIP luau_differential: Luau reference not found (set LUARC_LUAU_REF)");
        return;
    };
    let dir = repo().join("tests").join("diff");
    let mut files: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().map(|e| e == "luarc").unwrap_or(false))
        .collect();
    files.sort();
    assert!(!files.is_empty());
    let mut results = Vec::new();
    for f in &files {
        results.push(compare(&exe, f, false));
        results.push(compare(&exe, f, true));
    }
    collect(results);
}

// Generated Programs

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.below(xs.len())]
    }
}

const NUM_LITS: &[&str] = &["0", "1", "2", "3", "-1", "0.5", "2.5", "7", "10", "-3.25", "1e3", "0.1", "0x10", "1_000", "(-0)"];
const NUM_VARS: &[&str] = &["a", "b", "c", "z"];
const STR_LITS: &[&str] = &["\"\"", "\"a\"", "\"abc\"", "\"Hello\"", "\"a\\0b\"", "\"\\xff\"", "\"zz\"", "s1", "s2"];

/// Numeric expression. `t(x)` records `x` in the trace and returns it.
fn num_expr(r: &mut Rng, depth: u32) -> String {
    if depth == 0 {
        return match r.below(5) {
            0 | 1 => r.pick(NUM_LITS).to_string(),
            2 | 3 => r.pick(NUM_VARS).to_string(),
            _ => format!("t({})", r.pick(NUM_LITS)),
        };
    }
    match r.below(12) {
        0..=5 => {
            let op = r.pick(&["+", "-", "*", "/", "//", "%", "^", "+", "-", "*"]);
            format!("{} {op} {}", num_expr(r, depth - 1), num_expr(r, depth - 1))
        }
        6 => format!("-({})", num_expr(r, depth - 1)),
        7 => format!("({})", num_expr(r, depth - 1)),
        8 => format!("(if {} then {} else {})", bool_expr(r, depth - 1), num_expr(r, depth - 1), num_expr(r, depth - 1)),
        9 => format!("(#({}))", str_expr(r, depth - 1)),
        10 => format!("t({})", num_expr(r, depth - 1)),
        _ => {
            let f = r.pick(&["math.floor", "math.ceil", "math.abs", "math.sqrt"]);
            format!("{f}({})", num_expr(r, depth - 1))
        }
    }
}

fn bool_expr(r: &mut Rng, depth: u32) -> String {
    if depth == 0 {
        return r.pick(&["true", "false", "p", "q"]).to_string();
    }
    match r.below(8) {
        0 | 1 => {
            let op = r.pick(&["<", "<=", ">", ">=", "==", "~="]);
            format!("{} {op} {}", num_expr(r, depth - 1), num_expr(r, depth - 1))
        }
        2 => {
            let op = r.pick(&["<", "<=", ">", ">=", "==", "~="]);
            format!("{} {op} {}", str_expr(r, depth - 1), str_expr(r, depth - 1))
        }
        3 | 4 => {
            let op = r.pick(&["and", "or"]);
            format!("{} {op} {}", bool_expr(r, depth - 1), bool_expr(r, depth - 1))
        }
        5 => format!("not ({})", bool_expr(r, depth - 1)),
        6 => format!("({})", bool_expr(r, depth - 1)),
        _ => format!("tb({})", bool_expr(r, depth - 1)),
    }
}

fn str_expr(r: &mut Rng, depth: u32) -> String {
    if depth == 0 {
        return r.pick(STR_LITS).to_string();
    }
    match r.below(9) {
        0 | 1 => format!("{} .. {}", str_expr(r, depth - 1), str_expr(r, depth - 1)),
        2 => format!("string.sub({}, {}, {})", str_expr(r, depth - 1), small_int(r), small_int(r)),
        3 => format!("string.upper({})", str_expr(r, depth - 1)),
        4 => format!("string.lower({})", str_expr(r, depth - 1)),
        5 => format!("string.rep({}, {})", str_expr(r, depth - 1), r.below(4)),
        6 => format!("({}):sub({})", str_expr(r, depth - 1), small_int(r)),
        7 => format!("(if {} then {} else {})", bool_expr(r, depth - 1), str_expr(r, depth - 1), str_expr(r, depth - 1)),
        _ => format!("ts({})", str_expr(r, depth - 1)),
    }
}

fn small_int(r: &mut Rng) -> String {
    r.pick(&["-5", "-2", "-1", "0", "1", "2", "3", "4", "10"]).to_string()
}

/// One generated program: prelude + `count` printed expressions.
fn program(seed: u64, count: usize) -> String {
    let mut r = Rng(seed.max(1));
    let mut src = String::from(
        "-- generated by differential.rs (seed SEED)\n\
         local trace = \"\"\n\
         local function t(x: number): number trace ..= \"n\" .. show0(x) .. \";\" return x end\n",
    )
    .replace("SEED", &seed.to_string());
    // `show` prints numbers only where LUARC and Luau agree on formatting.
    src = format!(
        "local function show0(x: number): string\n\
         \x20 if x ~= x then return \"nan\" end\n\
         \x20 local m = math.abs(x)\n\
         \x20 if m ~= 0 and m ~= math.huge and (m < 1e-4 or m >= 1e15) then return \"oor\" end\n\
         \x20 return tostring(x)\n\
         end\n{src}\
         local function tb(x: boolean): boolean trace ..= (if x then \"T;\" else \"F;\") return x end\n\
         local function ts(x: string): string trace ..= \"s\" .. #x .. \";\" return x end\n\
         local a, b, c, z = 3, -2.5, 0.25, 0\n\
         local p, q = true, false\n\
         local s1, s2 = \"x\\ty\", \"\\0\"\n"
    );
    for i in 0..count {
        let line = match r.below(3) {
            0 => format!("print({i}, show0({}), trace)", num_expr(&mut r, 3)),
            1 => format!("print({i}, {}, trace)", bool_expr(&mut r, 3)),
            _ => format!("print({i}, {}, trace)", str_expr(&mut r, 3)),
        };
        src.push_str(&format!("trace = \"\"\n{line}\n"));
    }
    src
}

fn seeds() -> Vec<u64> {
    let mut v = Vec::new();
    if let Ok(s) = fs::read_to_string(repo().join("tests").join("diff").join("seeds.txt")) {
        for l in s.lines() {
            let l = l.split('#').next().unwrap().trim();
            if let Ok(n) = l.parse() {
                v.push(n);
            }
        }
    }
    if let Ok(s) = std::env::var("LUARC_DIFF_SEED") {
        v.extend(s.split(',').filter_map(|x| x.trim().parse::<u64>().ok()));
    }
    v
}

#[test]
fn luau_differential_generated() {
    let Some(exe) = luau_ref() else {
        eprintln!("SKIP luau_differential_generated: Luau reference not found (set LUARC_LUAU_REF)");
        return;
    };
    let dir = std::env::temp_dir().join(format!("luarc-diffgen-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let mut results = Vec::new();
    for seed in seeds() {
        let file = dir.join(format!("gen_{seed}.luarc"));
        fs::write(&file, program(seed, 150)).unwrap();
        let check = luarc(&dir, &["check", &format!("gen_{seed}.luarc")]);
        if !check.status.success() {
            results.push(Err(format!("seed {seed}: generated program rejected by luarc check:\n{}", text(&check.stderr))));
            continue;
        }
        results.push(compare(&exe, &file, false).map_err(|e| format!("seed {seed}: {e}\nprogram kept at {}", file.display())));
        results.push(compare(&exe, &file, true).map_err(|e| format!("seed {seed}: {e}\nprogram kept at {}", file.display())));
    }
    let ok = results.iter().all(|r| r.is_ok());
    collect(results);
    if ok {
        let _ = fs::remove_dir_all(&dir);
    }
}
