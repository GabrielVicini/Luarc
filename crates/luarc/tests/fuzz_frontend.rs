//! Bounded, seeded robustness fuzzing of the compiler front end and code generator
//! (no Cargo builds). Inputs are mutations of every source program in the
//! repository's tests and examples (byte/token deletion, duplication, swaps,
//! truncation, insertion of syntax fragments). For every input the lexer, parser,
//! resolver, checker and (for accepted programs) the Rust generator must either
//! succeed or report diagnostics; a panic is a bug.
//!
//! The invariant is independent of luarc's own output: "no input crashes the
//! compiler". Seeds are fixed; a failure prints the seed and a minimized input.
//! `LUARC_FUZZ_ITERS` raises the per-file iteration count (default 40).

use std::fs;
use std::panic;
use std::path::{Path, PathBuf};

use luarc::check::{Checker, ModuleUnit};
use luarc::codegen::Gen;
use luarc::diag::SourceMap;
use luarc::parser::parse_module;
use luarc::resolve::{Resolution, Resolver};

fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
}

fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = fs::read_dir(dir) else { return };
    for e in rd.flatten() {
        let p = e.path();
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        if p.is_dir() && !name.starts_with('.') && name != "target" {
            sources(&p, out);
        } else if p.extension().map(|x| x == "luarc").unwrap_or(false) {
            out.push(p);
        }
    }
}

/// Runs the whole front end + codegen on one source text (single module; `require`
/// of other modules is left unresolved, native imports see an empty world).
fn compile(src: &str) {
    let mut id = 1;
    let Ok(module) = parse_module(0, src, &mut id) else { return };
    let mut sm = SourceMap::default();
    sm.add("f.luarc".into(), "f.luarc".into(), src.into());
    let mut res = Resolution::default();
    let pseudo = id;
    {
        let mut r = Resolver::new(&mut res);
        r.module(&module, pseudo);
        r.finish();
        if !r.errors.is_empty() {
            return;
        }
    }
    let units = vec![ModuleUnit { module, pseudo_func: pseudo, ident: "m0".into(), requires: Default::default(), rust_requires: Default::default() }];
    let world = luarc::native::world::World::default();
    let adapters = luarc::native::adapters::AdapterSet::default();
    let mut ck = Checker::new(&res, &sm, &world, &adapters);
    ck.check_program(&units, &[0]);
    if !ck.errors.is_empty() || !world.missing.borrow().is_empty() {
        return;
    }
    let gen = Gen::new(&ck, &units);
    let _ = gen.generate(0);
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }
}

const FRAGMENTS: &[&str] = &[
    "(", ")", "{", "}", "[", "]", "end", "local", "function", "return", "nil", "...", "=", "==", "..", "#", "-", "not", ",", ";",
    "\"", "[[", "]]", "--[[", "`", "{x}", "0x", "1e", "and", "or", "if", "then", "else", "elseif", "do", "while", "repeat",
    "until", "for", "in", "break", "continue", ":", ".", "self", "true", "false", "x", "t", "f", "1", "-1", "0/0", "\\",
    "\n", " ", "local x: number? = nil", "type T = {x: number}", "x :: number", "<const>", "<close>", "require(\"./nope\")",
];

fn mutate(src: &[u8], r: &mut Rng) -> Vec<u8> {
    let mut v = src.to_vec();
    for _ in 0..1 + r.below(3) {
        let n = v.len();
        match r.below(6) {
            0 if n > 0 => {
                let a = r.below(n);
                let len = 1 + r.below(16.min(n - a));
                v.drain(a..a + len);
            }
            1 if n > 0 => {
                let a = r.below(n);
                let len = 1 + r.below(32.min(n - a));
                let chunk: Vec<u8> = v[a..a + len].to_vec();
                let at = r.below(v.len() + 1);
                v.splice(at..at, chunk);
            }
            2 if n > 1 => {
                let (a, b) = (r.below(n), r.below(n));
                v.swap(a, b);
            }
            3 if n > 0 => {
                v.truncate(r.below(n));
            }
            _ => {
                let frag = FRAGMENTS[r.below(FRAGMENTS.len())].as_bytes();
                let at = r.below(v.len() + 1);
                v.splice(at..at, frag.iter().copied());
            }
        }
    }
    v
}

fn crashes(src: &str) -> Option<String> {
    let s = src.to_string();
    let r = panic::catch_unwind(move || compile(&s));
    r.err().map(|p| {
        p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_else(|| "non-string panic".into())
    })
}

/// Line-wise then byte-wise delta reduction keeping the input crashing.
fn minimize(src: &str) -> String {
    let mut cur: Vec<String> = src.lines().map(String::from).collect();
    let mut i = 0;
    while i < cur.len() {
        let mut t = cur.clone();
        t.remove(i);
        if crashes(&t.join("\n")).is_some() {
            cur = t;
        } else {
            i += 1;
        }
    }
    cur.join("\n")
}

#[test]
fn frontend_never_panics_on_mutated_sources() {
    let mut files = Vec::new();
    for d in ["tests", "examples"] {
        sources(&repo().join(d), &mut files);
    }
    files.sort();
    assert!(files.len() > 20);
    let iters: usize = std::env::var("LUARC_FUZZ_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(40);
    // keep the default hook quiet while probing; restore it afterwards
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let mut failures = Vec::new();
    for (fi, f) in files.iter().enumerate() {
        let src = fs::read(f).unwrap();
        // the unmodified source must not crash either
        let base = String::from_utf8_lossy(&src).to_string();
        if let Some(msg) = crashes(&base) {
            failures.push(format!("{}: unmodified source panics: {msg}", f.display()));
            continue;
        }
        for k in 0..iters {
            let seed = 0x9E37_79B9_7F4A_7C15u64 ^ ((fi as u64) << 32) ^ k as u64;
            let mut r = Rng(seed | 1);
            let m = String::from_utf8_lossy(&mutate(&src, &mut r)).to_string();
            if let Some(msg) = crashes(&m) {
                let min = minimize(&m);
                failures.push(format!("{} seed {seed:#x}: {msg}\n--- minimized input\n{min}\n---", f.display()));
                break;
            }
        }
    }
    panic::set_hook(hook);
    assert!(failures.is_empty(), "{} crashing input(s):\n\n{}", failures.len(), failures.join("\n\n"));
}

/// Deep nesting must be a diagnostic, not a stack overflow of the compiler.
#[test]
fn deep_nesting_is_bounded() {
    for depth in [50usize, 500, 5_000] {
        let paren = format!("local x = {}1{}", "(".repeat(depth), ")".repeat(depth));
        let concat = format!("local s = \"a\"{}", " .. \"a\"".repeat(depth));
        let blocks = format!("{}local y = 1{}", "do ".repeat(depth), " end".repeat(depth));
        let unary = format!("local z = {}1", "-".repeat(depth).replace("--", "- -"));
        for src in [paren, concat, blocks, unary] {
            let h = std::thread::Builder::new().stack_size(256 << 20).spawn(move || crashes(&src)).unwrap();
            let r = h.join();
            assert!(matches!(r, Ok(None)), "depth {depth}: compiler crashed");
        }
    }
}
