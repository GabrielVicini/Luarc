//! Golden test for code generation: the Rust that `luarc emit-rust` writes for
//! every program in `tests/diff`, `tests/programs` and `tests/native` is compared
//! with the checked-in copy under `tests/golden/<group>/<program>/`.
//!
//! Changes to emitted Rust appear as a file diff even when every program
//! still prints the same output. Run with `LUARC_UPDATE_GOLDEN=1` to rewrite the
//! goldens, then review the diff with `git diff tests/golden`.
//!
//! Compared files: `main.rs`, `records.rs` and the module files (`m<N>_*.rs`).
//! `natives.rs` comes from the native wrapper generator (`native/wrap.rs`), which
//! has its own tests, and is left out to keep the goldens small.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

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

/// Programs of one group that are expected to compile (`fail_*` and compile-fail
/// sources have no Rust to compare).
fn programs(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().map(|e| e == "luarc").unwrap_or(false))
        .filter(|p| !p.file_name().unwrap().to_string_lossy().starts_with("fail_"))
        .collect();
    v.sort();
    v
}

fn compared(name: &str) -> bool {
    name == "main.rs" || name == "records.rs" || (name.starts_with('m') && name.ends_with(".rs") && name != "natives.rs")
}

/// Emits one program and returns its compared files (name, contents).
fn emit(src: &Path, out: &Path) -> Result<Vec<(String, String)>, String> {
    let _ = fs::remove_dir_all(out);
    let o = Command::new(env!("CARGO_BIN_EXE_luarc"))
        .args(["emit-rust", &src.file_name().unwrap().to_string_lossy(), "-o"])
        .arg(out)
        .current_dir(src.parent().unwrap())
        .output()
        .expect("run luarc");
    if !o.status.success() {
        return Err(format!("emit-rust failed:\n{}", text(&o.stderr)));
    }
    let mut files: Vec<(String, String)> = fs::read_dir(out.join("src"))
        .unwrap()
        .flatten()
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| compared(n))
        .map(|n| {
            let c = text(&fs::read(out.join("src").join(&n)).unwrap());
            (n, c)
        })
        .collect();
    files.sort();
    Ok(files)
}

/// First differing line, for a short report (the full diff is `git diff` after
/// updating).
fn first_diff(want: &str, got: &str) -> String {
    for (i, (a, b)) in want.lines().zip(got.lines()).enumerate() {
        if a != b {
            return format!("line {}:\n  golden: {a}\n  now:    {b}", i + 1);
        }
    }
    format!("length differs ({} vs {} lines)", want.lines().count(), got.lines().count())
}

fn check(group: &str, src: &Path, work: &Path, update: bool) -> Vec<String> {
    let stem = src.file_stem().unwrap().to_string_lossy().to_string();
    let gold = repo().join("tests").join("golden").join(group).join(&stem);
    let files = match emit(src, &work.join(group).join(&stem)) {
        Ok(f) => f,
        Err(e) => return vec![format!("{group}/{stem}: {e}")],
    };
    if update {
        let _ = fs::remove_dir_all(&gold);
        fs::create_dir_all(&gold).unwrap();
        for (n, c) in &files {
            fs::write(gold.join(n), c).unwrap();
        }
        return vec![];
    }
    let mut problems = vec![];
    let mut want: Vec<String> = match fs::read_dir(&gold) {
        Ok(rd) => rd.flatten().map(|e| e.file_name().to_string_lossy().to_string()).collect(),
        Err(_) => return vec![format!("{group}/{stem}: no golden (run with LUARC_UPDATE_GOLDEN=1)")],
    };
    want.sort();
    let got: Vec<String> = files.iter().map(|(n, _)| n.clone()).collect();
    if want != got {
        problems.push(format!("{group}/{stem}: file set differs: golden {want:?}, now {got:?}"));
    }
    for (n, c) in &files {
        if let Ok(w) = fs::read(gold.join(n)) {
            let w = text(&w);
            if &w != c {
                problems.push(format!("{group}/{stem}/{n}: {}", first_diff(&w, c)));
            }
        }
    }
    problems
}

#[test]
fn emitted_rust_matches_golden() {
    let update = std::env::var_os("LUARC_UPDATE_GOLDEN").is_some();
    let work = std::env::temp_dir().join(format!("luarc golden {}", std::process::id()));
    let mut jobs: Vec<(&str, PathBuf)> = vec![];
    for group in ["diff", "programs", "native"] {
        for p in programs(&repo().join("tests").join(group)) {
            jobs.push((group, p));
        }
    }
    // native programs load rustdoc JSON (seconds each): run the jobs in parallel
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).min(8);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let problems = std::sync::Mutex::new(Vec::<String>::new());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                let Some((group, src)) = jobs.get(i) else { break };
                let p = check(group, src, &work, update);
                problems.lock().unwrap().extend(p);
            });
        }
    });
    let _ = fs::remove_dir_all(&work);
    let mut problems = problems.into_inner().unwrap();
    problems.sort();
    assert!(
        problems.is_empty(),
        "{} golden mismatch(es); if intended, rerun with LUARC_UPDATE_GOLDEN=1 and review `git diff tests/golden`:\n{}",
        problems.len(),
        problems.join("\n")
    );
}
