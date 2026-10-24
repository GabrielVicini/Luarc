//! End-to-end test suite: compiles and runs source programs, checks diagnostics,
//! imports the fixture crate and real crates, and exercises the CLI.
//!
//! Every test drives the real `luarc` binary. Programs under `tests/programs` and
//! `tests/native` are compared against their `.out` files. Expectations embedded in
//! sources:
//! * `-- expect-exit: N`      exit status (default 0)
//! * `-- expect-stderr: text` substring of stderr
//! * `-- expect-error: [file:]L:C: text` diagnostic (compile-fail tests)

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn repo() -> PathBuf {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..");
    let c = fs::canonicalize(&p).unwrap();
    // strip Windows verbatim prefix
    let s = c.to_string_lossy().to_string();
    match s.strip_prefix(r"\\?\") {
        Some(r) => PathBuf::from(r),
        None => c,
    }
}

fn luarc(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_luarc")).args(args).current_dir(dir).output().expect("run luarc")
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).replace("\r\n", "\n")
}

struct Expect {
    exit: i32,
    stderr: Vec<String>,
    errors: Vec<String>,
}

fn expectations(src: &str) -> Expect {
    let mut e = Expect { exit: 0, stderr: vec![], errors: vec![] };
    for line in src.lines() {
        if let Some(v) = line.strip_prefix("-- expect-exit:") {
            e.exit = v.trim().parse().unwrap();
        } else if let Some(v) = line.strip_prefix("-- expect-stderr:") {
            e.stderr.push(v.trim().to_string());
        } else if let Some(v) = line.strip_prefix("-- expect-error:") {
            e.errors.push(v.trim().to_string());
        }
    }
    e
}

fn source_files(dir: &Path, prefix: Option<&str>) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().map(|e| e == "luarc").unwrap_or(false))
        .filter(|p| prefix.map(|pre| p.file_name().unwrap().to_string_lossy().starts_with(pre)).unwrap_or(true))
        .collect();
    v.sort();
    v
}

/// Builds and runs `file` (in its directory); compares stdout with `<file>.out`.
fn check_program(file: &Path, args: &[&str]) -> Result<(), String> {
    let dir = file.parent().unwrap();
    let name = file.file_name().unwrap().to_string_lossy().to_string();
    let src = fs::read_to_string(file).unwrap();
    let exp = expectations(&src);
    let mut a = vec!["run", name.as_str()];
    if !args.is_empty() {
        a.push("--");
        a.extend_from_slice(args);
    }
    let out = luarc(dir, &a);
    let stdout = text(&out.stdout);
    let stderr = text(&out.stderr);
    let expected = text(&fs::read(file.with_extension("out")).map_err(|e| format!("{name}: missing .out file: {e}"))?);
    let mut problems = Vec::new();
    if stdout != expected {
        problems.push(format!("stdout differs\n--- expected\n{expected}\n--- actual\n{stdout}"));
    }
    if out.status.code() != Some(exp.exit) {
        problems.push(format!("exit status {:?}, expected {}", out.status.code(), exp.exit));
    }
    for s in &exp.stderr {
        if !stderr.contains(s) {
            problems.push(format!("stderr lacks {s:?}"));
        }
    }
    if stderr.contains("warning in generated code") {
        problems.push("generated Rust produced warnings".into());
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(format!("{name}: {}\n--- stderr\n{stderr}", problems.join("\n")))
    }
}

/// Runs `cmd` (check or build) on a file that must fail with its expected diagnostics.
fn check_failure(file: &Path, cmd: &str) -> Result<(), String> {
    let dir = file.parent().unwrap();
    let name = file.file_name().unwrap().to_string_lossy().to_string();
    let src = fs::read_to_string(file).unwrap();
    let exp = expectations(&src);
    assert!(!exp.errors.is_empty(), "{name} has no expect-error line");
    let out = luarc(dir, &[cmd, &name]);
    let stderr = text(&out.stderr);
    if out.status.success() {
        return Err(format!("{name}: expected failure, but `luarc {cmd}` succeeded"));
    }
    for e in &exp.errors {
        // `[file.luarc:]L:C: message` must appear as `file.luarc:L:C: error: message`
        let (file, rest) = match e.split_once(".luarc:") {
            Some((f, r)) => (format!("{f}.luarc"), r.to_string()),
            None => (name.clone(), e.clone()),
        };
        let (loc, msg) = rest.split_once(": ").expect("expectation format: L:C: message");
        let prefix = format!("{file}:{loc}: error: ");
        let needle = format!("{prefix}...{msg}...");
        if !stderr.lines().any(|l| l.starts_with(&prefix) && l.contains(msg)) {
            return Err(format!("{name}: diagnostic {needle:?} not found in:\n{stderr}"));
        }
    }
    Ok(())
}

fn collect(results: Vec<Result<(), String>>) {
    let failures: Vec<String> = results.into_iter().filter_map(|r| r.err()).collect();
    if !failures.is_empty() {
        panic!("{} failure(s):\n\n{}", failures.len(), failures.join("\n\n"));
    }
}

#[test]
fn source_programs() {
    let dir = repo().join("tests").join("programs");
    let files = source_files(&dir, None);
    assert!(files.len() >= 12, "expected the source program corpus");
    collect(files.iter().map(|f| check_program(f, &[])).collect());
}

#[test]
fn compile_fail_diagnostics() {
    let dir = repo().join("tests").join("compile_fail");
    collect(source_files(&dir, None).iter().map(|f| check_failure(f, "check")).collect());
}

#[test]
fn native_fixture() {
    let dir = repo().join("tests").join("native");
    let positive: Vec<PathBuf> = source_files(&dir, None).into_iter().filter(|p| !p.file_name().unwrap().to_string_lossy().starts_with("fail_")).collect();
    assert!(positive.len() >= 3);
    let mut results: Vec<Result<(), String>> = positive.iter().map(|f| check_program(f, &[])).collect();
    // negative tests: item-level diagnostics; other items of the crate stay usable
    results.extend(source_files(&dir, Some("fail_")).iter().map(|f| check_failure(f, "build")));
    collect(results);
}

#[test]
fn bindings_report_classifies_items() {
    let dir = repo().join("tests").join("native");
    let out = luarc(&dir, &["bindings", "fixture"]);
    let s = text(&out.stdout);
    assert!(out.status.success(), "{}", text(&out.stderr));
    let line_after = |item: &str| -> String {
        let mut it = s.lines();
        while let Some(l) = it.next() {
            if l.trim_start().starts_with(item) {
                return it.next().unwrap_or("").to_string();
            }
        }
        panic!("item {item} not listed:\n{s}");
    };
    assert!(line_after("add ").contains("automatic"));
    assert!(line_after("largest ").contains("automatic"));
    assert!(line_after("shapes.Circle:scale ").contains("automatic"));
    assert!(line_after("shapes.Circle:label ").contains("automatic"));
    assert!(line_after("Ledger:finish ").contains("adapter-backed (fixture-ledger)"));
    assert!(line_after("Pool:checkout ").contains("adapter-backed (fixture-ledger)"));
    assert!(line_after("Ledger:close ").contains("adapter-backed (fixture-ledger)"));
    assert!(line_after("nested_option ").contains("automatic"));
    assert!(line_after("nested_tuple ").contains("automatic"));
    assert!(line_after("store_callback ").contains("automatic"));
    assert!(line_after("spawn_like ").contains("UNSUPPORTED"));
    assert!(line_after("dangerous ").contains("UNSUPPORTED"));
    assert!(line_after("later ").contains("automatic"));
    assert!(s.contains("Point") && s.contains("record (by value)"));
    assert!(s.contains("Disc") && s.contains("alias of Circle"));
    assert!(s.contains("Greeter: trait items are not imported"));
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for e in fs::read_dir(from).unwrap().flatten() {
        let p = e.path();
        let name = e.file_name();
        if name == "target" {
            continue;
        }
        if p.is_dir() {
            copy_dir(&p, &to.join(name));
        } else {
            fs::copy(&p, to.join(name)).unwrap();
        }
    }
}

/// A new public item from an ordinary crate
/// is imported without changing the compiler or writing glue; stale extraction
/// results are not reused after signature or feature changes.
#[test]
fn importer_new_function_signature_and_feature_changes() {
    let base = std::env::temp_dir().join(format!("luarc importer test {}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let krate = base.join("fixture copy");
    let app = base.join("my app");
    copy_dir(&repo().join("fixtures").join("fixture_crate"), &krate);
    fs::create_dir_all(&app).unwrap();
    let out = luarc(&app, &["add", "fixture", "--path", "../fixture copy"]);
    assert!(out.status.success(), "add failed: {}", text(&out.stderr));
    assert!(app.join("luarc.toml").is_file() && app.join("luarc.lock").is_file());

    fs::write(app.join("main.luarc"), "local fx = require(\"rust:fixture\")\nprint(fx.brand_new_function(20))\n").unwrap();
    let out = luarc(&app, &["check", "main.luarc"]);
    assert!(!out.status.success());
    assert!(text(&out.stderr).contains("has no importable item 'brand_new_function'"), "{}", text(&out.stderr));

    // 1. add a compatible public function to the crate
    let lib = krate.join("src").join("lib.rs");
    let mut src = fs::read_to_string(&lib).unwrap();
    src.push_str("\npub fn brand_new_function(x: i32) -> String {\n    format!(\"new:{}\", x * 2)\n}\n");
    fs::write(&lib, &src).unwrap();
    let out = luarc(&app, &["run", "main.luarc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "new:40\n");

    // 2. change its signature: the cached API/glue must not be reused
    let src2 = src.replace(
        "pub fn brand_new_function(x: i32) -> String {\n    format!(\"new:{}\", x * 2)\n}",
        "pub fn brand_new_function(x: f64, suffix: &str) -> String {\n    format!(\"v2:{}{}\", x / 4.0, suffix)\n}",
    );
    assert_ne!(src, src2);
    fs::write(&lib, &src2).unwrap();
    let out = luarc(&app, &["check", "main.luarc"]);
    assert!(!out.status.success(), "stale signature accepted");
    assert!(text(&out.stderr).contains("expects 2 argument(s), got 1"), "{}", text(&out.stderr));
    fs::write(app.join("main.luarc"), "local fx = require(\"rust:fixture\")\nprint(fx.brand_new_function(10, \"!\"))\n").unwrap();
    let out = luarc(&app, &["run", "main.luarc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "v2:2.5!\n");

    // 3. enable a feature: feature-gated items appear, and the lockfile records it
    fs::write(app.join("feat.luarc"), "local fx = require(\"rust:fixture\")\nprint(fx.extra_feature())\n").unwrap();
    let out = luarc(&app, &["check", "feat.luarc"]);
    assert!(text(&out.stderr).contains("has no importable item 'extra_feature'"), "{}", text(&out.stderr));
    let out = luarc(&app, &["add", "fixture", "--path", "../fixture copy", "--features", "extra"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    let lock = fs::read_to_string(app.join("luarc.lock")).unwrap();
    assert!(lock.contains("\"extra\""), "lockfile lacks feature:\n{lock}");
    let out = luarc(&app, &["run", "feat.luarc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "7\n");

    // 4. bump the path dependency's version in its own Cargo.toml (no `luarc add`):
    // the cached resolution must not keep the old package identity
    let cargo_toml = krate.join("Cargo.toml");
    let manifest = fs::read_to_string(&cargo_toml).unwrap();
    let bumped = manifest.replacen("version = \"0.3.0\"", "version = \"0.4.0\"", 1);
    assert_ne!(manifest, bumped, "fixture version line not found");
    fs::write(&cargo_toml, bumped).unwrap();
    let out = luarc(&app, &["run", "feat.luarc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "7\n");
    let lock = fs::read_to_string(app.join("luarc.lock")).unwrap();
    assert!(lock.contains("version = \"0.4.0\""), "lockfile keeps the old version:\n{lock}");

    // 5. edit luarc.toml by hand (drop the feature): the lock follows the manifest
    let m = fs::read_to_string(app.join("luarc.toml")).unwrap();
    let m2 = m.replace("features = [\"extra\"]", "");
    assert_ne!(m, m2, "manifest feature line not found:\n{m}");
    fs::write(app.join("luarc.toml"), m2).unwrap();
    let out = luarc(&app, &["check", "feat.luarc"]);
    assert!(text(&out.stderr).contains("has no importable item 'extra_feature'"), "{}", text(&out.stderr));
    let lock = fs::read_to_string(app.join("luarc.lock")).unwrap();
    assert!(!lock.contains("\"extra\""), "lockfile keeps a removed feature:\n{lock}");
    let _ = fs::remove_dir_all(&base);
}

#[test]
fn real_crate_regex() {
    let dir = repo().join("examples").join("regex_demo");
    collect(vec![check_program(&dir.join("main.luarc"), &[])]);
}

#[test]
fn real_crate_semver() {
    let dir = repo().join("examples").join("semver_demo");
    collect(vec![check_program(&dir.join("main.luarc"), &[])]);
}

#[test]
fn cli_smoke() {
    let base = std::env::temp_dir().join(format!("luarc cli smoke {}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    fs::create_dir_all(&base).unwrap();
    fs::write(
        base.join("app.luarc"),
        "local n = 0\nfor i, a in ipairs(arg) do n += #a end\nprint(\"args\", #arg, n)\nprint(\"hello from luarc\")\n",
    )
    .unwrap();
    let out = luarc(&base, &["check", "app.luarc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert!(out.stdout.is_empty(), "compiler output must stay off stdout");
    let out = luarc(&base, &["run", "app.luarc", "--", "one", "two words"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "args\t2\t12\nhello from luarc\n");
    let exe = base.join(format!("built app{}", std::env::consts::EXE_SUFFIX));
    let out = luarc(&base, &["build", "app.luarc", "--release", "-o", exe.to_str().unwrap()]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(text(&run.stdout), "args\t0\t0\nhello from luarc\n");
    let emitted = base.join("emitted rust");
    let out = luarc(&base, &["emit-rust", "app.luarc", "-o", emitted.to_str().unwrap()]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert!(emitted.join("src").join("main.rs").is_file());
    assert!(emitted.join("luarc-runtime").join("src").join("lib.rs").is_file());
    // the emitted package builds on its own (no luarc needed)
    let b = Command::new("cargo")
        .args(["build", "--quiet", "--manifest-path"])
        .arg(emitted.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(base.join("target"))
        .output()
        .unwrap();
    assert!(b.status.success(), "{}", text(&b.stderr));
    // re-emitting keeps files luarc did not generate
    fs::write(emitted.join("src").join("notes.rs"), "// my notes\n").unwrap();
    let out = luarc(&base, &["emit-rust", "app.luarc", "-o", emitted.to_str().unwrap()]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert!(emitted.join("src").join("notes.rs").is_file(), "emit-rust deleted a user file");
    // and never writes over a Cargo package it did not generate
    let foreign = base.join("foreign pkg");
    fs::create_dir_all(foreign.join("src")).unwrap();
    fs::write(foreign.join("Cargo.toml"), "[package]\nname = \"mine\"\n").unwrap();
    fs::write(foreign.join("src").join("lib.rs"), "// mine\n").unwrap();
    let out = luarc(&base, &["emit-rust", "app.luarc", "-o", foreign.to_str().unwrap()]);
    assert!(!out.status.success());
    assert!(text(&out.stderr).contains("refusing to write into"), "{}", text(&out.stderr));
    assert_eq!(fs::read_to_string(foreign.join("Cargo.toml")).unwrap(), "[package]\nname = \"mine\"\n");
    assert!(foreign.join("src").join("lib.rs").is_file());
    let _ = fs::remove_dir_all(&base);
}

/// An adapter naming an associated constant where a method is required is a
/// validation error, not a compiler panic.
#[test]
fn adapter_validation_errors_are_diagnostics() {
    let base = std::env::temp_dir().join(format!("luarc adapter validation {}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    fs::create_dir_all(base.join("adapters")).unwrap();
    let fixture = repo().join("fixtures").join("fixture_crate").to_string_lossy().replace('\\', "/");
    fs::write(base.join("luarc.toml"), format!("[package]\nname = \"probe\"\n\n[dependencies.fixture]\npath = \"{fixture}\"\n")).unwrap();
    fs::write(
        base.join("adapters").join("probe.toml"),
        "adapter = \"probe\"\nadapter_version = 1\ncrate = \"fixture\"\n[[returns_receiver]]\ntype = \"Meters\"\nmethod = \"ZERO\"\n",
    )
    .unwrap();
    fs::write(base.join("main.luarc"), "local fx = require(\"rust:fixture\")\nprint(fx.add(1, 2))\n").unwrap();
    let out = luarc(&base, &["check", "main.luarc"]);
    let err = text(&out.stderr);
    assert!(!out.status.success());
    assert!(!err.contains("panicked"), "{err}");
    assert!(err.contains("Meters.ZERO is not a method"), "{err}");
    let _ = fs::remove_dir_all(&base);
}

/// A shipped adapter written for another version of a crate is skipped with a
/// warning instead of failing the build: here a different crate
/// named `fixture` lacks the `Ledger` type the shipped `fixture-ledger` adapter names.
#[test]
fn shipped_adapter_for_other_version_is_skipped() {
    let base = std::env::temp_dir().join(format!("luarc shipped adapter {}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let krate = base.join("other fixture");
    fs::create_dir_all(krate.join("src")).unwrap();
    fs::write(krate.join("Cargo.toml"), "[package]\nname = \"fixture\"\nversion = \"9.0.0\"\nedition = \"2021\"\n\n[lib]\npath = \"src/lib.rs\"\n").unwrap();
    fs::write(krate.join("src").join("lib.rs"), "pub fn add(a: f64, b: f64) -> f64 {\n    a + b\n}\n").unwrap();
    let app = base.join("app");
    fs::create_dir_all(&app).unwrap();
    let out = luarc(&app, &["add", "fixture", "--path", "../other fixture"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    fs::write(app.join("main.luarc"), "local fx = require(\"rust:fixture\")\nprint(fx.add(1, 2))\n").unwrap();
    let out = luarc(&app, &["run", "main.luarc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "3\n");
    assert!(text(&out.stderr).contains("the shipped adapter is skipped"), "{}", text(&out.stderr));
    let _ = fs::remove_dir_all(&base);
}

/// `require("./x")` resolves `x.luarc`, `x/init.luarc`, then the legacy
/// `x.luau`, `x.lua`, `x/init.luau`; `.luarc` wins when several exist.
#[test]
fn module_extension_resolution() {
    let base = std::env::temp_dir().join(format!("luarc ext resolution {}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    fs::create_dir_all(base.join("pkg")).unwrap();
    fs::create_dir_all(base.join("oldpkg")).unwrap();
    fs::write(base.join("both.luarc"), "return \"both.luarc\"\n").unwrap();
    fs::write(base.join("both.luau"), "return \"both.luau\"\n").unwrap();
    fs::write(base.join("legacy.luau"), "return \"legacy.luau\"\n").unwrap();
    fs::write(base.join("plain.lua"), "return \"plain.lua\"\n").unwrap();
    fs::write(base.join("pkg").join("init.luarc"), "return \"pkg/init.luarc\"\n").unwrap();
    fs::write(base.join("oldpkg").join("init.luau"), "return \"oldpkg/init.luau\"\n").unwrap();
    fs::write(
        base.join("main.luarc"),
        "print(require(\"./both\"))\nprint(require(\"./legacy\"))\nprint(require(\"./plain\"))\n\
         print(require(\"./pkg\"))\nprint(require(\"./oldpkg\"))\n",
    )
    .unwrap();
    let out = luarc(&base, &["run", "main.luarc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "both.luarc\nlegacy.luau\nplain.lua\npkg/init.luarc\noldpkg/init.luau\n");
    fs::write(base.join("missing.luarc"), "print(require(\"./nope\"))\n").unwrap();
    let out = luarc(&base, &["check", "missing.luarc"]);
    assert!(!out.status.success());
    assert!(text(&out.stderr).contains("module './nope' not found (looked for ./nope.luarc"), "{}", text(&out.stderr));
    let _ = fs::remove_dir_all(&base);
}

/// `require("rust:std")`: the standard library is a toolchain crate (no registry
/// dependency, no manifest). The program works inside its own temp directory.
#[test]
fn rust_std_filesystem() {
    let dir = repo().join("tests").join("std");
    collect(source_files(&dir, None).iter().map(|f| check_program(f, &[])).collect());
}

/// The release's std example, run from a fresh temporary copy (it writes
/// `copy.txt` next to itself).
#[test]
fn rust_std_example_in_temp_copy() {
    let tmp = std::env::temp_dir().join(format!("luarc-std-example-{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    copy_dir(&repo().join("examples").join("std_files"), &tmp);
    let _ = fs::remove_dir_all(tmp.join(".luarc"));
    let out = luarc(&tmp, &["run", "main.luarc"]);
    let stdout = text(&out.stdout);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(stdout, "Hello from a luarc program reading a file.\n\n");
    assert_eq!(fs::read_to_string(tmp.join("copy.txt")).unwrap().replace("\r\n", "\n"), "Hello from a luarc program reading a file.\n");
    let _ = fs::remove_dir_all(&tmp);
}

/// Annotating every local of a program never changes its checked-read
/// behaviour: the annotated twin produces the same output.
#[test]
fn annotations_do_not_change_checked_reads() {
    let dir = repo().join("tests").join("programs");
    let a = luarc(&dir, &["run", "checked_reads.luarc"]);
    let b = luarc(&dir, &["run", "checked_reads_annotated.luarc"]);
    let (sa, sb) = (text(&a.stdout), text(&b.stdout).replace("checked_reads_annotated", "checked_reads"));
    assert!(a.status.success() && b.status.success());
    assert_eq!(sa, sb);
}
