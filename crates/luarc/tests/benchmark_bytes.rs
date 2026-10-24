//! The unchanged thirty-probe benchmark must match the pinned oracle's raw stdout.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

const MISSING_ORACLE: &str = "Luau 0.743 oracle is required in CI: provision LuaUCompare/luau[.exe] or set LUARC_LUAU_REF to the pinned executable";

#[derive(Debug, PartialEq, Eq)]
enum OraclePolicy {
    Run,
    SkipLocal,
}

fn oracle_policy(oracle_exists: bool, ci_enabled: bool) -> Result<OraclePolicy, &'static str> {
    if oracle_exists {
        Ok(OraclePolicy::Run)
    } else if ci_enabled {
        Err(MISSING_ORACLE)
    } else {
        Ok(OraclePolicy::SkipLocal)
    }
}

#[test]
fn missing_oracle_policy_distinguishes_local_and_ci() {
    assert_eq!(oracle_policy(false, false), Ok(OraclePolicy::SkipLocal));
    assert_eq!(oracle_policy(false, true), Err(MISSING_ORACLE));
    assert_eq!(oracle_policy(true, false), Ok(OraclePolicy::Run));
    assert_eq!(oracle_policy(true, true), Ok(OraclePolicy::Run));
}

#[test]
fn benchmark_matches_luau_bytes() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("repository");
    let repo = match repo.to_string_lossy().strip_prefix(r"\\?\") {
        Some(path) => PathBuf::from(path),
        None => repo,
    };
    let dir = repo.join("tests/diff");
    assert_eq!(
        fs::read(dir.join("bench_impostor.luarc")).expect("benchmark CI copy"),
        fs::read(repo.join("tests/bench/impostor.luarc")).expect("original benchmark"),
        "the CI benchmark must remain byte-identical to the original"
    );
    let oracle = std::env::var_os("LUARC_LUAU_REF")
        .map(PathBuf::from)
        .unwrap_or_else(|| repo.join("LuaUCompare").join(format!("luau{}", std::env::consts::EXE_SUFFIX)));
    // A set CI variable enables enforcement; local runs report an explicit skip.
    match oracle_policy(oracle.is_file(), std::env::var_os("CI").is_some()) {
        Ok(OraclePolicy::Run) => {}
        Ok(OraclePolicy::SkipLocal) => {
            eprintln!("SKIP benchmark_matches_luau_bytes: Luau 0.743 reference not found (set LUARC_LUAU_REF)");
            return;
        }
        Err(message) => panic!("{message}"),
    }
    let reference = Command::new(oracle).arg("bench_impostor.luarc").current_dir(&dir).output().expect("run Luau");
    assert!(reference.status.success(), "Luau stderr: {}", String::from_utf8_lossy(&reference.stderr));
    let summary = b"LUAU IMPOSTOR DETECTOR: 30 / 30 passed";
    assert!(reference.stdout.windows(summary.len()).any(|bytes| bytes == summary), "Luau did not report all thirty probes passing");
    for release in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_luarc"));
        command.args(["run", "bench_impostor.luarc"]).current_dir(&dir);
        if release {
            command.arg("--release");
        }
        let actual = command.output().expect("run luarc");
        let stderr = String::from_utf8_lossy(&actual.stderr);
        assert!(actual.status.success(), "release={release}, luarc stderr: {stderr}");
        assert!(!stderr.contains("warning in generated code"), "release={release}: {stderr}");
        assert_eq!(actual.stdout, reference.stdout, "raw benchmark stdout differs, release={release}");
        eprintln!("benchmark release={release}: {} raw stdout bytes match Luau; 30 / 30 passed", actual.stdout.len());
    }
}
