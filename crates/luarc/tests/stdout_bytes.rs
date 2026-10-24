//! Compare raw stdout with Luau, including non-UTF-8 bytes and Windows text-mode LF.

use std::path::PathBuf;
use std::process::Command;

#[test]
fn stdout_matches_luau_bytes() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("repository");
    let oracle = std::env::var_os("LUARC_LUAU_REF")
        .map(PathBuf::from)
        .unwrap_or_else(|| repo.join("LuaUCompare").join(format!("luau{}", std::env::consts::EXE_SUFFIX)));
    if !oracle.is_file() {
        eprintln!("SKIP stdout_matches_luau_bytes: Luau reference not found (set LUARC_LUAU_REF)");
        return;
    }
    let dir = repo.join("tests/diff");
    let reference = Command::new(oracle).arg("stdout_bytes.luarc").current_dir(&dir).output().expect("run Luau");
    assert!(reference.status.success(), "Luau stderr: {}", String::from_utf8_lossy(&reference.stderr));
    for release in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_luarc"));
        command.args(["run", "stdout_bytes.luarc"]).current_dir(&dir);
        if release {
            command.arg("--release");
        }
        let actual = command.output().expect("run luarc");
        let stderr = String::from_utf8_lossy(&actual.stderr);
        assert!(actual.status.success(), "release={release}, luarc stderr: {stderr}");
        assert!(!stderr.contains("warning in generated code"), "release={release}: {stderr}");
        assert_eq!(actual.stdout, reference.stdout, "raw stdout differs, release={release}");
    }
}
