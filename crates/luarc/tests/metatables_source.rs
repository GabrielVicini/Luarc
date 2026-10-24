//! Source-level module lookup compared with the pinned Luau oracle.

use std::path::PathBuf;
use std::process::Command;

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).replace("\r\n", "\n").replace("./modules.luau:", "modules.luau:")
}

#[test]
fn class_records_flow_across_source_modules_without_warnings() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("repository");
    let oracle = repo.join("LuaUCompare/luau.exe");
    if !oracle.is_file() {
        eprintln!("SKIP source module comparison: pinned Luau binary is absent");
        return;
    }
    let dir = repo.join("tests/metatables_source");
    let reference = Command::new(oracle).arg("modules.luau").current_dir(&dir).output().expect("run Luau");
    assert!(reference.status.success(), "{}", text(&reference.stderr));
    for release in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_luarc"));
        command.args(["run", "modules.luau"]).current_dir(&dir);
        if release { command.arg("--release"); }
        let output = command.output().expect("run luarc");
        assert!(output.status.success(), "{}", text(&output.stderr));
        assert!(!text(&output.stderr).contains("warning in generated code"), "{}", text(&output.stderr));
        assert_eq!(output.status.code(), reference.status.code());
        assert_eq!(text(&output.stdout), text(&reference.stdout), "release={release}");
    }
}
