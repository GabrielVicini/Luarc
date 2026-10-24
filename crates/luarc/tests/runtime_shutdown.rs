//! An uncaught language error must exit without a second failure in TLS teardown.

use std::path::PathBuf;
use std::process::Command;

#[test]
fn function_cache_shutdown_matches_luau_in_debug_and_release() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("repository");
    let dir = repo.join("tests/runtime_shutdown");
    let oracle = std::env::var_os("LUARC_LUAU_REF")
        .map(PathBuf::from)
        .unwrap_or_else(|| repo.join("LuaUCompare").join(format!("luau{}", std::env::consts::EXE_SUFFIX)));
    for (fixture, exit, stdout) in [
        ("alias_error", 1, &b""[..]),
        ("coroutine_alias_error", 1, &b""[..]),
        ("protected", 0, if cfg!(windows) { &b"false\tsentinel\r\n"[..] } else { &b"false\tsentinel\n"[..] }),
        ("success", 0, if cfg!(windows) { &b"word\r\n"[..] } else { &b"word\n"[..] }),
    ] {
        let name = format!("{fixture}.luarc");
        let reference = if oracle.is_file() {
            let output = Command::new(&oracle).arg(&name).current_dir(&dir).output().expect("run Luau");
            assert_eq!(output.status.code(), Some(exit), "{fixture}: Luau stderr {:?}", output.stderr);
            assert_eq!(output.stdout, stdout, "{fixture}: Luau stdout");
            Some(output)
        } else {
            eprintln!("SKIP oracle comparison: Luau reference not found (set LUARC_LUAU_REF)");
            None
        };
        for release in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_luarc"));
            command.args(["run", "-q", &name]).current_dir(&dir);
            if release { command.arg("--release"); }
            let output = command.output().expect("run luarc");
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(output.status.code(), Some(exit), "{fixture}, release={release}: {stderr}");
            assert_eq!(output.stdout, stdout, "{fixture}, release={release}");
            let expected_stderr = if exit == 1 { "luarc runtime error: sentinel\n" } else { "" };
            assert_eq!(stderr, expected_stderr, "{fixture}, release={release}");
            if let Some(reference) = &reference {
                assert_eq!(output.status.code(), reference.status.code(), "{fixture}, release={release}");
                assert_eq!(output.stdout, reference.stdout, "{fixture}, release={release}");
            }
        }
    }
}
