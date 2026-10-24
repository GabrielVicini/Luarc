//! Source execution and diagnostic expectations for record metadata.

use std::path::{Path, PathBuf};
use std::process::Command;

fn text(bytes: &[u8], name: &str) -> String {
    String::from_utf8_lossy(bytes)
        .replace("\r\n", "\n")
        .replace(&format!("./{name}:"), &format!("{name}:"))
}

fn compare(repo: &Path, dir: &Path, name: &str) {
    let oracle = repo.join("LuaUCompare/luau.exe");
    let reference = Command::new(oracle)
        .arg(name)
        .current_dir(dir)
        .output()
        .expect("run Luau");
    assert!(
        reference.status.success(),
        "{name}: {}",
        text(&reference.stderr, name)
    );
    for release in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_luarc"));
        command.args(["run", name]).current_dir(dir);
        if release {
            command.arg("--release");
        }
        let output = command.output().expect("run luarc");
        let stderr = text(&output.stderr, name);
        assert!(
            output.status.success(),
            "{name}, release={release}: {stderr}"
        );
        assert!(
            !stderr.contains("warning in generated code"),
            "{name}: {stderr}"
        );
        assert_eq!(
            output.status.code(),
            reference.status.code(),
            "{name}, release={release}"
        );
        assert_eq!(
            text(&output.stdout, name),
            text(&reference.stdout, name),
            "{name}, release={release}"
        );
    }
}

#[test]
fn general_metadata_source_modules_depth_and_migrated_cases_match_luau() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repository");
    if !repo.join("LuaUCompare/luau.exe").is_file() {
        eprintln!("SKIP general source comparison: pinned Luau binary is absent");
        return;
    }
    let dir = repo.join("tests/metatables_step2_source");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("source fixtures")
        .map(|e| {
            e.expect("source entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|name| {
            name.starts_with("metatables_") && (name.ends_with(".luarc") || name.ends_with(".luau"))
        })
        .collect();
    files.sort();
    assert_eq!(
        files.len(),
        26,
        "every approved migration must remain represented"
    );
    for name in files {
        compare(&repo, &dir, &name);
    }
    compare(&repo, &dir, "modules.luau");
    compare(&repo, &dir, "depth99.luarc");
    compare(&repo, &dir, "record_boundary.luarc");
}
