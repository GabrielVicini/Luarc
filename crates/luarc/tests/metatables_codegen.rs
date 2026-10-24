#[path = "support/metatables.rs"]
mod support;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).replace("\r\n", "\n").replace("./metatables.luarc:", "metatables.luarc:")
}

#[test]
fn dormant_record_lowering_matches_luau_in_debug_and_release_without_warnings() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("repository");
    let oracle = repo.join("LuaUCompare/luau.exe");
    if !oracle.is_file() {
        eprintln!("SKIP dormant lowering: pinned Luau binary is absent");
        return;
    }
    let runtime = repo.join("crates/luarc-runtime");
    let target = repo.join("target/metatables-dormant-target");
    for fixture in ["class", "order", "lookup", "errors", "attachment", "results", "extras", "receiver_timing", "receiver_upvalue"] {
        let src = fs::read_to_string(repo.join("tests/metatables_dormant").join(fixture).with_extension("luarc")).expect("fixture");
        let dir = repo.join("target/metatables-dormant").join(fixture);
        fs::create_dir_all(dir.join("src")).expect("create generated package");
        fs::write(dir.join("metatables.luarc"), &src).expect("oracle input");
        let reference = Command::new(&oracle).arg("metatables.luarc").current_dir(&dir).output().expect("run Luau");
        assert!(reference.status.success(), "{fixture}: {}", text(&reference.stderr));
        support::checked(&src, |checker, units| {
            assert!(checker.errors.is_empty(), "{fixture}: {:?}", checker.errors);
            let generated = luarc::codegen::Gen::new(checker, units).generate(0);
            for (name, code) in generated.files {
                fs::write(dir.join(name), code).expect("write generated Rust");
            }
        });
        let manifest = format!("[package]\nname = \"metatables-dormant\"\nversion = \"0.0.0\"\nedition = \"2021\"\n[dependencies]\nluarc-runtime = {{ path = {:?} }}\n[workspace]\n", runtime.to_string_lossy());
        fs::write(dir.join("Cargo.toml"), manifest).expect("manifest");
        for release in [false, true] {
            let mut build = Command::new("cargo");
            build.args(["build", "--message-format=json", "--manifest-path"]).arg(dir.join("Cargo.toml")).arg("--target-dir").arg(&target);
            if release { build.arg("--release"); }
            let output = build.output().expect("build generated package");
            let diagnostics: String = text(&output.stdout).lines()
                .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
                .filter_map(|message| message["message"]["rendered"].as_str().map(str::to_owned)).collect();
            assert!(output.status.success(), "{fixture} release={release}:\n{diagnostics}\n{}", text(&output.stderr));
            for line in text(&output.stdout).lines() {
                if let Ok(message) = serde_json::from_str::<serde_json::Value>(line) {
                    assert!(message["message"]["level"] != "warning", "{fixture}: {}", message["message"]["rendered"]);
                }
            }
            let exe = target.join(if release { "release" } else { "debug" }).join(Path::new("metatables-dormant").with_extension(std::env::consts::EXE_EXTENSION));
            let run = Command::new(exe).output().expect("run generated program");
            assert_eq!(run.status.code(), reference.status.code(), "{fixture}: {}", text(&run.stderr));
            assert_eq!(text(&run.stdout), text(&reference.stdout), "{fixture} release={release}");
        }
    }
}
