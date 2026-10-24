use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-env-changed=LUARC_BIN");
    let root = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let repo = root.ancestors().nth(3).unwrap();
    let compiler = env::var_os("LUARC_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let release = repo.join("target/release/luarc.exe");
            if release.is_file() {
                release
            } else {
                repo.join("target/debug/luarc.exe")
            }
        });
    println!("cargo:rerun-if-changed={}", compiler.display());
    let bytes = fs::read(&compiler)
        .expect("Build luarc first, or set LUARC_BIN to its absolute executable path");
    fs::write(
        PathBuf::from(env::var_os("OUT_DIR").unwrap()).join("luarc.exe"),
        bytes,
    )
    .unwrap();
}
