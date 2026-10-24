# Luarc Studio — egui example

A dark navy scratch editor with a Run button, output console, line numbers,
compiler errors highlighted on their source lines, and background checks every
1.5 seconds while edits are pending. Ctrl+Enter also runs the current source.

From the repository root (PowerShell):

```powershell
cargo build -p luarc
cd examples/egui_editor
../../target/debug/luarc.exe build main.luarc
./main.exe
```

The first build downloads egui/eframe and extracts the local bridge's API using
Luarc's configured nightly toolchain. Later launches reuse the caches. Once
built, `./main.exe` opens the editor directly. The build bundles the Luarc
compiler inside the editor. Set `LUARC_BIN` to an absolute compiler executable
path to override the bundled compiler (at build time or at launch).

You can copy or rename **just `main.exe`** into a new writable folder. At
launch it creates **`scratch/` beside that executable**, writes a fresh project
manifest and starter source when absent, and unpacks its compiler into
`scratch/.tools/luarc.exe`. Existing scratch projects are preserved. Nothing
depends on the original checkout or the directory from which it was launched.

On another Windows computer, native compilation still requires Rust/Cargo
and the MSVC build tools. Rust package API extraction requires Luarc's pinned
nightly (`rustup toolchain install nightly-2026-08-06 --component rust-docs-json`).
Package installation needs network access. These toolchains are not bundled;
missing-tool errors appear in Problems or Output.

Enter Luarc's supported Lua/Luau syntax, then press **Run**. Checks use
`luarc check`; Run performs a native build and executes it. Compilation,
installation, and execution run on a worker thread so editing stays responsive.
Output includes stdout, stderr, and build/install failures. It updates during
execution and keeps the last 128 KiB. **Stop** cancels the active job; programs
have a 30-second runtime limit and no interactive stdin. Build/install jobs
have a 10-minute limit.

For example, enter:

```lua
local regex = require("rust:regex")
local pattern = regex.Regex.new("^[A-Z]+$")
print(pattern:is_match("HELLO"))
```

If the compiler reports a missing project dependency, an **Install** / **Not
now** prompt appears. Install runs `luarc add regex` in the scratch project;
wait for it to finish, then press Run. Failed installs show their logs and can
be retried. Packages come from crates.io and must expose APIs supported by
Luarc. Ordinary Lua/LuaRocks packages are not supported. Local source imports
such as `require("./module")` resolve within the scratch project; missing local
files are reported as diagnostics, not offered as registry installations.

The **Packages** section lists direct project dependencies. Press **Uninstall**
beside a package to remove it from this scratch project's manifest and lock
entries, then automatically recheck. Imports that still use it become errors.
Other projects, transitive dependencies needed by remaining packages, cached
downloads and build artifacts are retained. Removing unused direct dependencies
reduces future dependency work; keeping caches avoids unnecessary rebuilds.

`main.luarc` owns check scheduling, stale-result rejection, run requests,
installation prompts and status. `native/` is a small local Rust crate for egui
text editing, window rendering and process/thread I/O. No compiler changes or
adapters are needed. The theme is defined at the end of `native/src/lib.rs`.

Scratch source is saved in `scratch/scratch.luarc` whenever a job starts and
restored at launch. Dependencies are isolated in `scratch/luarc.toml` and
persist between launches. This is a native-code playground: entered programs
execute with your normal user permissions.

Bridge checks:

```powershell
cargo test --manifest-path native/Cargo.toml
../../target/debug/luarc.exe check main.luarc
```
