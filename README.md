[![Luarc banner](assets/LuarcBanner.png)](https://github.com/GabrielVicini/Luarc)

<div align="center">

# Luarc

**Luau-style code. Native executables. Rust libraries.**

A statically checked, Luau-derived programming language that compiles to Rust and builds with Cargo.

[![Rust](https://img.shields.io/badge/Rust-000000?style=for-the-badge&logo=rust&logoColor=white)](https://www.rust-lang.org/)
[![Luau](https://img.shields.io/badge/Luau-00A2FF?style=for-the-badge&logo=robloxstudio&logoColor=white)](https://luau.org/)
[![MIT](https://img.shields.io/badge/MIT-000000?style=for-the-badge&logo=github&logoColor=white)](LICENSE)

</div>

> [!WARNING]
> Luarc is in pre-alpha. Expect bugs, missing features, and breaking changes. It is not ready for production use.

## What is Luarc?

Luarc lets you write familiar Luau-style code and compile it ahead of time to a native executable. It supports static type inference, shared tables, closures, modules, multiple returns, coroutines, and parts of Luau's metatable system.

The other half of Luarc is Rust interoperability. Supported Rust crates can be imported directly from source code, without handwritten bindings or Rust glue:

[Check out the wgpu pixel performance demo](https://www.youtube.com/watch?v=02XkP4el8mU) </p>
You can find the code in examples/playground [here](https://github.com/GabrielVicini/Luarc/blob/master/examples/playground/main.luarc), keep in mind in the video is that there was NO Rust glue to make wgpu work!


```lua
local regex = require("rust:regex")

local pattern = regex.Regex.new("^[A-Z]+$")
print(pattern:is_match("HELLO")) -- true
```

Luarc generates Rust, builds it with Cargo, and produces an executable that doesn't need a Lua installation or the Luarc compiler to run.

## Getting started

You'll need Rust and Cargo. Importing Rust crates also requires the pinned nightly toolchain for rustdoc JSON extraction (see `luarc-toolchain.toml`).

Build the compiler from source:

```bash
git clone https://github.com/GabrielVicini/Luarc.git
cd Luarc
cargo build --release
```

The binary is in `target/release/` (`luarc.exe` on Windows). Add that directory to your `PATH`, or invoke the binary directly.

In a new project directory, save the example above as `main.luarc`, then run:

```bash
luarc add regex
luarc run main.luarc
```

`luarc add` creates the project's `luarc.toml` and `luarc.lock` as needed. Programs that don't import Rust crates can be run without a manifest.

## Command line

| Command | Description |
| --- | --- |
| `luarc run main.luarc` | Build and run a program. |
| `luarc build main.luarc --release` | Compile a native executable. |
| `luarc check main.luarc` | Check source without building it. |
| `luarc add regex` | Add a Rust crate to the project. |
| `luarc bindings regex` | Show which APIs were imported and why others weren't. |
| `luarc emit-rust main.luarc` | Write out the generated Rust project. |

## Language and runtime

Luarc implements a growing subset of Luau, including:

- Functions, closures, methods, modules, and familiar Luau control flow.
- Type inference, annotations, optionals, generics, and a checked dynamic `any` type.
- Arrays, maps, records, 1-based indexing, and multiple return values.
- Varargs, `pcall`, coroutines, and supported metatable operations.
- Automatic memory management, including collection of cycles between managed values.

The compiler uses Rust's type system and Cargo to build the output. Native imports are discovered from Rust's public API metadata, with supported signatures converted automatically. You can inspect the generated code with `luarc emit-rust`.

## Current limitations

Luarc is not a drop-in replacement for Luau. Roblox APIs aren't included, and parts of the standard library and language remain unsupported. In particular, globals and dynamic code loading aren't available.

Rust interoperability is also selective: complex borrowing, unsafe functions, retained callbacks, and some asynchronous APIs cannot be imported automatically. Check a crate with `luarc bindings <crate>` before relying on a specific API. Cycles that pass through memory owned by native code are not currently collected.

Unsupported constructs are reported by the compiler rather than silently translated into different behavior. Compatibility and native interop continue to evolve during pre-alpha.

## Examples and testing

The repository includes working examples for [`regex`](examples/regex_demo) and [`semver`](examples/semver_demo), along with compiler and runtime tests.

```bash
cargo test
```

## License

Luarc is available under the [MIT License](LICENSE).
