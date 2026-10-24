//! `luarc`: a compiler from a statically checked Luau-style language to Rust.
//!
//! Pipeline: [`lexer`] → [`parser`] → [`resolve`] → [`check`] → [`codegen`] → Cargo
//! (driven by [`driver`] and [`project`]). Rust crates are imported through
//! [`native`] (rustdoc JSON extraction, adapters and generated wrappers).

pub mod ast;
pub mod ast_walk;
pub mod check;
pub mod check_xpcall;
pub mod check_table_library;
pub mod check_bit32;
pub mod check_builtin;
pub mod check_coroutine;
pub mod check_dynamic;
pub mod check_runtime_table;

pub mod check_packs;
pub mod check_int;
pub mod check_iter;
pub mod check_iteration;
mod check_layout;
pub mod check_next_identity;
pub mod check_metatable;
pub mod check_metatable_general;
pub mod check_representation;
pub mod check_task;
pub mod check_trait;
pub mod check_native;
pub mod codegen;
pub mod diag;
pub mod driver;
pub mod fmtspec;
pub mod lexer;
pub mod native;
pub mod parser;
pub mod progress;
pub mod project;
pub mod resolve;
pub mod rir;
pub mod specialize;
pub mod types;
