//! `luarc` command-line interface.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use luarc::driver::{self, Failure};
use luarc::progress::{self, Mode};
use luarc::project::{DepSpec, Project};

const USAGE: &str = "\
luarc — compile Luau-style programs to native executables via Rust

USAGE:
    luarc add <crate> [--version <constraint>] [--features <a,b>] [--path <dir>]
    luarc check <entry.luarc>
    luarc build <entry.luarc> [--release] [-o <executable>]
    luarc run <entry.luarc> [--release] [-- <program args>...]
    luarc emit-rust <entry.luarc> [-o <directory>]
    luarc bindings <crate>

OPTIONS (build, run, check, emit-rust, add, bindings):
    -q, --quiet      no progress output
    -v, --verbose    show every cargo status line
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // Compiler passes recurse over the syntax tree. Size this stack for the
    // parser's nesting limit; the default 1 MiB Windows stack is insufficient.
    let worker = std::thread::Builder::new().stack_size(256 << 20).spawn(move || run(args));
    let result = match worker.map(|h| h.join()) {
        Ok(Ok(r)) => r,
        Ok(Err(p)) => std::panic::resume_unwind(p),
        Err(e) => Err(Failure::Msg(format!("cannot start the compiler thread: {e}"))),
    };
    match result {
        // Preserve the program's full exit status. Narrowing to u8 would turn
        // Windows status 0xC0000100 (or 256) into zero and report success.
        Ok(code) if (0..=255).contains(&code) => ExitCode::from(code as u8),
        Ok(code) => std::process::exit(code),
        Err(f) => {
            eprintln!("{}", f.render());
            ExitCode::from(1)
        }
    }
}

struct Opts {
    positional: Vec<String>,
    release: bool,
    out: Option<PathBuf>,
    version: Option<String>,
    features: Vec<String>,
    path: Option<String>,
    rest: Vec<String>,
    mode: Mode,
}

fn parse_opts(args: &[String]) -> Result<Opts, Failure> {
    let mut o = Opts { positional: vec![], release: false, out: None, version: None, features: vec![], path: None, rest: vec![], mode: Mode::Normal };
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        let mut val = |name: &str| -> Result<String, Failure> {
            i += 1;
            args.get(i).cloned().ok_or_else(|| Failure::Msg(format!("{name} expects a value")))
        };
        match a.as_str() {
            "--" => {
                o.rest = args[i + 1..].to_vec();
                break;
            }
            "--release" => o.release = true,
            "-q" | "--quiet" => o.mode = Mode::Quiet,
            "-v" | "--verbose" => o.mode = Mode::Verbose,
            "-o" | "--output" => o.out = Some(PathBuf::from(val("-o")?)),
            "--version" => o.version = Some(val("--version")?),
            "--features" => o.features.extend(val("--features")?.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty())),
            "--path" => o.path = Some(val("--path")?),
            _ if a.starts_with('-') => return Err(Failure::Msg(format!("unknown option '{a}'\n\n{USAGE}"))),
            _ => o.positional.push(a.clone()),
        }
        i += 1;
    }
    Ok(o)
}

fn entry_of(o: &Opts) -> Result<PathBuf, Failure> {
    match o.positional.first() {
        Some(p) => Ok(PathBuf::from(p)),
        None => Err(Failure::Msg(format!("missing entry file\n\n{USAGE}"))),
    }
}

fn project_for(entry: &Path) -> Result<Project, Failure> {
    let dir = entry.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    Ok(Project::locate(dir)?)
}

fn run(args: Vec<String>) -> Result<i32, Failure> {
    let Some(cmd) = args.first().cloned() else {
        eprint!("{USAGE}");
        return Ok(2);
    };
    let o = parse_opts(&args[1..])?;
    progress::set_mode(o.mode);
    match cmd.as_str() {
        "add" => {
            let name = o.positional.first().cloned().ok_or_else(|| Failure::Msg("missing crate name".into()))?;
            let mut p = Project::locate(Path::new("."))?;
            let spec = DepSpec {
                version: if o.path.is_some() { None } else { Some(o.version.clone().unwrap_or_else(|| "*".into())) },
                path: o.path.clone(),
                features: o.features.clone(),
                ..Default::default()
            };
            p.manifest.dependencies.insert(name.clone(), spec);
            p.lock.crates.retain(|c| c.name != name);
            p.save_manifest()?;
            p.resolve()?;
            p.save_lock()?;
            let (_, auto, adapter, unsup, version) = driver::crate_report(&mut p, &name)?;
            eprintln!(
                "added {name} {version} — {} item(s): {auto} automatic, {adapter} adapter-backed, {unsup} unsupported (see `luarc bindings {name}`)",
                auto + adapter + unsup
            );
            Ok(0)
        }
        "bindings" => {
            let name = o.positional.first().cloned().ok_or_else(|| Failure::Msg("missing crate name".into()))?;
            let mut p = Project::locate(Path::new("."))?;
            let (text, ..) = driver::crate_report(&mut p, &name)?;
            print!("{text}");
            Ok(0)
        }
        "check" => {
            let entry = entry_of(&o)?;
            let mut p = project_for(&entry)?;
            driver::check(&entry, &mut p)?;
            eprintln!("{}: ok", entry.display());
            Ok(0)
        }
        "emit-rust" => {
            let entry = entry_of(&o)?;
            let mut p = project_for(&entry)?;
            let dir = o.out.clone();
            let g = driver::generate(&entry, &mut p, dir.as_deref(), dir.is_some())?;
            eprintln!("generated Rust package in {}", g.package_dir.display());
            Ok(0)
        }
        "build" => {
            let entry = entry_of(&o)?;
            let mut p = project_for(&entry)?;
            let b = driver::build(&entry, &mut p, o.release)?;
            for w in &b.warnings {
                eprintln!("luarc: warning in generated code (please report):\n{w}");
            }
            let out = o.out.clone().unwrap_or_else(|| {
                let stem = entry.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_else(|| "main".into());
                entry.with_file_name(format!("{stem}{}", std::env::consts::EXE_SUFFIX))
            });
            std::fs::copy(&b.exe, &out).map_err(|e| Failure::Msg(format!("cannot write {}: {e}", out.display())))?;
            eprintln!("built {}", out.display());
            Ok(0)
        }
        "run" => {
            let entry = entry_of(&o)?;
            let mut p = project_for(&entry)?;
            let b = driver::build(&entry, &mut p, o.release)?;
            for w in &b.warnings {
                eprintln!("luarc: warning in generated code (please report):\n{w}");
            }
            driver::run_exe(&b.exe, &o.rest)
        }
        "help" | "--help" | "-h" => {
            print!("{USAGE}");
            Ok(0)
        }
        other => Err(Failure::Msg(format!("unknown command '{other}'\n\n{USAGE}"))),
    }
}
