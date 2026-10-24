//! Build progress: runs cargo with its output streamed, reporting named phases.
//!
//! The full stdout and stderr are still captured and returned (error reports
//! quote them); progress only observes the stderr status lines (`Updating`,
//! `Downloaded`, `Compiling`, ...). On a terminal one status line is rewritten in
//! place; otherwise a plain line is printed when a phase starts and ends.

use std::io::{BufRead, BufReader, IsTerminal, Read, Write};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Mutex;
use std::time::Instant;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// No progress output.
    Quiet,
    /// Named phases; a live status line on a terminal.
    Normal,
    /// Every cargo status line, plain.
    Verbose,
}

static MODE: AtomicU8 = AtomicU8::new(1);
/// Width of the status line currently shown (0 when none).
static LINE: Mutex<usize> = Mutex::new(0);

/// Status lines longer than this are cut (no terminal width probe on Windows).
const MAX_WIDTH: usize = 78;

pub fn set_mode(m: Mode) {
    MODE.store(m as u8, Ordering::Relaxed);
}

pub fn mode() -> Mode {
    match MODE.load(Ordering::Relaxed) {
        0 => Mode::Quiet,
        2 => Mode::Verbose,
        _ => Mode::Normal,
    }
}

fn live() -> bool {
    mode() == Mode::Normal && std::io::stderr().is_terminal()
}

/// Erases the status line (call before printing anything else to stderr).
pub fn clear() {
    let mut w = LINE.lock().unwrap_or_else(|e| e.into_inner());
    if *w > 0 {
        eprint!("\r{}\r", " ".repeat(*w));
        *w = 0;
    }
}

/// A permanent line, printed unless quiet.
pub fn note(msg: &str) {
    if mode() == Mode::Quiet {
        return;
    }
    clear();
    eprintln!("{msg}");
}

fn status(msg: &str) {
    if !live() {
        return;
    }
    let mut w = LINE.lock().unwrap_or_else(|e| e.into_inner());
    let mut text: String = msg.chars().take(MAX_WIDTH).collect();
    let len = text.chars().count();
    if len < *w {
        text.push_str(&" ".repeat(*w - len));
    }
    eprint!("\r{text}");
    let _ = std::io::stderr().flush();
    *w = (*w).max(len);
}

/// Counters of one cargo run, reduced from its stderr status lines.
#[derive(Default)]
struct Tally {
    compiled: usize,
    downloaded: usize,
}

impl Tally {
    /// Updates the counters from one stderr line; returns the status to show.
    fn line(&mut self, phase: &str, line: &str) -> Option<String> {
        let t = line.trim_start();
        let (verb, rest) = t.split_once(' ')?;
        match verb {
            "Updating" => Some(format!("{phase}: updating the registry index")),
            "Downloading" => Some(format!("{phase}: downloading crates ({} done)", self.downloaded)),
            "Downloaded" => {
                self.downloaded += 1;
                Some(format!("{phase}: downloaded {} ({} done)", short(rest), self.downloaded))
            }
            "Compiling" | "Checking" | "Documenting" => {
                self.compiled += 1;
                let what = if verb == "Documenting" { "documenting" } else { "compiling" };
                Some(format!("{phase}: {what} {} ({} built)", short(rest), self.compiled))
            }
            _ => None,
        }
    }

    fn summary(&self) -> String {
        let mut parts = Vec::new();
        if self.downloaded > 0 {
            parts.push(format!("{} downloaded", self.downloaded));
        }
        if self.compiled > 0 {
            parts.push(format!("{} built", self.compiled));
        }
        parts.join(", ")
    }
}

/// `name vX.Y.Z (path)` → `name vX.Y.Z`.
fn short(rest: &str) -> &str {
    rest.split(" (").next().unwrap_or(rest).trim()
}

/// Runs `cmd` like `Command::output`, reporting progress under the name `phase`
/// (e.g. "building", "resolving dependencies").
pub fn run(mut cmd: Command, phase: &str) -> std::io::Result<Output> {
    let started = Instant::now();
    let m = mode();
    if m != Mode::Quiet && !live() {
        eprintln!("luarc: {phase}...");
    }
    status(&format!("{phase}..."));
    cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = cmd.spawn()?;
    let mut out_pipe = child.stdout.take().expect("piped stdout");
    let err_pipe = child.stderr.take().expect("piped stderr");
    // stdout must be drained concurrently or a full pipe would stall cargo
    let reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = out_pipe.read_to_end(&mut buf);
        buf
    });
    let mut tally = Tally::default();
    let mut stderr = Vec::new();
    let mut r = BufReader::new(err_pipe);
    let mut raw = Vec::new();
    loop {
        raw.clear();
        match r.read_until(b'\n', &mut raw) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        stderr.extend_from_slice(&raw);
        let line = String::from_utf8_lossy(&raw);
        let line = line.trim_end();
        if m == Mode::Verbose {
            clear();
            eprintln!("{line}");
        }
        if let Some(s) = tally.line(phase, line) {
            status(&s);
        }
    }
    let status_code = child.wait()?;
    let stdout = reader.join().unwrap_or_default();
    clear();
    if m != Mode::Quiet {
        let secs = started.elapsed().as_secs_f32();
        let detail = tally.summary();
        let tail = if detail.is_empty() { String::new() } else { format!(" ({detail})") };
        if status_code.success() {
            // quick phases (cached, nothing to build) stay silent on a terminal
            if !live() || secs >= 1.0 || !detail.is_empty() {
                eprintln!("luarc: {phase} done in {secs:.1}s{tail}");
            }
        } else {
            eprintln!("luarc: {phase} failed after {secs:.1}s{tail}");
        }
    }
    Ok(Output { status: status_code, stdout, stderr })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn status_lines_are_reduced_to_counters() {
        let mut t = Tally::default();
        assert_eq!(t.line("building", "    Updating crates.io index").unwrap(), "building: updating the registry index");
        assert_eq!(t.line("building", " Downloaded regex v1.13.1").unwrap(), "building: downloaded regex v1.13.1 (1 done)");
        assert!(t.line("building", "   Compiling serde v1.0.0").unwrap().ends_with("compiling serde v1.0.0 (1 built)"));
        // the path of a local package is not part of the status
        assert_eq!(
            t.line("building", "   Compiling main v0.1.0 (C:/a b/c)").unwrap(),
            "building: compiling main v0.1.0 (2 built)"
        );
        assert!(t.line("building", "warning: unused variable").is_none());
        assert!(t.line("building", "").is_none());
        assert_eq!(t.summary(), "1 downloaded, 2 built");
    }
}
