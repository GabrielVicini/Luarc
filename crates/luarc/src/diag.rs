//! Source locations and diagnostics.

use std::fmt;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub file: u32,
    pub line: u32,
    pub col: u32,
}

/// Registry of source files (index = `Span::file`).
#[derive(Default, Clone)]
pub struct SourceMap {
    pub files: Vec<SourceFile>,
}

#[derive(Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    /// Short display name used in diagnostics and runtime error positions.
    pub display: String,
    pub text: String,
}

impl SourceMap {
    pub fn add(&mut self, path: PathBuf, display: String, text: String) -> u32 {
        self.files.push(SourceFile { path, display, text });
        (self.files.len() - 1) as u32
    }
    pub fn display(&self, file: u32) -> &str {
        &self.files[file as usize].display
    }
    /// `file:line` as used by runtime error messages.
    pub fn loc(&self, sp: Span) -> String {
        format!("{}:{}", self.display(sp.file), sp.line)
    }
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub span: Span,
    pub msg: String,
    pub notes: Vec<String>,
}

impl Diagnostic {
    pub fn new(span: Span, msg: impl Into<String>) -> Self {
        Diagnostic { span, msg: msg.into(), notes: Vec::new() }
    }
    pub fn note(mut self, n: impl Into<String>) -> Self {
        self.notes.push(n.into());
        self
    }
    pub fn render(&self, sm: &SourceMap) -> String {
        let mut s = format!(
            "{}:{}:{}: error: {}",
            sm.files.get(self.span.file as usize).map(|f| f.display.as_str()).unwrap_or("<unknown>"),
            self.span.line,
            self.span.col,
            self.msg
        );
        if let Some(f) = sm.files.get(self.span.file as usize) {
            if let Some(line) = f.text.lines().nth(self.span.line.saturating_sub(1) as usize) {
                // Columns count bytes. The caret copies the line's tabs and puts one
                // space per character before it, so it lines up under tab-indented
                // and non-ASCII source.
                let n = (self.span.col.saturating_sub(1) as usize).min(line.len());
                let pad: String =
                    String::from_utf8_lossy(&line.as_bytes()[..n]).chars().map(|c| if c == '\t' { '\t' } else { ' ' }).collect();
                s.push_str(&format!("\n  {:>4} | {}\n       | {}^", self.span.line, line, pad));
            }
        }
        for n in &self.notes {
            s.push_str(&format!("\n  note: {n}"));
        }
        s
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.span.line, self.span.col, self.msg)
    }
}

pub type DResult<T> = Result<T, Vec<Diagnostic>>;

pub fn err<T>(span: Span, msg: impl Into<String>) -> DResult<T> {
    Err(vec![Diagnostic::new(span, msg)])
}
