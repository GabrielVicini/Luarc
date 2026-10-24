//! Narrow egui/text-buffer and background-process bridge for main.luarc.
use eframe::egui::{self, Color32, FontId, RichText, Stroke, TextFormat};
use std::{
    collections::BTreeSet,
    fs,
    io::Read,
    path::PathBuf,
    process::{Command, Stdio},
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc, Arc,
    },
    time::{Duration, Instant},
};

const STARTER: &str = "-- Welcome to Luarc Studio\n-- Ctrl+Enter to compile and run. Checks run every 1.5s.\n\nlocal name = \"world\"\nprint(\"Hello, \" .. name .. \"!\")\n\nfor i = 1, 5 do\n    print(i, i * i)\nend\n\n-- Try: local regex = require(\"rust:regex\")\n";
const LIMIT: u64 = 128 * 1024;
const COMPILER: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/luarc.exe"));
const MANIFEST: &str = "[package]\nname = \"editor_scratch\"\n";

pub trait EditorApp {
    fn tick(&mut self, editor: &mut Editor);
}

struct ResultData {
    kind: String,
    ok: bool,
    text: String,
}
struct Worker {
    rx: mpsc::Receiver<ResultData>,
    cancel: Arc<AtomicBool>,
    log: PathBuf,
    kind: String,
}

/// Mutable frame state, lent to the Luarc callback on the UI thread only.
pub struct Editor {
    source: String,
    status: String,
    output: String,
    diagnostic: String,
    bad_lines: BTreeSet<usize>,
    package: String,
    installing: String,
    offer: bool,
    action: String,
    started: Instant,
    worker: Option<Worker>,
    result: ResultData,
    workspace: PathBuf,
    compiler: PathBuf,
    last_log: Instant,
    packages: Vec<String>,
    package_error: String,
}

impl Editor {
    pub fn source(&self) -> String {
        self.source.clone()
    }
    pub fn seconds(&self) -> f64 {
        self.started.elapsed().as_secs_f64()
    }
    pub fn busy(&self) -> bool {
        self.worker.is_some()
    }
    pub fn action(&mut self) -> String {
        std::mem::take(&mut self.action)
    }
    pub fn package(&self) -> String {
        self.package.clone()
    }
    pub fn installing_package(&self) -> String {
        self.installing.clone()
    }
    pub fn status(&mut self, text: String) {
        self.status = text;
    }
    pub fn output(&mut self, text: String) {
        self.output = text;
    }
    pub fn result_kind(&self) -> String {
        self.result.kind.clone()
    }
    pub fn result_ok(&self) -> bool {
        self.result.ok
    }
    pub fn result_text(&self) -> String {
        self.result.text.clone()
    }
    pub fn offer_package(&mut self, name: String) {
        self.package = name;
        self.offer = true;
    }
    pub fn clear_diagnostics(&mut self) {
        self.diagnostic.clear();
        self.bad_lines.clear();
    }
    pub fn diagnostics(&mut self, text: String) {
        self.bad_lines = diagnostic_lines(&text);
        self.diagnostic = text;
    }
    pub fn poll(&mut self) -> bool {
        let Some(worker) = &self.worker else {
            return false;
        };
        if worker.kind != "check" && self.last_log.elapsed() > Duration::from_millis(150) {
            self.output = read_log(&worker.log);
            self.last_log = Instant::now();
        }
        match worker.rx.try_recv() {
            Ok(result) => {
                self.result = result;
                self.worker = None;
                self.refresh_packages();
                true
            }
            Err(mpsc::TryRecvError::Disconnected) => {
                self.result = ResultData {
                    kind: worker.kind.clone(),
                    ok: false,
                    text: "Background worker stopped unexpectedly".into(),
                };
                self.worker = None;
                true
            }
            Err(_) => false,
        }
    }
    pub fn start_check(&mut self) {
        self.start("check", "");
    }
    pub fn start_run(&mut self) {
        self.start("run", "");
    }
    pub fn start_install(&mut self, package: String) {
        if valid_package(&package) {
            self.installing = package.clone();
            self.offer = false;
            self.start("install", &package);
        }
    }
    pub fn start_uninstall(&mut self, package: String) {
        if valid_package(&package) {
            self.offer = false;
            self.start("uninstall", &package);
        }
    }
    fn refresh_packages(&mut self) {
        match installed_packages(&self.workspace) {
            Ok(packages) => {
                self.packages = packages;
                self.package_error.clear();
            }
            Err(error) => {
                self.packages.clear();
                self.package_error = error;
            }
        }
    }
    fn start(&mut self, kind: &str, package: &str) {
        if self.busy() {
            return;
        }
        let entry = self.workspace.join("scratch.luarc");
        if let Err(e) = fs::write(&entry, &self.source) {
            self.status = format!("Cannot save scratch.luarc: {e}");
            return;
        }
        let log = self.workspace.join("worker.log");
        let cancel = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel();
        let compiler = self.compiler.clone();
        let workspace = self.workspace.clone();
        let kind_owned = kind.to_owned();
        let package = package.to_owned();
        let flag = cancel.clone();
        let worker_log = log.clone();
        std::thread::spawn(move || {
            let outcome = (|| -> Result<bool, String> {
                let file = fs::File::create(&worker_log).map_err(|e| e.to_string())?;
                if kind_owned == "uninstall" {
                    uninstall_package(&workspace, &package)?;
                    use std::io::Write;
                    writeln!(&file, "Uninstalled {package} from this scratch project.\nCached downloads and build artifacts were retained for faster builds.").map_err(|e| e.to_string())?;
                    return Ok(true);
                }
                let mut cmd = Command::new(&compiler);
                if kind_owned == "install" {
                    cmd.args(["add", &package]);
                } else if kind_owned == "run" {
                    cmd.args(["build", "scratch.luarc", "-o", "scratch-run.exe"]);
                } else {
                    cmd.args(["check", "scratch.luarc", "--quiet"]);
                }
                cmd.current_dir(&workspace);
                let ok = execute(cmd, &file, &flag, Duration::from_secs(600))?;
                if !ok || kind_owned != "run" {
                    return Ok(ok);
                }
                use std::io::Write;
                let mut file_ref = &file;
                writeln!(file_ref, "\n── Program output ──").map_err(|e| e.to_string())?;
                let mut program = Command::new(workspace.join("scratch-run.exe"));
                program.current_dir(&workspace);
                execute(program, &file, &flag, Duration::from_secs(30))
            })();
            let mut text = read_log(&worker_log);
            let ok = match outcome {
                Ok(ok) => ok,
                Err(e) => {
                    text.push_str(&format!("\n{e}"));
                    false
                }
            };
            if text.is_empty() {
                text = if ok {
                    "Check passed."
                } else {
                    "Command failed."
                }
                .into();
            }
            let _ = tx.send(ResultData {
                kind: kind_owned,
                ok,
                text,
            });
        });
        if kind != "check" {
            self.output = "Starting…".into();
        }
        self.worker = Some(Worker {
            rx,
            cancel,
            log,
            kind: kind.into(),
        });
    }
}

fn installed_packages(workspace: &std::path::Path) -> Result<Vec<String>, String> {
    let text = fs::read_to_string(workspace.join("luarc.toml")).map_err(|e| e.to_string())?;
    let manifest: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    let mut names = manifest
        .get("dependencies")
        .and_then(toml::Value::as_table)
        .map(|deps| deps.keys().cloned().collect::<Vec<_>>())
        .unwrap_or_default();
    names.sort();
    Ok(names)
}

fn uninstall_package(workspace: &std::path::Path, name: &str) -> Result<(), String> {
    if !valid_package(name) {
        return Err("Invalid package name".into());
    }
    let path = workspace.join("luarc.toml");
    let text = fs::read_to_string(&path).map_err(|e| e.to_string())?;
    let mut manifest: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    let deps = manifest
        .get_mut("dependencies")
        .and_then(toml::Value::as_table_mut)
        .ok_or("Project has no dependencies")?;
    if deps.remove(name).is_none() {
        return Err(format!("Package {name} is not installed"));
    }
    // Parse the lock before modifying either file; preserve other dependencies' pins.
    let lock_path = workspace.join("luarc.lock");
    let lock_text = match fs::read_to_string(&lock_path) {
        Ok(text) => Some(text),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
        Err(e) => return Err(e.to_string()),
    };
    let new_lock = if let Some(text) = lock_text {
        let mut lock: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
        if let Some(crates) = lock.get_mut("crate").and_then(toml::Value::as_array_mut) {
            crates.retain(|entry| entry.get("name").and_then(toml::Value::as_str) != Some(name));
        }
        Some(toml::to_string(&lock).map_err(|e| e.to_string())?)
    } else {
        None
    };
    // Publish the lock first: until the manifest changes, Luarc can re-resolve it.
    if let Some(text) = new_lock {
        fs::write(lock_path, text).map_err(|e| e.to_string())?;
    }
    fs::write(path, toml::to_string(&manifest).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())
}

fn prepare_workspace(executable: &std::path::Path) -> Result<(PathBuf, PathBuf), String> {
    let root = executable
        .parent()
        .ok_or("Executable has no parent directory")?;
    let workspace = root.join("scratch");
    fs::create_dir_all(&workspace)
        .map_err(|e| format!("Cannot create {}: {e}", workspace.display()))?;
    // create_new preserves an existing project, even when another launch races us.
    use std::io::Write;
    match fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(workspace.join("luarc.toml"))
    {
        Ok(mut file) => file
            .write_all(MANIFEST.as_bytes())
            .map_err(|e| e.to_string())?,
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(e) => return Err(e.to_string()),
    }
    if !workspace.join("scratch.luarc").exists() {
        fs::write(workspace.join("scratch.luarc"), STARTER).map_err(|e| e.to_string())?;
    }
    let compiler = if let Some(path) = std::env::var_os("LUARC_BIN") {
        let path = PathBuf::from(path);
        fs::canonicalize(path).map_err(|e| format!("Invalid LUARC_BIN: {e}"))?
    } else {
        let tools = workspace.join(".tools");
        fs::create_dir_all(&tools).map_err(|e| e.to_string())?;
        let path = tools.join("luarc.exe");
        if fs::read(&path).ok().as_deref() != Some(COMPILER) {
            fs::write(&path, COMPILER).map_err(|e| format!("Cannot unpack compiler: {e}"))?;
        }
        path
    };
    Ok((workspace, compiler))
}

fn valid_package(name: &str) -> bool {
    !name.is_empty()
        && name.as_bytes()[0].is_ascii_alphabetic()
        && name
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_' || c == b'-')
}

fn diagnostic_lines(text: &str) -> BTreeSet<usize> {
    text.lines()
        .filter_map(|line| {
            let (position, _) = line.split_once(": error:")?;
            let mut parts = position.rsplitn(3, ':');
            let _column = parts.next()?.parse::<usize>().ok()?;
            let row = parts.next()?.parse::<usize>().ok()?;
            let file = parts.next()?;
            if file.ends_with("scratch.luarc") {
                Some(row)
            } else {
                None
            }
        })
        .collect()
}

fn read_log(path: &std::path::Path) -> String {
    let Ok(mut file) = fs::File::open(path) else {
        return String::new();
    };
    use std::io::{Seek, SeekFrom};
    let size = file.metadata().map(|m| m.len()).unwrap_or(0);
    let _ = file.seek(SeekFrom::Start(size.saturating_sub(LIMIT)));
    let mut bytes = Vec::new();
    let _ = file.take(LIMIT).read_to_end(&mut bytes);
    let text = String::from_utf8_lossy(&bytes);
    if size > LIMIT {
        format!("[Earlier output truncated]\n{text}")
    } else {
        text.into_owned()
    }
}

fn execute(
    mut cmd: Command,
    file: &fs::File,
    cancel: &AtomicBool,
    timeout: Duration,
) -> Result<bool, String> {
    cmd.stdin(Stdio::null())
        .stdout(file.try_clone().map_err(|e| e.to_string())?)
        .stderr(file.try_clone().map_err(|e| e.to_string())?);
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        cmd.creation_flags(0x08000000); // CREATE_NO_WINDOW
    }
    let mut child = cmd
        .spawn()
        .map_err(|e| format!("Cannot start command: {e}"))?;
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            if !status.success() {
                return Err(format!("Process exited with {status}"));
            }
            return Ok(true);
        }
        if cancel.load(Ordering::Relaxed) || started.elapsed() >= timeout {
            // Kill descendants too: luarc build starts Cargo and rustc.
            #[cfg(windows)]
            {
                use std::os::windows::process::CommandExt;
                let _ = Command::new("taskkill")
                    .args(["/PID", &child.id().to_string(), "/T", "/F"])
                    .creation_flags(0x08000000)
                    .output();
            }
            let _ = child.kill();
            let _ = child.wait();
            return Err("Stopped or timed out (program limit: 30 seconds).".into());
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

struct Window<A> {
    app: A,
    editor: Editor,
}
impl<A: EditorApp> eframe::App for Window<A> {
    fn update(&mut self, ctx: &egui::Context, _: &mut eframe::Frame) {
        self.app.tick(&mut self.editor);
        let e = &mut self.editor;
        let busy = e.busy();
        if ctx.input(|i| i.modifiers.ctrl && i.key_pressed(egui::Key::Enter)) && !busy {
            e.action = "run".into();
        }
        egui::TopBottomPanel::top("toolbar").show(ctx, |ui| {
            ui.add_space(12.0);
            ui.horizontal(|ui| {
                ui.heading(
                    RichText::new("◈  LUARC STUDIO").color(Color32::from_rgb(145, 192, 255)),
                );
                ui.separator();
                ui.label("scratch.luarc");
                ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                    if ui
                        .add_enabled(
                            !busy,
                            egui::Button::new("▶  Run").fill(Color32::from_rgb(37, 99, 210)),
                        )
                        .clicked()
                    {
                        e.action = "run".into();
                    }
                    if ui.add_enabled(busy, egui::Button::new("■  Stop")).clicked() {
                        if let Some(w) = &e.worker {
                            w.cancel.store(true, Ordering::Relaxed);
                        }
                    }
                    ui.weak("Ctrl+Enter");
                });
            });
            ui.add_space(10.0);
        });
        egui::TopBottomPanel::bottom("status").show(ctx, |ui| {
            ui.horizontal(|ui| {
                if busy {
                    ui.spinner();
                }
                ui.label(&e.status);
                ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                    ui.weak("Luarc / native Rust  •  background checks: 1.5s");
                });
            });
        });
        egui::TopBottomPanel::bottom("output")
            .resizable(true)
            .default_height(215.0)
            .min_height(100.0)
            .show(ctx, |ui| {
                ui.horizontal(|ui| {
                    ui.strong("OUTPUT");
                    if ui.small_button("Clear").clicked() {
                        e.output.clear();
                    }
                });
                egui::ScrollArea::both()
                    .id_salt("output_scroll")
                    .stick_to_bottom(true)
                    .show(ui, |ui| {
                        ui.add(
                            egui::Label::new(RichText::new(&e.output).monospace()).selectable(true),
                        );
                    });
            });
        egui::SidePanel::right("problems")
            .default_width(290.0)
            .min_width(180.0)
            .show(ctx, |ui| {
                ui.add_space(12.0);
                ui.heading("Problems");
                ui.weak("Compiler diagnostics");
                ui.separator();
                ui.strong("Packages");
                ui.weak("Direct scratch-project dependencies");
                if !e.package_error.is_empty() {
                    ui.colored_label(Color32::LIGHT_RED, &e.package_error);
                }
                if e.packages.is_empty() {
                    ui.weak("No packages installed");
                }
                for package in e.packages.clone() {
                    ui.horizontal(|ui| {
                        ui.label(&package);
                        if ui
                            .add_enabled(!busy, egui::Button::new("Uninstall"))
                            .clicked()
                        {
                            e.package = package.clone();
                            e.action = "uninstall".into();
                        }
                    });
                }
                ui.separator();
                egui::ScrollArea::vertical().show(ui, |ui| {
                    if e.diagnostic.is_empty() {
                        ui.weak("Waiting for the next check…");
                    } else {
                        ui.add(
                            egui::Label::new(RichText::new(&e.diagnostic).monospace().color(
                                if e.bad_lines.is_empty() {
                                    Color32::from_rgb(149, 190, 215)
                                } else {
                                    Color32::from_rgb(255, 145, 156)
                                },
                            ))
                            .selectable(true),
                        );
                    }
                });
            });
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.add_space(8.0);
            ui.weak("EDITOR    /    Lua • Luau subset");
            ui.add_space(8.0);
            let bad = e.bad_lines.clone();
            let mut layouter = |ui: &egui::Ui, text: &str, _: f32| {
                let mut job = egui::text::LayoutJob::default();
                for (index, line) in text.split_inclusive('\n').enumerate() {
                    let invalid = bad.contains(&(index + 1));
                    let comment = line.trim_start().starts_with("--");
                    job.append(
                        line,
                        0.0,
                        TextFormat {
                            font_id: FontId::monospace(15.0),
                            color: if invalid {
                                Color32::from_rgb(255, 155, 165)
                            } else if comment {
                                Color32::from_rgb(102, 139, 168)
                            } else {
                                Color32::from_rgb(202, 221, 247)
                            },
                            background: if invalid {
                                Color32::from_rgb(65, 28, 46)
                            } else {
                                Color32::TRANSPARENT
                            },
                            underline: if invalid {
                                Stroke::new(1.0_f32, Color32::from_rgb(255, 100, 125))
                            } else {
                                Stroke::NONE
                            },
                            ..Default::default()
                        },
                    );
                }
                ui.fonts(|f| f.layout_job(job))
            };
            egui::ScrollArea::both()
                .id_salt("code_scroll")
                .show(ui, |ui| {
                    ui.horizontal_top(|ui| {
                        let numbers = (1..=e.source.lines().count().max(1)
                            + usize::from(e.source.ends_with('\n')))
                            .map(|n| format!("{n:>3}"))
                            .collect::<Vec<_>>()
                            .join("\n");
                        ui.add(egui::Label::new(
                            RichText::new(numbers)
                                .font(FontId::monospace(15.0))
                                .color(Color32::from_rgb(80, 112, 150)),
                        ));
                        if ui
                            .add(
                                egui::TextEdit::multiline(&mut e.source)
                                    .font(FontId::monospace(15.0))
                                    .code_editor()
                                    .desired_width(ui.available_width().max(500.0))
                                    .desired_rows(28)
                                    .frame(false)
                                    .layouter(&mut layouter),
                            )
                            .changed()
                        {
                            e.clear_diagnostics();
                            e.status = "Edited · waiting for background check".into();
                            e.offer = false;
                        }
                    });
                });
        });
        if e.offer {
            egui::Window::new("Install missing package?")
                .collapsible(false)
                .resizable(false)
                .anchor(egui::Align2::CENTER_CENTER, [0.0, 0.0])
                .show(ctx, |ui| {
                    ui.label(format!(
                        "require(\"rust:{}\") needs a project dependency.",
                        e.package
                    ));
                    ui.weak("Install from crates.io using luarc add. This can take a few minutes.");
                    ui.horizontal(|ui| {
                        if ui
                            .add_enabled(!busy, egui::Button::new("Install"))
                            .clicked()
                        {
                            e.action = "install".into();
                        }
                        if ui.button("Not now").clicked() {
                            e.action = "dismiss".into();
                            e.offer = false;
                        }
                    });
                });
        }
        ctx.request_repaint_after(Duration::from_millis(100));
    }
}

impl Drop for Editor {
    fn drop(&mut self) {
        if let Some(w) = &self.worker {
            w.cancel.store(true, Ordering::Relaxed);
        }
    }
}

/// Start the native window and invoke the Luarc controller once per UI frame.
pub fn run<A: EditorApp + 'static>(app: A) -> Result<(), String> {
    let executable = std::env::current_exe().map_err(|e| e.to_string())?;
    let (workspace, compiler) = prepare_workspace(&executable)?;
    let source =
        fs::read_to_string(workspace.join("scratch.luarc")).unwrap_or_else(|_| STARTER.into());
    let mut editor = Editor {
        source,
        status: "Ready".into(),
        output:
            "Program output will appear here.\nPrograms run with a 30 second limit and no stdin."
                .into(),
        diagnostic: String::new(),
        bad_lines: BTreeSet::new(),
        package: String::new(),
        installing: String::new(),
        offer: false,
        action: String::new(),
        started: Instant::now(),
        worker: None,
        result: ResultData {
            kind: String::new(),
            ok: false,
            text: String::new(),
        },
        workspace,
        compiler,
        last_log: Instant::now(),
        packages: Vec::new(),
        package_error: String::new(),
    };
    editor.refresh_packages();
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size([1200.0, 800.0])
            .with_min_inner_size([800.0, 560.0]),
        ..Default::default()
    };
    eframe::run_native(
        "Luarc Studio",
        options,
        Box::new(move |cc| {
            let mut visuals = egui::Visuals::dark();
            visuals.panel_fill = Color32::from_rgb(12, 21, 38);
            visuals.window_fill = Color32::from_rgb(18, 31, 53);
            visuals.extreme_bg_color = Color32::from_rgb(8, 16, 30);
            visuals.faint_bg_color = Color32::from_rgb(21, 36, 59);
            visuals.widgets.inactive.bg_fill = Color32::from_rgb(27, 45, 73);
            visuals.widgets.hovered.bg_fill = Color32::from_rgb(40, 66, 103);
            visuals.selection.bg_fill = Color32::from_rgb(38, 77, 136);
            cc.egui_ctx.set_visuals(visuals);
            Ok(Box::new(Window { app, editor }))
        }),
    )
    .map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn temp_project(label: &str) -> PathBuf {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "luarc editor {label} {} {nonce}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        path
    }

    #[test]
    fn relocated_editor_bootstraps_and_compiles_without_repository_paths() {
        let root = temp_project("portable");
        let (workspace, compiler) = prepare_workspace(&root.join("renamed-editor.exe")).unwrap();
        assert_eq!(workspace, root.join("scratch"));
        assert!(compiler.is_file());
        assert_eq!(
            installed_packages(&workspace).unwrap(),
            Vec::<String>::new()
        );
        fs::write(workspace.join("scratch.luarc"), "print(42)\n").unwrap();
        let output = Command::new(&compiler)
            .args(["run", "scratch.luarc", "--quiet"])
            .current_dir(&workspace)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
        // Reopening preserves source and the user's manifest.
        let manifest = "[package]\nname = \"kept\"\n[dependencies.regex]\nversion = \"1\"\n";
        fs::write(workspace.join("luarc.toml"), manifest).unwrap();
        prepare_workspace(&root.join("renamed-editor.exe")).unwrap();
        assert_eq!(
            fs::read_to_string(workspace.join("luarc.toml")).unwrap(),
            manifest
        );
        assert_eq!(
            fs::read_to_string(workspace.join("scratch.luarc")).unwrap(),
            "print(42)\n"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn uninstall_preserves_other_packages_and_build_cache() {
        let root = temp_project("uninstall");
        fs::write(root.join("luarc.toml"), "[package]\nname = \"scratch\"\n[dependencies.regex]\nversion = \"1\"\n[dependencies.semver]\nversion = \"1\"\n").unwrap();
        fs::write(root.join("luarc.lock"), "version = 1\n[[crate]]\nname = \"regex\"\nversion = \"1.0.0\"\n[[crate]]\nname = \"semver\"\nversion = \"1.0.28\"\n").unwrap();
        fs::create_dir(root.join(".luarc")).unwrap();
        fs::write(root.join(".luarc/keep"), "cached").unwrap();
        uninstall_package(&root, "regex").unwrap();
        assert_eq!(installed_packages(&root).unwrap(), vec!["semver"]);
        let lock: toml::Value =
            toml::from_str(&fs::read_to_string(root.join("luarc.lock")).unwrap()).unwrap();
        let crates = lock["crate"].as_array().unwrap();
        assert_eq!(crates.len(), 1);
        assert_eq!(crates[0]["name"].as_str(), Some("semver"));
        assert_eq!(crates[0]["version"].as_str(), Some("1.0.28"));
        assert!(root.join(".luarc/keep").exists());
        uninstall_package(&root, "semver").unwrap();
        assert!(installed_packages(&root).unwrap().is_empty());
        assert!(uninstall_package(&root, "missing").is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn windows_diagnostics_only_mark_scratch() {
        let text = "C:\\my project\\scratch.luarc:12:3: error: wrong type\nother.luarc:4:1: error: missing\nscratch.luarc:2:1: error: syntax";
        assert_eq!(diagnostic_lines(text), BTreeSet::from([2, 12]));
    }
    #[test]
    fn package_argument_validation() {
        assert!(valid_package("my-crate_2"));
        for name in ["", "--help", "x;whoami", "../x", "x y"] {
            assert!(!valid_package(name));
        }
    }
}
