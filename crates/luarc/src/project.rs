//! Project manifest (`luarc.toml`), lockfile (`luarc.lock`), the managed Cargo
//! workspaces under `.luarc/`, and the extraction cache.
//!
//! Layout:
//! ```text
//! luarc.toml            manifest (dependencies)
//! luarc.lock            resolved versions/features + pinned Cargo.lock
//! adapters/*.toml       project adapters (optional)
//! .luarc/runtime/       copy of the runtime crate linked into programs
//! .luarc/deps/          dependency workspace (metadata + rustdoc extraction)
//! .luarc/probe/         path-validation crate for imported items
//! .luarc/build/<name>/  generated Cargo package for one entry point
//! .luarc/target*/       Cargo target directories
//! .luarc/cache/         extracted API models (keyed by fingerprint)
//! ```

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::{Deserialize, Serialize};

use std::collections::HashMap;

use crate::native::adapters;
use crate::native::world::{self, CrateInfo, LoadedCrate};

pub const LUARC_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Runtime crate sources embedded into the compiler (generated programs link this).
pub const RUNTIME_FILES: &[(&str, &str)] = &[
    ("src/lib.rs", include_str!("../../luarc-runtime/src/lib.rs")),
    ("src/value.rs", include_str!("../../luarc-runtime/src/value.rs")),
    ("src/error.rs", include_str!("../../luarc-runtime/src/error.rs")),
    ("src/show.rs", include_str!("../../luarc-runtime/src/show.rs")),
    ("src/handle.rs", include_str!("../../luarc-runtime/src/handle.rs")),
    ("src/callback.rs", include_str!("../../luarc-runtime/src/callback.rs")),
    ("src/conv.rs", include_str!("../../luarc-runtime/src/conv.rs")),
    ("src/dynamic.rs", include_str!("../../luarc-runtime/src/dynamic.rs")),
    ("src/dynamic_key.rs", include_str!("../../luarc-runtime/src/dynamic_key.rs")),
    ("src/dynamic_fn.rs", include_str!("../../luarc-runtime/src/dynamic_fn.rs")),
    ("src/table.rs", include_str!("../../luarc-runtime/src/table.rs")),

    ("src/bit32.rs", include_str!("../../luarc-runtime/src/bit32.rs")),
    ("src/library.rs", include_str!("../../luarc-runtime/src/library.rs")),
    ("src/table_library.rs", include_str!("../../luarc-runtime/src/table_library.rs")),

    ("src/coroutine.rs", include_str!("../../luarc-runtime/src/coroutine.rs")),

    ("src/table_layout.rs", include_str!("../../luarc-runtime/src/table_layout.rs")),

    ("src/stdlib.rs", include_str!("../../luarc-runtime/src/stdlib.rs")),
    ("src/gc.rs", include_str!("../../luarc-runtime/src/gc.rs")),
    ("src/subst.rs", include_str!("../../luarc-runtime/src/subst.rs")),
    ("src/fmt.rs", include_str!("../../luarc-runtime/src/fmt.rs")),
    ("src/pattern.rs", include_str!("../../luarc-runtime/src/pattern.rs")),
    ("src/int.rs", include_str!("../../luarc-runtime/src/int.rs")),
    ("src/task.rs", include_str!("../../luarc-runtime/src/task.rs")),
    ("src/shutdown.rs", include_str!("../../luarc-runtime/src/shutdown.rs")),
    ("src/va.rs", include_str!("../../luarc-runtime/src/va.rs")),
    ("src/packs.rs", include_str!("../../luarc-runtime/src/packs.rs")),
    ("src/traversal.rs", include_str!("../../luarc-runtime/src/traversal.rs")),
];

/// Exact versions of the runtime's own dependencies (kept in sync with
/// `crates/luarc-runtime/Cargo.toml`).
pub const RUNTIME_DEPS: &str = "dumpster = \"=2.1.0\"\ncorosensei = \"=0.3.4\"\n";

/// `Cargo.toml` of the runtime copy linked into generated programs.
pub fn runtime_manifest() -> String {
    format!(
        "[package]\nname = \"luarc-runtime\"\nversion = \"{LUARC_VERSION}\"\nedition = \"2021\"\npublish = false\n\n[lib]\npath = \"src/lib.rs\"\n\n[dependencies]\n{RUNTIME_DEPS}"
    )
}

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct Manifest {
    #[serde(default)]
    pub package: PackageSection,
    #[serde(default)]
    pub dependencies: BTreeMap<String, DepSpec>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct PackageSection {
    pub name: String,
}

impl Default for PackageSection {
    fn default() -> Self {
        PackageSection { name: "app".into() }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, Default, PartialEq)]
pub struct DepSpec {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub git: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rev: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub features: Vec<String>,
    #[serde(rename = "default-features", skip_serializing_if = "Option::is_none")]
    pub default_features: Option<bool>,
}

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct Lockfile {
    pub version: u32,
    #[serde(default, rename = "crate")]
    pub crates: Vec<LockedCrate>,
    #[serde(default)]
    pub cargo_lock: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct LockedCrate {
    pub name: String,
    pub version: String,
    pub source: String,
    pub features: Vec<String>,
    pub api_fingerprint: String,
    /// Fingerprint of the manifest entry (and a path dependency's own Cargo.toml)
    /// this resolution was made from; a different one re-resolves.
    /// Empty in lockfiles written before it existed (then the lock is trusted).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub spec: String,
}

pub struct Project {
    pub root: PathBuf,
    pub manifest: Manifest,
    pub has_manifest: bool,
    pub lock: Lockfile,
    /// Messages for the user (stderr), e.g. progress of extraction.
    pub verbose: bool,
}

fn hash_bytes(data: &[u8], mut h: u64) -> u64 {
    // FNV-1a (stable across Rust versions, unlike `DefaultHasher`).
    for b in data {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

pub fn fingerprint(parts: &[&[u8]]) -> String {
    let mut a = 0xcbf29ce484222325u64;
    let mut b = 0x84222325cbf29ce4u64;
    for p in parts {
        a = hash_bytes(p, a);
        a = hash_bytes(&[0xff], a);
        b = hash_bytes(p, b ^ 0x9e3779b97f4a7c15);
    }
    format!("{a:016x}{b:016x}")
}

/// Hash of all files of a local crate (sources and manifest), excluding `target`.
fn dir_hash(dir: &Path) -> String {
    let mut files = Vec::new();
    fn walk(d: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = fs::read_dir(d) else { return };
        for e in rd.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            if p.is_dir() {
                if name != "target" && !name.starts_with('.') {
                    walk(&p, out);
                }
            } else {
                out.push(p);
            }
        }
    }
    walk(dir, &mut files);
    files.sort();
    let mut parts: Vec<Vec<u8>> = Vec::new();
    for f in files {
        parts.push(f.strip_prefix(dir).unwrap_or(&f).to_string_lossy().replace('\\', "/").into_bytes());
        parts.push(fs::read(&f).unwrap_or_default());
    }
    let refs: Vec<&[u8]> = parts.iter().map(|v| v.as_slice()).collect();
    fingerprint(&refs)
}

/// `fs::canonicalize` without Windows verbatim prefixes (`\\?\C:\...`), which Cargo
/// manifests and many tools do not accept.
pub fn canon(p: &Path) -> std::io::Result<PathBuf> {
    let c = fs::canonicalize(p)?;
    let s = c.to_string_lossy();
    if let Some(rest) = s.strip_prefix(r"\\?\") {
        if rest.as_bytes().get(1) == Some(&b':') {
            return Ok(PathBuf::from(rest));
        }
    }
    Ok(c)
}

/// Writes a file only when its content changed (keeps Cargo's incremental state).
/// The write is atomic (see [`write_atomic`]).
pub fn write_if_changed(path: &Path, content: &str) -> Result<(), String> {
    if let Ok(old) = fs::read_to_string(path) {
        if old == content {
            return Ok(());
        }
    }
    write_atomic(path, content.as_bytes())
}

pub fn toml_str(s: &str) -> String {
    format!("{s:?}").replace("\\\\", "/")
}

/// `cargo` from PATH (the rustup proxy, so `+toolchain` selection works).
pub fn cargo() -> Command {
    Command::new("cargo")
}


impl Project {
    /// Finds the project for `start` (a directory): nearest ancestor with
    /// `luarc.toml`, else `start` itself (manifest created on demand).
    pub fn locate(start: &Path) -> Result<Project, String> {
        let start = canon(start).map_err(|e| format!("cannot access {}: {e}", start.display()))?;
        let mut dir = Some(start.as_path());
        let mut found = None;
        while let Some(d) = dir {
            if d.join("luarc.toml").is_file() {
                found = Some(d.to_path_buf());
                break;
            }
            dir = d.parent();
        }
        let (root, has) = match found {
            Some(r) => (r, true),
            None => (start.clone(), false),
        };
        let manifest = if has {
            let text = fs::read_to_string(root.join("luarc.toml")).map_err(|e| e.to_string())?;
            toml::from_str(&text).map_err(|e| format!("luarc.toml: {e}"))?
        } else {
            Manifest {
                package: PackageSection {
                    name: root.file_name().map(|n| n.to_string_lossy().to_string()).unwrap_or_else(|| "app".into()),
                },
                ..Default::default()
            }
        };
        let lock = match fs::read_to_string(root.join("luarc.lock")) {
            Ok(t) => toml::from_str(&t).map_err(|e| format!("luarc.lock: {e}"))?,
            Err(_) => Lockfile { version: 1, ..Default::default() },
        };
        Ok(Project { root, manifest, has_manifest: has, lock, verbose: true })
    }

    pub fn dot(&self) -> PathBuf {
        self.root.join(".luarc")
    }

    pub fn save_manifest(&mut self) -> Result<(), String> {
        let text = format!(
            "# luarc project manifest\n{}",
            toml::to_string_pretty(&self.manifest).map_err(|e| e.to_string())?
        );
        fs::write(self.root.join("luarc.toml"), text).map_err(|e| e.to_string())?;
        self.has_manifest = true;
        Ok(())
    }

    pub fn save_lock(&self) -> Result<(), String> {
        let text = format!(
            "# Generated by luarc {LUARC_VERSION}. Pins resolved dependency versions and features.\n{}",
            toml::to_string_pretty(&self.lock).map_err(|e| e.to_string())?
        );
        write_if_changed(&self.root.join("luarc.lock"), &text)
    }

    fn log(&self, msg: &str) {
        if self.verbose {
            crate::progress::note(msg);
        }
    }

    /// Absolute path of a path dependency.
    /// Fingerprint of a dependency's manifest entry plus, for a path dependency,
    /// its Cargo.toml (version, features, lib name).
    pub fn dep_spec_fingerprint(&self, spec: &DepSpec) -> String {
        let entry = serde_json::to_string(spec).unwrap_or_default();
        let local = self.dep_path(spec).and_then(|p| fs::read(p.join("Cargo.toml")).ok()).unwrap_or_default();
        fingerprint(&[entry.as_bytes(), &local])
    }

    /// The locked crate of `name` if it was resolved from the current manifest entry.
    fn locked_current(&self, name: &str, spec: &DepSpec) -> Option<&LockedCrate> {
        let c = self.lock.crates.iter().find(|c| c.name == name)?;
        (c.spec.is_empty() || c.spec == self.dep_spec_fingerprint(spec)).then_some(c)
    }

    pub fn dep_path(&self, spec: &DepSpec) -> Option<PathBuf> {
        spec.path.as_ref().map(|p| {
            let pb = PathBuf::from(p);
            let abs = if pb.is_absolute() { pb } else { self.root.join(pb) };
            canon(&abs).unwrap_or(abs)
        })
    }

    /// `[dependencies]` lines for generated Cargo manifests (versions pinned by the lock).
    pub fn cargo_deps(&self) -> String {
        let mut s = String::new();
        for (name, spec) in &self.manifest.dependencies {
            let mut parts = Vec::new();
            if let Some(p) = self.dep_path(spec) {
                parts.push(format!("path = {}", toml_str(&p.to_string_lossy())));
            } else if let Some(g) = &spec.git {
                parts.push(format!("git = {}", toml_str(g)));
                if let Some(r) = &spec.rev {
                    parts.push(format!("rev = {}", toml_str(r)));
                }
            } else {
                // the lock pins the version only while the manifest entry is unchanged
                let locked = self.locked_current(name, spec).map(|c| format!("={}", c.version));
                let v = locked.or_else(|| spec.version.clone()).unwrap_or_else(|| "*".into());
                parts.push(format!("version = {}", toml_str(&v)));
            }
            if !spec.features.is_empty() {
                parts.push(format!("features = [{}]", spec.features.iter().map(|f| toml_str(f)).collect::<Vec<_>>().join(", ")));
            }
            if let Some(d) = spec.default_features {
                parts.push(format!("default-features = {d}"));
            }
            s.push_str(&format!("{} = {{ {} }}\n", name, parts.join(", ")));
        }
        s
    }

    pub fn write_runtime(&self) -> Result<PathBuf, String> {
        let dir = self.dot().join("runtime");
        write_if_changed(&dir.join("Cargo.toml"), &runtime_manifest())?;
        for (p, c) in RUNTIME_FILES {
            write_if_changed(&dir.join(p), c)?;
        }
        Ok(dir)
    }

    fn write_lock_into(&self, dir: &Path) -> Result<(), String> {
        if !self.lock.cargo_lock.is_empty() {
            write_if_changed(&dir.join("Cargo.lock"), &self.lock.cargo_lock)?;
        }
        Ok(())
    }

    fn deps_dir(&self) -> Result<PathBuf, String> {
        let dir = self.dot().join("deps");
        let toml = format!(
            "[package]\nname = \"luarc-deps\"\nversion = \"0.0.0\"\nedition = \"2021\"\npublish = false\n\n[lib]\npath = \"lib.rs\"\n\n[dependencies]\n# the runtime is part of the workspace so Cargo.lock pins its dependencies too\nluarc-runtime = {{ path = {} }}\n{}\n[workspace]\n",
            toml_str(&self.write_runtime()?.to_string_lossy()),
            self.cargo_deps()
        );
        write_if_changed(&dir.join("Cargo.toml"), &toml)?;
        write_if_changed(&dir.join("lib.rs"), "// dependency workspace managed by luarc\n")?;
        self.write_lock_into(&dir)?;
        Ok(dir)
    }

    /// Resolves dependencies with `cargo metadata`; refreshes the lockfile.
    pub fn resolve(&mut self) -> Result<(), String> {
        let dir = self.deps_dir()?;
        let mut cmd = cargo();
        cmd.arg("metadata").arg("--format-version").arg("1").arg("--manifest-path").arg(dir.join("Cargo.toml"));
        let out = crate::progress::run(cmd, "resolving dependencies").map_err(|e| format!("cannot run cargo: {e}"))?;
        if !out.status.success() {
            return Err(format!("dependency resolution failed:\n{}", String::from_utf8_lossy(&out.stderr)));
        }
        let meta: serde_json::Value = serde_json::from_slice(&out.stdout).map_err(|e| e.to_string())?;
        let packages = meta["packages"].as_array().cloned().unwrap_or_default();
        let nodes = meta["resolve"]["nodes"].as_array().cloned().unwrap_or_default();
        let root = meta["resolve"]["root"].as_str().unwrap_or("").to_string();
        let root_node = nodes.iter().find(|n| n["id"] == root.as_str()).cloned().unwrap_or_default();
        let mut crates = Vec::new();
        for d in root_node["deps"].as_array().cloned().unwrap_or_default() {
            let id = d["pkg"].as_str().unwrap_or("");
            let Some(p) = packages.iter().find(|p| p["id"] == id) else { continue };
            let node = nodes.iter().find(|n| n["id"] == id).cloned().unwrap_or_default();
            let name = p["name"].as_str().unwrap_or("").to_string();
            if !self.manifest.dependencies.contains_key(&name) {
                continue;
            }
            let mut features: Vec<String> =
                node["features"].as_array().cloned().unwrap_or_default().iter().filter_map(|f| f.as_str().map(String::from)).collect();
            features.sort();
            let source = p["source"].as_str().map(String::from).unwrap_or_else(|| {
                format!("path+{}", p["manifest_path"].as_str().unwrap_or("").replace('\\', "/"))
            });
            let old_fp = self.lock.crates.iter().find(|c| c.name == name).map(|c| c.api_fingerprint.clone()).unwrap_or_default();
            let spec = self.dep_spec_fingerprint(&self.manifest.dependencies[&name]);
            crates.push(LockedCrate {
                spec,
                name,
                version: p["version"].as_str().unwrap_or("").to_string(),
                source,
                features,
                api_fingerprint: old_fp,
            });
        }
        self.lock.version = 1;
        self.lock.crates = crates;
        self.lock.cargo_lock = fs::read_to_string(dir.join("Cargo.lock")).unwrap_or_default();
        Ok(())
    }

    /// Adapter files: shipped ones first, then the project's `adapters/*.toml`.
    pub fn adapter_texts(&self) -> Vec<(String, String)> {
        let mut v: Vec<(String, String)> = adapters::SHIPPED.iter().map(|(n, t)| (format!("shipped:{n}"), t.to_string())).collect();
        if let Ok(rd) = fs::read_dir(self.root.join("adapters")) {
            let mut files: Vec<PathBuf> = rd.flatten().map(|e| e.path()).filter(|p| p.extension().map(|e| e == "toml").unwrap_or(false)).collect();
            files.sort();
            for f in files {
                if let Ok(t) = fs::read_to_string(&f) {
                    v.push((f.display().to_string(), t));
                }
            }
        }
        v
    }

    /// The resolved package graph of the dependency workspace (cached by the
    /// contents of its manifest and `Cargo.lock`).
    pub fn package_graph(&mut self) -> Result<PackageGraph, String> {
        if self.manifest.dependencies.is_empty() {
            return Ok(PackageGraph::default());
        }
        if self.lock.crates.is_empty() || self.manifest.dependencies.iter().any(|(n, s)| self.locked_current(n, s).is_none()) {
            self.resolve()?;
            self.save_lock()?;
        }
        let dir = self.deps_dir()?;
        let key = fingerprint(&[
            fs::read(dir.join("Cargo.toml")).unwrap_or_default().as_slice(),
            fs::read(dir.join("Cargo.lock")).unwrap_or_default().as_slice(),
            LUARC_VERSION.as_bytes(),
        ]);
        let cache = self.dot().join("cache").join(format!("graph-{key}.json"));
        if let Ok(text) = fs::read_to_string(&cache) {
            if let Ok(g) = serde_json::from_str::<PackageGraph>(&text) {
                return Ok(g);
            }
        }
        let mut cmd = cargo();
        cmd.arg("metadata").arg("--format-version").arg("1").arg("--manifest-path").arg(dir.join("Cargo.toml"));
        let out = crate::progress::run(cmd, "resolving dependencies").map_err(|e| format!("cannot run cargo: {e}"))?;
        if !out.status.success() {
            return Err(format!("dependency resolution failed:\n{}", String::from_utf8_lossy(&out.stderr)));
        }
        let meta: serde_json::Value = serde_json::from_slice(&out.stdout).map_err(|e| e.to_string())?;
        let g = PackageGraph::from_metadata(&meta, &self.manifest);
        write_if_changed(&cache, &serde_json::to_string(&g).map_err(|e| e.to_string())?)?;
        Ok(g)
    }

    /// Loads the model of package `key` (`name@version`) or a toolchain crate
    /// (`std@toolchain`), extracting it on first use.
    pub fn load_crate(&mut self, graph: &PackageGraph, key: &str) -> Result<LoadedCrate, String> {
        if let Some(lib) = key.strip_suffix("@toolchain") {
            return self.load_toolchain_crate(lib);
        }
        let pkg = graph.packages.get(key).ok_or_else(|| format!("package {key} is not part of the resolved dependency graph"))?.clone();
        let tc = check_extraction_toolchain()?;
        let content = match &pkg.local_dir {
            Some(p) => dir_hash(Path::new(p)),
            None => String::new(),
        };
        let fp = fingerprint(&[
            pkg.name.as_bytes(),
            pkg.version.as_bytes(),
            pkg.source.as_bytes(),
            pkg.features.join(",").as_bytes(),
            content.as_bytes(),
            tc.rustc.as_bytes(),
            world::FORMAT_VERSION.to_string().as_bytes(), world::MODEL_VERSION.as_bytes(),
            LUARC_VERSION.as_bytes(),
            std::env::consts::ARCH.as_bytes(),
            std::env::consts::OS.as_bytes(),
        ]);
        let info = CrateInfo {
            package: pkg.name.clone(),
            version: pkg.version.clone(),
            lib: pkg.lib.clone(),
            key: key.to_string(),
            direct: pkg.direct,
            toolchain: false,
            deps: pkg.deps.clone(),
            features: pkg.features.clone(),
        };
        let cache = self.dot().join("cache").join(format!("{}-{fp}.json", pkg.name));
        if let Ok(bytes) = fs::read(&cache) {
            if let Ok(doc) = serde_json::from_slice::<rustdoc_types::Crate>(&bytes) {
                return Ok(LoadedCrate::new(info, doc));
            }
        }
        let dir = self.deps_dir()?;
        let target = self.dot().join("target-doc");
        let mut cmd = cargo();
        cmd.arg(format!("+{}", tc.toolchain))
            .arg("doc")
            .arg("--no-deps")
            .arg("--lib")
            .arg("-p")
            .arg(format!("{}@{}", pkg.name, pkg.version))
            .arg("--manifest-path")
            .arg(dir.join("Cargo.toml"))
            .arg("--target-dir")
            .arg(&target)
            .env("RUSTDOCFLAGS", "-Z unstable-options --output-format json")
            .env_remove("RUSTC")
            .env_remove("RUSTDOC");
        let out = crate::progress::run(cmd, &format!("extracting API of {}", pkg.name)).map_err(|e| format!("cannot run cargo: {e}"))?;
        if !out.status.success() {
            return Err(format!(
                "rustdoc JSON extraction for '{}' failed (toolchain '{}'):\n{}",
                pkg.name,
                tc.toolchain,
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        let json_path = target.join("doc").join(format!("{}.json", pkg.lib));
        let text = fs::read(&json_path).map_err(|e| format!("cannot read {}: {e}", json_path.display()))?;
        let mut doc = parse_rustdoc(&text, &pkg.name)?;
        world::prune(&mut doc);
        write_atomic(&cache, &serde_json::to_vec(&doc).map_err(|e| e.to_string())?)?;
        Ok(LoadedCrate::new(info, doc))
    }

    /// `std`, `core` or `alloc` from the pinned nightly's `rust-docs-json`
    /// component. Toolchain models are cached under the project.
    fn load_toolchain_crate(&mut self, lib: &str) -> Result<LoadedCrate, String> {
        let tc = check_extraction_toolchain()?;
        let deps: BTreeMap<String, String> = match lib {
            "std" => [("core", "core@toolchain"), ("alloc", "alloc@toolchain")].iter().map(|(a, b)| (a.to_string(), b.to_string())).collect(),
            "alloc" => [("core", "core@toolchain")].iter().map(|(a, b)| (a.to_string(), b.to_string())).collect(),
            _ => BTreeMap::new(),
        };
        let info = CrateInfo {
            package: lib.to_string(),
            version: tc.rustc.clone(),
            lib: lib.to_string(),
            key: format!("{lib}@toolchain"),
            direct: lib == "std",
            toolchain: true,
            deps,
            features: Vec::new(),
        };
        let fp = fingerprint(&[lib.as_bytes(), tc.rustc.as_bytes(), world::FORMAT_VERSION.to_string().as_bytes(), world::MODEL_VERSION.as_bytes(), LUARC_VERSION.as_bytes()]);
        let cache = self.dot().join("cache").join(format!("toolchain-{lib}-{fp}.json"));
        if let Ok(bytes) = fs::read(&cache) {
            if let Ok(doc) = serde_json::from_slice::<rustdoc_types::Crate>(&bytes) {
                return Ok(LoadedCrate::new(info, doc));
            }
        }
        let path = tc.sysroot.join("share").join("doc").join("rust").join("json").join(format!("{lib}.json"));
        let text = fs::read(&path).map_err(|_| {
            format!(
                "the standard library API model is missing ({}): install it with `rustup component add rust-docs-json --toolchain {}`",
                path.display(),
                tc.toolchain
            )
        })?;
        self.log(&format!("luarc: loading {lib} API model ({})", tc.rustc));
        let mut doc = parse_rustdoc(&text, lib)?;
        world::prune(&mut doc);
        write_atomic(&cache, &serde_json::to_vec(&doc).map_err(|e| e.to_string())?)?;
        Ok(LoadedCrate::new(info, doc))
    }

    /// Package key of a direct dependency (or the standard library).
    pub fn crate_key(&self, graph: &PackageGraph, name: &str) -> Result<String, String> {
        if name == "std" {
            return Ok("std@toolchain".into());
        }
        let pkg = if self.manifest.dependencies.contains_key(name) {
            name.to_string()
        } else {
            self.manifest
                .dependencies
                .keys()
                .find(|k| k.replace('-', "_") == name)
                .cloned()
                .ok_or_else(|| format!("crate '{name}' is not a dependency of this project; run `luarc add {name}`"))?
        };
        graph
            .packages
            .values()
            .find(|p| p.direct && p.name == pkg)
            .map(|p| format!("{}@{}", p.name, p.version))
            .ok_or_else(|| format!("crate '{name}' is not resolved; run `luarc add {name}`"))
    }
}

/// Parses rustdoc JSON, checking the format version first for a clear message.
fn parse_rustdoc(text: &[u8], name: &str) -> Result<rustdoc_types::Crate, String> {
    let head = String::from_utf8_lossy(&text[..text.len().min(4096)]).to_string();
    let fv = head.split("\"format_version\":").nth(1).and_then(|s| s.trim().split(|c: char| !c.is_ascii_digit()).next().map(String::from));
    // format_version is usually at the end of the document
    let fv = fv.or_else(|| {
        let tail = String::from_utf8_lossy(&text[text.len().saturating_sub(4096)..]).to_string();
        tail.split("\"format_version\":").nth(1).and_then(|s| s.trim().split(|c: char| !c.is_ascii_digit()).next().map(String::from))
    });
    if let Some(v) = fv.and_then(|v| v.parse::<u32>().ok()) {
        if v != world::FORMAT_VERSION {
            return Err(format!(
                "rustdoc JSON format version {v} of '{name}' is not supported (luarc reads version {}); use the pinned extraction toolchain (see luarc-toolchain.toml)",
                world::FORMAT_VERSION
            ));
        }
    }
    serde_json::from_slice(text).map_err(|e| format!("invalid rustdoc JSON for '{name}': {e}"))
}

/// The pinned rustdoc-JSON extraction toolchain (machine-readable pin compiled
/// into luarc from `luarc-toolchain.toml`).
pub const TOOLCHAIN_PIN: &str = include_str!("../../../luarc-toolchain.toml");

#[derive(Deserialize)]
struct PinFile {
    extraction: PinSection,
}

#[derive(Deserialize)]
struct PinSection {
    toolchain: String,
    rustc: String,
    format_version: u32,
}

#[derive(Clone)]
pub struct ExtractionToolchain {
    pub toolchain: String,
    pub rustc: String,
    pub sysroot: PathBuf,
}

/// Verifies the extraction toolchain against the pin. `LUARC_NIGHTLY` selects
/// the rustup toolchain name; its `rustc --version` must equal the pinned one.
pub fn check_extraction_toolchain() -> Result<ExtractionToolchain, String> {
    thread_local! {
        static CACHED: std::cell::RefCell<Option<ExtractionToolchain>> = const { std::cell::RefCell::new(None) };
    }
    if let Some(t) = CACHED.with(|c| c.borrow().clone()) {
        return Ok(t);
    }
    let pin: PinFile = toml::from_str(TOOLCHAIN_PIN).map_err(|e| format!("luarc-toolchain.toml: {e}"))?;
    if pin.extraction.format_version != world::FORMAT_VERSION {
        return Err("luarc-toolchain.toml does not match this luarc build's rustdoc format".into());
    }
    let tc = std::env::var("LUARC_NIGHTLY").unwrap_or_else(|_| pin.extraction.toolchain.clone());
    let found = toolchain_version(&tc);
    if found.is_empty() {
        return Err(format!(
            "the rustdoc extraction toolchain '{tc}' is not installed: run `rustup toolchain install {} --component rust-docs-json` (pinned: {})",
            pin.extraction.toolchain, pin.extraction.rustc
        ));
    }
    if found != pin.extraction.rustc && std::env::var("LUARC_ALLOW_TOOLCHAIN_MISMATCH").is_err() {
        return Err(format!(
            "extraction toolchain mismatch: luarc is pinned to `{}` but `{tc}` is `{found}`; install the pinned toolchain or select it with LUARC_NIGHTLY",
            pin.extraction.rustc
        ));
    }
    let sysroot = Command::new("rustc")
        .arg(format!("+{tc}"))
        .arg("--print")
        .arg("sysroot")
        .output()
        .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim().to_string()))
        .map_err(|e| format!("cannot run rustc: {e}"))?;
    let t = ExtractionToolchain { toolchain: tc, rustc: found, sysroot };
    CACHED.with(|c| *c.borrow_mut() = Some(t.clone()));
    Ok(t)
}

/// One package of the resolved dependency graph.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphPackage {
    pub name: String,
    pub version: String,
    pub lib: String,
    pub source: String,
    pub features: Vec<String>,
    pub direct: bool,
    /// Directory of a path dependency (content-hashed for cache keys).
    pub local_dir: Option<String>,
    /// Rust crate name of each dependency → its package key.
    pub deps: BTreeMap<String, String>,
}

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct PackageGraph {
    /// `name@version` → package.
    pub packages: BTreeMap<String, GraphPackage>,
}

impl PackageGraph {
    fn from_metadata(meta: &serde_json::Value, manifest: &Manifest) -> PackageGraph {
        let packages = meta["packages"].as_array().cloned().unwrap_or_default();
        let nodes = meta["resolve"]["nodes"].as_array().cloned().unwrap_or_default();
        let root = meta["resolve"]["root"].as_str().unwrap_or("").to_string();
        let mut by_id: HashMap<String, (String, String)> = HashMap::new();
        for p in &packages {
            let id = p["id"].as_str().unwrap_or("").to_string();
            let name = p["name"].as_str().unwrap_or("").to_string();
            let version = p["version"].as_str().unwrap_or("").to_string();
            let lib = p["targets"]
                .as_array()
                .and_then(|ts| {
                    ts.iter()
                        .find(|t| t["kind"].as_array().map(|k| k.iter().any(|x| matches!(x.as_str(), Some("lib" | "rlib" | "proc-macro" | "dylib")))).unwrap_or(false))
                        .and_then(|t| t["name"].as_str().map(|s| s.replace('-', "_")))
                })
                .unwrap_or_else(|| name.replace('-', "_"));
            by_id.insert(id, (format!("{name}@{version}"), lib));
        }
        let root_deps: Vec<String> = nodes
            .iter()
            .find(|n| n["id"] == root.as_str())
            .and_then(|n| n["deps"].as_array().cloned())
            .unwrap_or_default()
            .iter()
            .filter_map(|d| d["pkg"].as_str().map(String::from))
            .collect();
        let mut out = PackageGraph::default();
        for p in &packages {
            let id = p["id"].as_str().unwrap_or("");
            if id == root {
                continue;
            }
            let node = nodes.iter().find(|n| n["id"] == id).cloned().unwrap_or_default();
            let (key, lib) = by_id[id].clone();
            let name = p["name"].as_str().unwrap_or("").to_string();
            let mut deps = BTreeMap::new();
            for d in node["deps"].as_array().cloned().unwrap_or_default() {
                if let Some((k, l)) = d["pkg"].as_str().and_then(|x| by_id.get(x)) {
                    deps.insert(l.clone(), k.clone());
                }
            }
            let mut features: Vec<String> = node["features"].as_array().cloned().unwrap_or_default().iter().filter_map(|f| f.as_str().map(String::from)).collect();
            features.sort();
            let source = p["source"].as_str().map(String::from).unwrap_or_else(|| format!("path+{}", p["manifest_path"].as_str().unwrap_or("").replace('\\', "/")));
            let local_dir = if p["source"].is_null() {
                p["manifest_path"].as_str().and_then(|m| Path::new(m).parent().map(|d| d.to_string_lossy().to_string()))
            } else {
                None
            };
            let direct = root_deps.iter().any(|r| r == id) && manifest.dependencies.contains_key(&name);
            out.packages.insert(
                key,
                GraphPackage { name, version: p["version"].as_str().unwrap_or("").to_string(), lib, source, features, direct, local_dir, deps },
            );
        }
        out
    }
}

/// Writes a file atomically (temporary file + rename), so an interrupted or
/// concurrent build never leaves a truncated cache entry.
pub fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if let Some(p) = path.parent() {
        fs::create_dir_all(p).map_err(|e| format!("cannot create {}: {e}", p.display()))?;
    }
    let tmp = path.with_extension(format!("tmp{}", std::process::id()));
    fs::write(&tmp, bytes).map_err(|e| format!("cannot write {}: {e}", tmp.display()))?;
    match fs::rename(&tmp, path) {
        Ok(()) => Ok(()),
        Err(e) => {
            let _ = fs::remove_file(&tmp);
            // a concurrent writer may have produced the same content first; anything
            // else (e.g. a locked stale file) is an error, never silently kept
            if fs::read(path).map(|b| b == bytes).unwrap_or(false) {
                Ok(())
            } else {
                Err(format!("cannot write {}: {e}", path.display()))
            }
        }
    }
}

/// Formats generated code with `rustfmt` when available (readability only; the
/// unformatted code is used if rustfmt is missing or fails).
pub fn rustfmt(code: &str) -> String {
    use std::io::Write;
    use std::process::Stdio;
    let child = Command::new("rustfmt")
        .args(["--edition", "2021", "--emit", "stdout", "--quiet"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn();
    let Ok(mut child) = child else { return code.to_string() };
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(code.as_bytes());
    }
    match child.wait_with_output() {
        Ok(o) if o.status.success() && !o.stdout.is_empty() => String::from_utf8(o.stdout).unwrap_or_else(|_| code.to_string()),
        _ => code.to_string(),
    }
}

/// rustc version string for a toolchain (part of cache keys).
pub fn toolchain_version(tc: &str) -> String {
    let mut c = Command::new("rustc");
    if tc != "stable-or-default" {
        c.arg(format!("+{tc}"));
    }
    c.arg("--version").output().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default()
}

/// Error messages (line, message) reported by rustc for a file name suffix.
pub fn rustc_errors(stdout: &[u8], file_suffix: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    for line in String::from_utf8_lossy(stdout).lines() {
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else { continue };
        if v["reason"] != "compiler-message" || v["message"]["level"] != "error" {
            continue;
        }
        let msg = v["message"]["message"].as_str().unwrap_or("").to_string();
        for sp in v["message"]["spans"].as_array().cloned().unwrap_or_default() {
            if sp["is_primary"] == true && sp["file_name"].as_str().map(|f| f.replace('\\', "/").ends_with(file_suffix)).unwrap_or(false) {
                out.push((sp["line_start"].as_u64().unwrap_or(0) as usize, msg.clone()));
            }
        }
    }
    out
}
