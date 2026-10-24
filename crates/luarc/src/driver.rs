//! Compilation pipeline:
//! `source → AST → module/name resolution → type inference/checking → lowering → Rust → Cargo`.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::ast::*;
use crate::check::{Checker, ModuleUnit};
use crate::codegen::Gen;
use crate::diag::{Diagnostic, SourceMap, Span};
use crate::native::adapters::{self, AdapterSet};
use crate::native::world::World;
use crate::project::PackageGraph;
use crate::parser::parse_module;
use crate::project::{cargo, fingerprint, toml_str, write_if_changed, Project};
use crate::resolve::{Builtin, Res, Resolution, Resolver};

pub enum Failure {
    /// Source-level diagnostics.
    Diags(Vec<Diagnostic>, SourceMap),
    /// Source-level diagnostics plus rustc errors that map to no source item.
    DiagsAndRust(Vec<Diagnostic>, SourceMap, Vec<String>),
    /// Any other error (I/O, toolchain, dependency resolution).
    Msg(String),
}

impl Failure {
    pub fn render(&self) -> String {
        match self {
            Failure::Diags(ds, sm) => {
                let mut s = ds.iter().map(|d| d.render(sm)).collect::<Vec<_>>().join("\n\n");
                s.push_str(&format!("\n\n{} error(s)", ds.len()));
                s
            }
            Failure::DiagsAndRust(ds, sm, rust) => {
                let mut s = ds.iter().map(|d| d.render(sm)).collect::<Vec<_>>().join("\n\n");
                s.push_str("\n\nthe Rust compiler also reported errors that map to no luarc source item:\n");
                s.push_str(&rust.join("\n"));
                s.push_str(&format!("\n{} error(s) mapped to source, {} unmapped", ds.len(), rust.len()));
                s
            }
            Failure::Msg(m) => format!("error: {m}"),
        }
    }
}

impl From<String> for Failure {
    fn from(s: String) -> Self {
        Failure::Msg(s)
    }
}

pub struct Generated {
    pub package_dir: PathBuf,
    pub bin_name: String,
    pub sm: SourceMap,
    pub wrapper_lines: Vec<(usize, usize, Span, String)>,
}

/// Collects `require("...")` calls with literal arguments (syntactic scan).
fn find_requires(b: &Block, builtin: Option<&HashSet<NodeId>>, out: &mut Vec<(NodeId, Span, String)>) {
    fn expr(e: &Expr, builtin: Option<&HashSet<NodeId>>, out: &mut Vec<(NodeId, Span, String)>) {
        match &e.kind {
            ExprKind::Call(f, args) => {
                if let (ExprKind::Name(n), [a]) = (&f.kind, args.as_slice()) {
                    // a local named `require` shadows the builtin
                    if n.text == "require" && builtin.is_none_or(|b| b.contains(&n.id)) {
                        if let ExprKind::Str(s) = &a.kind {
                            out.push((e.id, e.span, String::from_utf8_lossy(s).to_string()));
                        }
                    }
                }
                expr(f, builtin, out);
                args.iter().for_each(|a| expr(a, builtin, out));
            }
            ExprKind::Method(o, _, args) => {
                expr(o, builtin, out);
                args.iter().for_each(|a| expr(a, builtin, out));
            }
            ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) => {
                expr(a, builtin, out);
                expr(b, builtin, out);
            }
            ExprKind::Field(a, _) | ExprKind::Unary(_, a) | ExprKind::Paren(a) | ExprKind::Cast(a, _) => expr(a, builtin, out),
            ExprKind::IfElse(a, b, c) => {
                expr(a, builtin, out);
                expr(b, builtin, out);
                expr(c, builtin, out);
            }
            ExprKind::Function(f) => find_requires(&f.body, builtin, out),
            ExprKind::Table(items) => {
                for it in items {
                    match it {
                        TableItem::Pos(x) | TableItem::Named(_, x) => expr(x, builtin, out),
                        TableItem::Keyed(k, v) => {
                            expr(k, builtin, out);
                            expr(v, builtin, out);
                        }
                    }
                }
            }
            ExprKind::Interp(parts) => {
                for p in parts {
                    if let InterpPart::Expr(x) = p {
                        expr(x, builtin, out);
                    }
                }
            }
            _ => {}
        }
    }
    for s in &b.stats {
        match &s.kind {
            StatKind::Local(_, es) | StatKind::Return(es) => es.iter().for_each(|e| expr(e, builtin, out)),
            StatKind::LocalFunction(_, f) => find_requires(&f.body, builtin, out),
            StatKind::Function(t, f) => {
                expr(t, builtin, out);
                find_requires(&f.body, builtin, out);
            }
            StatKind::Assign(ts, es) => {
                ts.iter().for_each(|e| expr(e, builtin, out));
                es.iter().for_each(|e| expr(e, builtin, out));
            }
            StatKind::Compound(_, t, e) => {
                expr(t, builtin, out);
                expr(e, builtin, out);
            }
            StatKind::Call(e) => expr(e, builtin, out),
            StatKind::Do(b) => find_requires(b, builtin, out),
            StatKind::While(c, b) | StatKind::Repeat(b, c) => {
                expr(c, builtin, out);
                find_requires(b, builtin, out);
            }
            StatKind::If(arms, els) => {
                for (c, b) in arms {
                    expr(c, builtin, out);
                    find_requires(b, builtin, out);
                }
                if let Some(b) = els {
                    find_requires(b, builtin, out);
                }
            }
            StatKind::NumFor(_, a, b, c, body) => {
                expr(a, builtin, out);
                expr(b, builtin, out);
                if let Some(c) = c {
                    expr(c, builtin, out);
                }
                find_requires(body, builtin, out);
            }
            StatKind::GenFor(_, es, body) => {
                es.iter().for_each(|e| expr(e, builtin, out));
                find_requires(body, builtin, out);
            }
            _ => {}
        }
    }
}

struct Loaded {
    sm: SourceMap,
    modules: Vec<(Module, PathBuf)>,
    /// per module: require node → target module / crate name
    local_reqs: Vec<HashMap<NodeId, usize>>,
    rust_reqs: Vec<HashMap<NodeId, String>>,
    order: Vec<usize>,
    next_id: NodeId,
}

fn display_name(root: &Path, p: &Path) -> String {
    let rel = p.strip_prefix(root).unwrap_or(p);
    rel.to_string_lossy().replace('\\', "/")
}

fn load_modules(entry: &Path, root: &Path) -> Result<Loaded, Failure> {
    let mut sm = SourceMap::default();
    let mut modules: Vec<(Module, PathBuf)> = Vec::new();
    let mut index: HashMap<PathBuf, usize> = HashMap::new();
    let mut reqs: Vec<Vec<(NodeId, Span, String)>> = Vec::new();
    let mut next_id: NodeId = 1;
    let mut errors = Vec::new();
    let mut queue = vec![crate::project::canon(entry).map_err(|e| Failure::Msg(format!("cannot open {}: {e}", entry.display())))?];
    let mut local_reqs: Vec<HashMap<NodeId, usize>> = Vec::new();
    let mut rust_reqs: Vec<HashMap<NodeId, String>> = Vec::new();
    let mut pending_links: Vec<(usize, NodeId, PathBuf)> = Vec::new();
    while let Some(path) = queue.pop() {
        if index.contains_key(&path) {
            continue;
        }
        let text = fs::read_to_string(&path).map_err(|e| Failure::Msg(format!("cannot read {}: {e}", path.display())))?;
        let file = sm.add(path.clone(), display_name(root, &path), text.clone());
        let mi = modules.len();
        index.insert(path.clone(), mi);
        local_reqs.push(HashMap::new());
        rust_reqs.push(HashMap::new());
        match parse_module(file, &text, &mut next_id) {
            Ok(m) => {
                // names resolving to the builtin `require` (lexical: the module alone
                // decides; resolution errors are reported by the real pass later)
                let builtin: HashSet<NodeId> = {
                    let mut res = Resolution::default();
                    let mut r = Resolver::new(&mut res);
                    r.module(&m, next_id);
                    res.names.iter().filter(|(_, v)| matches!(v, Res::Builtin(Builtin::Require))).map(|(k, _)| *k).collect()
                };
                let mut rs = Vec::new();
                find_requires(&m.body, Some(&builtin), &mut rs);
                for (node, span, lit) in &rs {
                    if let Some(c) = lit.strip_prefix("rust:") {
                        rust_reqs[mi].insert(*node, c.to_string());
                    } else if lit.starts_with("./") || lit.starts_with("../") {
                        let base = path.parent().unwrap_or(Path::new("."));
                        // `.luarc` is the source extension; `.luau`/`.lua` stay accepted for existing code.
                        let cands = [
                            base.join(format!("{lit}.luarc")),
                            base.join(lit).join("init.luarc"),
                            base.join(format!("{lit}.luau")),
                            base.join(format!("{lit}.lua")),
                            base.join(lit).join("init.luau"),
                        ];
                        match cands.iter().find(|c| c.is_file()) {
                            Some(c) => {
                                let c = crate::project::canon(c).unwrap_or(c.clone());
                                pending_links.push((mi, *node, c.clone()));
                                queue.push(c);
                            }
                            None => errors.push(Diagnostic::new(*span, format!("module '{lit}' not found (looked for {lit}.luarc, {lit}/init.luarc, {lit}.luau, {lit}.lua)"))),
                        }
                    } else {
                        errors.push(Diagnostic::new(
                            *span,
                            format!("require path '{lit}' must start with './', '../' (source module) or 'rust:' (Rust crate)"),
                        ));
                    }
                }
                reqs.push(rs);
                modules.push((m, path));
            }
            Err(ds) => {
                errors.extend(ds);
                reqs.push(Vec::new());
                modules.push((Module { file, body: Block { stats: vec![], span: Span::default() }, options: Default::default(), attrs: Default::default() }, path));
            }
        }
    }
    for (mi, node, target) in pending_links {
        local_reqs[mi].insert(node, index[&target]);
    }
    if !errors.is_empty() {
        return Err(Failure::Diags(errors, sm));
    }
    // dependency order (post-order DFS) with cycle detection
    let mut state = vec![0u8; modules.len()];
    let mut order = Vec::new();
    fn visit(
        m: usize,
        state: &mut Vec<u8>,
        order: &mut Vec<usize>,
        stack: &mut Vec<usize>,
        local: &[HashMap<NodeId, usize>],
        reqs: &[Vec<(NodeId, Span, String)>],
        sm: &SourceMap,
        errors: &mut Vec<Diagnostic>,
    ) {
        state[m] = 1;
        stack.push(m);
        for (node, span, _) in &reqs[m] {
            if let Some(&t) = local[m].get(node) {
                if state[t] == 1 {
                    let pos = stack.iter().position(|x| *x == t).unwrap_or(0);
                    let mut cyc: Vec<String> = stack[pos..].iter().map(|i| sm.display(*i as u32).to_string()).collect();
                    cyc.push(sm.display(t as u32).to_string());
                    errors.push(Diagnostic::new(
                        *span,
                        format!(
                            "cyclic module require: {} (cyclic module initialization is unsupported; this is unrelated to cyclic tables at runtime)",
                            cyc.join(" -> ")
                        ),
                    ));
                } else if state[t] == 0 {
                    visit(t, state, order, stack, local, reqs, sm, errors);
                }
            }
        }
        stack.pop();
        state[m] = 2;
        order.push(m);
    }
    let mut stack = Vec::new();
    visit(0, &mut state, &mut order, &mut stack, &local_reqs, &reqs, &sm, &mut errors);
    if !errors.is_empty() {
        return Err(Failure::Diags(errors, sm));
    }
    Ok(Loaded { sm, modules, local_reqs, rust_reqs, order, next_id })
}

fn module_ident(i: usize, path: &Path) -> String {
    let stem = path.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let clean: String = stem.chars().map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_lowercase() } else { '_' }).collect();
    format!("m{i}_{clean}")
}

pub struct Frontend {
    pub sm: SourceMap,
    pub units: Vec<ModuleUnit>,
    pub res: Resolution,
    pub world: World,
    pub adapters: AdapterSet,
    pub order: Vec<usize>,
    pub graph: PackageGraph,
    /// First unused node id (specialization allocates the ids of function copies).
    pub next_id: NodeId,
}

/// Parses, resolves and loads the imported crates' API models (no type checking yet).
pub fn frontend(entry: &Path, project: &mut Project) -> Result<Frontend, Failure> {
    let loaded = load_modules(entry, &project.root)?;
    let mut res = Resolution::default();
    let mut next_id = loaded.next_id;
    let mut units = Vec::new();
    let mut errors = Vec::new();
    let mut world = World::default();
    {
        let mut r = Resolver::new(&mut res);
        for (m, _) in loaded.modules.iter() {
            let pseudo = next_id;
            next_id += 1;
            r.module(m, pseudo);
        }
        r.finish();
        errors.extend(std::mem::take(&mut r.errors));
    }
    let needs_graph = loaded.rust_reqs.iter().any(|r| r.values().any(|n| n != "std"));
    let graph = if needs_graph {
        match project.package_graph() {
            Ok(g) => g,
            Err(e) => return Err(Failure::Msg(e)),
        }
    } else {
        PackageGraph::default()
    };
    for (i, (m, path)) in loaded.modules.into_iter().enumerate() {
        let mut rust_requires = HashMap::new();
        for (node, name) in &loaded.rust_reqs[i] {
            let span = find_span(&m.body, *node).unwrap_or_default();
            let key = match project.crate_key(&graph, name) {
                Ok(k) => k,
                Err(e) => {
                    errors.push(Diagnostic::new(span, e));
                    continue;
                }
            };
            let idx = match world.by_key(&key) {
                Some(ix) => ix,
                None => match project.load_crate(&graph, &key) {
                    Ok(c) => world.add(c),
                    Err(e) => {
                        errors.push(Diagnostic::new(span, e));
                        continue;
                    }
                },
            };
            rust_requires.insert(*node, idx);
        }
        units.push(ModuleUnit {
            ident: module_ident(i, &path),
            pseudo_func: 0,
            requires: loaded.local_reqs[i].clone(),
            rust_requires,
            module: m,
        });
    }
    // pseudo ids were allocated in module order
    let first = loaded.next_id;
    for (i, u) in units.iter_mut().enumerate() {
        u.pseudo_func = first + i as NodeId;
    }
    if !errors.is_empty() {
        return Err(Failure::Diags(errors, loaded.sm));
    }
    let mut fe = Frontend { sm: loaded.sm, units, res, world, adapters: AdapterSet::default(), order: loaded.order, graph, next_id };
    apply_adapters(&mut fe, project)?;
    Ok(fe)
}

/// Validates and registers the adapters of every loaded crate.
fn apply_adapters(fe: &mut Frontend, project: &Project) -> Result<(), Failure> {
    let mut set = AdapterSet::default();
    for (origin, text) in project.adapter_texts() {
        let a = adapters::parse(&text, &origin)?;
        for c in 0..fe.world.crates.len() {
            if fe.world.crates[c].info.package == a.krate {
                // A shipped adapter describes one version of a crate; with another
                // version that it does not fit it is skipped with a warning instead of
                // failing every build. Project adapters stay errors.
                let before = set.clone();
                if let Err(e) = set.add(&fe.world, c, &a, &origin) {
                    if !origin.starts_with("shipped:") {
                        return Err(Failure::Msg(e));
                    }
                    set = before;
                    eprintln!("luarc: warning: {e}; the shipped adapter is skipped for {}", fe.world.crates[c].info.key);
                }
            }
        }
    }
    fe.adapters = set;
    Ok(())
}

/// Copies the local functions `specialize` selects and re-resolves.
/// Returns whether anything changed.
fn respecialize(fe: &mut Frontend, lazy: bool) -> Result<bool, Failure> {
    match crate::specialize::specialize(&mut fe.units, &mut fe.next_id, lazy) {
        Ok(0) => Ok(false),
        Ok(_) => {
            let mut res = Resolution::default();
            {
                let mut r = Resolver::new(&mut res);
                for u in &fe.units {
                    r.module(&u.module, u.pseudo_func);
                }
                r.finish();
            }
            fe.res = res;
            Ok(true)
        }
        Err(d) => Err(Failure::Diags(vec![d], fe.sm.clone())),
    }
}

/// Type checks. Functions with type parameters are first copied per call site; if
/// the program does not check, the functions with unannotated parameters are copied
/// per call site too and the program is checked again (programs that check without
/// copies are never changed).
pub fn checked<'f>(fe: &'f mut Frontend, project: &mut Project) -> Result<(), Failure> {
    let needs = crate::specialize::needs(&mut fe.units);
    // the program before any copy: the second attempt copies everything in one pass
    // (callers before callees), so it starts from the original
    let backup = needs.eager.then(|| (fe.units.clone(), fe.next_id));
    if needs.eager {
        respecialize(fe, false)?;
    }
    match checked_rounds(fe, project) {
        Err(Failure::Diags(errs, sm)) => {
            // only conflicts between the uses of a parameter are fixed by copies;
            // other restrictions (cyclic record parents, ...) are reported as they are
            let conflict = errs.iter().any(|d| {
                ["type mismatch", "function type mismatch", "cannot determine", "cannot infer", "nil is not allowed", "value may be nil"]
                    .iter()
                    .any(|p| d.msg.starts_with(p))
            });
            if conflict {
                if let Some((units, next_id)) = backup {
                    fe.units = units;
                    fe.next_id = next_id;
                }
            }
            if conflict && crate::specialize::needs(&mut fe.units).lazy && respecialize(fe, true)? {
                return match checked_rounds(fe, project) {
                    Err(Failure::Diags(retry, sm)) => {
                        // every copy repeats the diagnostics of its body: report each once
                        let mut seen = std::collections::HashSet::new();
                        let retry: Vec<Diagnostic> =
                            retry.into_iter().filter(|d| seen.insert((d.span, d.msg.clone()))).collect();
                        Err(Failure::Diags(retry, sm))
                    }
                    other => other,
                };
            }
            Err(Failure::Diags(errs, sm))
        }
        other => other,
    }
}

/// Type checks, loading further crates the program's types reach (re-export
/// targets, dependency crates) until the set of loaded crates is complete.
fn checked_rounds<'f>(fe: &'f mut Frontend, project: &mut Project) -> Result<(), Failure> {
    for _round in 0..16 {
        fe.world.missing.borrow_mut().clear();
        let errors = {
            let mut ck = Checker::new(&fe.res, &fe.sm, &fe.world, &fe.adapters);
            ck.check_program(&fe.units, &fe.order);
            ck.errors
        };
        let missing: Vec<String> = fe.world.missing.borrow().iter().cloned().collect();
        if std::env::var_os("LUARC_DEBUG_LOAD").is_some() {
            eprintln!("luarc: round {_round}: {} error(s), missing {:?}", errors.len(), missing);
        }
        if missing.is_empty() {
            if errors.is_empty() {
                return Ok(());
            }
            return Err(Failure::Diags(errors, fe.sm.clone()));
        }
        let mut loaded_any = false;
        // `lib:NAME`: a crate known only by its library name (reached through a
        // re-export chain): the package of the graph with that library, if unique
        let missing: Vec<String> = missing
            .into_iter()
            .filter_map(|k| match k.strip_prefix("lib:") {
                Some(lib) => {
                    let cands: Vec<String> = fe.graph.packages.iter().filter(|(_, p)| p.lib == lib).map(|(key, _)| key.clone()).collect();
                    (cands.len() == 1).then(|| cands[0].clone())
                }
                None => Some(k),
            })
            .collect();
        for key in missing {
            if fe.world.by_key(&key).is_some() {
                continue;
            }
            match project.load_crate(&fe.graph, &key) {
                Ok(c) => {
                    fe.world.add(c);
                    loaded_any = true;
                }
                Err(e) => {
                    if project.verbose {
                        crate::progress::note(&format!("luarc: note: crate {key} is unavailable ({e})"));
                    }
                }
            }
        }
        if !loaded_any {
            if errors.is_empty() {
                return Ok(());
            }
            return Err(Failure::Diags(errors, fe.sm.clone()));
        }
        apply_adapters(fe, project)?;
    }
    Err(Failure::Msg("native API loading did not converge".into()))
}

fn find_span(b: &Block, node: NodeId) -> Option<Span> {
    let mut rs = Vec::new();
    find_requires(b, None, &mut rs);
    rs.into_iter().find(|(n, _, _)| *n == node).map(|(_, s, _)| s)
}

/// Type checks; returns diagnostics on failure.
pub fn check(entry: &Path, project: &mut Project) -> Result<(), Failure> {
    let mut fe = frontend(entry, project)?;
    checked(&mut fe, project)
}

fn entry_index(fe: &Frontend) -> usize {
    0.min(fe.units.len().saturating_sub(1))
}

/// Generates the Cargo package for `entry` into `out_dir` (or the managed build dir).
pub fn generate(entry: &Path, project: &mut Project, out_dir: Option<&Path>, standalone: bool) -> Result<Generated, Failure> {
    let mut fe = frontend(entry, project)?;
    checked(&mut fe, project)?;
    let mut ck = Checker::new(&fe.res, &fe.sm, &fe.world, &fe.adapters);
    ck.check_program(&fe.units, &fe.order);
    if !ck.errors.is_empty() {
        let errs = ck.errors.clone();
        return Err(Failure::Diags(errs, fe.sm.clone()));
    }
    let gen = Gen::new(&ck, &fe.units);
    let out = gen.generate(entry_index(&fe));
    let canon = crate::project::canon(entry).unwrap_or(entry.to_path_buf());
    let stem: String = canon
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "main".into())
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' || c == '-' { c } else { '_' })
        .collect();
    let tag = &fingerprint(&[canon.to_string_lossy().as_bytes()])[..8];
    let bin_name = format!("{stem}-{tag}");
    let dir = match out_dir {
        Some(d) => d.to_path_buf(),
        None => project.dot().join("build").join(&bin_name),
    };
    if out_dir.is_some() && dir.join("Cargo.toml").is_file() {
        let head = fs::read_to_string(dir.join("Cargo.toml")).unwrap_or_default();
        if !head.starts_with("# Generated by luarc") {
            return Err(Failure::Msg(format!(
                "refusing to write into {}: it contains a Cargo package that luarc did not generate",
                dir.display()
            )));
        }
    }
    let runtime_dep = if standalone {
        // self-contained output: copy the runtime next to the generated package
        let rt = dir.join("luarc-runtime");
        write_if_changed(&rt.join("Cargo.toml"), &crate::project::runtime_manifest())?;
        for (p, c) in crate::project::RUNTIME_FILES {
            write_if_changed(&rt.join(p), c)?;
        }
        "luarc-runtime".to_string()
    } else {
        project.write_runtime()?.to_string_lossy().to_string()
    };
    let cargo_toml = format!(
        "# Generated by luarc from {}. Do not edit.\n[package]\nname = \"{bin_name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n\n[[bin]]\nname = \"{bin_name}\"\npath = \"src/main.rs\"\n\n[dependencies]\nluarc-runtime = {{ path = {} }}\n{}\n[workspace]\n\n[profile.release]\ncodegen-units = 1\n",
        fe.sm.display(0),
        toml_str(&runtime_dep),
        project.cargo_deps()
    );
    write_if_changed(&dir.join("Cargo.toml"), &cargo_toml)?;
    if !project.lock.cargo_lock.is_empty() {
        write_if_changed(&dir.join("Cargo.lock"), &project.lock.cargo_lock)?;
    }
    // Remove stale generated module files without deleting user-owned files.
    let generated = |p: &Path| fs::read_to_string(p).map(|t| t.lines().next().unwrap_or("").contains("Generated by luarc")).unwrap_or(false);
    if let Ok(rd) = fs::read_dir(dir.join("src")) {
        for e in rd.flatten() {
            let rel = format!("src/{}", e.file_name().to_string_lossy());
            if !out.files.iter().any(|(p, _)| *p == rel) && generated(&e.path()) {
                let _ = fs::remove_file(e.path());
            }
        }
    }
    for (p, c) in &out.files {
        // natives.rs is formatted per wrapper (its line map must stay exact)
        let code = if p.ends_with("natives.rs") { c.clone() } else { crate::project::rustfmt(c) };
        write_if_changed(&dir.join(p), &code)?;
    }
    Ok(Generated { package_dir: dir, bin_name, sm: fe.sm.clone(), wrapper_lines: out.wrapper_lines })
}

pub struct Built {
    pub exe: PathBuf,
    /// Warnings rustc reported in generated (project-owned) code.
    pub warnings: Vec<String>,
}

/// Builds the generated package; maps Rust errors in native wrappers to source.
pub fn build(entry: &Path, project: &mut Project, release: bool) -> Result<Built, Failure> {
    let g = generate(entry, project, None, false)?;
    let target = project.dot().join("target");
    let mut cmd = cargo();
    cmd.arg("build").arg("--message-format=json").arg("--manifest-path").arg(g.package_dir.join("Cargo.toml")).arg("--target-dir").arg(&target);
    if release {
        cmd.arg("--release");
    }
    let out = crate::progress::run(cmd, "building").map_err(|e| Failure::Msg(format!("cannot run cargo: {e}")))?;
    let pkg_src = g.package_dir.join("src").to_string_lossy().replace('\\', "/");
    let mut warnings = Vec::new();
    let mut diags = Vec::new();
    let mut internal = Vec::new();
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else { continue };
        if v["reason"] != "compiler-message" {
            continue;
        }
        let level = v["message"]["level"].as_str().unwrap_or("");
        let rendered = v["message"]["rendered"].as_str().unwrap_or("").to_string();
        let msg = v["message"]["message"].as_str().unwrap_or("").to_string();
        let primary = v["message"]["spans"].as_array().cloned().unwrap_or_default().into_iter().find(|s| s["is_primary"] == true);
        let file = primary.as_ref().and_then(|s| s["file_name"].as_str()).unwrap_or("").replace('\\', "/");
        let in_generated = !file.is_empty() && (file.starts_with("src/") || file.contains(&pkg_src));
        if level == "warning" && in_generated {
            warnings.push(rendered);
            continue;
        }
        if level != "error" {
            continue;
        }
        if file.ends_with("natives.rs") {
            let line_no = primary.as_ref().and_then(|s| s["line_start"].as_u64()).unwrap_or(0) as usize;
            if let Some((_, _, span, item)) = g.wrapper_lines.iter().find(|(a, b, _, _)| line_no >= *a && line_no <= *b) {
                if let Some(reason) = msg.strip_prefix("luarc: ") {
                    // luarc itself refused to generate this wrapper (`compile_error!`):
                    // not a rustc rejection, and the generics note does not apply
                    let reason = reason.strip_prefix(&format!("{item}: ")).unwrap_or(reason);
                    diags.push(Diagnostic::new(*span, format!("unsupported use of native item '{item}': {reason}")));
                    continue;
                }
                diags.push(
                    Diagnostic::new(*span, format!("the Rust compiler rejected this use of native item '{item}': {msg}"))
                        .note("generic arguments are inferred from the source types (number → f64, string → String); check the item's trait bounds with `luarc bindings`"),
                );
                continue;
            }
        }
        internal.push(rendered);
    }
    if !diags.is_empty() {
        diags.dedup_by(|a, b| a.span == b.span);
        if !internal.is_empty() {
            return Err(Failure::DiagsAndRust(diags, g.sm, internal));
        }
        return Err(Failure::Diags(diags, g.sm));
    }
    if !out.status.success() {
        let detail = if internal.is_empty() { String::from_utf8_lossy(&out.stderr).to_string() } else { internal.join("\n") };
        return Err(Failure::Msg(format!(
            "the generated Rust failed to compile (this is a luarc bug; generated code kept in {}):\n{detail}",
            g.package_dir.display()
        )));
    }
    let exe = target.join(if release { "release" } else { "debug" }).join(format!("{}{}", g.bin_name, std::env::consts::EXE_SUFFIX));
    Ok(Built { exe, warnings })
}

/// Runs a built program with arguments, inheriting stdio; returns its exit code.
pub fn run_exe(exe: &Path, args: &[String]) -> Result<i32, Failure> {
    let status = Command::new(exe).args(args).status().map_err(|e| Failure::Msg(format!("cannot run {}: {e}", exe.display())))?;
    Ok(status.code().unwrap_or(1))
}

pub fn is_require_builtin(res: &Resolution, n: &Name) -> bool {
    matches!(res.res(n.id), Some(Res::Builtin(Builtin::Require)))
}

/// Bindings report of one dependency (`luarc bindings`, `luarc add` summary):
/// (rendered report, automatic, adapter-backed, unsupported, version).
pub fn crate_report(project: &mut Project, name: &str) -> Result<(String, usize, usize, usize, String), Failure> {
    let graph = project.package_graph()?;
    let key = project.crate_key(&graph, name)?;
    let mut world = World::default();
    let c = world.add(project.load_crate(&graph, &key)?);
    for _ in 0..8 {
        let mut fe = Frontend {
            sm: SourceMap::default(),
            units: Vec::new(),
            res: Resolution::default(),
            world,
            adapters: AdapterSet::default(),
            order: Vec::new(),
            graph: graph.clone(),
            next_id: 0,
        };
        apply_adapters(&mut fe, project)?;
        world = fe.world;
        world.missing.borrow_mut().clear();
        let rep = crate::native::report::report(&world, &fe.adapters, c);
        let missing: Vec<String> = world.missing.borrow().iter().cloned().collect();
        let mut loaded = false;
        for k in missing {
            if world.by_key(&k).is_none() {
                if let Ok(lc) = project.load_crate(&graph, &k) {
                    world.add(lc);
                    loaded = true;
                }
            }
        }
        if !loaded {
            let (a, b, u) = rep.counts();
            let text = crate::native::report::render_report(&world, c, &rep);
            return Ok((text, a, b, u, world.info(c).version.clone()));
        }
    }
    Err(Failure::Msg("native API loading did not converge".into()))
}
