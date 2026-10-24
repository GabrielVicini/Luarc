//! Adapter extension mechanism (versioned, declarative).
//!
//! An adapter is a TOML file that describes, for one crate, protocol facts that a
//! Rust signature alone does not express. Adapters never touch the parser: the
//! checker and wrapper generator consult them, and every declaration is
//! validated against the crate's extracted signatures when the crate is loaded.
//!
//! ```toml
//! adapter = "fixture-ledger"   # name shown in diagnostics and `luarc bindings`
//! adapter_version = 1
//! crate = "fixture"            # package the adapter applies to
//!
//! [[consume]]                  # documents a by-value `self` method (consumption is
//! type = "Ledger"              # the default for non-Copy receivers; validated)
//! method = "finish"
//!
//! [[retain_owner]]             # the returned handle keeps the receiver alive
//! type = "Pool"
//! method = "checkout"
//!
//! [[returns_receiver]]         # a `&Self`/`&mut Self` result IS the receiver
//! type = "RegexBuilder"        # (identity shortcut; verified protocol metadata)
//! method = "case_insensitive"
//!
//! [[close]]                    # adds `obj:close()`: deterministic release
//! type = "Ledger"
//! method = "close"
//!
//! [[rename]]                   # source-visible name for a method
//! item = "Ledger.add_entry"
//! name = "add"
//!
//! [[scoped_borrow]]            # `begin_x(&mut self) -> X<'self>`: the result is made
//! type = "CommandEncoder"      # `'static` with `forget` and the receiver stays locked
//! method = "begin_render_pass" # until the result is dropped or closed
//! forget = "forget_lifetime"
//!
//! [[trait_error]]              # a source error in a `()`-returning method of a
//! trait = "application.ApplicationHandler"  # table-implemented trait is stored
//! arg = "event_loop"          # and later callbacks are suppressed; additionally
//! method = "exit"             # `event_loop.exit()` asks the native loop to return
//!
//! [[task_waker]]               # `task.wake_through(proxy)`: waking a task calls
//! type = "event_loop.EventLoopProxy"  # `proxy.send_event(())` from any thread
//! method = "send_event"
//! arg = "()"
//! ```
//!
//! Adding an adapter: drop a file in the project's `adapters/` directory (or in
//! luarc's shipped `adapters/` directory). No compiler change is needed.

use rustdoc_types as rd;
use serde::Deserialize;

use super::world::{ItemRef, World};

pub const ADAPTER_FORMAT: u32 = 1;

/// Adapters shipped with luarc.
pub const SHIPPED: &[(&str, &str)] = &[
    ("fixture-ledger.toml", include_str!("../../../../adapters/fixture-ledger.toml")),
    ("regex-builders.toml", include_str!("../../../../adapters/regex-builders.toml")),
    ("winit-app.toml", include_str!("../../../../adapters/winit-app.toml")),
    ("wgpu-passes.toml", include_str!("../../../../adapters/wgpu-passes.toml")),
];

#[derive(Deserialize, Debug, Clone)]
pub struct AdapterFile {
    pub adapter: String,
    pub adapter_version: u32,
    #[serde(rename = "crate")]
    pub krate: String,
    #[serde(default)]
    pub consume: Vec<TypeMethod>,
    #[serde(default)]
    pub retain_owner: Vec<TypeMethod>,
    #[serde(default)]
    pub returns_receiver: Vec<TypeMethod>,
    #[serde(default)]
    pub close: Vec<TypeMethod>,
    #[serde(default)]
    pub rename: Vec<Rename>,
    #[serde(default)]
    pub scoped_borrow: Vec<ScopedBorrow>,
    #[serde(default)]
    pub trait_error: Vec<TraitError>,
    #[serde(default)]
    pub task_waker: Vec<TaskWaker>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct TypeMethod {
    #[serde(rename = "type")]
    pub ty: String,
    pub method: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Rename {
    pub item: String,
    pub name: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct TraitError {
    #[serde(rename = "trait")]
    pub trait_: String,
    pub arg: String,
    pub method: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct TaskWaker {
    #[serde(rename = "type")]
    pub ty: String,
    pub method: String,
    /// The argument expression (a unit value or a constant).
    pub arg: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct ScopedBorrow {
    #[serde(rename = "type")]
    pub ty: String,
    pub method: String,
    pub forget: String,
}

pub fn parse(text: &str, origin: &str) -> Result<AdapterFile, String> {
    let a: AdapterFile = toml::from_str(text).map_err(|e| format!("adapter {origin}: {e}"))?;
    if a.adapter_version != ADAPTER_FORMAT {
        return Err(format!(
            "adapter {origin}: adapter_version {} is not supported (this luarc understands version {ADAPTER_FORMAT})",
            a.adapter_version
        ));
    }
    Ok(a)
}

/// Protocol facts for the loaded crates, keyed by item.
#[derive(Default, Debug, Clone)]
pub struct AdapterSet {
    /// (type, method name) of adapter-provided `close` methods.
    closes: Vec<(ItemRef, String, String)>,
    /// (type, source name) → Rust method name.
    renames: Vec<(ItemRef, String, String)>,
    /// (type, method) whose returned handle retains the receiver.
    retains: Vec<(ItemRef, String, String)>,
    /// (type, method) returning its own receiver.
    receivers: Vec<(ItemRef, String, String)>,
    /// (type, method, forget method).
    scoped: Vec<(ItemRef, String, String, String)>,
    /// (type, method) documented as consuming.
    consumes: Vec<(ItemRef, String, String)>,
    /// trait → (argument name, method called on it after a stored error, adapter).
    trait_errors: Vec<(ItemRef, String, String, String)>,
    /// type → (method, argument expression, adapter).
    wakers: Vec<(ItemRef, String, String, String)>,
}

/// Receiver kind of a method item: `Some(true)` = `&mut self`, `Some(false)` =
/// `&self`, `None` = other (by value or none).
fn receiver(w: &World, f: ItemRef) -> Option<&'static str> {
    let rd::ItemEnum::Function(func) = &w.item(f)?.inner else { return None };
    let (n, t) = func.sig.inputs.first()?;
    if n != "self" {
        return None;
    }
    Some(match t {
        rd::Type::Generic(s) if s == "Self" => "self",
        rd::Type::BorrowedRef { is_mutable: true, .. } => "&mut self",
        rd::Type::BorrowedRef { .. } => "&self",
        _ => "other",
    })
}

fn inherent_method(w: &World, ty: ItemRef, name: &str) -> Option<ItemRef> {
    for imp in w.impls_of(ty) {
        let Some(rd::Item { inner: rd::ItemEnum::Impl(i), .. }) = w.item(imp) else { continue };
        if i.trait_.is_some() {
            continue;
        }
        for it in w.impl_items(imp) {
            // Only functions are methods; reject associated constants and types.
            if let Some(x) = w.item(it) {
                if x.name.as_deref() == Some(name) && matches!(x.inner, rd::ItemEnum::Function(_)) {
                    return Some(it);
                }
            }
        }
    }
    None
}

impl AdapterSet {
    /// Validates and registers one adapter for crate root `root` (a loaded crate
    /// whose package matches the adapter's `crate`).
    pub fn add(&mut self, w: &World, c: usize, a: &AdapterFile, origin: &str) -> Result<(), String> {
        let ty = |name: &str| -> Result<ItemRef, String> {
            let path: Vec<String> = name.split('.').map(String::from).collect();
            let r = w.lookup_path(c, &path).ok_or_else(|| format!("adapter {origin}: type '{name}' does not exist in crate '{}'", a.krate))?;
            // follow a type alias
            if let Some(rd::Item { inner: rd::ItemEnum::TypeAlias(al), .. }) = w.item(r) {
                if let rd::Type::ResolvedPath(p) = &al.type_ {
                    if let Some(t) = w.resolve(r.krate, &p.id) {
                        return Ok(t);
                    }
                }
            }
            Ok(r)
        };
        let method = |t: ItemRef, tn: &str, m: &str| -> Result<ItemRef, String> {
            inherent_method(w, t, m).ok_or_else(|| format!("adapter {origin}: {tn}.{m} is not a method"))
        };
        for x in &a.consume {
            let t = ty(&x.ty)?;
            let f = method(t, &x.ty, &x.method)?;
            if receiver(w, f) != Some("self") {
                return Err(format!(
                    "adapter {origin}: {}.{} does not take `self` by value; a consume declaration does not apply",
                    x.ty, x.method
                ));
            }
            self.consumes.push((t, x.method.clone(), a.adapter.clone()));
        }
        for x in &a.retain_owner {
            let t = ty(&x.ty)?;
            let f = method(t, &x.ty, &x.method)?;
            if !matches!(receiver(w, f), Some("&self" | "&mut self")) {
                return Err(format!("adapter {origin}: {}.{} does not borrow its receiver; retain_owner does not apply", x.ty, x.method));
            }
            self.retains.push((t, x.method.clone(), a.adapter.clone()));
        }
        for x in &a.returns_receiver {
            let t = ty(&x.ty)?;
            let f = method(t, &x.ty, &x.method)?;
            let Some(rd::Item { inner: rd::ItemEnum::Function(func), .. }) = w.item(f) else { return Err(format!("adapter {origin}: {}.{} is not a method", x.ty, x.method)) };
            let returns_self_ref = match &func.sig.output {
                Some(rd::Type::BorrowedRef { type_, .. }) => match &**type_ {
                    rd::Type::Generic(s) => s == "Self",
                    rd::Type::ResolvedPath(p) => w.resolve(f.krate, &p.id) == Some(t),
                    _ => false,
                },
                _ => false,
            };
            if !returns_self_ref || !matches!(receiver(w, f), Some("&self" | "&mut self")) {
                return Err(format!(
                    "adapter {origin}: {}.{} does not return `&Self`/`&mut Self` from a borrowed receiver; returns_receiver does not apply",
                    x.ty, x.method
                ));
            }
            self.receivers.push((t, x.method.clone(), a.adapter.clone()));
        }
        for x in &a.close {
            let t = ty(&x.ty)?;
            if inherent_method(w, t, &x.method).is_some() {
                return Err(format!("adapter {origin}: {}.{} already exists; choose another close method name", x.ty, x.method));
            }
            self.closes.push((t, x.method.clone(), a.adapter.clone()));
        }
        for x in &a.rename {
            let parts: Vec<&str> = x.item.split('.').collect();
            let (m, tparts) = parts.split_last().ok_or_else(|| format!("adapter {origin}: empty item path"))?;
            let tn = tparts.join(".");
            let t = ty(&tn)?;
            method(t, &tn, m).map_err(|_| format!("adapter {origin}: item '{}' does not exist", x.item))?;
            self.renames.push((t, x.name.clone(), m.to_string()));
        }
        for x in &a.trait_error {
            let path: Vec<String> = x.trait_.split('.').map(String::from).collect();
            let t = w.lookup_path(c, &path).ok_or_else(|| format!("adapter {origin}: trait '{}' does not exist in crate '{}'", x.trait_, a.krate))?;
            if !matches!(w.item(t).map(|i| &i.inner), Some(rd::ItemEnum::Trait(_))) {
                return Err(format!("adapter {origin}: '{}' is not a trait", x.trait_));
            }
            let has_arg = w.trait_items(t).into_iter().any(|m| match w.item(m).map(|i| &i.inner) {
                Some(rd::ItemEnum::Function(f)) => f.sig.inputs.iter().any(|(n, _)| *n == x.arg),
                _ => false,
            });
            if !has_arg {
                return Err(format!("adapter {origin}: no method of {} has a parameter '{}'", x.trait_, x.arg));
            }
            self.trait_errors.push((t, x.arg.clone(), x.method.clone(), a.adapter.clone()));
        }
        for x in &a.task_waker {
            let t = ty(&x.ty)?;
            let f = method(t, &x.ty, &x.method)?;
            if receiver(w, f) != Some("&self") {
                return Err(format!("adapter {origin}: {}.{} must take `&self` to be called from a waker", x.ty, x.method));
            }
            self.wakers.push((t, x.method.clone(), x.arg.clone(), a.adapter.clone()));
        }
        for x in &a.scoped_borrow {
            let t = ty(&x.ty)?;
            let f = method(t, &x.ty, &x.method)?;
            if receiver(w, f) != Some("&mut self") {
                return Err(format!("adapter {origin}: {}.{} does not borrow its receiver mutably; scoped_borrow does not apply", x.ty, x.method));
            }
            self.scoped.push((t, x.method.clone(), x.forget.clone(), a.adapter.clone()));
        }
        Ok(())
    }

    pub fn close_method(&self, _w: &World, t: ItemRef, name: &str) -> bool {
        self.closes.iter().any(|(x, m, _)| *x == t && m == name)
    }

    pub fn rust_name(&self, _w: &World, t: ItemRef, name: &str) -> Option<String> {
        self.renames.iter().find(|(x, n, _)| *x == t && n == name).map(|r| r.2.clone())
    }

    pub fn retains_owner(&self, t: ItemRef, method: &str) -> Option<&str> {
        self.retains.iter().find(|(x, m, _)| *x == t && m == method).map(|r| r.2.as_str())
    }

    pub fn returns_receiver(&self, t: ItemRef, method: &str) -> Option<&str> {
        self.receivers.iter().find(|(x, m, _)| *x == t && m == method).map(|r| r.2.as_str())
    }

    pub fn scoped_borrow(&self, t: ItemRef, method: &str) -> Option<(&str, &str)> {
        self.scoped.iter().find(|(x, m, _, _)| *x == t && m == method).map(|r| (r.2.as_str(), r.3.as_str()))
    }

    /// Error channel of a table-implemented trait: (argument, method).
    pub fn trait_error(&self, t: ItemRef) -> Option<(&str, &str)> {
        self.trait_errors.iter().find(|x| x.0 == t).map(|x| (x.1.as_str(), x.2.as_str()))
    }

    /// Waker protocol of a type: (method, argument expression).
    pub fn task_waker(&self, t: ItemRef) -> Option<(&str, &str)> {
        self.wakers.iter().find(|x| x.0 == t).map(|x| (x.1.as_str(), x.2.as_str()))
    }

    pub fn consumes(&self, t: ItemRef, method: &str) -> Option<&str> {
        self.consumes.iter().find(|(x, m, _)| *x == t && m == method).map(|r| r.2.as_str())
    }

    /// Adapter names applying to a method (for `luarc bindings`).
    pub fn describe(&self, t: ItemRef, method: &str) -> Option<String> {
        self.consumes(t, method)
            .or_else(|| self.retains_owner(t, method))
            .or_else(|| self.returns_receiver(t, method))
            .or_else(|| self.scoped_borrow(t, method).map(|x| x.1))
            .map(String::from)
            .or_else(|| self.closes.iter().find(|(x, m, _)| *x == t && m == method).map(|r| r.2.clone()))
            .or_else(|| self.renames.iter().find(|(x, _, m)| *x == t && m == method).map(|_| "rename".to_string()))
    }
}

impl AdapterSet {
    /// Source-visible name of a renamed method.
    pub fn source_name(&self, t: ItemRef, rust_name: &str) -> Option<String> {
        self.renames.iter().find(|(x, _, m)| *x == t && m == rust_name).map(|r| r.1.clone())
    }

    /// Adapter-provided `close` methods of a type: (method, adapter).
    pub fn closes_of(&self, t: ItemRef) -> Vec<(String, String)> {
        self.closes.iter().filter(|(x, _, _)| *x == t).map(|(_, m, a)| (m.clone(), a.clone())).collect()
    }
}
