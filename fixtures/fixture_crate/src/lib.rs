//! An ordinary Rust library used as an import fixture. Nothing in this crate knows
//! about luarc: no registration attributes, no glue.

use std::fmt;
use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};

// Free functions: scalars, strings, bytes, options, results, tuples, vectors

pub fn add(a: f64, b: f64) -> f64 {
    a + b
}

pub fn greet(name: &str) -> String {
    format!("hello, {name}!")
}

pub fn shout(s: String) -> String {
    s.to_uppercase()
}

pub fn count_bytes(data: &[u8]) -> usize {
    data.len()
}

pub fn bytes_echo(data: &[u8]) -> Vec<u8> {
    data.to_vec()
}

pub fn checked_div(a: i32, b: i32) -> Option<i32> {
    if b == 0 {
        None
    } else {
        Some(a / b)
    }
}

pub fn first_char(s: &str) -> Option<char> {
    s.chars().next()
}

pub fn min_max(values: &[f64]) -> (f64, f64) {
    let mut lo = f64::INFINITY;
    let mut hi = f64::NEG_INFINITY;
    for &v in values {
        lo = lo.min(v);
        hi = hi.max(v);
    }
    (lo, hi)
}

pub fn squares(n: u32) -> Vec<u32> {
    (1..=n).map(|i| i * i).collect()
}

pub fn sum_all(values: Vec<i64>) -> i64 {
    values.iter().sum()
}

pub fn join_words(words: Vec<String>, sep: &str) -> String {
    words.join(sep)
}

pub fn halve(x: f32) -> f32 {
    x / 2.0
}

pub fn to_u8(x: u8) -> u8 {
    x
}

/// Larger than 2^53: not exactly representable as a source number.
pub fn big_number() -> u64 {
    u64::MAX - 1
}

pub fn max_safe() -> u64 {
    1 << 53
}

pub fn fixed_pair(v: [i32; 2]) -> i32 {
    v[0] * v[1]
}

pub const ANSWER: i32 = 42;
pub const GREETING: &str = "hi there";

#[derive(Debug)]
pub struct ParseError {
    pub input: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid port number '{}'", self.input)
    }
}

impl std::error::Error for ParseError {}

pub fn parse_port(s: &str) -> Result<u16, ParseError> {
    s.trim().parse::<u16>().map_err(|_| ParseError { input: s.to_string() })
}

pub fn split_pair(s: &str) -> Result<(String, String), ParseError> {
    match s.split_once('=') {
        Some((a, b)) => Ok((a.to_string(), b.to_string())),
        None => Err(ParseError { input: s.to_string() }),
    }
}

#[cfg(feature = "extra")]
pub fn extra_feature() -> i32 {
    7
}

// Generic functions

pub fn largest<T: PartialOrd + Copy>(items: &[T]) -> T {
    let mut best = items[0];
    for &x in items {
        if x > best {
            best = x;
        }
    }
    best
}

pub fn describe<T: fmt::Display>(value: T) -> String {
    format!("<{value}>")
}

pub fn parse_num<T: FromStr>(s: &str) -> Option<T> {
    s.trim().parse().ok()
}

pub fn repeat_value<T: Clone>(value: T, n: usize) -> Vec<T> {
    vec![value; n]
}

// Re-exported type with inherent methods (opaque handle)

pub mod shapes {
    pub struct Circle {
        radius: f64,
        label: String,
    }

    impl Circle {
        pub fn new(radius: f64) -> Circle {
            Circle { radius, label: format!("circle r={radius}") }
        }
        pub fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
        pub fn radius(&self) -> f64 {
            self.radius
        }
        pub fn scale(&mut self, k: f64) {
            self.radius *= k;
            self.label = format!("circle r={}", self.radius);
        }
        /// Borrowed string result.
        pub fn label(&self) -> &str {
            &self.label
        }
    }
}

pub use shapes::Circle;

/// Alias path for the same type.
pub type Disc = shapes::Circle;

// Mutable methods, public fields on a handle, callbacks

#[derive(Debug, Default)]
pub struct Counter {
    pub step: i64,
    count: i64,
}

impl Counter {
    pub fn new() -> Counter {
        Counter { step: 1, count: 0 }
    }
    pub fn inc(&mut self) {
        self.count += self.step;
    }
    pub fn add(&mut self, n: i64) {
        self.count += n;
    }
    pub fn get(&self) -> i64 {
        self.count
    }
    /// Calls `f` with each value 1..=count while the counter is borrowed mutably.
    pub fn visit(&mut self, mut f: impl FnMut(i64)) {
        for i in 1..=self.count {
            f(i);
        }
        self.count += 0;
    }
}

pub fn apply_twice<F: Fn(f64) -> f64>(f: F, x: f64) -> f64 {
    f(f(x))
}

pub fn for_each_word(text: &str, mut f: impl FnMut(&str)) {
    for w in text.split_whitespace() {
        f(w);
    }
}

pub fn map_values(values: &[i32], f: &dyn Fn(i32) -> i32) -> Vec<i32> {
    values.iter().map(|&v| f(v)).collect()
}

pub fn call_n<F: FnMut()>(n: u32, mut f: F) {
    for _ in 0..n {
        f();
    }
}

// Unsupported on purpose: the callback may be retained or sent to another thread.
pub fn store_callback(f: Box<dyn Fn()>) -> usize {
    let _ = f;
    0
}

pub fn spawn_like<F: Fn() + Send + 'static>(f: F) {
    f()
}

// Plain public data (record conversion) and enums

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

pub fn midpoint(a: &Point, b: &Point) -> Point {
    Point { x: (a.x + b.x) / 2.0, y: (a.y + b.y) / 2.0 }
}

pub fn translate(p: Point, dx: f64) -> Point {
    Point { x: p.x + dx, y: p.y }
}

pub fn centroid(points: Vec<Point>) -> Point {
    let n = points.len() as f64;
    let (sx, sy) = points.iter().fold((0.0, 0.0), |(a, b), p| (a + p.x, b + p.y));
    Point { x: sx / n, y: sy / n }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Green,
    Blue,
}

pub fn color_name(c: Color) -> &'static str {
    match c {
        Color::Red => "red",
        Color::Green => "green",
        Color::Blue => "blue",
    }
}

pub fn next_color(c: Color) -> Color {
    match c {
        Color::Red => Color::Green,
        Color::Green => Color::Blue,
        Color::Blue => Color::Red,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Shape {
    Circle(f64),
    Rect(f64, f64),
}

pub fn shape_area(s: &Shape) -> f64 {
    match s {
        Shape::Circle(r) => std::f64::consts::PI * r * r,
        Shape::Rect(w, h) => w * h,
    }
}

// Resources with drop counters (cleanup / owner retention / consumption)

static LIVE_TRACKED: AtomicUsize = AtomicUsize::new(0);
static LIVE_LEDGERS: AtomicUsize = AtomicUsize::new(0);
static LIVE_POOLS: AtomicUsize = AtomicUsize::new(0);

pub struct Tracked {
    name: String,
}

impl Tracked {
    pub fn new(name: &str) -> Tracked {
        LIVE_TRACKED.fetch_add(1, Ordering::SeqCst);
        Tracked { name: name.to_string() }
    }
    pub fn name(&self) -> String {
        self.name.clone()
    }
}

impl Drop for Tracked {
    fn drop(&mut self) {
        LIVE_TRACKED.fetch_sub(1, Ordering::SeqCst);
    }
}

pub fn live_tracked() -> usize {
    LIVE_TRACKED.load(Ordering::SeqCst)
}

/// Fails after creating a temporary resource (error-path cleanup test).
pub fn tracked_then_fail(name: &str) -> Result<Tracked, ParseError> {
    let t = Tracked::new(name);
    drop(t);
    Err(ParseError { input: name.to_string() })
}

/// A non-Clone resource with a consuming method (needs the ledger adapter).
pub struct Ledger {
    name: String,
    total: i64,
}

pub struct Receipt {
    pub name: String,
    pub total: i64,
}

impl Receipt {
    pub fn summary(&self) -> String {
        format!("{}: {}", self.name, self.total)
    }
}

impl Ledger {
    pub fn open(name: &str) -> Ledger {
        LIVE_LEDGERS.fetch_add(1, Ordering::SeqCst);
        Ledger { name: name.to_string(), total: 0 }
    }
    pub fn add_entry(&mut self, amount: i64) {
        self.total += amount;
    }
    pub fn total(&self) -> i64 {
        self.total
    }
    /// Consumes the ledger.
    pub fn finish(self) -> Receipt {
        Receipt { name: self.name.clone(), total: self.total }
    }
}

impl Drop for Ledger {
    fn drop(&mut self) {
        LIVE_LEDGERS.fetch_sub(1, Ordering::SeqCst);
    }
}

pub fn live_ledgers() -> usize {
    LIVE_LEDGERS.load(Ordering::SeqCst)
}

pub struct Pool {
    next: std::cell::Cell<u32>,
}

/// Logically tied to the pool that created it (owner retention via adapter).
pub struct Lease {
    id: u32,
}

impl Pool {
    pub fn new() -> Pool {
        LIVE_POOLS.fetch_add(1, Ordering::SeqCst);
        Pool { next: std::cell::Cell::new(1) }
    }
    pub fn checkout(&self) -> Lease {
        let id = self.next.get();
        self.next.set(id + 1);
        Lease { id }
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        LIVE_POOLS.fetch_sub(1, Ordering::SeqCst);
    }
}

impl Lease {
    pub fn id(&self) -> u32 {
        self.id
    }
}

pub fn live_pools() -> usize {
    LIVE_POOLS.load(Ordering::SeqCst)
}

// Unsupported signatures next to supported ones

pub fn nested_option(x: i32) -> Option<Option<i32>> {
    if x > 0 {
        Some(Some(x))
    } else {
        Some(None)
    }
}

pub fn nested_tuple() -> ((i32, i32), i32) {
    ((1, 2), 3)
}

pub fn takes_tuple(t: (i32, i32)) -> i32 {
    t.0 + t.1
}

/// Tuple arguments in nested positions, shaped like wgpu's
/// `PipelineCompilationOptions { constants: &[(&str, f64)], .. }` inside a
/// pipeline descriptor.
#[derive(Clone, Debug, Default)]
pub struct CompileOptions<'a> {
    pub constants: &'a [(&'a str, f64)],
    pub zero_init: bool,
}

pub struct StageDesc<'a> {
    pub entry: &'a str,
    pub options: CompileOptions<'a>,
}

pub fn describe_stage(d: &StageDesc) -> String {
    let cs: Vec<String> = d.options.constants.iter().map(|(k, v)| format!("{k}={v}")).collect();
    format!("{}[{}]{}", d.entry, cs.join(","), if d.options.zero_init { " zero" } else { "" })
}

pub fn sample_options() -> CompileOptions<'static> {
    CompileOptions { constants: &[("WIDTH", 640.0), ("HEIGHT", 480.0)], zero_init: true }
}

pub fn weigh(pairs: &[(&str, f64)]) -> f64 {
    pairs.iter().map(|(k, v)| k.len() as f64 * v).sum()
}

pub fn owned_pairs(v: Vec<(String, i32)>) -> String {
    v.iter().map(|(k, n)| format!("{k}:{n}")).collect::<Vec<_>>().join(" ")
}

/// A record field whose type core defines in a private module
/// (`core::num::nonzero::NonZero`), like wgpu's `multiview_mask`.
pub struct Limits {
    pub max: Option<std::num::NonZeroU32>,
}

pub fn limit(n: u32) -> Option<std::num::NonZeroU32> {
    std::num::NonZeroU32::new(n)
}

pub fn describe_limits(l: &Limits) -> String {
    match l.max {
        Some(m) => format!("max {m}"),
        None => "unlimited".to_string(),
    }
}

// Borrowed enum variants and generic arguments.
// Tests nested buffer references in create_bind_group and
// generic conversions through Option<&BindGroup> in set_bind_group.

pub struct GpuBuffer {
    name: String,
    size: u64,
}

impl GpuBuffer {
    pub fn new(name: &str, size: u64) -> GpuBuffer {
        GpuBuffer { name: name.to_string(), size }
    }
    pub fn name(&self) -> String {
        self.name.clone()
    }
}

pub struct GpuSampler {
    filter: String,
}

impl GpuSampler {
    pub fn new(filter: &str) -> GpuSampler {
        GpuSampler { filter: filter.to_string() }
    }
}

#[derive(Clone)]
pub struct GpuBufferBinding<'a> {
    pub buffer: &'a GpuBuffer,
    pub offset: u64,
    pub size: Option<u64>,
}

#[derive(Clone)]
pub enum GpuResource<'a> {
    Buffer(GpuBufferBinding<'a>),
    BufferArray(&'a [GpuBufferBinding<'a>]),
    Sampler(&'a GpuSampler),
    SamplerArray(&'a [&'a GpuSampler]),
    SamplerAt(&'a GpuSampler, u32),
    Nothing,
}

pub struct GpuEntry<'a> {
    pub binding: u32,
    pub resource: GpuResource<'a>,
}

pub struct GpuGroupDesc<'a> {
    pub label: Option<&'a str>,
    pub entries: &'a [GpuEntry<'a>],
}

pub struct GpuGroup {
    summary: String,
}

impl GpuGroup {
    pub fn summary(&self) -> String {
        self.summary.clone()
    }
}

fn describe_resource(r: &GpuResource) -> String {
    let b = |x: &GpuBufferBinding| format!("{}@{}+{}", x.buffer.name, x.offset, x.size.unwrap_or(x.buffer.size - x.offset));
    match r {
        GpuResource::Buffer(x) => b(x),
        GpuResource::BufferArray(xs) => format!("[{}]", xs.iter().map(b).collect::<Vec<_>>().join(",")),
        GpuResource::Sampler(s) => format!("sampler {}", s.filter),
        GpuResource::SamplerArray(ss) => format!("samplers {}", ss.iter().map(|s| s.filter.as_str()).collect::<Vec<_>>().join("+")),
        GpuResource::SamplerAt(s, i) => format!("sampler {}#{i}", s.filter),
        GpuResource::Nothing => "nothing".to_string(),
    }
}

pub fn create_group(d: &GpuGroupDesc) -> GpuGroup {
    let es: Vec<String> = d.entries.iter().map(|e| format!("{}:{}", e.binding, describe_resource(&e.resource))).collect();
    GpuGroup { summary: format!("{} {{{}}}", d.label.unwrap_or("?"), es.join(" ")) }
}

pub fn describe_one(r: GpuResource) -> String {
    describe_resource(&r)
}

pub fn nothing_resource() -> GpuResource<'static> {
    GpuResource::Nothing
}

pub struct GpuPass {
    log: Vec<String>,
}

impl GpuPass {
    pub fn new() -> GpuPass {
        GpuPass { log: Vec::new() }
    }
    pub fn set_group<'a, G>(&mut self, index: u32, group: G)
    where
        Option<&'a GpuGroup>: From<G>,
    {
        let g: Option<&GpuGroup> = group.into();
        self.log.push(format!("{index}={}", g.map(|g| g.summary.as_str()).unwrap_or("none")));
    }
    pub fn log(&self) -> String {
        self.log.join("; ")
    }
}

// An enum that borrows only plain data stays a handle: a builder keeps it in its
// result (glyphon `Attrs::family(self, Family<'a>) -> Attrs<'a>`).
pub enum FontFamily<'a> {
    Name(&'a str),
    Serif,
}

pub struct TextStyle<'a> {
    family: FontFamily<'a>,
}

impl<'a> TextStyle<'a> {
    pub fn new() -> TextStyle<'static> {
        TextStyle { family: FontFamily::Name("default") }
    }
    pub fn family(mut self, family: FontFamily<'a>) -> TextStyle<'a> {
        self.family = family;
        self
    }
    pub fn describe(&self) -> String {
        match &self.family {
            FontFamily::Name(n) => format!("font {n}"),
            FontFamily::Serif => "serif".to_string(),
        }
    }
}

pub fn optional_pair(p: (Option<i32>, bool)) -> i32 {
    if p.1 { p.0.unwrap_or(-1) } else { 0 }
}

/// # Safety
/// Never imported automatically.
pub unsafe fn dangerous() -> i32 {
    1
}

pub async fn later() -> i32 {
    1
}

pub fn huge(x: u128) -> u128 {
    x
}

pub trait Greeter {
    fn hello(&self) -> String;
}

#[macro_export]
macro_rules! fixture_macro {
    () => {
        1
    };
}

/// A genuine bug in native code: panics are not converted into catchable
/// language errors.
pub fn always_panics(n: i32) -> i32 {
    if n >= 0 {
        panic!("native invariant violated ({n})");
    }
    n
}

// Exact 64-bit integers

/// Identity on u64 (IDs, flags and timestamps above 2^53 must round-trip).
pub fn echo_u64(x: u64) -> u64 {
    x
}

pub fn add_i64(a: i64, b: i64) -> i64 {
    a.wrapping_add(b)
}

pub fn set_flag(flags: u64, bit: u32) -> u64 {
    flags | (1u64 << bit)
}

/// A record with exact integer fields.
#[derive(Clone, Debug, PartialEq)]
pub struct Stamp {
    pub id: u64,
    pub nanos: i64,
}

pub fn next_stamp(s: Stamp) -> Stamp {
    Stamp { id: s.id + 1, nanos: s.nanos - 1 }
}

// Borrowed results: identity, children, invalidation

/// A tree whose `&mut Self` accessors return a *different* node of the same type.
#[derive(Debug, Default)]
pub struct Tree {
    pub label: String,
    children: Vec<Tree>,
}

impl Tree {
    pub fn new(label: &str) -> Tree {
        Tree { label: label.to_string(), children: Vec::new() }
    }
    pub fn add(&mut self, label: &str) -> &mut Tree {
        self.children.push(Tree::new(label));
        self.children.last_mut().unwrap()
    }
    pub fn child(&self, i: usize) -> Option<&Tree> {
        self.children.get(i)
    }
    pub fn child_mut(&mut self, i: usize) -> &mut Tree {
        &mut self.children[i]
    }
    pub fn rename(&mut self, label: &str) -> &mut Self {
        self.label = label.to_string();
        self
    }
    pub fn label(&self) -> String {
        self.label.clone()
    }
    pub fn count(&self) -> usize {
        self.children.len()
    }
    pub fn clear(&mut self) {
        self.children.clear();
    }
}

/// Keyed lookup returning borrowed objects.
#[derive(Default)]
pub struct Registry {
    items: std::collections::BTreeMap<String, Tree>,
}

impl Registry {
    pub fn new() -> Registry {
        Registry::default()
    }
    pub fn insert(&mut self, key: &str, t: Tree) {
        self.items.insert(key.to_string(), t);
    }
    pub fn get(&self, key: &str) -> Option<&Tree> {
        self.items.get(key)
    }
}

// Clone semantics

/// An independent value: `clone()` copies the data.
#[derive(Clone, Debug, Default)]
pub struct Notes {
    lines: Vec<String>,
}

impl Notes {
    pub fn new() -> Notes {
        Notes::default()
    }
    pub fn push(&mut self, s: &str) {
        self.lines.push(s.to_string());
    }
    pub fn len(&self) -> usize {
        self.lines.len()
    }
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }
}

/// A shared resource: `clone()` returns another handle to the same counter.
#[derive(Clone, Debug, Default)]
pub struct SharedCount {
    n: std::rc::Rc<std::cell::Cell<i64>>,
}

impl SharedCount {
    pub fn new() -> SharedCount {
        SharedCount::default()
    }
    pub fn bump(&self) {
        self.n.set(self.n.get() + 1);
    }
    pub fn get(&self) -> i64 {
        self.n.get()
    }
}

/// Consumes its argument (by value): the source handle becomes consumed, it is
/// never silently cloned.
pub fn seal(n: Notes) -> usize {
    n.lines.len()
}

// Futures: real wakeups from another thread

/// A timer future: the first poll starts a thread that sleeps, then wakes the
/// task. Executor-independent (no runtime reactor).
pub struct Delay {
    ms: u64,
    state: std::sync::Arc<std::sync::Mutex<(bool, Option<std::task::Waker>)>>,
    started: bool,
}

impl Delay {
    pub fn new(ms: u64) -> Delay {
        Delay { ms, state: Default::default(), started: false }
    }
}

impl std::future::Future for Delay {
    type Output = u64;
    fn poll(mut self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<u64> {
        let mut st = self.state.lock().unwrap();
        if st.0 {
            return std::task::Poll::Ready(self.ms);
        }
        st.1 = Some(cx.waker().clone());
        drop(st);
        if !self.started {
            self.started = true;
            let (ms, state) = (self.ms, self.state.clone());
            std::thread::spawn(move || {
                std::thread::sleep(std::time::Duration::from_millis(ms));
                let mut st = state.lock().unwrap();
                st.0 = true;
                if let Some(w) = st.1.take() {
                    w.wake();
                }
            });
        }
        std::task::Poll::Pending
    }
}

/// `impl Future` result (the future owns its state; no argument is borrowed).
pub fn delay_ms(ms: u64) -> impl std::future::Future<Output = u64> {
    Delay::new(ms)
}

/// An `async fn` with a fallible result.
pub async fn parse_later(ms: u64, s: String) -> Result<u16, ParseError> {
    Delay::new(ms).await;
    s.parse::<u16>().map_err(|_| ParseError { input: s })
}

/// A future that never completes while holding `t`: cancelling (dropping) it
/// must release `t`.
pub fn hold_forever(t: Tracked) -> impl std::future::Future<Output = ()> {
    async move {
        let _keep = t;
        std::future::pending::<()>().await
    }
}

// Traits implemented by source tables

pub fn greet_with<G: Greeter>(g: &G) -> String {
    format!("[{}]", g.hello())
}

/// A trait with `&mut self`, a lent argument, a provided method and a
/// `Result`-returning method.
pub trait Visitor {
    fn enter(&mut self, node: &Tree, depth: usize);
    fn leave(&mut self, _depth: usize) {}
    fn accept(&self, _label: &str) -> Result<bool, String> {
        Ok(true)
    }
}

/// Walks a tree depth-first; stops with the visitor's error.
pub fn walk<V: Visitor>(t: &Tree, v: &mut V) -> Result<usize, String> {
    fn go<V: Visitor>(t: &Tree, v: &mut V, depth: usize, n: &mut usize) -> Result<(), String> {
        if !v.accept(&t.label)? {
            return Ok(());
        }
        *n += 1;
        v.enter(t, depth);
        for c in &t.children {
            go(c, v, depth + 1, n)?;
        }
        v.leave(depth);
        Ok(())
    }
    let mut n = 0;
    go(t, v, 0, &mut n)?;
    Ok(n)
}

// Retained callbacks: registration owns the closure

/// An event bus storing callbacks until they are unsubscribed.
#[derive(Default)]
pub struct Bus {
    subs: Vec<(u64, Box<dyn FnMut(i64)>)>,
    next: u64,
}

impl Bus {
    pub fn new() -> Bus {
        Bus::default()
    }
    pub fn subscribe(&mut self, f: Box<dyn FnMut(i64)>) -> u64 {
        self.next += 1;
        self.subs.push((self.next, f));
        self.next
    }
    pub fn unsubscribe(&mut self, id: u64) -> bool {
        let before = self.subs.len();
        self.subs.retain(|(i, _)| *i != id);
        self.subs.len() != before
    }
    pub fn emit(&mut self, v: i64) -> usize {
        for (_, f) in self.subs.iter_mut() {
            f(v);
        }
        self.subs.len()
    }
    pub fn count(&self) -> usize {
        self.subs.len()
    }
}

// Ownership contracts: arrays of consumed objects, shared (`Arc`) objects --

/// Consumes every element of the array (objects passed by value).
pub fn seal_all(ns: Vec<Notes>) -> usize {
    ns.iter().map(|n| n.lines.len()).sum()
}

/// Consumes an array and one more object.
pub fn seal_with(ns: Vec<Notes>, last: Notes) -> usize {
    seal_all(ns) + last.lines.len()
}

/// `Send + Sync`, not `Clone`, only `&self` methods: shared through an `Arc`.
pub struct Beacon {
    id: u32,
    hits: std::sync::atomic::AtomicU32,
}

impl Beacon {
    pub fn new(id: u32) -> Beacon {
        Beacon { id, hits: std::sync::atomic::AtomicU32::new(0) }
    }
    pub fn hit(&self) {
        self.hits.fetch_add(1, Ordering::SeqCst);
    }
    pub fn hits(&self) -> u32 {
        self.hits.load(Ordering::SeqCst)
    }
    pub fn id(&self) -> u32 {
        self.id
    }
}

/// Holds shared references to beacons.
#[derive(Default)]
pub struct Tower {
    beacons: Vec<std::sync::Arc<Beacon>>,
}

impl Tower {
    pub fn new() -> Tower {
        Tower::default()
    }
    pub fn watch(&mut self, b: std::sync::Arc<Beacon>) {
        self.beacons.push(b);
    }
    pub fn release(&mut self) {
        self.beacons.clear();
    }
    pub fn total_hits(&self) -> u32 {
        self.beacons.iter().map(|b| b.hits()).sum()
    }
}

/// Takes a beacon by value: only possible when nothing else shares it.
pub fn retire(b: Beacon) -> u32 {
    b.hits()
}

/// Consumes a beacon and an object: neither may be consumed when one cannot be.
pub fn retire_with(b: Beacon, n: Notes) -> u32 {
    b.hits() + n.lines.len() as u32
}

impl Tree {
    /// A future borrowing the tree: the label after `ms` milliseconds.
    pub async fn label_after(&self, ms: u64) -> String {
        Delay::new(ms).await;
        self.label.clone()
    }
}

/// Ends the process with `code` (exit statuses beyond 0..=255 are possible on Windows).
pub fn exit_with(code: i32) {
    std::process::exit(code)
}

// Importer resolution: shared fields, specialized impls, several trait impls --

/// Shared (`Arc`) object with a public field holding another native object.
pub struct Hub {
    pub beacon: Beacon,
    pub notes: Notes,
    pub name: String,
}

impl Hub {
    pub fn new(name: &str) -> Hub {
        let mut notes = Notes::new();
        notes.push(name);
        Hub { beacon: Beacon::new(1), notes, name: name.to_string() }
    }
    pub fn ping(&self) -> u32 {
        self.beacon.hit();
        self.beacon.hits()
    }
}

/// A generic wrapper whose inherent impls are specialized per argument type.
pub struct Wrapper<T>(pub T);

impl Wrapper<u32> {
    pub fn of_int(x: u32) -> Wrapper<u32> {
        Wrapper(x)
    }
    pub fn describe(&self) -> String {
        format!("int {}", self.0)
    }
}

impl Wrapper<String> {
    pub fn of_text(s: &str) -> Wrapper<String> {
        Wrapper(s.to_string())
    }
    pub fn describe(&self) -> String {
        format!("text {}", self.0)
    }
}

/// Several impls of one generic trait.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Meters(pub f64);

impl From<f64> for Meters {
    fn from(x: f64) -> Meters {
        Meters(x)
    }
}

impl From<u32> for Meters {
    fn from(km: u32) -> Meters {
        Meters(km as f64 * 1000.0)
    }
}

impl Meters {
    pub fn value(&self) -> f64 {
        self.0
    }
}

/// Consumes an array of shared (Arc-represented) objects.
pub fn retire_all(bs: Vec<Beacon>) -> u32 {
    bs.iter().map(|b| b.hits()).sum()
}

/// A generic bound with `Send`: a source table cannot satisfy it.
pub fn greet_send<G: Greeter + Send>(g: G) -> String {
    g.hello()
}

/// A result-only generic next to an `impl Trait` parameter.
pub fn parse_text<T: FromStr>(s: impl AsRef<str>) -> Option<T> {
    s.as_ref().trim().parse().ok()
}

/// An associated constant (for adapter validation tests).
impl Meters {
    pub const ZERO: Meters = Meters(0.0);
}
