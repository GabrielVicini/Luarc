//! The language error channel.

use crate::value::LStr;

/// A catchable source-language error. Raised by `error(...)`, failed runtime checks,
/// conversion failures and native `Err` results; caught by `pcall`.
#[derive(Clone, Debug)]
pub struct LuaError {
    pub msg: LStr,
    located: bool,
}

pub type LResult<T> = Result<T, LuaError>;

impl LuaError {
    pub fn new(msg: impl Into<LStr>) -> Self {
        LuaError { msg: msg.into(), located: false }
    }
    /// An error message that already carries its position (e.g. `error("x")`).
    pub fn located(msg: impl Into<LStr>) -> Self {
        LuaError { msg: msg.into(), located: true }
    }
    /// Error produced by a native `Result::Err`.
    pub fn native(item: &str, msg: String) -> Self {
        LuaError::new(format!("{item}: {msg}"))
    }
    /// Prefixes `file:line: ` unless the message is already located.
    pub fn with_loc(mut self, loc: &str) -> Self {
        if !self.located {
            let mut b = Vec::with_capacity(loc.len() + 2 + self.msg.as_bytes().len());
            b.extend_from_slice(loc.as_bytes());
            b.extend_from_slice(b": ");
            b.extend_from_slice(self.msg.as_bytes());
            self.msg = LStr::from_vec(b);
            self.located = true;
        }
        self
    }
}

/// Attaches a source location to a failing runtime-library operation.
#[inline]
pub fn at<T>(r: LResult<T>, loc: &'static str) -> LResult<T> {
    r.map_err(|e| e.with_loc(loc))
}

/// `error(msg)`: raises a located error (level-1 position, like Lua).
pub fn raise<T>(msg: LStr, loc: &'static str) -> LResult<T> {
    Err(LuaError::new(msg).with_loc(loc))
}

/// `error(msg, 0)`: an error without a position.
pub fn raise_unlocated<T>(msg: LStr) -> LResult<T> {
    Err(LuaError::located(msg))
}

/// Extracts a readable message from a native error value: `Display` if implemented,
/// otherwise `Debug`, otherwise the type name. Uses autoref method resolution so the
/// choice is made by the Rust compiler for each concrete error type.
#[macro_export]
macro_rules! native_error_message {
    ($e:expr) => {{
        #[allow(unused_imports)]
        use $crate::error::{MsgViaDebug as _, MsgViaDisplay as _, MsgViaName as _};
        (&&&$crate::error::ErrMsg(&$e)).lua_msg()
    }};
}

pub struct ErrMsg<'a, T>(pub &'a T);

pub trait MsgViaDisplay {
    fn lua_msg(&self) -> String;
}
impl<T: std::fmt::Display> MsgViaDisplay for &&ErrMsg<'_, T> {
    fn lua_msg(&self) -> String {
        self.0.to_string()
    }
}
pub trait MsgViaDebug {
    fn lua_msg(&self) -> String;
}
impl<T: std::fmt::Debug> MsgViaDebug for &ErrMsg<'_, T> {
    fn lua_msg(&self) -> String {
        format!("{:?}", self.0)
    }
}
pub trait MsgViaName {
    fn lua_msg(&self) -> String;
}
impl<T> MsgViaName for ErrMsg<'_, T> {
    fn lua_msg(&self) -> String {
        format!("native error of type {}", std::any::type_name::<T>())
    }
}
