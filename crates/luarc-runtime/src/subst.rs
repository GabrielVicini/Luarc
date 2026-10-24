//! `string.gsub` and `string.gmatch`.
//!
//! Both follow Luau 0.743's scanning rules (those of Lua 5.1, not 5.4): after a
//! non-empty match scanning resumes at its end, where an empty match is allowed
//! (`("abc"):gsub("%a*", "-")` is `--`, 2), and `^` is an anchor only in `gsub`.

use crate::error::{LResult, LuaError};
use crate::pattern::{match_at, Capture};
use crate::show::num_to_string;
use crate::stdlib::Found;
use crate::value::{LMap, LStr};

/// One match as seen by a replacement.
pub struct Match<'a> {
    whole: &'a [u8],
    caps: &'a [Capture],
}

impl Match<'_> {
    /// Capture `i`: a string, or the whole match when the pattern has no captures.
    pub fn str_arg(&self, i: usize) -> LStr {
        LStr::from_vec(self.capture_text(i))
    }

    /// Position capture `i` (`()` in the pattern).
    pub fn pos_arg(&self, i: usize) -> f64 {
        match self.caps.get(i) {
            Some(Capture::Pos(p)) => *p,
            _ => f64::NAN,
        }
    }

    fn capture_text(&self, i: usize) -> Vec<u8> {
        match self.caps.get(i) {
            Some(Capture::Str(b)) => b.clone(),
            Some(Capture::Pos(p)) => num_to_string(*p).into_bytes(),
            None if self.caps.is_empty() && i == 0 => self.whole.to_vec(),
            None => Vec::new(),
        }
    }
}

/// What a replacement function or table gives for a match: a string replaces it,
/// nothing (`nil`) keeps it.
pub trait ReplValue {
    fn into_repl(self) -> Option<Vec<u8>>;
}

impl ReplValue for LStr {
    fn into_repl(self) -> Option<Vec<u8>> {
        Some(self.as_bytes().to_vec())
    }
}

impl ReplValue for Option<LStr> {
    fn into_repl(self) -> Option<Vec<u8>> {
        self.map(|s| s.as_bytes().to_vec())
    }
}

/// The scanning loop shared by every replacement kind. `repl` returns the
/// replacement text, or `None` to keep the matched text.
fn gsub(s: &LStr, p: &LStr, max: Option<f64>, mut repl: impl FnMut(&Match) -> LResult<Option<Vec<u8>>>) -> LResult<(LStr, f64)> {
    let sb = s.as_bytes();
    let (anchor, pat) = match p.as_bytes().split_first() {
        Some((b'^', rest)) => (true, rest),
        _ => (false, p.as_bytes()),
    };
    // `luaL_optinteger`: a fractional count is truncated; the default is "all"
    let limit = max.map_or(sb.len() as f64 + 1.0, f64::trunc);
    let mut out = Vec::with_capacity(sb.len());
    let (mut src, mut n) = (0, 0.0);
    while n < limit {
        let mut copy_one = true;
        if let Some((end, caps)) = match_at(sb, pat, src)? {
            n += 1.0;
            let whole = &sb[src..end];
            match repl(&Match { whole, caps: &caps })? {
                Some(r) => out.extend_from_slice(&r),
                None => out.extend_from_slice(whole),
            }
            if end > src {
                src = end;
                copy_one = false;
            }
        }
        if copy_one {
            // no match, or an empty one: step over one byte
            match sb.get(src) {
                Some(&b) => {
                    out.push(b);
                    src += 1;
                }
                None => break,
            }
        }
        if anchor {
            break;
        }
    }
    out.extend_from_slice(&sb[src..]);
    Ok((LStr::from_vec(out), n))
}

/// `string.gsub(s, p, template, n)`: `%0`..`%9` stand for the whole match and the
/// captures, `%%` for a percent sign.
pub fn gsub_template(s: &LStr, p: &LStr, template: &LStr, max: Option<f64>) -> LResult<(LStr, f64)> {
    gsub(s, p, max, |m| {
        let mut r = Vec::new();
        let mut t = template.as_bytes().iter();
        while let Some(&b) = t.next() {
            if b != b'%' {
                r.push(b);
                continue;
            }
            match t.next() {
                Some(b'%') => r.push(b'%'),
                Some(&d @ b'0'..=b'9') => {
                    let i = (d - b'0') as usize;
                    if i == 0 {
                        r.extend_from_slice(m.whole);
                    } else if i > m.caps.len().max(1) {
                        return Err(LuaError::new("invalid capture index"));
                    } else {
                        r.extend_from_slice(&m.capture_text(i - 1));
                    }
                }
                _ => return Err(LuaError::new("invalid use of '%' in replacement string")),
            }
        }
        Ok(Some(r))
    })
}

/// `string.gsub(s, p, t, n)`: the first capture (or the whole match) is the key.
pub fn gsub_table(s: &LStr, p: &LStr, t: &LMap<LStr, LStr>, max: Option<f64>) -> LResult<(LStr, f64)> {
    gsub(s, p, max, |m| Ok(t.get(&m.str_arg(0)).and_then(ReplValue::into_repl)))
}

/// `string.gsub(s, p, f, n)`: `f` gets the match's captures and may return nothing.
pub fn gsub_fn<R: ReplValue>(s: &LStr, p: &LStr, max: Option<f64>, mut f: impl FnMut(&Match) -> LResult<R>) -> LResult<(LStr, f64)> {
    // Luau cannot yield through string.gsub's replacement callback.
    gsub(s, p, max, |m| Ok(crate::coroutine::non_yielding(|| f(m))?.into_repl()))
}

/// State of a `string.gmatch` loop.
pub struct Gmatch {
    s: LStr,
    p: LStr,
    src: usize,
}

impl Gmatch {
    pub fn new(s: &LStr, p: &LStr) -> Gmatch {
        Gmatch { s: s.clone(), p: p.clone(), src: 0 }
    }

    /// The next match, or `None` when the subject is exhausted.
    pub fn next(&mut self) -> LResult<Option<Found>> {
        let sb = self.s.as_bytes();
        while self.src <= sb.len() {
            let start = self.src;
            if let Some((end, caps)) = match_at(sb, self.p.as_bytes(), start)? {
                // resume after the match; an empty one must move on by a byte
                self.src = if end == start { end + 1 } else { end };
                return Ok(Some(Found::matched(start, end, LStr::from_bytes(&sb[start..end]), caps)));
            }
            self.src += 1;
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(x: &str) -> LStr {
        LStr::from(x)
    }

    fn sub(subject: &str, p: &str, t: &str, max: Option<f64>) -> (String, f64) {
        let (r, n) = gsub_template(&s(subject), &s(p), &s(t), max).unwrap();
        (r.to_string_lossy().to_string(), n)
    }

    // expected values come from Luau 0.743 (tests/diff/gsub.luarc)

    #[test]
    fn empty_matches_follow_lua_51() {
        assert_eq!(sub("abc", "%a*", "-", None), ("--".into(), 2.0));
        assert_eq!(sub("abc def", "%a*", "-", None), ("-- --".into(), 4.0));
        assert_eq!(sub("hello", "", "-", None), ("-h-e-l-l-o-".into(), 6.0));
    }

    #[test]
    fn counts_and_anchors() {
        assert_eq!(sub("hello world", "o", "0", Some(1.0)), ("hell0 world".into(), 1.0));
        assert_eq!(sub("abc", "b", "x", Some(0.0)), ("abc".into(), 0.0));
        assert_eq!(sub("abc", "b", "x", Some(-1.0)), ("abc".into(), 0.0));
        assert_eq!(sub("abc", "b", "x", Some(1.9)), ("axc".into(), 1.0));
        assert_eq!(sub("aaa", "^a", "X", None), ("Xaa".into(), 1.0));
    }

    #[test]
    fn templates() {
        assert_eq!(sub("hello world", "(%w+) (%w+)", "%2 %1", None).0, "world hello");
        assert_eq!(sub("abc", "b", "%0%0", None).0, "abbc");
        assert_eq!(sub("abc", "b", "%%", None).0, "a%c");
        assert_eq!(sub("abc", "()b", "%1", None).0, "a2c");
        for bad in ["%2", "%x", "%"] {
            assert!(gsub_template(&s("abc"), &s("b"), &s(bad), None).is_err(), "{bad}");
        }
        assert!(gsub_template(&s("abc"), &s("(b)"), &s("%2"), None).is_err());
    }

    #[test]
    fn tables_and_functions() {
        let t: LMap<LStr, LStr> = LMap::new();
        t.set(s("b"), s("B"));
        assert_eq!(gsub_table(&s("abc"), &s("b"), &t, None).unwrap().0.as_bytes(), b"aBc");
        assert_eq!(gsub_table(&s("abc"), &s("c"), &t, None).unwrap(), (s("abc"), 1.0));
        let (r, n) = gsub_fn(&s("abc"), &s("%w"), None, |m| Ok((m.str_arg(0).as_bytes() != b"b").then(|| s("x")))).unwrap();
        assert_eq!((r.as_bytes(), n), (&b"xbx"[..], 3.0));
        let (r, _) = gsub_fn(&s("abc"), &s("()"), None, |m| Ok(Some(s(&num_to_string(m.pos_arg(0)))))).unwrap();
        assert_eq!(r.as_bytes(), b"1a2b3c4");
    }

    fn all(subject: &str, p: &str) -> Vec<String> {
        let (subject, p) = (s(subject), s(p));
        let mut g = Gmatch::new(&subject, &p);
        let mut out = Vec::new();
        while let Some(f) = g.next().unwrap() {
            out.push(f.cap(0).map(|c| c.to_string_lossy().to_string()).unwrap_or_default());
        }
        out
    }

    #[test]
    fn gmatch_scanning() {
        assert_eq!(all("one two  three", "%a+"), ["one", "two", "three"]);
        assert_eq!(all("abc", "%a*"), ["abc", ""]);
        assert_eq!(all("abc", ""), ["", "", "", ""]);
        assert_eq!(all("", "x*"), [""]);
        assert!(all("aaa", "^a").is_empty());
        assert_eq!(all("^a^a", "^a"), ["^a", "^a"]);
        assert_eq!(all("abc", "()"), ["1", "2", "3", "4"]);
        assert!(Gmatch::new(&s("abc"), &s("(")).next().is_err());
    }
}
