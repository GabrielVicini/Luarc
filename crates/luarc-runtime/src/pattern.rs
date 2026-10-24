//! Lua 5.4 string patterns (`string.find`, `string.match`), byte-oriented like
//! the reference implementation (`lstrlib.c`): character classes `%a %c %d %g %l
//! %p %s %u %w %x` (and their complements), sets `[...]`, quantifiers `* + - ?`,
//! anchors, captures (including position captures `()`), `%b` and `%f`.

use crate::error::{LResult, LuaError};

const MAX_CAPTURES: usize = 32;
const MAX_DEPTH: usize = 200;

#[derive(Clone, Copy, Debug)]
enum Cap {
    /// Still open (start).
    Open(usize),
    /// Closed (start, len).
    Closed(usize, usize),
    /// Position capture `()` (1-based position).
    Pos(usize),
}

struct M<'a> {
    s: &'a [u8],
    p: &'a [u8],
    caps: Vec<Cap>,
    depth: usize,
}

/// One captured value.
#[derive(Clone, Debug, PartialEq)]
pub enum Capture {
    Str(Vec<u8>),
    Pos(f64),
}

fn class_end(p: &[u8], mut i: usize) -> LResult<usize> {
    let c = p[i];
    i += 1;
    if c == b'%' {
        if i >= p.len() {
            return Err(LuaError::new("malformed pattern (ends with '%')"));
        }
        return Ok(i + 1);
    }
    if c == b'[' {
        if i < p.len() && p[i] == b'^' {
            i += 1;
        }
        loop {
            if i >= p.len() {
                return Err(LuaError::new("malformed pattern (missing ']')"));
            }
            let cc = p[i];
            i += 1;
            if cc == b'%' {
                i += 1;
            }
            if i < p.len() && p[i] == b']' {
                return Ok(i + 1);
            }
            if i >= p.len() {
                return Err(LuaError::new("malformed pattern (missing ']')"));
            }
        }
    }
    Ok(i)
}

fn class_matches(c: u8, cl: u8) -> bool {
    let r = match cl.to_ascii_lowercase() {
        b'a' => c.is_ascii_alphabetic(),
        b'c' => c.is_ascii_control(),
        b'd' => c.is_ascii_digit(),
        b'g' => c.is_ascii_graphic(),
        b'l' => c.is_ascii_lowercase(),
        b'p' => c.is_ascii_punctuation(),
        b's' => c == b' ' || (b'\t'..=b'\r').contains(&c),
        b'u' => c.is_ascii_uppercase(),
        b'w' => c.is_ascii_alphanumeric(),
        b'x' => c.is_ascii_hexdigit(),
        _ => return cl == c,
    };
    if cl.is_ascii_uppercase() {
        !r
    } else {
        r
    }
}

/// `p[start..end]` is a `[...]` set (end exclusive, pointing after `]`).
fn set_matches(c: u8, p: &[u8], start: usize, end: usize) -> bool {
    let mut i = start + 1;
    let mut neg = false;
    if p[i] == b'^' {
        neg = true;
        i += 1;
    }
    let last = end - 1; // index of ']'
    while i < last {
        if p[i] == b'%' && i + 1 < last {
            if class_matches(c, p[i + 1]) {
                return !neg;
            }
            i += 2;
        } else if i + 2 < last && p[i + 1] == b'-' {
            if p[i] <= c && c <= p[i + 2] {
                return !neg;
            }
            i += 3;
        } else {
            if p[i] == c {
                return !neg;
            }
            i += 1;
        }
    }
    neg
}

impl<'a> M<'a> {
    fn single(&self, si: usize, pi: usize, ep: usize) -> bool {
        if si >= self.s.len() {
            return false;
        }
        let c = self.s[si];
        match self.p[pi] {
            b'.' => true,
            b'%' => class_matches(c, self.p[pi + 1]),
            b'[' => set_matches(c, self.p, pi, ep),
            pc => pc == c,
        }
    }

    fn do_match(&mut self, mut si: usize, mut pi: usize) -> LResult<Option<usize>> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(LuaError::new("pattern too complex"));
        }
        let r = loop {
            if pi >= self.p.len() {
                break Some(si);
            }
            match self.p[pi] {
                b'(' => {
                    break if pi + 1 < self.p.len() && self.p[pi + 1] == b')' {
                        self.start_cap(si, pi + 2, true)?
                    } else {
                        self.start_cap(si, pi + 1, false)?
                    };
                }
                b')' => break self.end_cap(si, pi + 1)?,
                b'$' if pi + 1 == self.p.len() => break if si == self.s.len() { Some(si) } else { None },
                b'%' if pi + 1 < self.p.len() && self.p[pi + 1] == b'b' => {
                    match self.match_balance(si, pi + 2)? {
                        Some(n) => {
                            si = n;
                            pi += 4;
                            continue;
                        }
                        None => break None,
                    }
                }
                b'%' if pi + 1 < self.p.len() && self.p[pi + 1] == b'f' => {
                    pi += 2;
                    if pi >= self.p.len() || self.p[pi] != b'[' {
                        return Err(LuaError::new("missing '[' after '%f' in pattern"));
                    }
                    let ep = class_end(self.p, pi)?;
                    let prev = if si == 0 { 0 } else { self.s[si - 1] };
                    let cur = if si < self.s.len() { self.s[si] } else { 0 };
                    if !set_matches(prev, self.p, pi, ep) && set_matches(cur, self.p, pi, ep) {
                        pi = ep;
                        continue;
                    }
                    break None;
                }
                b'%' if pi + 1 < self.p.len() && self.p[pi + 1].is_ascii_digit() => {
                    let l = (self.p[pi + 1] - b'0') as usize;
                    match self.match_capture(si, l)? {
                        Some(n) => {
                            si = n;
                            pi += 2;
                            continue;
                        }
                        None => break None,
                    }
                }
                _ => {
                    let ep = class_end(self.p, pi)?;
                    let q = self.p.get(ep).copied();
                    if !self.single(si, pi, ep) {
                        if matches!(q, Some(b'*' | b'?' | b'-')) {
                            pi = ep + 1;
                            continue;
                        }
                        break None;
                    }
                    match q {
                        Some(b'?') => {
                            if let Some(r) = self.do_match(si + 1, ep + 1)? {
                                break Some(r);
                            }
                            pi = ep + 1;
                            continue;
                        }
                        Some(b'+') => break self.max_expand(si + 1, pi, ep)?,
                        Some(b'*') => break self.max_expand(si, pi, ep)?,
                        Some(b'-') => break self.min_expand(si, pi, ep)?,
                        _ => {
                            si += 1;
                            pi = ep;
                            continue;
                        }
                    }
                }
            }
        };
        self.depth -= 1;
        Ok(r)
    }

    fn max_expand(&mut self, si: usize, pi: usize, ep: usize) -> LResult<Option<usize>> {
        let mut i = 0;
        while self.single(si + i, pi, ep) {
            i += 1;
        }
        loop {
            if let Some(r) = self.do_match(si + i, ep + 1)? {
                return Ok(Some(r));
            }
            if i == 0 {
                return Ok(None);
            }
            i -= 1;
        }
    }

    fn min_expand(&mut self, mut si: usize, pi: usize, ep: usize) -> LResult<Option<usize>> {
        loop {
            if let Some(r) = self.do_match(si, ep + 1)? {
                return Ok(Some(r));
            }
            if self.single(si, pi, ep) {
                si += 1;
            } else {
                return Ok(None);
            }
        }
    }

    fn start_cap(&mut self, si: usize, pi: usize, pos: bool) -> LResult<Option<usize>> {
        if self.caps.len() >= MAX_CAPTURES {
            return Err(LuaError::new("too many captures"));
        }
        self.caps.push(if pos { Cap::Pos(si + 1) } else { Cap::Open(si) });
        let r = self.do_match(si, pi)?;
        if r.is_none() {
            self.caps.pop();
        }
        Ok(r)
    }

    fn end_cap(&mut self, si: usize, pi: usize) -> LResult<Option<usize>> {
        let Some(l) = self.caps.iter().rposition(|c| matches!(c, Cap::Open(_))) else {
            return Err(LuaError::new("invalid pattern capture"));
        };
        let Cap::Open(start) = self.caps[l] else { unreachable!() };
        self.caps[l] = Cap::Closed(start, si - start);
        let r = self.do_match(si, pi)?;
        if r.is_none() {
            self.caps[l] = Cap::Open(start);
        }
        Ok(r)
    }

    fn match_balance(&mut self, si: usize, pi: usize) -> LResult<Option<usize>> {
        if pi + 1 >= self.p.len() {
            return Err(LuaError::new("missing arguments to '%b'"));
        }
        if si >= self.s.len() || self.s[si] != self.p[pi] {
            return Ok(None);
        }
        let (b, e) = (self.p[pi], self.p[pi + 1]);
        let mut cont = 1;
        let mut i = si + 1;
        while i < self.s.len() {
            let c = self.s[i];
            if c == e {
                cont -= 1;
                if cont == 0 {
                    return Ok(Some(i + 1));
                }
            } else if c == b {
                cont += 1;
            }
            i += 1;
        }
        Ok(None)
    }

    fn match_capture(&mut self, si: usize, l: usize) -> LResult<Option<usize>> {
        let Some(Cap::Closed(start, len)) = l.checked_sub(1).and_then(|i| self.caps.get(i)).copied() else {
            return Err(LuaError::new(format!("invalid capture index %{l}")));
        };
        if self.s.len() - si >= len && self.s[start..start + len] == self.s[si..si + len] {
            Ok(Some(si + len))
        } else {
            Ok(None)
        }
    }
}

fn has_specials(p: &[u8]) -> bool {
    p.iter().any(|c| b"^$*+?.([%-".contains(c))
}

/// Translates Lua's `init` argument (1-based, negative from the end) to an offset.
fn start_offset(len: usize, init: Option<f64>) -> Option<usize> {
    // Luau converts `init` with a C cast to int, truncating toward zero.
    // NaN starts at the beginning, like any value below -len.
    let i = init.unwrap_or(1.0);
    let i = if i.is_nan() { 1.0 } else { i.trunc().clamp(-9e15, 9e15) };
    let l = len as f64;
    let i = if i > 0.0 {
        i
    } else if i == 0.0 {
        1.0
    } else if -i > l {
        1.0
    } else {
        l + i + 1.0
    };
    if i > l + 1.0 {
        return None;
    }
    Some(i as usize - 1)
}

/// Captures of a Lua pattern in order (`true`: a position capture `()`): each
/// unescaped `(` outside a set. Mirrors the compiler's `pattern_captures`
/// (`%bxy` takes two operand bytes; a leading `]` in a set is literal).
pub fn capture_kinds(p: &[u8]) -> Vec<bool> {
    let mut n = Vec::new();
    let mut i = 0;
    while i < p.len() {
        match p[i] {
            b'%' if p.get(i + 1) == Some(&b'b') => i += 3,
            b'%' => i += 1,
            b'[' => {
                i += 1;
                if i < p.len() && p[i] == b'^' {
                    i += 1;
                }
                if i < p.len() {
                    i += 1;
                }
                while i < p.len() && p[i] != b']' {
                    if p[i] == b'%' {
                        i += 1;
                    }
                    i += 1;
                }
            }
            b'(' => n.push(p.get(i + 1) == Some(&b')')),
            _ => {}
        }
        i += 1;
    }
    n
}

/// Core matcher: (start offset, end offset, captures) of the first match at or
/// after `init`.
pub fn find_at(s: &[u8], p: &[u8], init: Option<f64>, plain: bool) -> LResult<Option<(usize, usize, Vec<Capture>)>> {
    let Some(start) = start_offset(s.len(), init) else { return Ok(None) };
    if plain || !has_specials(p) {
        if p.is_empty() {
            return Ok(Some((start, start, vec![])));
        }
        return Ok(s[start..].windows(p.len()).position(|w| w == p).map(|i| (start + i, start + i + p.len(), vec![])));
    }
    let (anchor, p) = match p.first() {
        Some(b'^') => (true, &p[1..]),
        _ => (false, p),
    };
    let mut si = start;
    loop {
        if let Some((e, caps)) = match_at(s, p, si)? {
            return Ok(Some((si, e, caps)));
        }
        si += 1;
        if anchor || si > s.len() {
            return Ok(None);
        }
    }
}

/// Matches `p` (an anchor `^` is an ordinary character here) starting exactly at
/// byte offset `si`: the end of the match and its captures.
pub fn match_at(s: &[u8], p: &[u8], si: usize) -> LResult<Option<(usize, Vec<Capture>)>> {
    let mut m = M { s, p, caps: Vec::new(), depth: 0 };
    let Some(e) = m.do_match(si, 0)? else { return Ok(None) };
    let caps = m
        .caps
        .iter()
        .map(|c| match *c {
            Cap::Closed(st, len) => Ok(Capture::Str(s[st..st + len].to_vec())),
            Cap::Pos(p) => Ok(Capture::Pos(p as f64)),
            Cap::Open(_) => Err(LuaError::new("unfinished capture")),
        })
        .collect::<LResult<Vec<_>>>()?;
    Ok(Some((e, caps)))
}

#[cfg(test)]
mod capture_tests {
    use super::*;

    /// Same cases as the compiler's `pattern_captures`; the two scanners must agree.
    #[test]
    fn capture_kinds_cases() {
        let k = |p: &str| capture_kinds(p.as_bytes());
        assert_eq!(k("(%w+)=(%w+)"), vec![false, false]);
        assert_eq!(k("()b()"), vec![true, true]);
        assert_eq!(k("%((%w)%)"), vec![false]);
        assert_eq!(k("[(]"), Vec::<bool>::new());
        assert_eq!(k("[]()]"), Vec::<bool>::new());
        assert_eq!(k("[^(]+(x)"), vec![false]);
        assert_eq!(k("%b()"), Vec::<bool>::new());
        assert_eq!(k("%b()(.)"), vec![false]);
        assert_eq!(k("[%]](a)"), vec![false]);
        assert_eq!(k("%"), Vec::<bool>::new());
        assert_eq!(k("("), vec![false]);
        assert_eq!(k("[("), Vec::<bool>::new());
    }
}
