use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::time::Instant;

const NONE: u32 = u32::MAX;

/// FxHash-style hasher for integer keys (memo tables); not exposed to adversarial collision concerns beyond
/// speed (equality is always checked by the table).
#[derive(Default, Clone, Copy)]
struct Fx(u64);
impl std::hash::Hasher for Fx {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(5) ^ b as u64).wrapping_mul(0x517cc1b727220a95);
        }
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.0 = (self.0.rotate_left(5) ^ i as u64).wrapping_mul(0x517cc1b727220a95);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(0x517cc1b727220a95);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64);
    }
}
type FxB = std::hash::BuildHasherDefault<Fx>;
type FxSet<K> = HashSet<K, FxB>;
type FxMap<K, V> = HashMap<K, V, FxB>;

#[derive(Debug)]
enum Fail {
    Decline(String),
    Reject(String),
}
type R<T> = Result<T, Fail>;

macro_rules! decline { ($($t:tt)*) => { return Err(Fail::Decline(format!($($t)*))) } }
macro_rules! reject { ($($t:tt)*) => { return Err(Fail::Reject(format!($($t)*))) } }

// ---------------------------------------------------------------------------------------------------
// JSON (one line at a time), the subset of Lean's Json.parse that lean4export writes
// ---------------------------------------------------------------------------------------------------

const J_OBJ: u8 = 1;
const J_ARR: u8 = 2;
const J_STR: u8 = 3;
const J_NUM: u8 = 4;
const J_TRUE: u8 = 5;
const J_FALSE: u8 = 6;
const J_NULL: u8 = 7;

#[derive(Clone, Copy)]
struct JNode {
    kind: u8,
    esc: bool, // string contains escapes
    ks: u32,   // key span (object members), raw bytes (escaped keys are declined)
    ke: u32,
    s: u32, // value span: string content (between quotes) / digits
    e: u32,
    first: u32, // first child (object member / array element)
    last: u32,
    next: u32, // next sibling
}

struct JP<'a> {
    b: &'a [u8],
    p: usize,
    nodes: Vec<JNode>,
}

type JR<T> = Result<T, &'static str>;

impl<'a> JP<'a> {
    fn new() -> JP<'static> {
        JP { b: &[], p: 0, nodes: Vec::with_capacity(64) }
    }
    #[inline]
    fn ws(&mut self) {
        while self.p < self.b.len() {
            match self.b[self.p] {
                b' ' | b'\t' | b'\n' | b'\r' => self.p += 1,
                _ => break,
            }
        }
    }
    #[inline]
    fn peek(&self) -> Option<u8> {
        self.b.get(self.p).copied()
    }
    fn push(&mut self, kind: u8) -> u32 {
        let id = self.nodes.len() as u32;
        self.nodes.push(JNode { kind, esc: false, ks: 0, ke: 0, s: 0, e: 0, first: NONE, last: NONE, next: NONE });
        id
    }
    fn link(&mut self, parent: u32, child: u32) {
        let l = self.nodes[parent as usize].last;
        if l == NONE {
            self.nodes[parent as usize].first = child;
        } else {
            self.nodes[l as usize].next = child;
        }
        self.nodes[parent as usize].last = child;
    }
    fn hex(c: u8) -> JR<u32> {
        match c {
            b'0'..=b'9' => Ok((c - b'0') as u32),
            b'a'..=b'f' => Ok((c - b'a' + 10) as u32),
            b'A'..=b'F' => Ok((c - b'A' + 10) as u32),
            _ => Err("bad hex escape"),
        }
    }
    fn u4(&self, at: usize) -> JR<u32> {
        if at + 4 > self.b.len() {
            return Err("short \\u escape");
        }
        let mut v = 0;
        for i in 0..4 {
            v = (v << 4) | Self::hex(self.b[at + i])?;
        }
        Ok(v)
    }
    /// String body after the opening quote; leaves p at the closing quote. Returns (has escapes).
    fn string_body(&mut self) -> JR<bool> {
        let s = self.p;
        let mut esc = false;
        let mut hi = false;
        loop {
            let c = *self.b.get(self.p).ok_or("unterminated string")?;
            if c == b'"' {
                break;
            }
            if c < 0x20 {
                return Err("control character in string");
            }
            if c >= 0x80 {
                hi = true;
                self.p += 1;
                continue;
            }
            if c == b'\\' {
                esc = true;
                let d = *self.b.get(self.p + 1).ok_or("unterminated escape")?;
                match d {
                    b'\\' | b'"' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => self.p += 2,
                    b'u' => {
                        let v = self.u4(self.p + 2)?;
                        if (0xD800..0xDC00).contains(&v) {
                            // must be followed by a low surrogate escape (Lean: else U+FFFD -> declined)
                            if self.b.get(self.p + 6) != Some(&b'\\') || self.b.get(self.p + 7) != Some(&b'u') {
                                return Err("lone surrogate escape");
                            }
                            let w = self.u4(self.p + 8)?;
                            if !(0xDC00..0xE000).contains(&w) {
                                return Err("lone surrogate escape");
                            }
                            // Lean requires the 'd'/'D' literally (it is the first hex digit of DCxx..DFxx): ok
                            self.p += 12;
                        } else if (0xDC00..0xE000).contains(&v) {
                            return Err("lone surrogate escape");
                        } else {
                            self.p += 6;
                        }
                    }
                    _ => return Err("illegal escape"),
                }
                continue;
            }
            self.p += 1;
        }
        if hi && std::str::from_utf8(&self.b[s..self.p]).is_err() {
            return Err("invalid UTF-8 in string");
        }
        Ok(esc)
    }
    fn value(&mut self, depth: u32) -> JR<u32> {
        if depth > 48 {
            return Err("JSON nesting too deep");
        }
        let c = self.peek().ok_or("unexpected end of line")?;
        match c {
            b'{' => {
                let id = self.push(J_OBJ);
                self.p += 1;
                self.ws();
                if self.peek() == Some(b'}') {
                    self.p += 1;
                    self.ws();
                    return Ok(id);
                }
                loop {
                    if self.peek() != Some(b'"') {
                        return Err("expected key");
                    }
                    self.p += 1;
                    let ks = self.p;
                    loop {
                        let ch = *self.b.get(self.p).ok_or("unterminated key")?;
                        if ch == b'"' {
                            break;
                        }
                        if ch == b'\\' || ch < 0x20 || ch >= 0x80 {
                            return Err("unsupported key");
                        }
                        self.p += 1;
                    }
                    let ke = self.p;
                    self.p += 1;
                    self.ws();
                    if self.peek() != Some(b':') {
                        return Err("expected ':'");
                    }
                    self.p += 1;
                    self.ws();
                    // duplicate keys: Lean rejects; we decline
                    let mut q = self.nodes[id as usize].first;
                    while q != NONE {
                        let n = self.nodes[q as usize];
                        if self.b[n.ks as usize..n.ke as usize] == self.b[ks..ke] {
                            return Err("duplicate key");
                        }
                        q = n.next;
                    }
                    let v = self.value(depth + 1)?;
                    self.nodes[v as usize].ks = ks as u32;
                    self.nodes[v as usize].ke = ke as u32;
                    self.link(id, v);
                    match self.peek() {
                        Some(b',') => {
                            self.p += 1;
                            self.ws();
                        }
                        Some(b'}') => {
                            self.p += 1;
                            self.ws();
                            return Ok(id);
                        }
                        _ => return Err("expected ',' or '}'"),
                    }
                }
            }
            b'[' => {
                let id = self.push(J_ARR);
                self.p += 1;
                self.ws();
                if self.peek() == Some(b']') {
                    self.p += 1;
                    self.ws();
                    return Ok(id);
                }
                loop {
                    let v = self.value(depth + 1)?;
                    self.link(id, v);
                    match self.peek() {
                        Some(b',') => {
                            self.p += 1;
                            self.ws();
                        }
                        Some(b']') => {
                            self.p += 1;
                            self.ws();
                            return Ok(id);
                        }
                        _ => return Err("expected ',' or ']'"),
                    }
                }
            }
            b'"' => {
                let id = self.push(J_STR);
                self.p += 1;
                let s = self.p;
                let esc = self.string_body()?;
                let n = &mut self.nodes[id as usize];
                n.s = s as u32;
                n.e = self.p as u32;
                n.esc = esc;
                self.p += 1;
                self.ws();
                Ok(id)
            }
            b'0'..=b'9' => {
                let id = self.push(J_NUM);
                let s = self.p;
                while let Some(b'0'..=b'9') = self.peek() {
                    self.p += 1;
                }
                if self.b[s] == b'0' && self.p - s > 1 {
                    return Err("leading zero");
                }
                if let Some(b'.' | b'e' | b'E') = self.peek() {
                    return Err("non-integer number");
                }
                let n = &mut self.nodes[id as usize];
                n.s = s as u32;
                n.e = self.p as u32;
                self.ws();
                Ok(id)
            }
            b't' | b'f' | b'n' => {
                let (lit, kind): (&[u8], u8) = match c {
                    b't' => (b"true", J_TRUE),
                    b'f' => (b"false", J_FALSE),
                    _ => (b"null", J_NULL),
                };
                if self.b.len() < self.p + lit.len() || &self.b[self.p..self.p + lit.len()] != lit {
                    return Err("bad literal");
                }
                self.p += lit.len();
                let id = self.push(kind);
                self.ws();
                Ok(id)
            }
            _ => Err("unexpected character"),
        }
    }
    /// Parse a whole line (without its '\n'): ws value ws EOF.
    fn line(&mut self, b: &'a [u8]) -> JR<u32> {
        self.b = b;
        self.p = 0;
        self.nodes.clear();
        if b.len() >= u32::MAX as usize {
            return Err("line too long");
        }
        self.ws();
        let v = self.value(0)?;
        self.ws();
        if self.p != b.len() {
            return Err("trailing characters");
        }
        Ok(v)
    }
    #[inline]
    fn key(&self, n: u32) -> &[u8] {
        let n = self.nodes[n as usize];
        &self.b[n.ks as usize..n.ke as usize]
    }
}

// ---------------------------------------------------------------------------------------------------
// Export records
// ---------------------------------------------------------------------------------------------------

const K_NAME: usize = 0;
const K_LEVEL: usize = 1;
const K_EXPR: usize = 2;

const N_ANON: u8 = 1;
const N_STR: u8 = 2; // raw string span, no escapes
const N_STRESC: u8 = 3; // string span with escapes
const N_NUM: u8 = 4;

#[derive(Clone, Copy)]
struct NameRec {
    kind: u8,
    pre: u32,
    len: u32, // string length (bytes of the raw span)
    off: u64, // string span offset in the file / numeric value
}

const L_ZERO: u8 = 1;
const L_SUCC: u8 = 2;
const L_MAX: u8 = 3;
const L_IMAX: u8 = 4;
const L_PARAM: u8 = 5;

#[derive(Clone, Copy)]
struct LevelRec {
    kind: u8,
    a: u32,
    b: u32,
}

const E_BVAR: u8 = 1;
const E_SORT: u8 = 2;
const E_CONST: u8 = 3;
const E_APP: u8 = 4;
const E_LAM: u8 = 5;
const E_PI: u8 = 6;
const E_LET: u8 = 7;
const E_PROJ: u8 = 8;
const E_NAT: u8 = 9;
const E_STR: u8 = 10;
const E_MDATA: u8 = 11;

/// bvar: a|b<<32 = index; sort: a = level; const: a = name, b = level-pool start, c = count;
/// app: a = fn, b = arg; lam/pi: a = type, b = body, c = binder name; let: a = type, b = value, c = body,
/// flag = nondep; proj: a = struct name, b = struct expr, c = field index; nat/str literal: a|b<<32 =
/// offset of the string content in the file, c = its length, flag = has escapes; mdata: a = expr.
#[derive(Clone, Copy)]
struct ExprRec {
    kind: u8,
    flag: u8,
    a: u32,
    b: u32,
    c: u32,
}

const D_AXIOM: u8 = 1;
const D_DEFN: u8 = 2;
const D_THM: u8 = 3;
const D_OPAQUE: u8 = 4;
const D_QUOT: u8 = 5;
const D_INDUCT: u8 = 6;
const D_CTOR: u8 = 7;
const D_REC: u8 = 8;

#[derive(Clone, Default)]
struct Decl {
    kind: u8,
    name: u32,
    lparams: Vec<u32>,
    ty: u32,
    val: u32,
    hints_kind: u8, // 1 opaque 2 abbrev 3 regular
    hints_val: u32,
    safety: u8, // 1 unsafe 2 safe 3 partial
    all: Vec<u32>,
    is_unsafe: bool,
    quot_kind: u8,
    nums: [u64; 4], // induct: numParams numIndices numNested; ctor: cidx numParams numFields; rec: numParams numIndices numMotives numMinors
    ctors: Vec<u32>,
    induct: u32,
    is_rec: bool,
    is_reflexive: bool,
    k: bool,
    rules: Vec<(u32, u64, u32)>, // ctor name, nfields, rhs
}

impl Decl {
    fn kind_name(&self) -> &'static str {
        match self.kind {
            D_AXIOM => "axiom",
            D_DEFN => "definition",
            D_THM => "theorem",
            D_OPAQUE => "opaque",
            D_QUOT => "quot",
            D_INDUCT => "inductive",
            D_CTOR => "constructor",
            D_REC => "recursor",
            _ => "?",
        }
    }
}

/// Output of one parsing thread (a range of whole lines).
struct Chunk {
    names: Vec<NameRec>,
    levels: Vec<LevelRec>,
    exprs: Vec<ExprRec>,
    pool: Vec<u32>,
    decls: Vec<Decl>,
    first: [u64; 3], // index of the first record of each kind in this chunk
    slack: [i64; 3], // max over references of (ref - records of that kind seen before in this chunk)
    lets: Vec<(u32, u32)>, // (global expr index, binder name) of letE records (expdiff: binder names of let/have)
}

struct Cur<'b> {
    b: &'b [u8],
    p: usize,
}

impl<'b> Cur<'b> {
    #[inline]
    fn lit(&mut self, s: &[u8]) -> bool {
        if self.b.len() - self.p >= s.len() && &self.b[self.p..self.p + s.len()] == s {
            self.p += s.len();
            true
        } else {
            false
        }
    }
    /// plain decimal: non-empty, no leading zero, fits u64
    #[inline]
    fn num(&mut self) -> Option<u64> {
        let s = self.p;
        let mut v: u64 = 0;
        while self.p < self.b.len() {
            let d = self.b[self.p].wrapping_sub(b'0');
            if d > 9 {
                break;
            }
            v = v.checked_mul(10)?.checked_add(d as u64)?;
            self.p += 1;
        }
        if self.p == s || (self.b[s] == b'0' && self.p - s > 1) {
            None
        } else {
            Some(v)
        }
    }
    #[inline]
    fn end(&self) -> bool {
        self.p == self.b.len()
    }
}

struct LineParser<'a> {
    file: &'a [u8],
    base: usize, // offset of the current line in the file
    jp: JP<'a>,
    ch: Chunk,
}

type PR<T> = Result<T, String>;

impl<'a> LineParser<'a> {
    fn count(&self, k: usize) -> usize {
        match k {
            K_NAME => self.ch.names.len(),
            K_LEVEL => self.ch.levels.len(),
            _ => self.ch.exprs.len(),
        }
    }
    fn node(&self, n: u32) -> JNode {
        self.jp.nodes[n as usize]
    }
    fn num(&self, n: u32) -> PR<u64> {
        let nd = self.node(n);
        if nd.kind != J_NUM {
            return Err("expected a number".into());
        }
        let mut v: u64 = 0;
        for &c in &self.jp.b[nd.s as usize..nd.e as usize] {
            v = v.checked_mul(10).and_then(|v| v.checked_add((c - b'0') as u64)).ok_or("number too large")?;
        }
        Ok(v)
    }
    fn num32(&self, n: u32) -> PR<u32> {
        let v = self.num(n)?;
        if v >= NONE as u64 {
            return Err("index too large".into());
        }
        Ok(v as u32)
    }
    fn boolean(&self, n: u32) -> PR<bool> {
        match self.node(n).kind {
            J_TRUE => Ok(true),
            J_FALSE => Ok(false),
            _ => Err("expected a boolean".into()),
        }
    }
    fn string(&self, n: u32) -> PR<&[u8]> {
        let nd = self.node(n);
        if nd.kind != J_STR {
            return Err("expected a string".into());
        }
        Ok(&self.jp.b[nd.s as usize..nd.e as usize])
    }
    /// A reference to an index of kind k: must be bound on an earlier line.
    fn r(&mut self, n: u32, k: usize) -> PR<u32> {
        let v = self.num(n)?;
        self.rv(v, k)
    }
    /// Fields of an object; every key must be in `keys` (Lean ignores unknown nested keys; we decline).
    fn fields<const N: usize>(&self, obj: u32, keys: [&[u8]; N], optional: u32) -> PR<[u32; N]> {
        let nd = self.node(obj);
        if nd.kind != J_OBJ {
            return Err("expected an object".into());
        }
        let mut out = [NONE; N];
        let mut q = nd.first;
        while q != NONE {
            let k = self.jp.key(q);
            match keys.iter().position(|x| *x == k) {
                Some(i) => out[i] = q,
                None => return Err(format!("unsupported key {:?}", String::from_utf8_lossy(k))),
            }
            q = self.node(q).next;
        }
        for i in 0..N {
            if out[i] == NONE && optional & (1 << i) == 0 {
                return Err(format!("missing key {:?}", String::from_utf8_lossy(keys[i])));
            }
        }
        Ok(out)
    }
    fn arr(&self, n: u32) -> PR<Vec<u32>> {
        let nd = self.node(n);
        if nd.kind != J_ARR {
            return Err("expected an array".into());
        }
        let mut v = Vec::new();
        let mut q = nd.first;
        while q != NONE {
            v.push(q);
            q = self.node(q).next;
        }
        Ok(v)
    }
    fn name_list(&mut self, n: u32) -> PR<Vec<u32>> {
        let items = self.arr(n)?;
        let mut v = Vec::with_capacity(items.len());
        for q in items {
            v.push(self.r(q, K_NAME)?);
        }
        Ok(v)
    }
    fn index_rec(&mut self, k: usize, idx_node: u32) -> PR<()> {
        let idx = self.num(idx_node)?;
        self.index_val(k, idx)
    }
    fn file_off(&self, n: u32) -> u64 {
        (self.base + self.node(n).s as usize) as u64
    }

    /// Fast path for the canonical byte forms lean4export writes for the most frequent lines (sorted
    /// keys, no whitespace). A line that does not match exactly is left to the general parser; nothing
    /// is recorded before the whole line has matched.
    fn fast_line(&mut self, line: &[u8], base: usize) -> PR<bool> {
        let mut c = Cur { b: line, p: 0 };
        macro_rules! m {
            ($e:expr) => {
                match $e {
                    Some(v) => v,
                    None => return Ok(false),
                }
            };
        }
        macro_rules! lit {
            ($s:expr) => {
                if !c.lit($s) {
                    return Ok(false);
                }
            };
        }
        if c.lit(b"{\"app\":{\"arg\":") {
            let a = m!(c.num());
            lit!(b",\"fn\":");
            let f = m!(c.num());
            lit!(b"},\"ie\":");
            let i = m!(c.num());
            lit!(b"}");
            if !c.end() {
                return Ok(false);
            }
            self.index_val(K_EXPR, i)?;
            let f = self.rv(f, K_EXPR)?;
            let a = self.rv(a, K_EXPR)?;
            self.ch.exprs.push(ExprRec { kind: E_APP, flag: 0, a: f, b: a, c: 0 });
            return Ok(true);
        }
        let (kind, idx_first) = if c.lit(b"{\"forallE\":{\"binderInfo\":\"") {
            (E_PI, None)
        } else if c.lit(b"{\"ie\":") {
            let i = m!(c.num());
            if c.lit(b",\"lam\":{\"binderInfo\":\"") {
                (E_LAM, Some(i))
            } else if c.lit(b",\"sort\":") {
                let l = m!(c.num());
                lit!(b"}");
                if !c.end() {
                    return Ok(false);
                }
                self.index_val(K_EXPR, i)?;
                let l = self.rv(l, K_LEVEL)?;
                self.ch.exprs.push(ExprRec { kind: E_SORT, flag: 0, a: l, b: 0, c: 0 });
                return Ok(true);
            } else {
                return Ok(false);
            }
        } else if c.lit(b"{\"in\":") {
            let i = m!(c.num());
            if c.lit(b",\"str\":{\"pre\":") {
                let pre = m!(c.num());
                lit!(b",\"str\":\"");
                let s = c.p;
                let mut hi = false;
                loop {
                    let ch = m!(line.get(c.p).copied());
                    if ch == b'"' {
                        break;
                    }
                    if ch == b'\\' || ch < 0x20 {
                        return Ok(false);
                    }
                    hi |= ch >= 0x80;
                    c.p += 1;
                }
                let e = c.p;
                c.p += 1;
                lit!(b"}}");
                if !c.end() {
                    return Ok(false);
                }
                if hi && std::str::from_utf8(&line[s..e]).is_err() {
                    return Ok(false);
                }
                self.index_val(K_NAME, i)?;
                let pre = self.rv(pre, K_NAME)?;
                self.ch.names.push(NameRec { kind: N_STR, pre, len: (e - s) as u32, off: (base + s) as u64 });
                return Ok(true);
            } else if c.lit(b",\"num\":{\"i\":") {
                let v = m!(c.num());
                lit!(b",\"pre\":");
                let pre = m!(c.num());
                lit!(b"}}");
                if !c.end() {
                    return Ok(false);
                }
                self.index_val(K_NAME, i)?;
                let pre = self.rv(pre, K_NAME)?;
                self.ch.names.push(NameRec { kind: N_NUM, pre, len: 0, off: v });
                return Ok(true);
            }
            return Ok(false);
        } else if c.lit(b"{\"const\":{\"name\":") {
            let n = m!(c.num());
            lit!(b",\"us\":[");
            let mut us = [0u64; 8];
            let mut nu = 0;
            if !c.lit(b"]") {
                loop {
                    if nu == us.len() {
                        return Ok(false);
                    }
                    us[nu] = m!(c.num());
                    nu += 1;
                    if c.lit(b"]") {
                        break;
                    }
                    lit!(b",");
                }
            }
            lit!(b"},\"ie\":");
            let i = m!(c.num());
            lit!(b"}");
            if !c.end() {
                return Ok(false);
            }
            self.index_val(K_EXPR, i)?;
            let n = self.rv(n, K_NAME)?;
            let start = self.ch.pool.len();
            for &u in &us[..nu] {
                let l = self.rv(u, K_LEVEL)?;
                self.ch.pool.push(l);
            }
            if self.ch.pool.len() >= NONE as usize {
                return Err("too many universe arguments".into());
            }
            self.ch.exprs.push(ExprRec { kind: E_CONST, flag: 0, a: n, b: start as u32, c: nu as u32 });
            return Ok(true);
        } else if c.lit(b"{\"bvar\":") {
            let v = m!(c.num());
            lit!(b",\"ie\":");
            let i = m!(c.num());
            lit!(b"}");
            if !c.end() {
                return Ok(false);
            }
            self.index_val(K_EXPR, i)?;
            self.ch.exprs.push(ExprRec { kind: E_BVAR, flag: 0, a: v as u32, b: (v >> 32) as u32, c: 0 });
            return Ok(true);
        } else {
            return Ok(false);
        };
        // binder: forallE / lam
        let bif: u8 = if c.lit(b"default\"") {
            0
        } else if c.lit(b"implicit\"") {
            1
        } else if c.lit(b"strictImplicit\"") {
            2
        } else if c.lit(b"instImplicit\"") {
            3
        } else {
            return Ok(false);
        };
        lit!(b",\"body\":");
        let body = m!(c.num());
        lit!(b",\"name\":");
        let name = m!(c.num());
        lit!(b",\"type\":");
        let ty = m!(c.num());
        let i = match idx_first {
            Some(i) => {
                lit!(b"}}");
                i
            }
            None => {
                lit!(b"},\"ie\":");
                let i = m!(c.num());
                lit!(b"}");
                i
            }
        };
        if !c.end() {
            return Ok(false);
        }
        self.index_val(K_EXPR, i)?;
        let name = self.rv(name, K_NAME)?;
        let ty = self.rv(ty, K_EXPR)?;
        let body = self.rv(body, K_EXPR)?;
        self.ch.exprs.push(ExprRec { kind, flag: bif, a: ty, b: body, c: name });
        Ok(true)
    }
    fn rv(&mut self, v: u64, k: usize) -> PR<u32> {
        if v >= NONE as u64 {
            return Err("index too large".into());
        }
        let s = v as i64 - self.count(k) as i64;
        if s > self.ch.slack[k] {
            self.ch.slack[k] = s;
        }
        Ok(v as u32)
    }
    fn index_val(&mut self, k: usize, idx: u64) -> PR<()> {
        let c = self.count(k) as u64;
        if c == 0 {
            self.ch.first[k] = idx;
        } else if idx != self.ch.first[k] + c {
            return Err("indices not dense and increasing (unsupported)".into());
        }
        if idx >= (NONE - 1) as u64 {
            return Err("index too large".into());
        }
        Ok(())
    }

    fn parse_line(&mut self, line: &'a [u8], base: usize) -> PR<()> {
        self.base = base;
        if self.fast_line(line, base)? {
            return Ok(());
        }
        let root = self.jp.line(line).map_err(|e| e.to_string())?;
        let rn = self.node(root);
        if rn.kind != J_OBJ {
            return Err("line is not an object".into());
        }
        let m1 = rn.first;
        if m1 == NONE {
            return Err("empty object".into());
        }
        let m2 = self.node(m1).next;
        if m2 == NONE {
            let v = m1;
            return match self.jp.key(m1) {
                b"axiom" => self.decl_axiom(v),
                b"def" => self.decl_def(v),
                b"thm" => self.decl_thm(v),
                b"opaque" => self.decl_opaque(v),
                b"quot" => self.decl_quot(v),
                b"inductive" => self.decl_inductive(v),
                k => Err(format!("unknown object {:?}", String::from_utf8_lossy(k))),
            };
        }
        if self.node(m2).next != NONE {
            return Err("unknown object with more than two keys".into());
        }
        let (idx, data) = {
            let k1 = self.jp.key(m1);
            if k1 == b"in" || k1 == b"il" || k1 == b"ie" {
                (m1, m2)
            } else {
                (m2, m1)
            }
        };
        let ik = self.jp.key(idx).to_vec();
        let dk = self.jp.key(data).to_vec();
        match (&ik[..], &dk[..]) {
            (b"in", b"str") | (b"in", b"num") => {
                self.index_rec(K_NAME, idx)?;
                let rec = if dk == b"str" {
                    let [pre, s] = self.fields(data, [b"pre", b"str"], 0)?;
                    let pre = self.r(pre, K_NAME)?;
                    let sn = self.node(s);
                    if sn.kind != J_STR {
                        return Err("Name.str invalid".into());
                    }
                    NameRec { kind: if sn.esc { N_STRESC } else { N_STR }, pre, len: sn.e - sn.s, off: self.file_off(s) }
                } else {
                    let [pre, i] = self.fields(data, [b"pre", b"i"], 0)?;
                    let pre = self.r(pre, K_NAME)?;
                    let i = self.num(i)?;
                    NameRec { kind: N_NUM, pre, len: 0, off: i }
                };
                self.ch.names.push(rec);
            }
            (b"il", _) => {
                self.index_rec(K_LEVEL, idx)?;
                let rec = match &dk[..] {
                    b"succ" => LevelRec { kind: L_SUCC, a: self.r(data, K_LEVEL)?, b: 0 },
                    b"max" | b"imax" => {
                        let a = self.arr(data)?;
                        if a.len() != 2 {
                            return Err("Level.max invalid".into());
                        }
                        let x = self.r(a[0], K_LEVEL)?;
                        let y = self.r(a[1], K_LEVEL)?;
                        LevelRec { kind: if dk == b"max" { L_MAX } else { L_IMAX }, a: x, b: y }
                    }
                    b"param" => LevelRec { kind: L_PARAM, a: self.r(data, K_NAME)?, b: 0 },
                    _ => return Err("unknown level object".into()),
                };
                self.ch.levels.push(rec);
            }
            (b"ie", _) => {
                self.index_rec(K_EXPR, idx)?;
                let rec = match &dk[..] {
                    b"bvar" => {
                        let v = self.num(data)?;
                        ExprRec { kind: E_BVAR, flag: 0, a: v as u32, b: (v >> 32) as u32, c: 0 }
                    }
                    b"sort" => ExprRec { kind: E_SORT, flag: 0, a: self.r(data, K_LEVEL)?, b: 0, c: 0 },
                    b"const" => {
                        let [name, us] = self.fields(data, [b"name", b"us"], 0)?;
                        let name = self.r(name, K_NAME)?;
                        let items = self.arr(us)?;
                        let start = self.ch.pool.len();
                        for q in items {
                            let l = self.r(q, K_LEVEL)?;
                            self.ch.pool.push(l);
                        }
                        let cnt = self.ch.pool.len() - start;
                        if self.ch.pool.len() >= NONE as usize {
                            return Err("too many universe arguments".into());
                        }
                        ExprRec { kind: E_CONST, flag: 0, a: name, b: start as u32, c: cnt as u32 }
                    }
                    b"app" => {
                        let [f, a] = self.fields(data, [b"fn", b"arg"], 0)?;
                        ExprRec { kind: E_APP, flag: 0, a: self.r(f, K_EXPR)?, b: self.r(a, K_EXPR)?, c: 0 }
                    }
                    b"lam" | b"forallE" => {
                        let [name, ty, body, bi] = self.fields(data, [b"name", b"type", b"body", b"binderInfo"], 0)?;
                        let name = self.r(name, K_NAME)?;
                        let ty = self.r(ty, K_EXPR)?;
                        let body = self.r(body, K_EXPR)?;
                        let bif = match self.string(bi)? {
                            b"default" => 0,
                            b"implicit" => 1,
                            b"strictImplicit" => 2,
                            b"instImplicit" => 3,
                            _ => return Err("invalid binder info".into()),
                        };
                        ExprRec { kind: if dk == b"lam" { E_LAM } else { E_PI }, flag: bif, a: ty, b: body, c: name }
                    }
                    b"letE" => {
                        let [name, ty, val, body, nd] =
                            self.fields(data, [b"name", b"type", b"value", b"body", b"nondep"], 0)?;
                        let lname = self.r(name, K_NAME)?;
                        let gidx = (self.ch.first[K_EXPR] + self.ch.exprs.len() as u64) as u32;
                        self.ch.lets.push((gidx, lname));
                        let ty = self.r(ty, K_EXPR)?;
                        let val = self.r(val, K_EXPR)?;
                        let body = self.r(body, K_EXPR)?;
                        let nd = self.boolean(nd)?;
                        ExprRec { kind: E_LET, flag: nd as u8, a: ty, b: val, c: body }
                    }
                    b"proj" => {
                        let [tn, i, st] = self.fields(data, [b"typeName", b"idx", b"struct"], 0)?;
                        let tn = self.r(tn, K_NAME)?;
                        let i = self.num(i)?;
                        if i >= NONE as u64 {
                            return Err("projection index too large".into());
                        }
                        let st = self.r(st, K_EXPR)?;
                        ExprRec { kind: E_PROJ, flag: 0, a: tn, b: st, c: i as u32 }
                    }
                    b"natVal" => {
                        let s = self.string(data)?;
                        if s.is_empty() || !s.iter().all(|c| c.is_ascii_digit()) || (s[0] == b'0' && s.len() > 1) {
                            return Err("unsupported natVal literal".into());
                        }
                        let off = self.file_off(data);
                        ExprRec { kind: E_NAT, flag: 0, a: off as u32, b: (off >> 32) as u32, c: s.len() as u32 }
                    }
                    b"strVal" => {
                        let sn = self.node(data);
                        if sn.kind != J_STR {
                            return Err("Expr.lit strVal invalid".into());
                        }
                        let off = self.file_off(data);
                        ExprRec { kind: E_STR, flag: sn.esc as u8, a: off as u32, b: (off >> 32) as u32, c: sn.e - sn.s }
                    }
                    b"mdata" => {
                        let [e, d] = self.fields(data, [b"expr", b"data"], 0)?;
                        let e = self.r(e, K_EXPR)?;
                        if self.node(d).kind != J_OBJ {
                            return Err("Expr.mdata invalid".into());
                        }
                        ExprRec { kind: E_MDATA, flag: 0, a: e, b: 0, c: 0 }
                    }
                    _ => return Err("unknown expression object".into()),
                };
                self.ch.exprs.push(rec);
            }
            _ => return Err("unknown export object".into()),
        }
        Ok(())
    }

    fn common(&mut self, d: &mut Decl, name: u32, lps: u32, ty: u32) -> PR<()> {
        d.name = self.r(name, K_NAME)?;
        d.lparams = self.name_list(lps)?;
        d.ty = self.r(ty, K_EXPR)?;
        Ok(())
    }
    fn decl_axiom(&mut self, v: u32) -> PR<()> {
        let [name, lps, ty, uns] = self.fields(v, [b"name", b"levelParams", b"type", b"isUnsafe"], 0)?;
        let mut d = Decl { kind: D_AXIOM, ..Default::default() };
        self.common(&mut d, name, lps, ty)?;
        d.is_unsafe = self.boolean(uns)?;
        self.ch.decls.push(d);
        Ok(())
    }
    fn decl_def(&mut self, v: u32) -> PR<()> {
        let [name, lps, ty, val, hints, safety, all] =
            self.fields(v, [b"name", b"levelParams", b"type", b"value", b"hints", b"safety", b"all"], 0)?;
        let mut d = Decl { kind: D_DEFN, ..Default::default() };
        self.common(&mut d, name, lps, ty)?;
        d.val = self.r(val, K_EXPR)?;
        let hn = self.node(hints);
        match hn.kind {
            J_STR => match self.string(hints)? {
                b"opaque" => d.hints_kind = 1,
                b"abbrev" => d.hints_kind = 2,
                _ => return Err("defnInfo invalid".into()),
            },
            J_OBJ => {
                let [reg] = self.fields(hints, [b"regular"], 0)?;
                let h = self.num(reg)?;
                if h > u32::MAX as u64 {
                    return Err("reducibility height too large (unsupported)".into());
                }
                d.hints_kind = 3;
                d.hints_val = h as u32;
            }
            _ => return Err("defnInfo invalid".into()),
        }
        d.safety = match self.string(safety)? {
            b"unsafe" => 1,
            b"safe" => 2,
            b"partial" => 3,
            _ => return Err("unknown safety".into()),
        };
        d.all = self.name_list(all)?;
        self.ch.decls.push(d);
        Ok(())
    }
    fn decl_thm(&mut self, v: u32) -> PR<()> {
        let [name, lps, ty, val, all] = self.fields(v, [b"name", b"levelParams", b"type", b"value", b"all"], 0)?;
        let mut d = Decl { kind: D_THM, ..Default::default() };
        self.common(&mut d, name, lps, ty)?;
        d.val = self.r(val, K_EXPR)?;
        d.all = self.name_list(all)?;
        self.ch.decls.push(d);
        Ok(())
    }
    fn decl_opaque(&mut self, v: u32) -> PR<()> {
        let [name, lps, ty, val, uns, all] =
            self.fields(v, [b"name", b"levelParams", b"type", b"value", b"isUnsafe", b"all"], 1 << 4)?;
        let mut d = Decl { kind: D_OPAQUE, ..Default::default() };
        self.common(&mut d, name, lps, ty)?;
        d.val = self.r(val, K_EXPR)?;
        d.is_unsafe = if uns == NONE { false } else { self.boolean(uns)? };
        d.all = self.name_list(all)?;
        self.ch.decls.push(d);
        Ok(())
    }
    fn decl_quot(&mut self, v: u32) -> PR<()> {
        let [name, lps, ty, kind] = self.fields(v, [b"name", b"levelParams", b"type", b"kind"], 0)?;
        let mut d = Decl { kind: D_QUOT, ..Default::default() };
        self.common(&mut d, name, lps, ty)?;
        d.quot_kind = match self.string(kind)? {
            b"type" => 1,
            b"ctor" => 2,
            b"lift" => 3,
            b"ind" => 4,
            _ => return Err("unknown quot kind".into()),
        };
        self.ch.decls.push(d);
        Ok(())
    }
    fn decl_inductive(&mut self, v: u32) -> PR<()> {
        let [types, ctors, recs] = self.fields(v, [b"types", b"ctors", b"recs"], 0)?;
        let types = self.arr(types)?;
        let ctors = self.arr(ctors)?;
        let recs = self.arr(recs)?;
        for t in types {
            let [name, lps, ty, np, ni, all, cs, nn, isrec, uns, refl] = self.fields(
                t,
                [
                    b"name", b"levelParams", b"type", b"numParams", b"numIndices", b"all", b"ctors", b"numNested",
                    b"isRec", b"isUnsafe", b"isReflexive",
                ],
                0,
            )?;
            let mut d = Decl { kind: D_INDUCT, ..Default::default() };
            self.common(&mut d, name, lps, ty)?;
            d.nums = [self.num(np)?, self.num(ni)?, self.num(nn)?, 0];
            d.all = self.name_list(all)?;
            d.ctors = self.name_list(cs)?;
            d.is_rec = self.boolean(isrec)?;
            d.is_unsafe = self.boolean(uns)?;
            d.is_reflexive = self.boolean(refl)?;
            self.ch.decls.push(d);
        }
        for c in ctors {
            let [name, lps, ty, ind, cidx, np, nf, uns] = self.fields(
                c,
                [b"name", b"levelParams", b"type", b"induct", b"cidx", b"numParams", b"numFields", b"isUnsafe"],
                0,
            )?;
            let mut d = Decl { kind: D_CTOR, ..Default::default() };
            self.common(&mut d, name, lps, ty)?;
            d.induct = self.r(ind, K_NAME)?;
            d.nums = [self.num(cidx)?, self.num(np)?, self.num(nf)?, 0];
            d.is_unsafe = self.boolean(uns)?;
            self.ch.decls.push(d);
        }
        for r in recs {
            let [name, lps, ty, all, np, ni, nmot, nmin, k, rules, uns] = self.fields(
                r,
                [
                    b"name", b"levelParams", b"type", b"all", b"numParams", b"numIndices", b"numMotives",
                    b"numMinors", b"k", b"rules", b"isUnsafe",
                ],
                0,
            )?;
            let mut d = Decl { kind: D_REC, ..Default::default() };
            self.common(&mut d, name, lps, ty)?;
            d.all = self.name_list(all)?;
            d.nums = [self.num(np)?, self.num(ni)?, self.num(nmot)?, self.num(nmin)?];
            d.k = self.boolean(k)?;
            for rule in self.arr(rules)? {
                let [ctor, nf, rhs] = self.fields(rule, [b"ctor", b"nfields", b"rhs"], 0)?;
                let ctor = self.r(ctor, K_NAME)?;
                let nf = self.num(nf)?;
                let rhs = self.r(rhs, K_EXPR)?;
                d.rules.push((ctor, nf, rhs));
            }
            d.is_unsafe = self.boolean(uns)?;
            self.ch.decls.push(d);
        }
        Ok(())
    }
}

extern "C" {
    fn memchr(s: *const std::ffi::c_void, c: i32, n: usize) -> *mut std::ffi::c_void;
}

fn find_nl(b: &[u8], from: usize) -> Option<usize> {
    if from >= b.len() {
        return None;
    }
    let p = unsafe { memchr(b.as_ptr().add(from) as *const _, b'\n' as i32, b.len() - from) };
    if p.is_null() {
        None
    } else {
        Some(p as usize - b.as_ptr() as usize)
    }
}

fn parse_chunk(file: &[u8], start: usize, end: usize) -> Result<Chunk, (usize, String)> {
    let mut lp = LineParser {
        file,
        base: start,
        jp: JP::new(),
        ch: Chunk {
            names: Vec::new(),
            levels: Vec::new(),
            exprs: Vec::new(),
            pool: Vec::new(),
            decls: Vec::new(),
            first: [0; 3],
            slack: [i64::MIN; 3],
            lets: Vec::new(),
        },
    };
    let est = (end - start) / 48 + 16;
    lp.ch.exprs.reserve(est);
    let mut p = start;
    while p < end {
        let e = find_nl(file, p).unwrap_or(file.len()).min(end);
        // Lean reads the line including its '\n'; the '\n' is whitespace for Json.parse, so parsing
        // the line without it is the same.
        let line: &[u8] = &lp.file[p..e];
        lp.parse_line(line, p).map_err(|m| (p, m))?;
        p = e + 1;
    }
    Ok(lp.ch)
}

// ---------------------------------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum Comp {
    Str(Vec<u8>),
    Num(u64),
}

/// A name component without allocation (escaped strings are decoded into an owned buffer).
enum CompRef<'a> {
    Str(std::borrow::Cow<'a, [u8]>),
    Num(u64),
}

impl<'a> CompRef<'a> {
    fn eq(&self, o: &CompRef) -> bool {
        match (self, o) {
            (CompRef::Str(a), CompRef::Str(b)) => a[..] == b[..],
            (CompRef::Num(a), CompRef::Num(b)) => a == b,
            _ => false,
        }
    }
    fn of(c: &'a Comp) -> CompRef<'a> {
        match c {
            Comp::Str(s) => CompRef::Str(std::borrow::Cow::Borrowed(&s[..])),
            Comp::Num(n) => CompRef::Num(*n),
        }
    }
}

#[inline]
fn mix(h: u64, w: u64) -> u64 {
    (h.rotate_left(5) ^ w).wrapping_mul(0x517cc1b727220a95)
}

/// Per-process random seed for the name table (an adversary cannot pre-compute colliding names; equality is
/// always checked in full, so the seed only affects speed, never results).
fn name_seed() -> u64 {
    use std::hash::{BuildHasher, Hasher};
    static SEED: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *SEED.get_or_init(|| {
        let mut h = std::collections::hash_map::RandomState::new().build_hasher();
        h.write_u64(0x9e3779b97f4a7c15);
        h.finish() | 1
    })
}

fn hash_key(pre: u32, c: &CompRef) -> u64 {
    let mut h = mix(name_seed(), pre as u64);
    match c {
        CompRef::Num(n) => {
            h = mix(h, 2);
            h = mix(h, *n);
        }
        CompRef::Str(s) => {
            h = mix(h, 1 ^ ((s.len() as u64) << 8));
            let mut ch = s.chunks_exact(8);
            for w in &mut ch {
                h = mix(h, u64::from_le_bytes(w.try_into().unwrap()));
            }
            let r = ch.remainder();
            let mut last = [0u8; 8];
            last[..r.len()].copy_from_slice(r);
            h = mix(h, u64::from_le_bytes(last));
        }
    }
    h ^ (h >> 29)
}

struct Env {
    file: &'static [u8],
    names: Vec<NameRec>,
    levels: Vec<LevelRec>,
    exprs: Vec<ExprRec>,
    pool: Vec<u32>,
    decls: Vec<Decl>,
    canon: Vec<u32>,   // name index -> representative (first index with the same Lean.Name)
    slots: Vec<u32>,   // open addressing: representatives keyed by (representative of prefix, component)
    decl_of: Vec<u32>, // representative name -> declaration index
    let_name: FxMap<u32, u32>, // letE expr index -> binder name (expdiff)
}

fn decode_json_string(raw: &[u8]) -> Vec<u8> {
    // raw has been validated by JP::string_body
    let mut out = Vec::with_capacity(raw.len());
    let mut i = 0;
    let hex4 = |s: &[u8]| -> u32 { s.iter().fold(0u32, |v, &c| (v << 4) | (c as char).to_digit(16).unwrap()) };
    while i < raw.len() {
        let c = raw[i];
        if c != b'\\' {
            out.push(c);
            i += 1;
            continue;
        }
        let d = raw[i + 1];
        let ch: u32 = match d {
            b'\\' => 0x5c,
            b'"' => 0x22,
            b'/' => 0x2f,
            b'b' => 0x08,
            b'f' => 0x0c,
            b'n' => 0x0a,
            b'r' => 0x0d,
            b't' => 0x09,
            b'u' => {
                let v = hex4(&raw[i + 2..i + 6]);
                if (0xD800..0xDC00).contains(&v) {
                    let w = hex4(&raw[i + 8..i + 12]);
                    i += 6;
                    (((v & 0x3FF) << 10) | (w & 0x3FF)) + 0x10000
                } else {
                    v
                }
            }
            _ => unreachable!(),
        };
        i += if d == b'u' { 6 } else { 2 };
        let mut buf = [0u8; 4];
        out.extend_from_slice(char::from_u32(ch).unwrap().encode_utf8(&mut buf).as_bytes());
    }
    out
}

impl Env {
    fn comp_ref(&self, i: u32) -> CompRef<'static> {
        let n = self.names[i as usize];
        let f: &'static [u8] = self.file;
        match n.kind {
            N_STR => CompRef::Str(std::borrow::Cow::Borrowed(&f[n.off as usize..n.off as usize + n.len as usize])),
            N_STRESC => CompRef::Str(std::borrow::Cow::Owned(decode_json_string(
                &f[n.off as usize..n.off as usize + n.len as usize],
            ))),
            N_NUM => CompRef::Num(n.off),
            _ => unreachable!(),
        }
    }
    fn name_comp(&self, i: u32) -> Comp {
        match self.comp_ref(i) {
            CompRef::Str(s) => Comp::Str(s.into_owned()),
            CompRef::Num(n) => Comp::Num(n),
        }
    }
    fn name_str(&self, i: u32) -> String {
        let mut comps = Vec::new();
        let mut c = i;
        while self.names[c as usize].kind != N_ANON {
            comps.push(match self.name_comp(c) {
                Comp::Str(s) => String::from_utf8_lossy(&s).into_owned(),
                Comp::Num(n) => n.to_string(),
            });
            c = self.names[c as usize].pre;
        }
        comps.reverse();
        if comps.is_empty() {
            "[anonymous]".into()
        } else {
            comps.join(".")
        }
    }
    /// The representative of the name (pre, comp), if this file has it. `pre` is a representative.
    fn find(&self, pre: u32, c: &CompRef) -> Option<u32> {
        let mask = self.slots.len() - 1;
        let mut pos = hash_key(pre, c) as usize & mask;
        loop {
            let s = self.slots[pos];
            if s == NONE {
                return None;
            }
            if self.canon[self.names[s as usize].pre as usize] == pre && self.comp_ref(s).eq(c) {
                return Some(s);
            }
            pos = (pos + 1) & mask;
        }
    }
    fn lookup(&self, path: &[Comp]) -> Option<u32> {
        let mut cur = 0u32;
        for c in path {
            cur = self.find(cur, &CompRef::of(c))?;
        }
        Some(cur)
    }
    fn decl_by_path(&self, path: &[Comp]) -> Option<u32> {
        let r = self.lookup(path)?;
        let d = self.decl_of[r as usize];
        if d == NONE {
            None
        } else {
            Some(d)
        }
    }
    fn lit(&self, e: &ExprRec) -> &[u8] {
        let off = e.a as usize | ((e.b as usize) << 32);
        &self.file[off..off + e.c as usize]
    }
}

extern "C" {
    fn mmap(addr: *mut std::ffi::c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut std::ffi::c_void;
}

/// Maps the file read-only for the life of the process.
fn map_file(path: &str) -> std::io::Result<&'static [u8]> {
    use std::os::unix::io::AsRawFd;
    let f = File::open(path)?;
    let len = f.metadata()?.len() as usize;
    if len == 0 {
        return Ok(&[]);
    }
    // PROT_READ = 1, MAP_PRIVATE = 2
    let p = unsafe { mmap(std::ptr::null_mut(), len, 1, 2, f.as_raw_fd(), 0) };
    if p as isize == -1 {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: the mapping is never unmapped; inputs are not modified while we run (read-only inputs).
    Ok(unsafe { std::slice::from_raw_parts(p as *const u8, len) })
}

/// Copies `parts` (in order) into one vector, in parallel.
fn concat_par<T: Copy + Send + Sync>(parts: Vec<&[T]>, prefix: Option<T>, total: usize) -> Vec<T> {
    let mut v: Vec<T> = Vec::with_capacity(total);
    let mut off = 0usize;
    if let Some(x) = prefix {
        v.push(x);
        off = 1;
    }
    let base = v.as_mut_ptr() as usize;
    std::thread::scope(|s| {
        let mut o = off;
        for part in &parts {
            let start = o;
            o += part.len();
            let part: &[T] = part;
            s.spawn(move || unsafe {
                std::ptr::copy_nonoverlapping(part.as_ptr(), (base as *mut T).add(start), part.len());
            });
        }
        assert!(o == total);
    });
    // SAFETY: elements [0, total) were all written above (prefix + every part).
    unsafe { v.set_len(total) };
    v
}

fn load(path: &str, threads: usize, verbose: bool) -> R<Env> {
    let t0 = Instant::now();
    let file = match map_file(path) {
        Ok(f) => f,
        Err(e) => decline!("cannot read {}: {}", path, e),
    };
    let t1 = Instant::now();
    let len = file.len();
    // the first line is the metadata line, skipped unread (LeanExport.Parse.parseMdata)
    let body = match find_nl(file, 0) {
        Some(p) => p + 1,
        None => len,
    };
    let nthreads = threads.max(1).min((len - body) / (1 << 16) + 1);
    // more pieces than threads, for balance; each thread takes pieces in order
    let npieces = if nthreads == 1 { 1 } else { nthreads * 4 };
    let mut starts = vec![body];
    for t in 1..npieces {
        let nominal = body + (len - body) * t / npieces;
        let prev = *starts.last().unwrap();
        let s = if nominal <= prev { prev } else { find_nl(file, nominal - 1).map(|p| p + 1).unwrap_or(len) };
        starts.push(s.max(prev));
    }
    starts.push(len);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut chunks: Vec<(usize, Result<Chunk, (usize, String)>)> = std::thread::scope(|s| {
        let hs: Vec<_> = (0..nthreads)
            .map(|_| {
                let starts = &starts;
                let next = &next;
                s.spawn(move || {
                    let mut out = Vec::new();
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= npieces {
                            break;
                        }
                        let r = parse_chunk(file, starts[i], starts[i + 1]);
                        let stop = r.is_err();
                        out.push((i, r));
                        if stop {
                            break;
                        }
                    }
                    out
                })
            })
            .collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    });
    chunks.sort_by_key(|c| c.0);
    let mut cs = Vec::with_capacity(chunks.len());
    for (_, c) in chunks {
        match c {
            Ok(c) => cs.push(c),
            Err((off, m)) => {
                let line_no = file[..off].iter().filter(|&&c| c == b'\n').count() + 1;
                decline!("{}: line {}: {}", path, line_no, m)
            }
        }
    }
    if cs.len() != npieces {
        decline!("{}: internal error (pieces)", path);
    }
    let t2 = Instant::now();
    // indices: dense and increasing across chunks; references bound on earlier lines
    let mut base = [1u64, 1, 0];
    let mut pool_base = 0usize;
    for c in cs.iter_mut() {
        let counts = [c.names.len(), c.levels.len(), c.exprs.len()];
        for k in 0..3 {
            if counts[k] > 0 && c.first[k] != base[k] {
                decline!("{}: indices not dense and increasing (unsupported)", path);
            }
            if c.slack[k] != i64::MIN && c.slack[k] >= base[k] as i64 {
                // some reference is not bound on an earlier line: Lean's parser fails
                reject!("{}: reference to an index that is not bound on an earlier line", path);
            }
            base[k] += counts[k] as u64;
        }
        c.first[0] = pool_base as u64; // reuse: pool base of this chunk
        pool_base += c.pool.len();
    }
    if base[2] >= NONE as u64 || base[0] >= NONE as u64 || base[1] >= NONE as u64 || pool_base >= NONE as usize {
        decline!("{}: too many records", path);
    }
    // const expressions: chunk-local pool offsets -> global
    std::thread::scope(|s| {
        for c in cs.iter_mut() {
            let pb = c.first[0] as u32;
            if pb != 0 {
                s.spawn(move || {
                    for e in c.exprs.iter_mut() {
                        if e.kind == E_CONST {
                            e.b += pb;
                        }
                    }
                });
            }
        }
    });
    let names = concat_par(
        cs.iter().map(|c| &c.names[..]).collect(),
        Some(NameRec { kind: N_ANON, pre: 0, len: 0, off: 0 }),
        base[0] as usize,
    );
    let levels =
        concat_par(cs.iter().map(|c| &c.levels[..]).collect(), Some(LevelRec { kind: L_ZERO, a: 0, b: 0 }), base[1] as usize);
    let exprs = concat_par(cs.iter().map(|c| &c.exprs[..]).collect(), None, base[2] as usize);
    let pool = concat_par(cs.iter().map(|c| &c.pool[..]).collect(), None, pool_base);
    let mut decls = Vec::new();
    let mut let_name: FxMap<u32, u32> = FxMap::default();
    for c in cs.iter_mut() {
        decls.append(&mut c.decls);
        for &(e, n) in &c.lets {
            let_name.insert(e, n);
        }
    }
    std::mem::forget(cs); // freeing is wasted time; the process exits soon
    let t3 = Instant::now();
    let mut env = Env { file, names, levels, exprs, pool, decls, canon: Vec::new(), slots: Vec::new(), decl_of: Vec::new(), let_name };
    // canonical names (structural equality of Lean.Name), in line order (a prefix is bound earlier)
    let n = env.names.len();
    env.canon = vec![0u32; n];
    let cap = (n * 2).next_power_of_two().max(16);
    env.slots = vec![NONE; cap];
    let mask = cap - 1;
    for i in 1..n {
        let pre = env.canon[env.names[i].pre as usize];
        let c = env.comp_ref(i as u32);
        let mut pos = hash_key(pre, &c) as usize & mask;
        let rep = loop {
            let s = env.slots[pos];
            if s == NONE {
                env.slots[pos] = i as u32;
                break i as u32;
            }
            if env.canon[env.names[s as usize].pre as usize] == pre && env.comp_ref(s).eq(&c) {
                break s;
            }
            pos = (pos + 1) & mask;
        };
        env.canon[i] = rep;
    }
    let t4 = Instant::now();
    let mut decl_of = vec![NONE; n];
    for (i, d) in env.decls.iter().enumerate() {
        let r = env.canon[d.name as usize];
        if decl_of[r as usize] != NONE {
            reject!("{}: Duplicate declaration: {}", path, env.name_str(r));
        }
        decl_of[r as usize] = i as u32;
    }
    env.decl_of = decl_of;
    let t5 = Instant::now();
    if verbose {
        eprintln!(
            "expdiff: {}: {} bytes, {} names, {} levels, {} exprs, {} decls; map {:.3}s parse {:.3}s merge {:.3}s names {:.3}s decls {:.3}s ({} threads)",
            path,
            len,
            env.names.len(),
            env.levels.len(),
            env.exprs.len(),
            env.decls.len(),
            (t1 - t0).as_secs_f64(),
            (t2 - t1).as_secs_f64(),
            (t3 - t2).as_secs_f64(),
            (t4 - t3).as_secs_f64(),
            (t5 - t4).as_secs_f64(),
            nthreads
        );
    }
    Ok(env)
}


// ---------------------------------------------------------------------------------------------------
// Structural digest (test aid): two parses of the same environment give the same digest, whatever the
// index numbering. mdata is transparent and letE's nondep flag and binder name are left out (Susz drops
// mdata/nondep), so `kcompare --digest X` can be compared with the digest of `susz unpack (susz pack X)`.
// ---------------------------------------------------------------------------------------------------

#[inline]
fn hmix(h: u64, x: u64) -> u64 {
    let v = (h ^ x).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    v ^ (v >> 31)
}
fn hparts(seed: u64, tag: u64, parts: &[u64]) -> u64 {
    let mut x = hmix(seed, tag);
    for &p in parts {
        x = hmix(x, p);
    }
    hmix(x, parts.len() as u64)
}
fn hbytes(seed: u64, b: &[u8]) -> u64 {
    let mut x = seed ^ 0xcbf2_9ce4_8422_2325;
    for &c in b {
        x = (x ^ c as u64).wrapping_mul(0x100_0000_01b3);
    }
    hmix(x, b.len() as u64)
}

fn digest_seed(env: &Env, seed: u64) -> (u64, Vec<u64>) {
    let nn = env.names.len();
    let mut hn = vec![0u64; nn];
    hn[0] = hparts(seed, 1, &[]);
    for i in 1..nn {
        let r = env.names[i];
        let pre = hn[r.pre as usize];
        hn[i] = match env.comp_ref(i as u32) {
            CompRef::Str(b) => hparts(seed, 2, &[pre, hbytes(seed, &b)]),
            CompRef::Num(n) => hparts(seed, 3, &[pre, n]),
        };
    }
    let nl = env.levels.len();
    let mut hl = vec![0u64; nl];
    hl[0] = hparts(seed, 10, &[]);
    for i in 1..nl {
        let l = env.levels[i];
        hl[i] = match l.kind {
            L_SUCC => hparts(seed, 11, &[hl[l.a as usize]]),
            L_MAX => hparts(seed, 12, &[hl[l.a as usize], hl[l.b as usize]]),
            L_IMAX => hparts(seed, 13, &[hl[l.a as usize], hl[l.b as usize]]),
            L_PARAM => hparts(seed, 14, &[hn[l.a as usize]]),
            _ => hparts(seed, 10, &[]),
        };
    }
    let ne = env.exprs.len();
    let mut he = vec![0u64; ne];
    for i in 0..ne {
        let e = env.exprs[i];
        he[i] = match e.kind {
            E_BVAR => hparts(seed, 20, &[e.a as u64 | ((e.b as u64) << 32)]),
            E_SORT => hparts(seed, 21, &[hl[e.a as usize]]),
            E_CONST => {
                let mut v = vec![hn[e.a as usize]];
                for k in 0..e.c {
                    v.push(hl[env.pool[(e.b + k) as usize] as usize]);
                }
                hparts(seed, 22, &v)
            }
            E_APP => hparts(seed, 23, &[he[e.a as usize], he[e.b as usize]]),
            E_LAM | E_PI => hparts(
                seed,
                if e.kind == E_LAM { 24 } else { 25 },
                &[hn[e.c as usize], e.flag as u64, he[e.a as usize], he[e.b as usize]],
            ),
            E_LET => hparts(seed, 26, &[he[e.a as usize], he[e.b as usize], he[e.c as usize]]),
            E_PROJ => hparts(seed, 27, &[hn[e.a as usize], e.c as u64, he[e.b as usize]]),
            E_NAT => hparts(seed, 28, &[hbytes(seed, env.lit(&e))]),
            E_STR => {
                let raw = env.lit(&e);
                let b = if e.flag != 0 { decode_json_string(raw) } else { raw.to_vec() };
                hparts(seed, 29, &[hbytes(seed, &b)])
            }
            E_MDATA => he[e.a as usize],
            _ => 0,
        };
    }
    let names = |v: &[u32]| -> Vec<u64> { v.iter().map(|&n| hn[n as usize]).collect() };
    let mut hd = Vec::with_capacity(env.decls.len());
    for d in &env.decls {
        let mut v = vec![hn[d.name as usize], hparts(seed, 40, &names(&d.lparams)), he[d.ty as usize]];
        match d.kind {
            D_AXIOM => v.push(d.is_unsafe as u64),
            D_DEFN => {
                v.extend([he[d.val as usize], d.hints_kind as u64, d.hints_val as u64, d.safety as u64]);
                v.push(hparts(seed, 41, &names(&d.all)));
            }
            D_THM => {
                v.push(he[d.val as usize]);
                v.push(hparts(seed, 41, &names(&d.all)));
            }
            D_OPAQUE => {
                v.extend([he[d.val as usize], d.is_unsafe as u64]);
                v.push(hparts(seed, 41, &names(&d.all)));
            }
            D_QUOT => v.push(d.quot_kind as u64),
            D_INDUCT => {
                v.extend(d.nums[..3].iter().copied());
                v.push(hparts(seed, 41, &names(&d.all)));
                v.push(hparts(seed, 42, &names(&d.ctors)));
                v.extend([d.is_rec as u64, d.is_unsafe as u64, d.is_reflexive as u64]);
            }
            D_CTOR => {
                v.push(hn[d.induct as usize]);
                v.extend(d.nums[..3].iter().copied());
                v.push(d.is_unsafe as u64);
            }
            D_REC => {
                v.push(hparts(seed, 41, &names(&d.all)));
                v.extend(d.nums.iter().copied());
                v.extend([d.k as u64, d.is_unsafe as u64]);
                for &(c, nf, rhs) in &d.rules {
                    v.push(hparts(seed, 43, &[hn[c as usize], nf, he[rhs as usize]]));
                }
            }
            _ => {}
        }
        hd.push(hparts(seed, 50 + d.kind as u64, &v));
    }
    let mut acc = hparts(seed, 60, &[]);
    for &x in &hd {
        acc = hmix(acc, x);
    }
    (acc, hd)
}

// ---------------------------------------------------------------------------------------------------
// Used constants (Lake.Check.runForUsedConsts, Expr.getUsedConstants of Lean 4.36)
// ---------------------------------------------------------------------------------------------------

struct Bits(Vec<u64>);
impl Bits {
    fn new(n: usize) -> Bits {
        Bits(vec![0; n / 64 + 1])
    }
    #[inline]
    fn test_set(&mut self, i: u32) -> bool {
        let w = &mut self.0[(i >> 6) as usize];
        let m = 1u64 << (i & 63);
        let was = *w & m != 0;
        *w |= m;
        was
    }
}

/// Calls f(name index) for every constant name in expression `root` (const names and proj type names),
/// skipping subterms already visited (the result is used as a set).
fn expr_consts(env: &Env, root: u32, vis: &mut Bits, stack: &mut Vec<u32>, f: &mut dyn FnMut(u32) -> R<()>) -> R<()> {
    stack.push(root);
    while let Some(e) = stack.pop() {
        if vis.test_set(e) {
            continue;
        }
        let x = env.exprs[e as usize];
        match x.kind {
            E_CONST => f(x.a)?,
            E_APP => {
                stack.push(x.a);
                stack.push(x.b);
            }
            E_LAM | E_PI => {
                stack.push(x.a);
                stack.push(x.b);
            }
            E_LET => {
                stack.push(x.a);
                stack.push(x.b);
                stack.push(x.c);
            }
            E_PROJ => {
                f(x.a)?;
                stack.push(x.b);
            }
            E_MDATA => stack.push(x.a),
            _ => {}
        }
    }
    Ok(())
}

/// runForUsedConsts: type, the name itself, value (defn/thm/opaque), ctors+all (inductive),
/// induct (constructor), rule ctors + rule rhs (recursor).
fn decl_consts(env: &Env, d: &Decl, vis: &mut Bits, stack: &mut Vec<u32>, f: &mut dyn FnMut(u32) -> R<()>) -> R<()> {
    expr_consts(env, d.ty, vis, stack, f)?;
    f(d.name)?;
    match d.kind {
        D_DEFN | D_THM | D_OPAQUE => expr_consts(env, d.val, vis, stack, f)?,
        _ => {}
    }
    match d.kind {
        D_INDUCT => {
            for &c in &d.ctors {
                f(c)?;
            }
            for &c in &d.all {
                f(c)?;
            }
        }
        D_CTOR => f(d.induct)?,
        D_REC => {
            for &(c, _, rhs) in &d.rules {
                f(c)?;
                expr_consts(env, rhs, vis, stack, f)?;
            }
        }
        _ => {}
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------------
// checkAxioms (Lake/Check/Axioms.lean)
// ---------------------------------------------------------------------------------------------------

/// String.toName for plain dotted identifiers (the configuration's names); anything fancier is declined.
fn to_name(s: &str) -> R<Vec<Comp>> {
    if s.is_empty() || s.contains('«') || s.contains('»') {
        decline!("unsupported name in configuration: {:?}", s);
    }
    let mut v = Vec::new();
    for part in s.split('.') {
        if part.is_empty() {
            decline!("unsupported name in configuration: {:?}", s);
        }
        if part.chars().all(|c| c.is_ascii_digit()) {
            // expdiff: all-digit components are numeric name components (e.g. `_private.M.0.x`)
            match part.parse::<u64>() {
                Ok(n) => v.push(Comp::Num(n)),
                Err(_) => decline!("unsupported name in configuration: {:?}", s),
            }
            continue;
        }
        if part.chars().next().unwrap().is_ascii_digit() {
            decline!("unsupported name in configuration: {:?}", s);
        }
        v.push(Comp::Str(part.as_bytes().to_vec()));
    }
    Ok(v)
}

