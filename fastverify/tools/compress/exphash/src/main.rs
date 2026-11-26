// exphash — structural (Merkle) hashing of a lean4export NDJSON export (format 3.x), one sequential pass.
//
//   exphash [--classes] EXPORT OUTDIR
//
// Writes OUTDIR/decls.tsv (one row per declaration; inductive blocks: one row per type / constructor / recursor) and
// OUTDIR/summary.json.  Every expression gets two 128-bit hashes computed bottom-up from its children:
//   hk  "kernel" hash: binder names, binder infos, mdata and the let `nondep` flag are ignored (none of them matters to
//       kernel type checking), constants by full name, levels structurally (level parameters by name);
//   hs  "source" hash: as hk but binder infos are included (an implicit/explicit change matters for source-level reuse).
// Equal hk of two theorem types (and equal level-parameter lists) => one theorem can be used wherever the other is
// (proof irrelevance), so the duplicate can be shared.  The hashes are not cryptographic; this is an ANALYSIS tool
// (untrusted): its output never decides a verdict.
//
// Also computed per declaration, attributing every expression node to the declaration whose line follows it in the
// export (= the first declaration that uses it; the export is hash-consed, so every node is counted exactly once):
//   new_nodes/new_bytes  expression nodes / bytes introduced by the declaration (its "own" proof size in the export)
//   dead_have/dead_let   `have`/`let` (letE nondep=true / false) whose body does not use the bound variable
//   dead_beta            beta-redexes (fun x => b) a whose body does not use x
//   dead_tsize           sum of the tree sizes of the dead values (the proof text that could be removed)
//   unused_hyp           top-level binders of the value (lambda chain, matched against the type's forall chain) that the
//                        body never uses although the type's binder is a non-dependent arrow (= an unused hypothesis)
//   unused_inst          the same for instance-implicit binders (unused instance arguments)
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};

type H = [u64; 2];

#[inline(always)]
fn fmix(mut k: u64) -> u64 {
    k ^= k >> 33;
    k = k.wrapping_mul(0xff51afd7ed558ccd);
    k ^= k >> 33;
    k = k.wrapping_mul(0xc4ceb9fe1a85ec53);
    k ^= k >> 33;
    k
}

#[derive(Clone, Copy)]
struct Hs {
    a: u64,
    b: u64,
}
impl Hs {
    #[inline(always)]
    fn new(tag: u64) -> Hs {
        Hs { a: fmix(tag ^ 0x9e3779b97f4a7c15), b: fmix(tag.wrapping_add(0x632be59bd9b4e019)) }
    }
    #[inline(always)]
    fn add(&mut self, x: u64) {
        self.a = fmix(self.a ^ x).wrapping_mul(0x9fb21c651e98df25).wrapping_add(0x2545f4914f6cdd1d);
        self.b = fmix(self.b.wrapping_add(x.rotate_left(29)) ^ 0xd6e8feb86659fd93).rotate_left(7);
    }
    #[inline(always)]
    fn addh(&mut self, h: &H) {
        self.add(h[0]);
        self.add(h[1]);
    }
    #[inline(always)]
    fn fin(&self) -> H {
        [fmix(self.a ^ self.b.rotate_left(32)), fmix(self.b ^ 0x5851f42d4c957f2d)]
    }
}

fn hash_bytes(tag: u64, s: &[u8]) -> H {
    let mut h = Hs::new(tag);
    let mut chunks = s.chunks_exact(8);
    for c in &mut chunks {
        h.add(u64::from_le_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]));
    }
    let r = chunks.remainder();
    let mut last = [0u8; 8];
    last[..r.len()].copy_from_slice(r);
    h.add(u64::from_le_bytes(last));
    h.add(s.len() as u64);
    h.fin()
}

const T_ANON: u64 = 1;
const T_NSTR: u64 = 2;
const T_NNUM: u64 = 3;
const T_LZERO: u64 = 10;
const T_LSUCC: u64 = 11;
const T_LMAX: u64 = 12;
const T_LIMAX: u64 = 13;
const T_LPARAM: u64 = 14;
const T_BVAR: u64 = 20;
const T_SORT: u64 = 21;
const T_CONST: u64 = 22;
const T_APP: u64 = 23;
const T_LAM: u64 = 24;
const T_PI: u64 = 25;
const T_LET: u64 = 26;
const T_NAT: u64 = 27;
const T_STR: u64 = 28;
const T_PROJ: u64 = 29;

const K_BVAR: u8 = 1;
const K_SORT: u8 = 2;
const K_CONST: u8 = 3;
const K_APP: u8 = 4;
const K_LAM: u8 = 5;
const K_PI: u8 = 6;
const K_LET: u8 = 7;
const K_LIT: u8 = 8;
const K_MDATA: u8 = 9;
const K_PROJ: u8 = 10;

const OVF: u64 = 1u64 << 63;
#[inline(always)]
fn shift(m: u64) -> u64 {
    ((m & !OVF) >> 1) | (m & OVF)
}
#[inline(always)]
fn uses0(m: u64) -> bool {
    m & 1 != 0 || m & OVF != 0
}

// ---------------------------------------------------------------- minimal JSON field scanner (no allocation)
#[inline]
fn skip_ws(s: &[u8], mut i: usize) -> usize {
    while i < s.len() && (s[i] == b' ' || s[i] == b'\t' || s[i] == b'\r' || s[i] == b'\n') {
        i += 1;
    }
    i
}
fn skip_string(s: &[u8], mut i: usize) -> usize {
    // s[i] == '"'; returns index after the closing quote
    i += 1;
    while i < s.len() {
        match s[i] {
            b'\\' => i += 2,
            b'"' => return i + 1,
            _ => i += 1,
        }
    }
    i
}
fn skip_value(s: &[u8], i: usize) -> usize {
    match s[i] {
        b'"' => skip_string(s, i),
        b'{' | b'[' => {
            let mut depth = 0i32;
            let mut j = i;
            while j < s.len() {
                match s[j] {
                    b'"' => {
                        j = skip_string(s, j);
                        continue;
                    }
                    b'{' | b'[' => depth += 1,
                    b'}' | b']' => {
                        depth -= 1;
                        if depth == 0 {
                            return j + 1;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            j
        }
        _ => {
            let mut j = i;
            while j < s.len() && s[j] != b',' && s[j] != b'}' && s[j] != b']' {
                j += 1;
            }
            j
        }
    }
}
/// fields of the object starting at s[i] == '{' : (key, raw value)
fn fields<'a>(s: &'a [u8], i: usize, out: &mut Vec<(&'a [u8], &'a [u8])>) {
    out.clear();
    let mut i = skip_ws(s, i);
    if i >= s.len() || s[i] != b'{' {
        return;
    }
    i += 1;
    loop {
        i = skip_ws(s, i);
        if i >= s.len() || s[i] == b'}' {
            return;
        }
        if s[i] == b',' {
            i += 1;
            continue;
        }
        if s[i] != b'"' {
            return;
        }
        let ke = skip_string(s, i);
        let key = &s[i + 1..ke - 1];
        i = skip_ws(s, ke);
        if i >= s.len() || s[i] != b':' {
            return;
        }
        i = skip_ws(s, i + 1);
        let ve = skip_value(s, i);
        out.push((key, &s[i..ve]));
        i = ve;
    }
}
#[inline]
fn num(v: &[u8]) -> u64 {
    let mut x: u64 = 0;
    for &c in v {
        if c.is_ascii_digit() {
            x = x.wrapping_mul(10).wrapping_add((c - b'0') as u64);
        } else if c != b' ' {
            break;
        }
    }
    x
}
fn nums(v: &[u8]) -> Vec<u64> {
    // "[1,2,3]"
    let mut r = Vec::new();
    let mut cur: Option<u64> = None;
    for &c in v {
        if c.is_ascii_digit() {
            cur = Some(cur.unwrap_or(0) * 10 + (c - b'0') as u64);
        } else if let Some(x) = cur.take() {
            r.push(x);
        }
    }
    if let Some(x) = cur {
        r.push(x);
    }
    r
}
fn get<'a>(f: &[(&'a [u8], &'a [u8])], k: &[u8]) -> Option<&'a [u8]> {
    f.iter().find(|(a, _)| *a == k).map(|(_, v)| *v)
}
fn unquote(v: &[u8]) -> &[u8] {
    if v.len() >= 2 && v[0] == b'"' && v[v.len() - 1] == b'"' {
        &v[1..v.len() - 1]
    } else {
        v
    }
}

// ---------------------------------------------------------------- state
#[derive(Default, Clone)]
struct Owner {
    dead_names: Vec<u32>,
    new_nodes: u64,
    new_bytes: u64,
    dead_have: u64,
    dead_let: u64,
    dead_beta: u64,
    dead_tsize: u64,
}

struct St {
    classes: bool,
    // names
    npre: Vec<u32>,
    ncomp: Vec<Box<str>>, // component (string, or '#'+digits for num components)
    nh: Vec<H>,
    // levels and interned level lists (const universe arguments)
    lh: Vec<H>,
    lists: HashMap<Vec<u32>, u32>,
    listh: Vec<H>,
    // exprs: structure
    kind: Vec<u8>, // low 4 bits kind, high bits binder info for lam/pi (0 default 1 implicit 2 instImplicit 3 strict)
    c1: Vec<u32>,  // bvar idx | sort level | const name | app fn | lam/pi/let body | proj struct | mdata expr
    c2: Vec<u32>,  // const level list | app arg | lam/pi/let type | proj typeName
    c3: Vec<u32>,  // let value | proj idx | let nondep flag in bit 31
    bname: Vec<u32>,
    lit: HashMap<u32, H>,
    // exprs: derived
    hk: Vec<H>,
    hs: Vec<H>,
    ts: Vec<u64>,
    mask: Vec<u64>,
    // classes of declared constants (by name index), --classes mode only
    class_of: HashMap<u32, H>,
    // --project FILE: only these constants get classes; all others stay nominal (hashed by name)
    project: Option<std::collections::HashSet<String>>,
    // --nominal FILE: these constants stay nominal; all others get classes (e.g. every constant of the challenge export)
    nominal: Option<std::collections::HashSet<String>>,
    own: Owner,
    bad_lines: u64,
    // shared closed have/let values: value node -> (last decl, #decls, binder names, decls)
    cur_decl: u32,
    haves: HashMap<u32, HaveRec>,
}

#[derive(Default)]
struct HaveRec {
    last: u32,
    count: u32,
    names: Vec<u32>,
    decls: Vec<u32>,
}
const HAVE_MIN_TSIZE: u64 = 16;

fn setv<T: Copy + Default>(v: &mut Vec<T>, i: usize, x: T) {
    if i == v.len() {
        v.push(x);
    } else {
        if i > v.len() {
            v.resize(i + 1, T::default());
        }
        v[i] = x;
    }
}

impl St {
    fn name(&self, mut i: usize) -> String {
        let mut parts: Vec<&str> = Vec::new();
        while i != 0 && i < self.npre.len() {
            parts.push(&self.ncomp[i]);
            i = self.npre[i] as usize;
        }
        parts.reverse();
        let mut s = String::new();
        for (k, p) in parts.iter().enumerate() {
            if k > 0 {
                s.push('.');
            }
            s.push_str(p.strip_prefix('#').unwrap_or(p));
        }
        s
    }
    fn nhash(&self, i: usize) -> H {
        if i < self.nh.len() {
            self.nh[i]
        } else {
            [0, 0]
        }
    }
    fn lhash(&self, i: usize) -> H {
        if i < self.lh.len() {
            self.lh[i]
        } else {
            [0, 0]
        }
    }
    /// hash of a constant reference: its class (if declared and --classes) else its name
    fn chash(&self, name: u32) -> H {
        if self.classes {
            if let Some(h) = self.class_of.get(&name) {
                return *h;
            }
        }
        self.nhash(name as usize)
    }
    fn intern_list(&mut self, us: Vec<u32>) -> u32 {
        if let Some(&i) = self.lists.get(&us) {
            return i;
        }
        let mut h = Hs::new(T_CONST + 100);
        h.add(us.len() as u64);
        for u in &us {
            h.addh(&self.lhash(*u as usize));
        }
        let i = self.listh.len() as u32;
        self.listh.push(h.fin());
        self.lists.insert(us, i);
        i
    }
    /// (re)compute the derived data of node i from its structure and its children's derived data
    fn hash_node(&mut self, i: usize) {
        let k = self.kind[i] & 15;
        let bi = (self.kind[i] >> 4) as u64;
        let (a, b, c) = (self.c1[i] as usize, self.c2[i] as usize, self.c3[i]);
        let (hk, hs, ts, mask): (H, H, u64, u64) = match k {
            K_BVAR => {
                let mut h = Hs::new(T_BVAR);
                h.add(a as u64);
                let x = h.fin();
                (x, x, 1, if a < 63 { 1u64 << a } else { OVF })
            }
            K_SORT => {
                let mut h = Hs::new(T_SORT);
                h.addh(&self.lhash(a));
                let x = h.fin();
                (x, x, 1, 0)
            }
            K_CONST => {
                let mut h = Hs::new(T_CONST);
                h.addh(&self.chash(a as u32));
                h.addh(&self.listh[b]);
                let x = h.fin();
                (x, x, 1, 0)
            }
            K_APP => {
                let mut h = Hs::new(T_APP);
                h.addh(&self.hk[a]);
                h.addh(&self.hk[b]);
                let mut g = Hs::new(T_APP);
                g.addh(&self.hs[a]);
                g.addh(&self.hs[b]);
                (h.fin(), g.fin(), self.ts[a].saturating_add(self.ts[b]).saturating_add(1), self.mask[a] | self.mask[b])
            }
            K_LAM | K_PI => {
                let tag = if k == K_LAM { T_LAM } else { T_PI };
                let mut h = Hs::new(tag);
                h.addh(&self.hk[b]);
                h.addh(&self.hk[a]);
                let mut g = Hs::new(tag);
                g.add(bi);
                g.addh(&self.hs[b]);
                g.addh(&self.hs[a]);
                (h.fin(), g.fin(), self.ts[a].saturating_add(self.ts[b]).saturating_add(1), self.mask[b] | shift(self.mask[a]))
            }
            K_LET => {
                let v = (c & 0x7fff_ffff) as usize;
                let mut h = Hs::new(T_LET);
                h.addh(&self.hk[b]);
                h.addh(&self.hk[v]);
                h.addh(&self.hk[a]);
                let mut g = Hs::new(T_LET);
                g.addh(&self.hs[b]);
                g.addh(&self.hs[v]);
                g.addh(&self.hs[a]);
                (
                    h.fin(),
                    g.fin(),
                    self.ts[a].saturating_add(self.ts[b]).saturating_add(self.ts[v]).saturating_add(1),
                    self.mask[b] | self.mask[v] | shift(self.mask[a]),
                )
            }
            K_LIT => {
                let x = *self.lit.get(&(i as u32)).unwrap_or(&[0, 0]);
                (x, x, 1, 0)
            }
            K_MDATA => (self.hk[a], self.hs[a], self.ts[a], self.mask[a]),
            K_PROJ => {
                let mut h = Hs::new(T_PROJ);
                h.addh(&self.chash(b as u32));
                h.add(c as u64);
                let mut g = h;
                h.addh(&self.hk[a]);
                g.addh(&self.hs[a]);
                (h.fin(), g.fin(), self.ts[a].saturating_add(1), self.mask[a])
            }
            _ => ([0, 0], [0, 0], 1, OVF),
        };
        self.hk[i] = hk;
        self.hs[i] = hs;
        self.ts[i] = ts;
        self.mask[i] = mask;
    }
    fn note_have(&mut self, v: u32, bn: u32) {
        if self.mask[v as usize] != 0 || self.ts[v as usize] < HAVE_MIN_TSIZE {
            return;
        }
        let d = self.cur_decl;
        let r = self.haves.entry(v).or_default();
        if r.count == 0 || r.last != d {
            r.count += 1;
            r.last = d;
            if r.decls.len() < 12 {
                r.decls.push(d);
            }
        }
        if r.names.len() < 4 && !r.names.contains(&bn) {
            r.names.push(bn);
        }
    }
    fn push_node(&mut self, idx: usize, kind: u8, c1: u32, c2: u32, c3: u32, bn: u32) {
        setv(&mut self.kind, idx, kind);
        setv(&mut self.c1, idx, c1);
        setv(&mut self.c2, idx, c2);
        setv(&mut self.c3, idx, c3);
        setv(&mut self.bname, idx, bn);
        setv(&mut self.hk, idx, [0, 0]);
        setv(&mut self.hs, idx, [0, 0]);
        setv(&mut self.ts, idx, 0);
        setv(&mut self.mask, idx, 0);
        self.hash_node(idx);
        // dead-code detection (counted for the owning declaration)
        let k = kind & 15;
        if k == K_APP {
            let f = c1 as usize;
            if self.kind[f] & 15 == K_LAM {
                let fb = self.bname[f];
                self.note_have(c2, fb);
                let body = self.c1[f] as usize;
                if !uses0(self.mask[body]) {
                    self.own.dead_beta += 1;
                    self.own.dead_tsize = self.own.dead_tsize.saturating_add(self.ts[c2 as usize]);
                    if self.own.dead_names.len() < 64 {
                        let b = self.bname[f];
                        self.own.dead_names.push(b);
                    }
                }
            }
        } else if k == K_LET {
            self.note_have(c3 & 0x7fff_ffff, bn);
            let body = c1 as usize;
            if !uses0(self.mask[body]) {
                if c3 & 0x8000_0000 != 0 {
                    self.own.dead_have += 1;
                } else {
                    self.own.dead_let += 1;
                }
                let v = (c3 & 0x7fff_ffff) as usize;
                self.own.dead_tsize = self.own.dead_tsize.saturating_add(self.ts[v]);
                if self.own.dead_names.len() < 64 {
                    self.own.dead_names.push(bn);
                }
            }
        }
    }
}

fn binfo_code(v: &[u8]) -> u8 {
    match unquote(v) {
        b"implicit" => 1,
        b"instImplicit" => 2,
        b"strictImplicit" => 3,
        _ => 0,
    }
}

fn hex(h: &H) -> String {
    format!("{:016x}{:016x}", h[0], h[1])
}

struct Row {
    kind: &'static str,
    name_idx: u32,
    name: String,
    nlvl: usize,
    lvlh: H,
    ty: usize,
    value: Option<usize>,
    extra: String,
    unused_hyp: u64,
    unused_inst: u64,
    nbind: u64,
}

fn u(d: &serde_json::Value, k: &str) -> usize {
    d.get(k).and_then(|x| x.as_u64()).unwrap_or(0) as usize
}
fn s(d: &serde_json::Value, k: &str) -> String {
    d.get(k).map(|x| x.to_string()).unwrap_or_default()
}

fn mkrow(st: &St, kind: &'static str, d: &serde_json::Value, value: Option<usize>, extra: String) -> Row {
    let name = u(d, "name");
    let ty = u(d, "type");
    let lps: Vec<u64> =
        d.get("levelParams").and_then(|x| x.as_array()).map(|a| a.iter().filter_map(|y| y.as_u64()).collect()).unwrap_or_default();
    let mut lh = Hs::new(99);
    for p in &lps {
        lh.addh(&st.nhash(*p as usize));
    }
    // top-level binders: value lambda chain vs type forall chain
    let (mut unused_hyp, mut unused_inst, mut nbind) = (0u64, 0u64, 0u64);
    if let Some(vi) = value {
        let (mut a, mut t) = (vi, ty);
        loop {
            while st.kind[a] & 15 == K_MDATA {
                a = st.c1[a] as usize;
            }
            while st.kind[t] & 15 == K_MDATA {
                t = st.c1[t] as usize;
            }
            if st.kind[a] & 15 != K_LAM || st.kind[t] & 15 != K_PI {
                break;
            }
            nbind += 1;
            let body = st.c1[a] as usize;
            let tbody = st.c1[t] as usize;
            if !uses0(st.mask[body]) {
                let bi = st.kind[a] >> 4;
                if bi == 2 {
                    unused_inst += 1;
                } else if !uses0(st.mask[tbody]) && bi == 0 {
                    unused_hyp += 1;
                }
            }
            a = body;
            t = tbody;
        }
    }
    Row {
        kind,
        name_idx: name as u32,
        name: st.name(name),
        nlvl: lps.len(),
        lvlh: lh.fin(),
        ty,
        value,
        extra,
        unused_hyp,
        unused_inst,
        nbind,
    }
}

/// class of a non-inductive declaration row (theorem: statement only = proof irrelevance)
fn row_class(st: &St, r: &Row, hints_kind: &str) -> H {
    let mut h = Hs::new(1000);
    h.add(match r.kind {
        "thm" => 1,
        "def" => 2,
        "opaque" => 3,
        "axiom" => 4,
        "quot" => 5,
        _ => 9,
    });
    h.addh(&r.lvlh);
    h.addh(&st.hk[r.ty]);
    match r.kind {
        "def" | "opaque" => {
            if let Some(v) = r.value {
                h.addh(&st.hk[v]);
            }
            h.addh(&hash_bytes(7, hints_kind.as_bytes()));
        }
        "axiom" | "quot" => h.addh(&st.nhash(r.name_idx as usize)), // never merged
        _ => {}
    }
    h.fin()
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let classes = if let Some(p) = args.iter().position(|a| a == "--classes") {
        args.remove(p);
        true
    } else {
        false
    };
    let project = if let Some(p) = args.iter().position(|a| a == "--project") {
        let f = args[p + 1].clone();
        args.remove(p);
        args.remove(p);
        let mut set = std::collections::HashSet::new();
        for l in std::fs::read_to_string(&f).expect("read --project file").lines() {
            let n = l.split('\t').next().unwrap_or("");
            if !n.is_empty() {
                set.insert(n.to_string());
            }
        }
        eprintln!("--project: {} names", set.len());
        Some(set)
    } else {
        None
    };
    let nominal = if let Some(p) = args.iter().position(|a| a == "--nominal") {
        let f = args[p + 1].clone();
        args.remove(p);
        args.remove(p);
        let mut set = std::collections::HashSet::new();
        for l in std::fs::read_to_string(&f).expect("read --nominal file").lines() {
            let n = l.split('\t').next().unwrap_or("");
            if !n.is_empty() {
                set.insert(n.to_string());
            }
        }
        eprintln!("--nominal: {} names", set.len());
        Some(set)
    } else {
        None
    };
    if args.len() < 3 {
        eprintln!("usage: exphash [--classes [--project NAMES_TSV | --nominal NAMES_TSV]] EXPORT OUTDIR");
        std::process::exit(2);
    }
    let t0 = std::time::Instant::now();
    let f = File::open(&args[1]).expect("open export");
    let mut rd = BufReader::with_capacity(64 << 20, f);
    std::fs::create_dir_all(&args[2]).expect("mkdir");
    let mut out = BufWriter::with_capacity(16 << 20, File::create(format!("{}/decls.tsv", args[2])).expect("create"));
    writeln!(out, "kind\tname\tnlvl\tlvl_h\ttype_hk\ttype_hs\tvalue_hk\ttype_tsize\tvalue_tsize\tnew_nodes\tnew_bytes\tdead_have\tdead_let\tdead_beta\tdead_tsize\tunused_hyp\tunused_inst\tnbinders\textra\tdead_names\tclass").unwrap();

    let mut st = St {
        classes,
        npre: vec![0],
        ncomp: vec!["".into()],
        nh: vec![Hs::new(T_ANON).fin()],
        lh: vec![Hs::new(T_LZERO).fin()],
        lists: HashMap::new(),
        listh: Vec::new(),
        kind: Vec::new(),
        c1: Vec::new(),
        c2: Vec::new(),
        c3: Vec::new(),
        bname: Vec::new(),
        lit: HashMap::new(),
        hk: Vec::new(),
        hs: Vec::new(),
        ts: Vec::new(),
        mask: Vec::new(),
        class_of: HashMap::new(),
        project,
        nominal,
        own: Owner::default(),
        bad_lines: 0,
        cur_decl: 0,
        haves: HashMap::new(),
    };
    let mut line: Vec<u8> = Vec::with_capacity(1 << 20);
    let mut f1: Vec<(&[u8], &[u8])> = Vec::with_capacity(16);
    let mut f2: Vec<(&[u8], &[u8])> = Vec::with_capacity(16);
    let mut nlines: u64 = 0;
    let mut ndecl: u64 = 0;
    let mut kinds_count: HashMap<String, u64> = HashMap::new();
    let mut tot = Owner::default();
    let mut tot_unused_hyp = 0u64;
    let mut tot_unused_inst = 0u64;
    let mut range_start: usize = 0; // first expr index owned by the next declaration
    let mut decl_names: Vec<String> = Vec::new();
    let mut rehashed: u64 = 0;

    loop {
        line.clear();
        let n = rd.read_until(b'\n', &mut line).expect("read");
        if n == 0 {
            break;
        }
        nlines += 1;
        // f1/f2 borrow `line`; they are cleared before `line` is modified again.
        let l: &[u8] = unsafe { std::slice::from_raw_parts(line.as_ptr(), line.len()) };
        fields(l, 0, &mut f1);
        if f1.is_empty() {
            continue;
        }
        let (k0, v0) = f1[0];
        if k0 == b"in" {
            let idx = num(v0) as usize;
            if f1.len() < 2 {
                st.bad_lines += 1;
                continue;
            }
            let (k1, v1) = f1[1];
            fields(v1, 0, &mut f2);
            let pre = get(&f2, b"pre").map(num).unwrap_or(0) as usize;
            let ph = st.nhash(pre);
            let (h, comp) = if k1 == b"str" {
                let s = unquote(get(&f2, b"str").unwrap_or(b""));
                let sh = hash_bytes(T_NSTR, s);
                let mut h = Hs::new(T_NSTR);
                h.addh(&ph);
                h.addh(&sh);
                (h.fin(), String::from_utf8_lossy(s).into_owned())
            } else {
                let i = get(&f2, b"i").map(num).unwrap_or(0);
                let mut h = Hs::new(T_NNUM);
                h.addh(&ph);
                h.add(i);
                (h.fin(), format!("#{}", i))
            };
            setv(&mut st.nh, idx, h);
            setv(&mut st.npre, idx, pre as u32);
            if idx == st.ncomp.len() {
                st.ncomp.push(comp.into_boxed_str());
            } else {
                if idx > st.ncomp.len() {
                    st.ncomp.resize(idx + 1, "".into());
                }
                st.ncomp[idx] = comp.into_boxed_str();
            }
            continue;
        }
        if k0 == b"il" {
            let idx = num(v0) as usize;
            if f1.len() < 2 {
                st.bad_lines += 1;
                continue;
            }
            let (k1, v1) = f1[1];
            let h = match k1 {
                b"succ" => {
                    let mut h = Hs::new(T_LSUCC);
                    h.addh(&st.lhash(num(v1) as usize));
                    h.fin()
                }
                b"max" | b"imax" => {
                    let mut h = Hs::new(if k1 == b"max" { T_LMAX } else { T_LIMAX });
                    for x in nums(v1) {
                        h.addh(&st.lhash(x as usize));
                    }
                    h.fin()
                }
                b"param" => {
                    let mut h = Hs::new(T_LPARAM);
                    h.addh(&st.nhash(num(v1) as usize));
                    h.fin()
                }
                _ => {
                    st.bad_lines += 1;
                    Hs::new(0).fin()
                }
            };
            setv(&mut st.lh, idx, h);
            continue;
        }
        // expression?  ("ie" is the first or the last key)
        let (ie_v, kf) = if k0 == b"ie" && f1.len() >= 2 {
            (Some(v0), f1[1])
        } else if f1.len() >= 2 && f1[f1.len() - 1].0 == b"ie" {
            (Some(f1[f1.len() - 1].1), f1[0])
        } else {
            (None, f1[0])
        };
        if let Some(iev) = ie_v {
            let idx = num(iev) as usize;
            let (kk, kv) = kf;
            match kk {
                b"bvar" => st.push_node(idx, K_BVAR, num(kv) as u32, 0, 0, 0),
                b"sort" => st.push_node(idx, K_SORT, num(kv) as u32, 0, 0, 0),
                b"const" => {
                    fields(kv, 0, &mut f2);
                    let nm = get(&f2, b"name").map(num).unwrap_or(0) as u32;
                    let us: Vec<u32> = get(&f2, b"us").map(nums).unwrap_or_default().into_iter().map(|x| x as u32).collect();
                    let li = st.intern_list(us);
                    st.push_node(idx, K_CONST, nm, li, 0, 0);
                }
                b"app" => {
                    fields(kv, 0, &mut f2);
                    let fnn = get(&f2, b"fn").map(num).unwrap_or(0) as u32;
                    let arg = get(&f2, b"arg").map(num).unwrap_or(0) as u32;
                    st.push_node(idx, K_APP, fnn, arg, 0, 0);
                }
                b"lam" | b"forallE" => {
                    fields(kv, 0, &mut f2);
                    let ty = get(&f2, b"type").map(num).unwrap_or(0) as u32;
                    let body = get(&f2, b"body").map(num).unwrap_or(0) as u32;
                    let bi = get(&f2, b"binderInfo").map(binfo_code).unwrap_or(0);
                    let bn = get(&f2, b"name").map(num).unwrap_or(0) as u32;
                    let k = if kk == b"lam" { K_LAM } else { K_PI };
                    st.push_node(idx, k | (bi << 4), body, ty, 0, bn);
                }
                b"letE" => {
                    fields(kv, 0, &mut f2);
                    let ty = get(&f2, b"type").map(num).unwrap_or(0) as u32;
                    let val = get(&f2, b"value").map(num).unwrap_or(0) as u32;
                    let body = get(&f2, b"body").map(num).unwrap_or(0) as u32;
                    let nondep = get(&f2, b"nondep").map(|v| v == b"true").unwrap_or(false);
                    let bn = get(&f2, b"name").map(num).unwrap_or(0) as u32;
                    st.push_node(idx, K_LET, body, ty, val | if nondep { 0x8000_0000 } else { 0 }, bn);
                }
                b"natVal" | b"strVal" => {
                    let h = hash_bytes(if kk == b"natVal" { T_NAT } else { T_STR }, unquote(kv));
                    st.lit.insert(idx as u32, h);
                    st.push_node(idx, K_LIT, 0, 0, 0, 0);
                }
                b"mdata" => {
                    fields(kv, 0, &mut f2);
                    let e = get(&f2, b"expr").map(num).unwrap_or(0) as u32;
                    st.push_node(idx, K_MDATA, e, 0, 0, 0);
                }
                b"proj" => {
                    fields(kv, 0, &mut f2);
                    let tn = get(&f2, b"typeName").map(num).unwrap_or(0) as u32;
                    let pi = get(&f2, b"idx").map(num).unwrap_or(0) as u32;
                    let s_ = get(&f2, b"struct").map(num).unwrap_or(0) as u32;
                    st.push_node(idx, K_PROJ, s_, tn, pi, 0);
                }
                _ => {
                    st.bad_lines += 1;
                    st.push_node(idx, 0, 0, 0, 0, 0);
                }
            }
            st.own.new_nodes += 1;
            st.own.new_bytes += n as u64;
            continue;
        }
        // declaration (or meta) line
        st.own.new_bytes += n as u64;
        let v: serde_json::Value = match serde_json::from_slice(l) {
            Ok(v) => v,
            Err(_) => {
                st.bad_lines += 1;
                continue;
            }
        };
        let obj = match v.as_object() {
            Some(o) => o,
            None => continue,
        };
        let (dk, dv) = match obj.iter().next() {
            Some(x) => x,
            None => continue,
        };
        if dk == "meta" {
            continue;
        }
        ndecl += 1;
        *kinds_count.entry(dk.clone()).or_insert(0) += 1;
        let own = std::mem::take(&mut st.own);
        tot.new_nodes += own.new_nodes;
        tot.new_bytes += own.new_bytes;
        tot.dead_have += own.dead_have;
        tot.dead_let += own.dead_let;
        tot.dead_beta += own.dead_beta;
        tot.dead_tsize = tot.dead_tsize.saturating_add(own.dead_tsize);
        let range_end = st.kind.len();

        let mut rows: Vec<Row> = Vec::new();
        let mut cls: Vec<H> = Vec::new();
        match dk.as_str() {
            "thm" | "def" | "opaque" | "axiom" | "quot" => {
                let val = dv.get("value").and_then(|x| x.as_u64()).map(|x| x as usize);
                let (kind, extra, hk_): (&'static str, String, String) = match dk.as_str() {
                    "thm" => ("thm", String::new(), String::new()),
                    "def" => {
                        let hints = s(dv, "hints");
                        let hkind = if hints.contains("regular") { "regular".to_string() } else { hints.clone() };
                        ("def", format!("{} {}", hints, dv.get("safety").and_then(|x| x.as_str()).unwrap_or("")), hkind)
                    }
                    "opaque" => ("opaque", format!("unsafe={}", s(dv, "isUnsafe")), "opaque".into()),
                    "axiom" => ("axiom", format!("unsafe={}", s(dv, "isUnsafe")), String::new()),
                    _ => ("quot", s(dv, "kind"), String::new()),
                };
                let val = if kind == "axiom" || kind == "quot" { None } else { val };
                let r = mkrow(&st, kind, dv, val, extra);
                cls.push(row_class(&st, &r, &hk_));
                rows.push(r);
            }
            "inductive" => {
                let empty = Vec::new();
                let types = dv.get("types").and_then(|x| x.as_array()).unwrap_or(&empty);
                let ctors = dv.get("ctors").and_then(|x| x.as_array()).unwrap_or(&empty);
                let recs = dv.get("recs").and_then(|x| x.as_array()).unwrap_or(&empty);
                for t in types {
                    let ex = format!(
                        "params={} indices={} rec={} refl={} nested={} unsafe={} ctors={}",
                        s(t, "numParams"),
                        s(t, "numIndices"),
                        s(t, "isRec"),
                        s(t, "isReflexive"),
                        s(t, "numNested"),
                        s(t, "isUnsafe"),
                        t.get("ctors").and_then(|x| x.as_array()).map(|a| a.len()).unwrap_or(0)
                    );
                    rows.push(mkrow(&st, "ind", t, None, ex));
                }
                for c in ctors {
                    let ex = format!("cidx={} params={} fields={}", s(c, "cidx"), s(c, "numParams"), s(c, "numFields"));
                    rows.push(mkrow(&st, "ctor", c, None, ex));
                }
                for r in recs {
                    let mut rh = Hs::new(77);
                    let mut nr = 0;
                    for rule in r.get("rules").and_then(|x| x.as_array()).unwrap_or(&empty) {
                        rh.addh(&st.nhash(u(rule, "ctor")));
                        rh.add(u(rule, "nfields") as u64);
                        rh.addh(&st.hk[u(rule, "rhs")]);
                        nr += 1;
                    }
                    let ex = format!(
                        "k={} params={} indices={} motives={} minors={} rules={} rules_h={}",
                        s(r, "k"),
                        s(r, "numParams"),
                        s(r, "numIndices"),
                        s(r, "numMotives"),
                        s(r, "numMinors"),
                        nr,
                        hex(&rh.fin())
                    );
                    rows.push(mkrow(&st, "rec", r, None, ex));
                }
                if st.classes {
                    // block class with self-references normalized: placeholders for the block's own names, re-hash the
                    // owned expression range, hash the block, then the real classes and a second re-hash so that nodes
                    // shared with later declarations carry the final classes.
                    for (i, r) in rows.iter().enumerate() {
                        let mut h = Hs::new(5000);
                        h.add(i as u64);
                        st.class_of.insert(r.name_idx, h.fin());
                    }
                    for i in range_start..range_end {
                        st.hash_node(i);
                    }
                    rehashed += (range_end - range_start) as u64;
                    let mut bh = Hs::new(6000);
                    for r in rows.iter() {
                        if r.kind == "rec" {
                            continue; // recursors are determined by the types and constructors
                        }
                        bh.addh(&hash_bytes(1, r.kind.as_bytes()));
                        bh.addh(&r.lvlh);
                        bh.addh(&st.hk[r.ty]);
                        bh.addh(&hash_bytes(2, r.extra.as_bytes()));
                    }
                    let bh = bh.fin();
                    for (i, _r) in rows.iter().enumerate() {
                        let mut h = Hs::new(7000);
                        h.addh(&bh);
                        h.add(i as u64);
                        cls.push(h.fin());
                    }
                } else {
                    for r in rows.iter() {
                        cls.push(st.nhash(r.name_idx as usize));
                    }
                }
            }
            _ => {
                st.bad_lines += 1;
            }
        }
        if st.classes {
            let is_ind = dk == "inductive";
            let nominal = match (&st.project, &st.nominal) {
                (Some(set), _) => !rows.iter().all(|r| set.contains(&r.name)),
                (None, Some(nom)) => rows.iter().any(|r| nom.contains(&r.name)),
                (None, None) => false,
            };
            if nominal {
                // library constant: keep it nominal (its class is its name)
                for (ri, r) in rows.iter().enumerate() {
                    st.class_of.remove(&r.name_idx);
                    cls[ri] = st.nhash(r.name_idx as usize);
                }
            } else {
                for (r, c) in rows.iter().zip(cls.iter()) {
                    st.class_of.insert(r.name_idx, *c);
                }
            }
            if is_ind {
                for i in range_start..range_end {
                    st.hash_node(i);
                }
                rehashed += (range_end - range_start) as u64;
            }
        }
        range_start = range_end;
        decl_names.push(rows.first().map(|r| r.name.clone()).unwrap_or_default());
        st.cur_decl = decl_names.len() as u32;
        for (ri, r) in rows.iter().enumerate() {
            let o = if ri == 0 { own.clone() } else { Owner::default() };
            let dn: Vec<String> = o.dead_names.iter().map(|&b| st.name(b as usize)).collect();
            tot_unused_hyp += r.unused_hyp;
            tot_unused_inst += r.unused_inst;
            writeln!(
                out,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                r.kind,
                r.name,
                r.nlvl,
                hex(&r.lvlh),
                hex(&st.hk[r.ty]),
                hex(&st.hs[r.ty]),
                r.value.map(|v| hex(&st.hk[v])).unwrap_or_else(|| "-".into()),
                st.ts[r.ty],
                r.value.map(|v| st.ts[v]).unwrap_or(0),
                o.new_nodes,
                o.new_bytes,
                o.dead_have,
                o.dead_let,
                o.dead_beta,
                o.dead_tsize,
                r.unused_hyp,
                r.unused_inst,
                r.nbind,
                r.extra,
                if dn.is_empty() { "-".to_string() } else { dn.join(",") },
                hex(&cls[ri])
            )
            .unwrap();
        }
        if ndecl % 100000 == 0 {
            eprintln!("[{:.1}s] {} lines, {} decls, {} exprs", t0.elapsed().as_secs_f64(), nlines, ndecl, st.hk.len());
        }
    }
    out.flush().unwrap();
    // shared closed have/let values (the same closed sub-proof bound by `have`/`let` in >= 2 declarations)
    let mut hv = BufWriter::new(File::create(format!("{}/haves.tsv", args[2])).expect("haves"));
    writeln!(hv, "node\ttsize\tdecls\tbinder_names\tdecl_names").unwrap();
    let mut shared_haves = 0u64;
    let mut shared_have_redundant_tsize = 0u64;
    for (v, r) in st.haves.iter() {
        if r.count < 2 {
            continue;
        }
        shared_haves += 1;
        shared_have_redundant_tsize = shared_have_redundant_tsize.saturating_add(st.ts[*v as usize].saturating_mul((r.count - 1) as u64));
        let bn: Vec<String> = r.names.iter().map(|&b| st.name(b as usize)).collect();
        let dn: Vec<String> = r.decls.iter().map(|&d| decl_names.get(d as usize).cloned().unwrap_or_default()).collect();
        writeln!(hv, "{}\t{}\t{}\t{}\t{}", v, st.ts[*v as usize], r.count, bn.join(","), dn.join(" ")).unwrap();
    }
    hv.flush().unwrap();
    eprintln!("shared closed have/let values: {} (redundant tree size {})", shared_haves, shared_have_redundant_tsize);
    let mut sj = BufWriter::new(File::create(format!("{}/summary.json", args[2])).expect("summary"));
    let kc: Vec<String> = kinds_count.iter().map(|(k, v)| format!("\"{}\": {}", k, v)).collect();
    writeln!(
        sj,
        "{{\"export\": {:?}, \"classes_mode\": {}, \"lines\": {}, \"decl_lines\": {}, \"names\": {}, \"levels\": {}, \"exprs\": {}, \"rehashed_nodes\": {}, \"bad_lines\": {}, \"kinds\": {{{}}}, \"dead_have\": {}, \"dead_let\": {}, \"dead_beta\": {}, \"dead_tsize\": {}, \"unused_hyp\": {}, \"unused_inst\": {}, \"seconds\": {:.1}}}",
        args[1],
        st.classes,
        nlines,
        ndecl,
        st.nh.len(),
        st.lh.len(),
        st.hk.len(),
        rehashed,
        st.bad_lines,
        kc.join(", "),
        tot.dead_have,
        tot.dead_let,
        tot.dead_beta,
        tot.dead_tsize,
        tot_unused_hyp,
        tot_unused_inst,
        t0.elapsed().as_secs_f64()
    )
    .unwrap();
    eprintln!("done in {:.1}s: {} lines, {} decls, {} exprs, bad {}", t0.elapsed().as_secs_f64(), nlines, ndecl, st.hk.len(), st.bad_lines);
}
