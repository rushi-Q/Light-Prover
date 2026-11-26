//! Persistent multi-query warm mode for `gruszka` (veto-only second kernel).
//!
//!   gruszka --warm-base BASE_EXPORT [WORKERS]
//!
//! 1. Loads and verifies EVERY declaration of `BASE_EXPORT` from scratch (exact unchanged checker).
//!    Refuses to start if `BASE_EXPORT` is rejected or declined.
//! 2. Builds an immutable reverse-dependency graph + canonical-to-raw name index on `BASE_EXPORT`.
//! 3. After all verification worker threads have joined (process is 100% single-threaded), enters
//!    a stdin command loop. For each `CHECK_DELTA\tNONCE\tDELTA_PATH` or `CHECK_FULL\tNONCE\tFULL_PATH`:
//!    - `fork()`s a Copy-on-Write child (zero copy of base env, zero cross-query memory leaks or state).
//!    - In `CHECK_DELTA`, the child appends `DELTA_PATH`'s strings into the reserved anonymous tail
//!      after `env.bytes`, interns delta names/levels/exprs into `env` starting at `base_main_len`,
//!      computes `overridden` and `dirty` (failing closed to `"fallback"` if any kernel-implicit or
//!      Quot constant is touched), masks out every `dirty` base constant in `row_of_canon` and
//!      `row_of_name`, installs the delta declarations, and runs the UNCHANGED `tc::Worker::check_decl`
//!      on the new/resupplied declarations.
//!    - Emits ONE structured JSON object per query on stdout.

use crate::env::{
    self, CKind, ConstInfo, Env, Hint, LitVal, NONE, ThmVal, APP, BVAR, CONST, LAM, LET, NAT, PI,
    PROJ, SORT, STR, is_lam, is_pi,
};
use crate::tc::{self, Stop, Worker};
use num_bigint::BigUint;
use rustc_hash::{FxHashMap, FxHashSet};
use std::io::{BufRead, Read, Write};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, AtomicU32, Ordering};
use std::time::Instant;
use susz::canon::Part;

const ST_OK: u8 = 1;
const ST_REJECT: u8 = 2;
const ST_DECLINE: u8 = 3;
const ST_CANCEL: u8 = 4;

const TAIL_BYTES: usize = 256 << 20; // 256 MiB anonymous VA tail for zero-copy delta string appends

const IMPLICIT_NAMES: &[&str] = &[
    "Nat", "Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd",
    "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight",
    "String", "String.ofList", "String.mk", "Char", "Char.ofNat", "List", "List.cons", "List.nil",
    "Bool", "Bool.true", "Bool.false", "eagerReduce", "Eq", "Eq.refl",
    "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "dontcare",
    "optParam", "autoParam", "semiOutParam", "outParam",
];

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn emit_json(
    nonce: &str,
    status: &str,
    msg: &str,
    delta_consts: usize,
    overridden: usize,
    dirty: usize,
    eff: usize,
    checked: usize,
    ms: u128,
) -> String {
    format!(
        "{{\"nonce\":{},\"leg\":\"gruszka\",\"status\":{},\"delta_consts\":{},\"overridden\":{},\"dirty\":{},\"eff\":{},\"checked\":{},\"ms\":{},\"msg\":{}}}",
        json_escape(nonce),
        json_escape(status),
        delta_consts,
        overridden,
        dirty,
        eff,
        checked,
        ms,
        json_escape(msg),
    )
}

#[cfg(unix)]
unsafe fn alloc_bytes_with_tail(src: &[u8]) -> (*mut u8, usize) {
    unsafe extern "C" {
        fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    }
    const PROT_RW: i32 = 1 | 2;
    const MAP_PRIVATE: i32 = 2;
    const MAP_ANON: i32 = 0x20;
    const MAP_NORESERVE: i32 = 0x4000;
    let total = src.len() + TAIL_BYTES;
    let p = unsafe { mmap(std::ptr::null_mut(), total, PROT_RW, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0) };
    assert!(!p.is_null() && p as isize != -1, "mmap for base bytes + tail failed");
    unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), p, src.len()) };
    (p, total)
}

/// Run unchanged `tc::Worker::check_decl` over `decls` (joining all worker threads before returning).
fn check_decl_subset(
    env: &'static Env<'static>,
    decls: &[u32],
    workers: usize,
) -> Result<(), (u8, String)> {
    if decls.is_empty() {
        return Ok(());
    }
    let wcount = workers.min(decls.len()).max(1);
    let workers = match env::region().layout(env.main.len(), wcount) {
        Ok(w) => w,
        Err(m) => return Err((ST_DECLINE, m)),
    };
    tc::set_workers(workers);
    let nd = env.decl_rows.len();
    let shared = Box::new(tc::Shared::new(env.main.len(), env.consts.len()));
    let shared_ref: &'static tc::Shared = unsafe { &*(&*shared as *const tc::Shared) };
    let first_fail = Box::new(AtomicU32::new(u32::MAX));
    let ff_ref: &'static AtomicU32 = unsafe { &*(&*first_fail as *const AtomicU32) };
    let status: Vec<AtomicU8> = (0..nd).map(|_| AtomicU8::new(0)).collect();
    let msgs: Mutex<Vec<(u32, String)>> = Mutex::new(Vec::new());

    let stack: usize = std::env::var("GRUSZKA_STACK_MB")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&m| (4..=1 << 20).contains(&m))
        .map_or(256 << 20, |m| m << 20);
    let stack_limit = stack - (stack / 4).min(64 << 20);

    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let chunk: usize = if decls.len() <= 64 { 1 } else { 32 };

    std::thread::scope(|s| {
        for _wi in 0..workers {
            let (status, msgs, next_idx) = (&status, &msgs, &next_idx);
            std::thread::Builder::new()
                .stack_size(stack)
                .spawn_scoped(s, move || {
                    let mut w = Worker::new(env, shared_ref, ff_ref, stack_limit);
                    loop {
                        let start = next_idx.fetch_add(chunk, Ordering::Relaxed);
                        if start >= decls.len() {
                            break;
                        }
                        let end = (start + chunk).min(decls.len());
                        for &d32 in &decls[start..end] {
                            let d = d32 as usize;
                            if d32 > ff_ref.load(Ordering::Relaxed) {
                                status[d].store(ST_CANCEL, Ordering::Relaxed);
                                continue;
                            }
                            let mut r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                w.check_decl(d32)
                            }));
                            if w.arena_full && !matches!(r, Ok(Ok(()) | Err(Stop::Cancel))) {
                                if r.is_err() {
                                    w.after_panic();
                                }
                                let mut g = env::region().big.lock().unwrap_or_else(|e| e.into_inner());
                                let big = g.as_mut().expect("overflow arenas");
                                w.swap_big(big);
                                r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                    w.check_decl(d32)
                                }));
                                if r.is_err() {
                                    w.after_panic();
                                }
                                if w.arena_full && matches!(r, Ok(Err(Stop::Reject))) {
                                    r = Ok(tc::decline("the block arena is full"));
                                }
                                w.swap_big(big);
                            }
                            let (st, msg) = match r {
                                Ok(Ok(())) => (ST_OK, None),
                                Ok(Err(Stop::Reject)) => (ST_REJECT, Some(tc::stop_msg())),
                                Ok(Err(Stop::Decline)) => (ST_DECLINE, Some(tc::stop_msg())),
                                Ok(Err(Stop::Cancel)) => (ST_CANCEL, None),
                                Ok(Err(Stop::Budget)) => (ST_DECLINE, Some("probe budget escaped".into())),
                                Ok(Err(Stop::Deep)) => (ST_DECLINE, Some("deep whnf escaped".into())),
                                Ok(Err(Stop::Ground)) => (ST_DECLINE, Some("ground machine stop escaped".into())),
                                Ok(Err(Stop::DeepInfer)) => (ST_DECLINE, Some("deep inference escaped".into())),
                                Ok(Err(Stop::DeepDefeq)) => (ST_DECLINE, Some("deep comparison escaped".into())),
                                Err(p) => {
                                    w.after_panic();
                                    let m = p
                                        .downcast_ref::<String>()
                                        .cloned()
                                        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                                        .unwrap_or_default();
                                    (ST_DECLINE, Some(format!("internal error: {m}")))
                                }
                            };
                            if st == ST_REJECT || st == ST_DECLINE {
                                ff_ref.fetch_min(d32, Ordering::Relaxed);
                                msgs.lock().unwrap().push((d32, msg.unwrap_or_default()));
                            }
                            status[d].store(st, Ordering::Relaxed);
                        }
                    }
                    drop(w);
                })
                .expect("spawn worker");
        }
    });
    env::region().reset_next();
    let msgs = msgs.into_inner().unwrap();
    for &d32 in decls {
        let d = d32 as usize;
        match status[d].load(Ordering::Relaxed) {
            ST_OK => continue,
            st @ (ST_REJECT | ST_DECLINE) => {
                let m = msgs.iter().find(|x| x.0 == d32).map(|x| x.1.clone()).unwrap_or_default();
                let (first, _) = env.decl_rows[d];
                let name = env.name_str(env.consts[first as usize].name);
                return Err((st, format!("{name}: {m}")));
            }
            _ => return Err((ST_DECLINE, format!("declaration {d} was not checked"))),
        }
    }
    Ok(())
}

/// Immutable reverse-dependency index & canonical-to-raw name map for verified base `Env`.
struct BaseGraph {
    base_bytes_ptr: *mut u8,
    base_bytes_len: usize,
    base_bytes_cap: usize,
    base_main_len: usize,
    base_consts_len: usize,
    base_decls_len: usize,
    /// CSR reverse dependency graph on base decls: `d` -> decls that reference any constant of `d`.
    rev_start: Vec<u32>,
    rev_adj: Vec<u32>,
    /// CSR canonical name id -> all base raw name ids with that canonical id.
    raw_start: Vec<u32>,
    raw_adj: Vec<u32>,
    /// Canonical ids of kernel-implicit and Quotient names present in base.
    implicit_canons: FxHashSet<u32>,
}

fn collect_main_expr_refs(
    env: &Env<'_>,
    root: u32,
    visited: &mut FxHashSet<u32>,
    out_canons: &mut Vec<u32>,
) {
    let mut stack = vec![root];
    let nodes = env.main.n();
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        let n = nodes[id as usize];
        match n.kind {
            CONST => out_canons.push(env.canon(n.a)),
            APP => {
                stack.push(n.a);
                stack.push(n.b);
            }
            k if is_lam(k) || is_pi(k) => {
                stack.push(n.a);
                stack.push(n.b);
            }
            LET => {
                stack.push(n.a);
                stack.push(n.b);
                stack.push(env.side.lets[n.p as usize].1);
            }
            PROJ => {
                out_canons.push(env.canon(n.p));
                stack.push(n.a);
            }
            _ => {}
        }
    }
}

fn build_base_graph(
    env: &Env<'_>,
    base_bytes_ptr: *mut u8,
    base_bytes_len: usize,
    base_bytes_cap: usize,
    workers: usize,
) -> BaseGraph {
    let nd = env.decl_rows.len();
    let n_canon = env.st.canon.pre.len();

    // 1. Canonical id -> raw name ids CSR
    let mut raw_start = vec![0u32; n_canon + 1];
    for &c in &env.st.name_canon {
        raw_start[c as usize + 1] += 1;
    }
    for i in 0..n_canon {
        raw_start[i + 1] += raw_start[i];
    }
    let mut fill = raw_start.clone();
    let mut raw_adj = vec![0u32; env.st.name_canon.len()];
    for (rid, &c) in env.st.name_canon.iter().enumerate() {
        let pos = fill[c as usize] as usize;
        raw_adj[pos] = rid as u32;
        fill[c as usize] += 1;
    }

    // 2. Forward decl -> decl edges (in parallel across chunks)
    let nt = workers.clamp(1, 32);
    let decl_deps: Vec<Vec<u32>> = if nd == 0 {
        Vec::new()
    } else {
        let mut all_deps = vec![Vec::new(); nd];
        let chunk = (nd + nt - 1) / nt;
        std::thread::scope(|s| {
            let mut handles = Vec::new();
            for (ci, slice) in all_deps.chunks_mut(chunk).enumerate() {
                let d0 = ci * chunk;
                handles.push(s.spawn(move || {
                    let mut vis = FxHashSet::default();
                    let mut canons = Vec::new();
                    let mut seen_d = FxHashSet::default();
                    for (off, dst) in slice.iter_mut().enumerate() {
                        let d = d0 + off;
                        let (first, count) = env.decl_rows[d];
                        vis.clear();
                        canons.clear();
                        seen_d.clear();
                        for r in first..first + count {
                            let c = &env.consts[r as usize];
                            collect_main_expr_refs(env, c.ty, &mut vis, &mut canons);
                            match &c.kind {
                                CKind::Defn { value, .. } | CKind::Opaque { value, .. } => {
                                    collect_main_expr_refs(env, *value, &mut vis, &mut canons);
                                }
                                CKind::Thm { value: ThmVal::Main(v), .. } => {
                                    collect_main_expr_refs(env, *v, &mut vis, &mut canons);
                                }
                                CKind::Thm { value: ThmVal::Block(bi), .. } => {
                                    let blk = env.blocks[*bi as usize];
                                    let mut br = susz::read::Block::new(env.bytes, &env.st, blk).without_rule_p();
                                    while let Some(Ok((_, ex))) = br.next() {
                                        match ex {
                                            susz::read::Expr::Const(nm, _) => canons.push(env.canon(nm)),
                                            susz::read::Expr::Proj(sn, _, x) => {
                                                canons.push(env.canon(sn));
                                                if let susz::read::Ref::Main(am) = x {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                            }
                                            susz::read::Expr::App(f, x) => {
                                                if let susz::read::Ref::Main(am) = f {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                                if let susz::read::Ref::Main(am) = x {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                            }
                                            susz::read::Expr::Lam(_, _, t, bd) | susz::read::Expr::Pi(_, _, t, bd) => {
                                                if let susz::read::Ref::Main(am) = t {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                                if let susz::read::Ref::Main(am) = bd {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                            }
                                            susz::read::Expr::Let(_, t, v, bd) => {
                                                if let susz::read::Ref::Main(am) = t {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                                if let susz::read::Ref::Main(am) = v {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                                if let susz::read::Ref::Main(am) = bd {
                                                    collect_main_expr_refs(env, am, &mut vis, &mut canons);
                                                }
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                                CKind::Induct { all, ctors, .. } => {
                                    for &nm in all.iter().chain(ctors.iter()) {
                                        canons.push(env.canon(nm));
                                    }
                                }
                                CKind::Ctor { induct, .. } => canons.push(env.canon(*induct)),
                                CKind::Rec { all, rules, .. } => {
                                    for &nm in all.iter() {
                                        canons.push(env.canon(nm));
                                    }
                                    for &(ctor, _, rhs) in rules.iter() {
                                        canons.push(env.canon(ctor));
                                        collect_main_expr_refs(env, rhs, &mut vis, &mut canons);
                                    }
                                }
                                CKind::Quot { .. } => {
                                    if env.known.eq != NONE {
                                        canons.push(env.known.eq);
                                    }
                                }
                                CKind::Axiom { .. } => {}
                            }
                        }
                        for &cn in &canons {
                            let row = env.known_row(cn);
                            if row != NONE {
                                let td = env.consts[row as usize].decl;
                                if td != d as u32 && seen_d.insert(td) {
                                    dst.push(td);
                                }
                            }
                        }
                    }
                }));
            }
            for h in handles {
                h.join().unwrap();
            }
        });
        all_deps
    };

    // 3. Build CSR reverse adjacency list over decl_deps
    let mut rev_start = vec![0u32; nd + 1];
    for ds in &decl_deps {
        for &td in ds {
            rev_start[td as usize + 1] += 1;
        }
    }
    for i in 0..nd {
        rev_start[i + 1] += rev_start[i];
    }
    let mut rfill = rev_start.clone();
    let mut rev_adj = vec![0u32; rev_start[nd] as usize];
    for (d, ds) in decl_deps.iter().enumerate() {
        for &td in ds {
            let pos = rfill[td as usize] as usize;
            rev_adj[pos] = d as u32;
            rfill[td as usize] += 1;
        }
    }

    // 4. Implicit + Quot canonical ids present in base
    let mut implicit_canons = FxHashSet::default();
    for &dotted in IMPLICIT_NAMES {
        let mut c = susz::canon::ANON;
        let mut ok = true;
        for part in dotted.split('.') {
            match env.st.canon.find(env.bytes, c, Part::Str(part.as_bytes())) {
                Some(x) => c = x,
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if ok {
            implicit_canons.insert(c);
        }
    }

    BaseGraph {
        base_bytes_ptr,
        base_bytes_len,
        base_bytes_cap,
        base_main_len: env.main.len(),
        base_consts_len: env.consts.len(),
        base_decls_len: nd,
        rev_start,
        rev_adj,
        raw_start,
        raw_adj,
        implicit_canons,
    }
}

// ---------------------------------------------------------------------------
// Minimal strict RFC 8259 JSON parser for delta NDJSON (typically 10 KB - 2 MB)

#[derive(Debug)]
enum JVal {
    Int(u64),
    Big(String),
    Str(String),
    Bool(bool),
    Null,
    Arr(Vec<JVal>),
    Obj(Vec<(String, JVal)>),
}

impl JVal {
    fn as_obj(&self) -> Result<&[(String, JVal)], String> {
        match self {
            JVal::Obj(v) => Ok(v),
            _ => Err("expected JSON object".into()),
        }
    }
    fn get(&self, key: &str) -> Option<&JVal> {
        self.as_obj().ok()?.iter().find(|(k, _)| k == key).map(|(_, v)| v)
    }
    fn as_u64(&self) -> Result<u64, String> {
        match self {
            JVal::Int(v) => Ok(*v),
            _ => Err("expected u64".into()),
        }
    }
    fn as_str(&self) -> Result<&str, String> {
        match self {
            JVal::Str(s) => Ok(s),
            _ => Err("expected string".into()),
        }
    }
    fn as_bool(&self) -> Result<bool, String> {
        match self {
            JVal::Bool(b) => Ok(*b),
            _ => Err("expected bool".into()),
        }
    }
    fn as_arr(&self) -> Result<&[JVal], String> {
        match self {
            JVal::Arr(a) => Ok(a),
            _ => Err("expected array".into()),
        }
    }
}

struct JParser<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> JParser<'a> {
    fn ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\r' | b'\n') {
            self.i += 1;
        }
    }
    fn parse(s: &'a [u8]) -> Result<JVal, String> {
        let mut p = JParser { b: s, i: 0 };
        p.ws();
        let v = p.val()?;
        p.ws();
        if p.i != p.b.len() {
            return Err("trailing bytes in JSON".into());
        }
        Ok(v)
    }
    fn val(&mut self) -> Result<JVal, String> {
        self.ws();
        let c = *self.b.get(self.i).ok_or_else(|| "unexpected EOF".to_string())?;
        match c {
            b'{' => {
                self.i += 1;
                self.ws();
                let mut m = Vec::new();
                if self.b.get(self.i) == Some(&b'}') {
                    self.i += 1;
                    return Ok(JVal::Obj(m));
                }
                loop {
                    self.ws();
                    let k = self.str()?;
                    self.ws();
                    if self.b.get(self.i) != Some(&b':') {
                        return Err("expected ':'".into());
                    }
                    self.i += 1;
                    let v = self.val()?;
                    m.push((k, v));
                    self.ws();
                    match self.b.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b'}') => {
                            self.i += 1;
                            return Ok(JVal::Obj(m));
                        }
                        _ => return Err("expected ',' or '}'".into()),
                    }
                }
            }
            b'[' => {
                self.i += 1;
                self.ws();
                let mut a = Vec::new();
                if self.b.get(self.i) == Some(&b']') {
                    self.i += 1;
                    return Ok(JVal::Arr(a));
                }
                loop {
                    a.push(self.val()?);
                    self.ws();
                    match self.b.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b']') => {
                            self.i += 1;
                            return Ok(JVal::Arr(a));
                        }
                        _ => return Err("expected ',' or ']'".into()),
                    }
                }
            }
            b'"' => Ok(JVal::Str(self.str()?)),
            b't' if self.b[self.i..].starts_with(b"true") => {
                self.i += 4;
                Ok(JVal::Bool(true))
            }
            b'f' if self.b[self.i..].starts_with(b"false") => {
                self.i += 5;
                Ok(JVal::Bool(false))
            }
            b'n' if self.b[self.i..].starts_with(b"null") => {
                self.i += 4;
                Ok(JVal::Null)
            }
            b'0'..=b'9' => {
                let start = self.i;
                if c == b'0' && matches!(self.b.get(self.i + 1), Some(b'0'..=b'9')) {
                    return Err("leading zero".into());
                }
                while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
                    self.i += 1;
                }
                let txt = std::str::from_utf8(&self.b[start..self.i]).map_err(|_| "utf8")?;
                match txt.parse::<u64>() {
                    Ok(v) => Ok(JVal::Int(v)),
                    Err(_) => Ok(JVal::Big(txt.to_string())),
                }
            }
            _ => Err(format!("unexpected char '{}'", c as char)),
        }
    }
    fn hex4(&mut self) -> Result<u32, String> {
        if self.i + 4 > self.b.len() {
            return Err("truncated \\u".into());
        }
        let s = std::str::from_utf8(&self.b[self.i..self.i + 4]).map_err(|_| "utf8")?;
        self.i += 4;
        u32::from_str_radix(s, 16).map_err(|_| "bad hex".into())
    }
    fn str(&mut self) -> Result<String, String> {
        if self.b.get(self.i) != Some(&b'"') {
            return Err("expected '\"'".into());
        }
        self.i += 1;
        let mut out = Vec::new();
        while self.i < self.b.len() {
            let c = self.b[self.i];
            self.i += 1;
            match c {
                b'"' => return String::from_utf8(out).map_err(|_| "invalid utf8 in string".into()),
                b'\\' => {
                    let e = *self.b.get(self.i).ok_or_else(|| "eof in escape".to_string())?;
                    self.i += 1;
                    match e {
                        b'"' => out.push(b'"'),
                        b'\\' => out.push(b'\\'),
                        b'/' => out.push(b'/'),
                        b'b' => out.push(0x08),
                        b'f' => out.push(0x0c),
                        b'n' => out.push(b'\n'),
                        b'r' => out.push(b'\r'),
                        b't' => out.push(b'\t'),
                        b'u' => {
                            let h1 = self.hex4()?;
                            let cp = if (0xD800..=0xDBFF).contains(&h1) {
                                if !self.b[self.i..].starts_with(b"\\u") {
                                    return Err("unpaired high surrogate".into());
                                }
                                self.i += 2;
                                let h2 = self.hex4()?;
                                if !(0xDC00..=0xDFFF).contains(&h2) {
                                    return Err("bad low surrogate".into());
                                }
                                0x10000 + (((h1 - 0xD800) << 10) | (h2 - 0xDC00))
                            } else {
                                h1
                            };
                            let ch = char::from_u32(cp).ok_or_else(|| "invalid unicode".to_string())?;
                            let mut buf = [0u8; 4];
                            out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                        }
                        _ => return Err("unknown escape".into()),
                    }
                }
                c if c < 0x20 => return Err("raw control char in JSON string".into()),
                _ => out.push(c),
            }
        }
        Err("unterminated string".into())
    }
}

fn parse_binder(s: &str) -> Result<u8, String> {
    match s {
        "default" => Ok(0),
        "implicit" => Ok(1),
        "strictImplicit" => Ok(2),
        "instImplicit" => Ok(3),
        _ => Err(format!("bad binderInfo '{s}'")),
    }
}

fn parse_hint(v: &JVal) -> Result<Hint, String> {
    match v {
        JVal::Str(s) if s == "opaque" => Ok(Hint::Opaque),
        JVal::Str(s) if s == "abbrev" => Ok(Hint::Abbrev),
        JVal::Obj(_) => {
            let h = v.get("regular").ok_or("bad hints")?.as_u64()?;
            Ok(Hint::Regular(u32::try_from(h).unwrap_or(u32::MAX)))
        }
        _ => Err("bad hints".into()),
    }
}

fn parse_safety(s: &str) -> Result<u8, String> {
    match s {
        "safe" => Ok(0),
        "unsafe" => Ok(1),
        "partial" => Ok(2),
        _ => Err(format!("bad safety '{s}'")),
    }
}

/// Structural expression equality in `Env` (handles comparing MAIN nodes; ignores binder names).
fn expr_eq_main(env: &Env<'_>, a: u32, b: u32, memo: &mut FxHashMap<(u32, u32), bool>) -> bool {
    if a == b {
        return true;
    }
    if let Some(&r) = memo.get(&(a, b)) {
        return r;
    }
    let na = env.main.n()[a as usize];
    let nb = env.main.n()[b as usize];
    let ok = if na.kind != nb.kind {
        false
    } else {
        match na.kind {
            BVAR => na.p == nb.p,
            SORT => na.p == nb.p,
            CONST => env.canon(na.a) == env.canon(nb.a) && na.p == nb.p,
            APP => expr_eq_main(env, na.a, nb.a, memo) && expr_eq_main(env, na.b, nb.b, memo),
            k if is_lam(k) || is_pi(k) => {
                expr_eq_main(env, na.a, nb.a, memo) && expr_eq_main(env, na.b, nb.b, memo)
            }
            LET => {
                let la = env.side.lets[na.p as usize];
                let lb = env.side.lets[nb.p as usize];
                expr_eq_main(env, na.a, nb.a, memo)
                    && expr_eq_main(env, na.b, nb.b, memo)
                    && expr_eq_main(env, la.1, lb.1, memo)
            }
            NAT | STR => env.lits[na.p as usize] == env.lits[nb.p as usize],
            PROJ => {
                na.b == nb.b
                    && env.canon(na.p) == env.canon(nb.p)
                    && expr_eq_main(env, na.a, nb.a, memo)
            }
            _ => false,
        }
    };
    memo.insert((a, b), ok);
    ok
}

fn lparams_eq(env: &Env<'_>, a: &[u32], b: &[u32]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(&x, &y)| env.canon(x) == env.canon(y))
}

fn names_eq(env: &Env<'_>, a: &[u32], b: &[u32]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(&x, &y)| env.canon(x) == env.canon(y))
}

fn lvls_slice_eq(env: &Env<'_>, p: u32, ls: &[u32]) -> bool {
    if p == 0 {
        return ls.is_empty();
    }
    let n = env.side.lvls[p as usize] as usize;
    n == ls.len() && &env.side.lvls[p as usize + 1..p as usize + 1 + n] == ls
}

enum BlkNode {
    BVar(u32),
    Sort(u32),
    Const(u32, Box<[u32]>),
    App(susz::read::Ref, susz::read::Ref),
    Lam(u8, susz::read::Ref, susz::read::Ref),
    Pi(u8, susz::read::Ref, susz::read::Ref),
    Let(susz::read::Ref, susz::read::Ref, susz::read::Ref),
    Nat(BigUint),
    Str(Box<str>),
    Proj(u32, u32, susz::read::Ref),
}

/// Exact structural comparison of a `ThmVal::Block(bi)` against a MAIN expression `main_id`.
fn expr_eq_block_main(env: &Env<'_>, bi: u32, main_id: u32) -> bool {
    let b = env.blocks[bi as usize];
    let mut bnodes: Vec<BlkNode> = Vec::new();
    let lmap = |l: u32| -> u32 { if env.lvl_map.is_empty() { l } else { env.lvl_map[l as usize] } };
    let r: Result<(), susz::read::Stop<()>> = susz::read::decode_block(env.bytes, &env.st, b, |_k, e| {
        let bn = match *e {
            susz::read::Expr::BVar(i) => BlkNode::BVar(u32::try_from(i).unwrap_or(u32::MAX - 1)),
            susz::read::Expr::Sort(l) => BlkNode::Sort(lmap(l)),
            susz::read::Expr::Const(n, ls) => {
                let gls: Vec<u32> = ls.iter().map(lmap).collect();
                BlkNode::Const(n, gls.into_boxed_slice())
            }
            susz::read::Expr::App(f, x) => BlkNode::App(f, x),
            susz::read::Expr::Lam(bi, _n, t, bd) => BlkNode::Lam(bi, t, bd),
            susz::read::Expr::Pi(bi, _n, t, bd) => BlkNode::Pi(bi, t, bd),
            susz::read::Expr::Let(_n, t, v, bd) => BlkNode::Let(t, v, bd),
            susz::read::Expr::Nat(bytes) => BlkNode::Nat(BigUint::from_bytes_le(bytes)),
            susz::read::Expr::Str(s) => BlkNode::Str(s.into()),
            susz::read::Expr::Proj(sn, f, x) => BlkNode::Proj(sn, u32::try_from(f).unwrap_or(u32::MAX), x),
        };
        bnodes.push(bn);
        Ok(())
    });
    if r.is_err() || bnodes.is_empty() {
        return false;
    }
    fn cmp_ref(
        env: &Env<'_>,
        bnodes: &[BlkNode],
        a: susz::read::Ref,
        b: u32,
        memo_m: &mut FxHashMap<(u32, u32), bool>,
        memo_b: &mut FxHashMap<(u32, u32), bool>,
    ) -> bool {
        match a {
            susz::read::Ref::Main(am) => expr_eq_main(env, am, b, memo_m),
            susz::read::Ref::Block(bk) => {
                if let Some(&res) = memo_b.get(&(bk, b)) {
                    return res;
                }
                let nb = env.main.n()[b as usize];
                let ok = match &bnodes[bk as usize] {
                    BlkNode::BVar(i) => nb.kind == BVAR && *i == nb.p,
                    BlkNode::Sort(l) => nb.kind == SORT && *l == nb.p,
                    BlkNode::Const(n, ls) => {
                        nb.kind == CONST && env.canon(*n) == env.canon(nb.a) && lvls_slice_eq(env, nb.p, ls)
                    }
                    BlkNode::App(f, x) => {
                        nb.kind == APP
                            && cmp_ref(env, bnodes, *f, nb.a, memo_m, memo_b)
                            && cmp_ref(env, bnodes, *x, nb.b, memo_m, memo_b)
                    }
                    BlkNode::Lam(bi, t, bd) => {
                        nb.kind == LAM + *bi
                            && cmp_ref(env, bnodes, *t, nb.a, memo_m, memo_b)
                            && cmp_ref(env, bnodes, *bd, nb.b, memo_m, memo_b)
                    }
                    BlkNode::Pi(bi, t, bd) => {
                        nb.kind == PI + *bi
                            && cmp_ref(env, bnodes, *t, nb.a, memo_m, memo_b)
                            && cmp_ref(env, bnodes, *bd, nb.b, memo_m, memo_b)
                    }
                    BlkNode::Let(t, v, bd) => {
                        if nb.kind != LET {
                            false
                        } else {
                            let lb = env.side.lets[nb.p as usize];
                            cmp_ref(env, bnodes, *t, nb.a, memo_m, memo_b)
                                && cmp_ref(env, bnodes, *v, nb.b, memo_m, memo_b)
                                && cmp_ref(env, bnodes, *bd, lb.1, memo_m, memo_b)
                        }
                    }
                    BlkNode::Nat(v) => nb.kind == NAT && matches!(&env.lits[nb.p as usize], LitVal::Nat(x) if x == v),
                    BlkNode::Str(s) => nb.kind == STR && matches!(&env.lits[nb.p as usize], LitVal::Str(x) if x.as_ref() == s.as_ref()),
                    BlkNode::Proj(sn, f, x) => {
                        nb.kind == PROJ
                            && *f == nb.b
                            && env.canon(*sn) == env.canon(nb.p)
                            && cmp_ref(env, bnodes, *x, nb.a, memo_m, memo_b)
                    }
                };
                memo_b.insert((bk, b), ok);
                ok
            }
        }
    }
    let mut memo_m = FxHashMap::default();
    let mut memo_b = FxHashMap::default();
    cmp_ref(env, &bnodes, susz::read::Ref::Block(bnodes.len() as u32 - 1), main_id, &mut memo_m, &mut memo_b)
}

/// Exact structural comparison of a delta constant against an existing base constant.
fn const_eq_base(env: &Env<'_>, base: &ConstInfo, delta: &ConstInfo) -> bool {
    if env.canon(base.name) != env.canon(delta.name) || !lparams_eq(env, &base.lparams, &delta.lparams) {
        return false;
    }
    let mut memo = FxHashMap::default();
    if !expr_eq_main(env, base.ty, delta.ty, &mut memo) {
        return false;
    }
    match (&base.kind, &delta.kind) {
        (CKind::Axiom { unsafe_: u1 }, CKind::Axiom { unsafe_: u2 }) => u1 == u2,
        (
            CKind::Defn { value: v1, hint: h1, safety: s1, all: a1 },
            CKind::Defn { value: v2, hint: h2, safety: s2, all: a2 },
        ) => h1 == h2 && s1 == s2 && names_eq(env, a1, a2) && expr_eq_main(env, *v1, *v2, &mut memo),
        (
            CKind::Thm { value: ThmVal::Main(v1), all: a1 },
            CKind::Thm { value: ThmVal::Main(v2), all: a2 },
        ) => names_eq(env, a1, a2) && expr_eq_main(env, *v1, *v2, &mut memo),
        (
            CKind::Thm { value: ThmVal::Block(bi), all: a1 },
            CKind::Thm { value: ThmVal::Main(v2), all: a2 },
        ) => names_eq(env, a1, a2) && expr_eq_block_main(env, *bi, *v2),
        (
            CKind::Opaque { value: v1, unsafe_: u1, all: a1 },
            CKind::Opaque { value: v2, unsafe_: u2, all: a2 },
        ) => u1 == u2 && names_eq(env, a1, a2) && expr_eq_main(env, *v1, *v2, &mut memo),
        (CKind::Quot { kind: k1 }, CKind::Quot { kind: k2 }) => k1 == k2,
        (
            CKind::Induct { nparams: p1, nindices: i1, all: a1, ctors: c1, nnested: n1, is_rec: r1, is_reflexive: f1, unsafe_: u1 },
            CKind::Induct { nparams: p2, nindices: i2, all: a2, ctors: c2, nnested: n2, is_rec: r2, is_reflexive: f2, unsafe_: u2 },
        ) => p1 == p2 && i1 == i2 && n1 == n2 && r1 == r2 && f1 == f2 && u1 == u2 && names_eq(env, a1, a2) && names_eq(env, c1, c2),
        (
            CKind::Ctor { induct: i1, cidx: c1, nparams: p1, nfields: f1, unsafe_: u1 },
            CKind::Ctor { induct: i2, cidx: c2, nparams: p2, nfields: f2, unsafe_: u2 },
        ) => env.canon(*i1) == env.canon(*i2) && c1 == c2 && p1 == p2 && f1 == f2 && u1 == u2,
        (
            CKind::Rec { all: a1, nparams: p1, nindices: i1, nmotives: m1, nminors: n1, rules: r1, k: k1, unsafe_: u1 },
            CKind::Rec { all: a2, nparams: p2, nindices: i2, nmotives: m2, nminors: n2, rules: r2, k: k2, unsafe_: u2 },
        ) => {
            p1 == p2 && i1 == i2 && m1 == m2 && n1 == n2 && k1 == k2 && u1 == u2
                && names_eq(env, a1, a2)
                && r1.len() == r2.len()
                && r1.iter().zip(r2.iter()).all(|(x, y)| {
                    env.canon(x.0) == env.canon(y.0) && x.1 == y.1 && expr_eq_main(env, x.2, y.2, &mut memo)
                })
        }
        _ => false,
    }
}

/// Executed inside the CoW forked child for `CHECK_DELTA`.
fn child_check_delta(
    env: &mut Env<'static>,
    bg: &BaseGraph,
    nonce: &str,
    delta_path: &str,
    workers: usize,
) -> String {
    let t0 = Instant::now();
    let raw_bytes = match std::fs::read(delta_path) {
        Ok(b) => b,
        Err(e) => return emit_json(nonce, "error", &format!("cannot read delta: {e}"), 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
    };

    // Local NDJSON index tables for delta file
    let mut name_map: Vec<u32> = vec![0]; // local name idx -> global raw name id in env.st.name_canon
    let mut delta_canon_to_raw: FxHashMap<u32, u32> = FxHashMap::default();
    let mut lvl_map: Vec<u32> = vec![0];  // local level idx -> global level id in env.lvl
    let mut expr_map: Vec<u32> = Vec::new(); // local expr idx -> global MAIN node id
    let mut tail_cur = bg.base_bytes_len;

    // Parsed delta declaration units (each single decl = 1-elem Vec; each inductive bundle = all its types+ctors+recs)
    struct RawUnit {
        consts: Vec<ConstInfo>,
    }
    let mut parsed_units: Vec<RawUnit> = Vec::new();
    let mut seen_delta_canons: FxHashSet<u32> = FxHashSet::default();

    // Ensure `env.main` has capacity for delta expressions
    let est_exprs = raw_bytes.iter().filter(|&&b| b == b'\n').count() + 1024;
    env.main.extend_cap(est_exprs);

    let mut line_no = 0usize;
    let body_bytes = raw_bytes.strip_suffix(b"\n").unwrap_or(&raw_bytes);
    for raw_line in body_bytes.split(|&b| b == b'\n') {
        let line = if raw_line.ends_with(b"\r") { &raw_line[..raw_line.len() - 1] } else { raw_line };
        line_no += 1;
        if line.is_empty() {
            return emit_json(nonce, "reject", &format!("delta line {line_no}: empty line"), 0, 0, 0, 0, 0, t0.elapsed().as_millis());
        }
        if line_no == 1 {
            // Skip metadata line (verify it is valid JSON object)
            if JParser::parse(line).is_err() {
                return emit_json(nonce, "reject", "invalid metadata JSON in delta", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            }
            continue;
        }
        let j = match JParser::parse(line) {
            Ok(v) => v,
            Err(e) => return emit_json(nonce, "reject", &format!("delta line {line_no}: {e}"), 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
        };

        // 1. Name record: {"in": idx, "str": {"pre": p, "str": s}} or {"in": idx, "num": {"pre": p, "i": k}}
        if let Some(in_v) = j.get("in") {
            let idx = match in_v.as_u64() {
                Ok(v) => v as usize,
                Err(e) => return emit_json(nonce, "reject", &e, 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
            };
            if idx != name_map.len() {
                return emit_json(nonce, "fallback", "non-dense name index in delta", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            }
            let canon_id = if let Some(sv) = j.get("str") {
                let pre_local = match sv.get("pre").and_then(|v| v.as_u64().ok()) {
                    Some(v) if (v as usize) < name_map.len() => name_map[v as usize],
                    _ => return emit_json(nonce, "reject", "bad name str pre", 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
                };
                let pre_canon = env.st.name_canon[pre_local as usize];
                let s = match sv.get("str").and_then(|v| v.as_str().ok()) {
                    Some(s) => s.as_bytes(),
                    None => return emit_json(nonce, "reject", "bad name str", 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
                };
                if let Some(existing) = env.st.canon.find(env.bytes, pre_canon, Part::Str(s)) {
                    existing
                } else {
                    if tail_cur + s.len() > bg.base_bytes_cap {
                        return emit_json(nonce, "fallback", "delta string tail exhausted", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
                    }
                    let off = tail_cur as u64;
                    unsafe {
                        std::ptr::copy_nonoverlapping(s.as_ptr(), bg.base_bytes_ptr.add(tail_cur), s.len());
                        tail_cur += s.len();
                        env.bytes = std::slice::from_raw_parts(bg.base_bytes_ptr, tail_cur);
                    }
                    env.st.canon.str_id(env.bytes, pre_canon, off, s.len() as u32)
                }
            } else if let Some(nv) = j.get("num") {
                let pre_local = match nv.get("pre").and_then(|v| v.as_u64().ok()) {
                    Some(v) if (v as usize) < name_map.len() => name_map[v as usize],
                    _ => return emit_json(nonce, "reject", "bad name num pre", 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
                };
                let pre_canon = env.st.name_canon[pre_local as usize];
                let num_k = match nv.get("i").and_then(|v| v.as_u64().ok()) {
                    Some(k) => k,
                    None => return emit_json(nonce, "reject", "bad name num i", 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
                };
                env.st.canon.num_id(pre_canon, num_k)
            } else {
                return emit_json(nonce, "reject", "invalid name record", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            };
            // Reuse the canonical base raw_id when the name already exists in base (ensures identical raw sname
            // ids for tc::Worker::proj_map across base and delta projections, and avoids CoW growth).
            let raw_id = if (canon_id as usize) + 1 < bg.raw_start.len()
                && bg.raw_start[canon_id as usize] < bg.raw_start[canon_id as usize + 1]
            {
                bg.raw_adj[bg.raw_start[canon_id as usize] as usize]
            } else if let Some(&existing_raw) = delta_canon_to_raw.get(&canon_id) {
                existing_raw
            } else {
                let rid = env.st.name_canon.len() as u32;
                env.st.name_canon.push(canon_id);
                if canon_id as usize >= env.row_of_canon.len() {
                    env.row_of_canon.resize(canon_id as usize + 1, NONE);
                }
                env.row_of_name.push(env.row_of_canon[canon_id as usize]);
                delta_canon_to_raw.insert(canon_id, rid);
                rid
            };
            name_map.push(raw_id);
            continue;
        }

        // 2. Level record
        if let Some(il_v) = j.get("il") {
            let idx = match il_v.as_u64() {
                Ok(v) => v as usize,
                Err(e) => return emit_json(nonce, "reject", &e, 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
            };
            if idx != lvl_map.len() {
                return emit_json(nonce, "fallback", "non-dense level index in delta", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            }
            let key = if let Some(v) = j.get("succ") {
                let a = match v.as_u64().ok().and_then(|x| lvl_map.get(x as usize).copied()) {
                    Some(x) => x,
                    None => return emit_json(nonce, "reject", "bad level succ", 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
                };
                (1u8, a, 0u32)
            } else if let Some(v) = j.get("max") {
                let arr = match v.as_arr() { Ok(a) if a.len() == 2 => a, _ => return emit_json(nonce, "reject", "bad level max", 0, 0, 0, 0, 0, t0.elapsed().as_millis()) };
                let a = match arr[0].as_u64().ok().and_then(|x| lvl_map.get(x as usize).copied()) { Some(x) => x, None => return emit_json(nonce, "reject", "bad max[0]", 0, 0, 0, 0, 0, t0.elapsed().as_millis()) };
                let b = match arr[1].as_u64().ok().and_then(|x| lvl_map.get(x as usize).copied()) { Some(x) => x, None => return emit_json(nonce, "reject", "bad max[1]", 0, 0, 0, 0, 0, t0.elapsed().as_millis()) };
                (2u8, a, b)
            } else if let Some(v) = j.get("imax") {
                let arr = match v.as_arr() { Ok(a) if a.len() == 2 => a, _ => return emit_json(nonce, "reject", "bad level imax", 0, 0, 0, 0, 0, t0.elapsed().as_millis()) };
                let a = match arr[0].as_u64().ok().and_then(|x| lvl_map.get(x as usize).copied()) { Some(x) => x, None => return emit_json(nonce, "reject", "bad imax[0]", 0, 0, 0, 0, 0, t0.elapsed().as_millis()) };
                let b = match arr[1].as_u64().ok().and_then(|x| lvl_map.get(x as usize).copied()) { Some(x) => x, None => return emit_json(nonce, "reject", "bad imax[1]", 0, 0, 0, 0, 0, t0.elapsed().as_millis()) };
                (3u8, a, b)
            } else if let Some(v) = j.get("param") {
                let n = match v.as_u64().ok().and_then(|x| name_map.get(x as usize).copied()) { Some(x) => env.canon(x), None => return emit_json(nonce, "reject", "bad level param", 0, 0, 0, 0, 0, t0.elapsed().as_millis()) };
                (4u8, n, 0u32)
            } else {
                return emit_json(nonce, "reject", "invalid level record", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            };
            let gid = *env.lvl_intern.entry(key).or_insert_with(|| {
                env.lvl.push(key);
                env.lvl.len() as u32 - 1
            });
            lvl_map.push(gid);
            continue;
        }

        // 3. Expression record
        if let Some(ie_v) = j.get("ie") {
            let idx = match ie_v.as_u64() {
                Ok(v) => v as usize,
                Err(e) => return emit_json(nonce, "reject", &e, 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
            };
            if idx != expr_map.len() {
                return emit_json(nonce, "fallback", "non-dense expr index in delta", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            }
            let gid = env.main.len() as u32;
            let get_n = |v: Option<&JVal>| -> Result<u32, String> {
                let k = v.ok_or("missing name")?.as_u64()? as usize;
                name_map.get(k).copied().ok_or_else(|| "name idx out of bounds".into())
            };
            let get_l = |v: Option<&JVal>| -> Result<u32, String> {
                let k = v.ok_or("missing level")?.as_u64()? as usize;
                lvl_map.get(k).copied().ok_or_else(|| "level idx out of bounds".into())
            };
            let get_e = |v: Option<&JVal>| -> Result<u32, String> {
                let k = v.ok_or("missing expr")?.as_u64()? as usize;
                expr_map.get(k).copied().ok_or_else(|| "expr idx out of bounds".into())
            };

            let r: Result<u32, String> = (|| {
                if let Some(v) = j.get("bvar") {
                    let bi = u32::try_from(v.as_u64()?).unwrap_or(u32::MAX - 1);
                    env.main.push(BVAR, 0, 0, bi, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("sort") {
                    let l = get_l(Some(v))?;
                    env.main.push(SORT, 0, 0, l, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("const") {
                    let nm = get_n(v.get("name"))?;
                    let us = v.get("us").ok_or("missing us")?.as_arr()?;
                    let off = if us.is_empty() {
                        0u32
                    } else {
                        let mut ls = Vec::with_capacity(us.len());
                        for u in us {
                            ls.push(get_l(Some(u))?);
                        }
                        if let Some(&o) = env.ll_canon.get(ls.as_slice()) {
                            o
                        } else {
                            let o = env.side.lvls.len() as u32;
                            env.side.lvls.push(ls.len() as u32);
                            env.side.lvls.extend_from_slice(&ls);
                            env.ll_canon.insert(ls.into_boxed_slice(), o);
                            o
                        }
                    };
                    env.main.push(CONST, nm, 0, off, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("app") {
                    let f = get_e(v.get("fn"))?;
                    let a = get_e(v.get("arg"))?;
                    env.main.push(APP, f, a, 0, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("lam") {
                    let nm = get_n(v.get("name"))?;
                    let ty = get_e(v.get("type"))?;
                    let bd = get_e(v.get("body"))?;
                    let bi = parse_binder(v.get("binderInfo").ok_or("missing binderInfo")?.as_str()?)?;
                    env.main.push(LAM + bi, ty, bd, nm, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("forallE") {
                    let nm = get_n(v.get("name"))?;
                    let ty = get_e(v.get("type"))?;
                    let bd = get_e(v.get("body"))?;
                    let bi = parse_binder(v.get("binderInfo").ok_or("missing binderInfo")?.as_str()?)?;
                    env.main.push(PI + bi, ty, bd, nm, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("letE") {
                    let nm = get_n(v.get("name"))?;
                    let ty = get_e(v.get("type"))?;
                    let val = get_e(v.get("value"))?;
                    let bd = get_e(v.get("body"))?;
                    let _nondep = v.get("nondep").ok_or("missing nondep")?.as_bool()?;
                    let li = env.side.lets.len() as u32;
                    env.side.lets.push((nm, bd));
                    env.main.push(LET, ty, val, li, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("natVal") {
                    let s = v.as_str()?;
                    let big = BigUint::parse_bytes(s.as_bytes(), 10).ok_or("bad natVal")?;
                    let li = env.lits.len() as u32;
                    env.lits.push(LitVal::Nat(big));
                    env.main.push(NAT, 0, 0, li, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("strVal") {
                    let s = v.as_str()?;
                    let li = env.lits.len() as u32;
                    env.lits.push(LitVal::Str(s.into()));
                    env.main.push(STR, 0, 0, li, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("proj") {
                    let sn = get_n(v.get("typeName"))?;
                    let fi = u32::try_from(v.get("idx").ok_or("missing proj idx")?.as_u64()?)
                        .map_err(|_| "proj idx overflow")?;
                    let st = get_e(v.get("struct"))?;
                    env.main.push(PROJ, st, fi, sn, 0, 0);
                    Ok(gid)
                } else if let Some(v) = j.get("mdata") {
                    get_e(v.get("expr"))
                } else {
                    Err("unknown expr record".into())
                }
            })();
            match r {
                Ok(mapped) => expr_map.push(mapped),
                Err(e) => {
                    let st = if e.contains("fallback") { "fallback" } else { "reject" };
                    return emit_json(nonce, st, &e, 0, 0, 0, 0, 0, t0.elapsed().as_millis());
                }
            }
            continue;
        }

        // 4. Declaration record
        let get_n = |v: Option<&JVal>| -> Result<u32, String> {
            let k = v.ok_or("missing name")?.as_u64()? as usize;
            name_map.get(k).copied().ok_or_else(|| "name idx out of bounds".into())
        };
        let get_ns = |v: Option<&JVal>| -> Result<Box<[u32]>, String> {
            let arr = v.ok_or("missing names array")?.as_arr()?;
            let mut out = Vec::with_capacity(arr.len());
            for x in arr {
                let k = x.as_u64()? as usize;
                out.push(*name_map.get(k).ok_or("name idx out of bounds")?);
            }
            Ok(out.into_boxed_slice())
        };
        let get_e = |v: Option<&JVal>| -> Result<u32, String> {
            let k = v.ok_or("missing expr")?.as_u64()? as usize;
            expr_map.get(k).copied().ok_or_else(|| "expr idx out of bounds".into())
        };

        let unit_res: Result<RawUnit, String> = (|| {
            if let Some(v) = j.get("axiom") {
                let name = get_n(v.get("name"))?;
                let lparams = get_ns(v.get("levelParams"))?;
                let ty = get_e(v.get("type"))?;
                let unsafe_ = v.get("isUnsafe").and_then(|x| x.as_bool().ok()).unwrap_or(false);
                Ok(RawUnit {
                    consts: vec![ConstInfo { name, lparams, ty, decl: 0, group: 3, kind: CKind::Axiom { unsafe_ } }],
                })
            } else if let Some(v) = j.get("def") {
                let name = get_n(v.get("name"))?;
                let lparams = get_ns(v.get("levelParams"))?;
                let ty = get_e(v.get("type"))?;
                let value = get_e(v.get("value"))?;
                let hint = parse_hint(v.get("hints").ok_or("missing hints")?)?;
                let safety = parse_safety(v.get("safety").ok_or("missing safety")?.as_str()?)?;
                let all = get_ns(v.get("all"))?;
                Ok(RawUnit {
                    consts: vec![ConstInfo { name, lparams, ty, decl: 0, group: 3, kind: CKind::Defn { value, hint, safety, all } }],
                })
            } else if let Some(v) = j.get("thm") {
                let name = get_n(v.get("name"))?;
                let lparams = get_ns(v.get("levelParams"))?;
                let ty = get_e(v.get("type"))?;
                let value = get_e(v.get("value"))?;
                let all = get_ns(v.get("all"))?;
                Ok(RawUnit {
                    consts: vec![ConstInfo { name, lparams, ty, decl: 0, group: 3, kind: CKind::Thm { value: ThmVal::Main(value), all } }],
                })
            } else if let Some(v) = j.get("opaque") {
                let name = get_n(v.get("name"))?;
                let lparams = get_ns(v.get("levelParams"))?;
                let ty = get_e(v.get("type"))?;
                let value = get_e(v.get("value"))?;
                let unsafe_ = v.get("isUnsafe").and_then(|x| x.as_bool().ok()).unwrap_or(false);
                let all = get_ns(v.get("all"))?;
                Ok(RawUnit {
                    consts: vec![ConstInfo { name, lparams, ty, decl: 0, group: 3, kind: CKind::Opaque { value, unsafe_, all } }],
                })
            } else if let Some(v) = j.get("quot") {
                let name = get_n(v.get("name"))?;
                let lparams = get_ns(v.get("levelParams"))?;
                let ty = get_e(v.get("type"))?;
                let kind = match v.get("kind").ok_or("missing quot kind")?.as_str()? {
                    "type" => 0u8,
                    "ctor" => 1u8,
                    "lift" => 2u8,
                    "ind" => 3u8,
                    k => return Err(format!("unknown quot kind '{k}'")),
                };
                Ok(RawUnit {
                    consts: vec![ConstInfo { name, lparams, ty, decl: 0, group: 3, kind: CKind::Quot { kind } }],
                })
            } else if let Some(v) = j.get("inductive") {
                let types = v.get("types").ok_or("inductive missing types")?.as_arr()?;
                let ctors = v.get("ctors").ok_or("inductive missing ctors")?.as_arr()?;
                let recs = v.get("recs").ok_or("inductive missing recs")?.as_arr()?;
                let mut consts = Vec::with_capacity(types.len() + ctors.len() + recs.len());
                for tv in types {
                    let name = get_n(tv.get("name"))?;
                    let lparams = get_ns(tv.get("levelParams"))?;
                    let ty = get_e(tv.get("type"))?;
                    let nparams = u32::try_from(tv.get("numParams").ok_or("numParams")?.as_u64()?).unwrap_or(u32::MAX);
                    let nindices = u32::try_from(tv.get("numIndices").ok_or("numIndices")?.as_u64()?).unwrap_or(u32::MAX);
                    let all = get_ns(tv.get("all"))?;
                    let ctors_ns = get_ns(tv.get("ctors"))?;
                    let nnested = u32::try_from(tv.get("numNested").ok_or("numNested")?.as_u64()?).unwrap_or(u32::MAX);
                    let is_rec = tv.get("isRec").ok_or("isRec")?.as_bool()?;
                    let is_reflexive = tv.get("isReflexive").ok_or("isReflexive")?.as_bool()?;
                    let unsafe_ = tv.get("isUnsafe").and_then(|x| x.as_bool().ok()).unwrap_or(false);
                    consts.push(ConstInfo {
                        name, lparams, ty, decl: 0, group: 0,
                        kind: CKind::Induct { nparams, nindices, all, ctors: ctors_ns, nnested, is_rec, is_reflexive, unsafe_ },
                    });
                }
                for cv in ctors {
                    let name = get_n(cv.get("name"))?;
                    let lparams = get_ns(cv.get("levelParams"))?;
                    let ty = get_e(cv.get("type"))?;
                    let induct = get_n(cv.get("induct"))?;
                    let cidx = u32::try_from(cv.get("cidx").ok_or("cidx")?.as_u64()?).unwrap_or(u32::MAX);
                    let nparams = u32::try_from(cv.get("numParams").ok_or("numParams")?.as_u64()?).unwrap_or(u32::MAX);
                    let nfields = u32::try_from(cv.get("numFields").ok_or("numFields")?.as_u64()?).unwrap_or(u32::MAX);
                    let unsafe_ = cv.get("isUnsafe").and_then(|x| x.as_bool().ok()).unwrap_or(false);
                    consts.push(ConstInfo {
                        name, lparams, ty, decl: 0, group: 1,
                        kind: CKind::Ctor { induct, cidx, nparams, nfields, unsafe_ },
                    });
                }
                for rv in recs {
                    let name = get_n(rv.get("name"))?;
                    let lparams = get_ns(rv.get("levelParams"))?;
                    let ty = get_e(rv.get("type"))?;
                    let all = get_ns(rv.get("all"))?;
                    let nparams = u32::try_from(rv.get("numParams").ok_or("numParams")?.as_u64()?).unwrap_or(u32::MAX);
                    let nindices = u32::try_from(rv.get("numIndices").ok_or("numIndices")?.as_u64()?).unwrap_or(u32::MAX);
                    let nmotives = u32::try_from(rv.get("numMotives").ok_or("numMotives")?.as_u64()?).unwrap_or(u32::MAX);
                    let nminors = u32::try_from(rv.get("numMinors").ok_or("numMinors")?.as_u64()?).unwrap_or(u32::MAX);
                    let k_flag = rv.get("k").ok_or("k")?.as_bool()?;
                    let unsafe_ = rv.get("isUnsafe").and_then(|x| x.as_bool().ok()).unwrap_or(false);
                    let rarr = rv.get("rules").ok_or("rules")?.as_arr()?;
                    let mut rules = Vec::with_capacity(rarr.len());
                    for rrv in rarr {
                        let ctor = get_n(rrv.get("ctor"))?;
                        let nf = u32::try_from(rrv.get("nfields").ok_or("nfields")?.as_u64()?).unwrap_or(u32::MAX);
                        let rhs = get_e(rrv.get("rhs"))?;
                        rules.push((ctor, nf, rhs));
                    }
                    consts.push(ConstInfo {
                        name, lparams, ty, decl: 0, group: 2,
                        kind: CKind::Rec { all, nparams, nindices, nmotives, nminors, rules: rules.into_boxed_slice(), k: k_flag, unsafe_ },
                    });
                }
                if consts.is_empty() {
                    return Err("empty inductive block".into());
                }
                Ok(RawUnit { consts })
            } else {
                return Err(format!("unknown record on delta line {line_no}"));
            }
        })();

        let ru = match unit_res {
            Ok(u) => u,
            Err(e) => {
                let st = if e.contains("fallback") { "fallback" } else { "reject" };
                return emit_json(nonce, st, &e, 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            }
        };
        for ci in &ru.consts {
            let cn = env.canon(ci.name);
            if !seen_delta_canons.insert(cn) {
                return emit_json(nonce, "reject", &format!("duplicate declaration '{}'", env.name_str(ci.name)), 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            }
        }
        parsed_units.push(ru);
    }

    if env.main.full {
        return emit_json(nonce, "fallback", "delta main arena full", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
    }
    if env::fill_main(&env.main, &env.side.lets, bg.base_main_len, env.main.len()) {
        return emit_json(nonce, "decline", "delta expression has >= 65535 loose bvars", 0, 0, 0, 0, 0, t0.elapsed().as_millis());
    }

    let delta_consts: usize = parsed_units.iter().map(|u| u.consts.len()).sum();
    let implicit_str_set: FxHashSet<&str> = IMPLICIT_NAMES.iter().copied().collect();

    // Check overrides & implicit/Quot guards
    let mut overridden_decls: Vec<u32> = Vec::new();
    let mut overridden_consts: usize = 0;
    let mut fresh_consts: usize = 0;

    for ru in &parsed_units {
        for ci in &ru.consts {
            let cn = env.canon(ci.name);
            let is_imp = matches!(ci.kind, CKind::Quot { .. })
                || bg.implicit_canons.contains(&cn)
                || implicit_str_set.contains(env.name_str(ci.name).as_str());
            let base_row = env.known_row(cn);
            if base_row != NONE && (base_row as usize) < bg.base_consts_len {
                let bci = &env.consts[base_row as usize];
                if !const_eq_base(env, bci, ci) {
                    if is_imp {
                        return emit_json(nonce, "fallback", &format!("implicit/quot constant '{}' overridden", env.name_str(ci.name)), delta_consts, 0, 0, 0, 0, t0.elapsed().as_millis());
                    }
                    overridden_consts += 1;
                    overridden_decls.push(bci.decl);
                }
            } else {
                if is_imp {
                    return emit_json(nonce, "fallback", &format!("implicit/quot constant '{}' introduced", env.name_str(ci.name)), delta_consts, 0, 0, 0, 0, t0.elapsed().as_millis());
                }
                fresh_consts += 1;
            }
        }
    }

    // Reverse BFS on BaseGraph for dirty base decls
    let mut dirty_decls_set: FxHashSet<u32> = FxHashSet::default();
    let mut stack = overridden_decls;
    while let Some(d) = stack.pop() {
        if !dirty_decls_set.insert(d) {
            continue;
        }
        let lo = bg.rev_start[d as usize] as usize;
        let hi = bg.rev_start[d as usize + 1] as usize;
        for &u in &bg.rev_adj[lo..hi] {
            if !dirty_decls_set.contains(&u) {
                stack.push(u);
            }
        }
    }

    // Collect dirty canonical names & mask them out of row_of_canon + row_of_name
    let mut dirty_canons: FxHashSet<u32> = FxHashSet::default();
    for &d in &dirty_decls_set {
        let (first, count) = env.decl_rows[d as usize];
        for r in first..first + count {
            let cn = env.canon(env.consts[r as usize].name);
            if bg.implicit_canons.contains(&cn) || matches!(env.consts[r as usize].kind, CKind::Quot { .. }) {
                return emit_json(nonce, "fallback", "implicit/quot constant dirtied by delta", delta_consts, overridden_consts, 0, 0, 0, t0.elapsed().as_millis());
            }
            dirty_canons.insert(cn);
        }
    }
    for &cn in &dirty_canons {
        env.row_of_canon[cn as usize] = NONE;
        if (cn as usize) < bg.raw_start.len() - 1 {
            let lo = bg.raw_start[cn as usize] as usize;
            let hi = bg.raw_start[cn as usize + 1] as usize;
            for &rid in &bg.raw_adj[lo..hi] {
                env.row_of_name[rid as usize] = NONE;
            }
        }
    }
    // Also mask delta raw name ids pointing to dirty canons
    for rid in bg.raw_adj.len()..env.st.name_canon.len() {
        let cn = env.st.name_canon[rid];
        if dirty_canons.contains(&cn) {
            env.row_of_name[rid] = NONE;
        }
    }

    // Select delta declaration units to install & check (atomic for inductive bundles!)
    let mut grouped: Vec<Vec<ConstInfo>> = Vec::new();
    let mut dirty_resupplied: usize = 0;
    for ru in parsed_units {
        let mut needs_check = false;
        for ci in &ru.consts {
            let cn = env.canon(ci.name);
            let in_base = env.known_row(cn) != NONE && (env.known_row(cn) as usize) < bg.base_consts_len;
            let is_dirty = dirty_canons.contains(&cn);
            if is_dirty {
                dirty_resupplied += 1;
            }
            if !in_base || is_dirty {
                needs_check = true;
            }
        }
        if needs_check {
            // If an inductive bundle mixes an already-clean base constant with a new constant, mask base constant too
            grouped.push(ru.consts);
        }
    }

    let eff = bg.base_consts_len - dirty_canons.len() + fresh_consts + dirty_resupplied;
    if grouped.is_empty() {
        return emit_json(nonce, "ok", "all delta constants match verified base", delta_consts, overridden_consts, dirty_canons.len(), eff, 0, t0.elapsed().as_millis());
    }

    // Build delta raw-name lookup to update row_of_name for newly installed delta constants
    let mut delta_raw_by_canon: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
    for rid in bg.raw_adj.len()..env.st.name_canon.len() {
        delta_raw_by_canon.entry(env.st.name_canon[rid]).or_default().push(rid as u32);
    }

    let mut new_decls: Vec<u32> = Vec::with_capacity(grouped.len());
    for mut grp in grouped {
        // Order inductive group rows as: induct (0), ctor (1), rec (2)
        if grp.len() > 1 {
            grp.sort_by_key(|c| c.group);
        }
        let d_id = env.decl_rows.len() as u32;
        let first = env.consts.len() as u32;
        let mut dup_lp = false;
        for mut c in grp {
            c.decl = d_id;
            // Check duplicate universe params
            for i in 0..c.lparams.len() {
                for j in 0..i {
                    if env.canon(c.lparams[i]) == env.canon(c.lparams[j]) {
                        dup_lp = true;
                    }
                }
            }
            let row = env.consts.len() as u32;
            let cn = env.canon(c.name);
            // Update rec_major for recursors
            if let CKind::Rec { nparams, nindices, nmotives, nminors, .. } = &c.kind {
                let skip = *nparams as u64 + *nmotives as u64 + *nminors as u64 + *nindices as u64;
                let mut t = c.ty;
                let mut ok = true;
                for _ in 0..skip {
                    if is_pi(env.main.n()[t as usize].kind) {
                        t = env.main.n()[t as usize].b;
                    } else {
                        ok = false;
                        break;
                    }
                }
                if ok && is_pi(env.main.n()[t as usize].kind) {
                    let mut dm = env.main.n()[t as usize].a;
                    while env.main.n()[dm as usize].kind == APP {
                        dm = env.main.n()[dm as usize].a;
                    }
                    if env.main.n()[dm as usize].kind == CONST {
                        env.rec_major.insert(row, env.canon(env.main.n()[dm as usize].a));
                    }
                }
            }
            env.consts.push(c);
            env.nat_op.push(0);
            env.row_of_canon[cn as usize] = row;
            if (cn as usize) < bg.raw_start.len() - 1 {
                let lo = bg.raw_start[cn as usize] as usize;
                let hi = bg.raw_start[cn as usize + 1] as usize;
                for &rid in &bg.raw_adj[lo..hi] {
                    env.row_of_name[rid as usize] = row;
                }
            }
            if let Some(rids) = delta_raw_by_canon.get(&cn) {
                for &rid in rids {
                    env.row_of_name[rid as usize] = row;
                }
            }
        }
        let n = env.consts.len() as u32 - first;
        env.decl_rows.push((first, n));
        env.decl_dup_params.push(dup_lp);
        new_decls.push(d_id);
    }

    let env_static: &'static Env<'static> = unsafe { &*(env as *const Env<'static>) };
    let child_workers = if new_decls.len() <= 8 { 1 } else { workers.min(new_decls.len()) };
    match check_decl_subset(env_static, &new_decls, child_workers) {
        Ok(()) => emit_json(nonce, "ok", "gruszka accepts the delta", delta_consts, overridden_consts, dirty_canons.len(), eff, new_decls.len(), t0.elapsed().as_millis()),
        Err((ST_REJECT, m)) => emit_json(nonce, "reject", &m, delta_consts, overridden_consts, dirty_canons.len(), eff, new_decls.len(), t0.elapsed().as_millis()),
        Err((_, m)) => emit_json(nonce, "decline", &m, delta_consts, overridden_consts, dirty_canons.len(), eff, new_decls.len(), t0.elapsed().as_millis()),
    }
}

/// Executed inside a forked child for `CHECK_FULL` (unchanged full check from scratch).
fn child_check_full(nonce: &str, full_path: &str, workers: usize) -> String {
    let t0 = Instant::now();
    let is_ndjson = full_path.ends_with(".ndjson") || {
        let mut b = [0u8; 1];
        std::fs::File::open(full_path).and_then(|mut f| f.read_exact(&mut b)).is_ok() && b[0] == b'{'
    };
    let mut seg_starts = Vec::new();
    let bytes: &'static [u8] = if is_ndjson {
        let opts = susz::pack::Options { index: false, threads: workers };
        match susz::pack::pack_to_vec_segs(full_path, &opts) {
            Ok((v, _, ss)) => {
                seg_starts = ss;
                Box::leak(v.into_boxed_slice())
            }
            Err(e) => {
                let st = if e.fault == susz::pack::Fault::Invalid { "reject" } else { "decline" };
                return emit_json(nonce, st, &e.msg, 0, 0, 0, 0, 0, t0.elapsed().as_millis());
            }
        }
    } else {
        match unsafe { susz::open_mmap(full_path) } {
            Ok(m) => Box::leak(Box::new(m)),
            Err(e) => return emit_json(nonce, "decline", &format!("cannot open: {e}"), 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
        }
    };
    env::LOAD_THREADS.store(workers, Ordering::Relaxed);
    let loaded = if !seg_starts.is_empty() {
        env::load_par(bytes, &seg_starts, workers).unwrap_or_else(|| env::load_part(bytes, None))
    } else {
        env::load_part(bytes, None)
    };
    let env = match loaded {
        Ok(e) => Box::leak(Box::new(e)),
        Err(env::LoadError::Reject(m)) => return emit_json(nonce, "reject", &m, 0, 0, 0, 0, 0, t0.elapsed().as_millis()),
        Err(env::LoadError::Decline(m) | env::LoadError::IndexInvalid(m)) => {
            return emit_json(nonce, "decline", &m, 0, 0, 0, 0, 0, t0.elapsed().as_millis())
        }
    };
    let nd = env.decl_rows.len();
    let nc = env.consts.len();
    let all_decls: Vec<u32> = (0..nd as u32).collect();
    match check_decl_subset(env, &all_decls, workers) {
        Ok(()) => emit_json(nonce, "ok", "gruszka accepts the solution", nc, 0, 0, nc, nd, t0.elapsed().as_millis()),
        Err((ST_REJECT, m)) => emit_json(nonce, "reject", &m, nc, 0, 0, nc, nd, t0.elapsed().as_millis()),
        Err((_, m)) => emit_json(nonce, "decline", &m, nc, 0, 0, nc, nd, t0.elapsed().as_millis()),
    }
}

#[cfg(unix)]
fn run_in_forked_child<F: FnOnce() -> String>(f: F) -> String {
    unsafe extern "C" {
        fn pipe(fds: *mut i32) -> i32;
        fn fork() -> i32;
        fn close(fd: i32) -> i32;
        fn read(fd: i32, buf: *mut u8, count: usize) -> isize;
        fn write(fd: i32, buf: *const u8, count: usize) -> isize;
        fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
        fn _exit(status: i32) -> !;
    }
    let mut fds = [0i32; 2];
    if unsafe { pipe(fds.as_mut_ptr()) } != 0 {
        return emit_json("unknown", "error", "pipe() failed", 0, 0, 0, 0, 0, 0);
    }
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    let pid = unsafe { fork() };
    if pid < 0 {
        unsafe { close(fds[0]); close(fds[1]); }
        return emit_json("unknown", "error", "fork() failed", 0, 0, 0, 0, 0, 0);
    }
    if pid == 0 {
        unsafe { close(fds[0]); }
        let out = f();
        let bytes = out.as_bytes();
        let mut off = 0;
        while off < bytes.len() {
            let n = unsafe { write(fds[1], bytes.as_ptr().add(off), bytes.len() - off) };
            if n <= 0 { break; }
            off += n as usize;
        }
        unsafe { close(fds[1]); _exit(0); }
    }
    unsafe { close(fds[1]); }
    let mut buf = Vec::new();
    let mut tmp = [0u8; 4096];
    loop {
        let n = unsafe { read(fds[0], tmp.as_mut_ptr(), tmp.len()) };
        if n <= 0 { break; }
        buf.extend_from_slice(&tmp[..n as usize]);
    }
    unsafe { close(fds[0]); }
    let mut status: i32 = 0;
    unsafe { waitpid(pid, &mut status, 0); }
    if buf.is_empty() {
        return emit_json("unknown", "decline", &format!("child exited abnormally (status={status})"), 0, 0, 0, 0, 0, 0);
    }
    String::from_utf8_lossy(&buf).into_owned()
}

pub fn run_warm(base_path: &str, workers: usize) -> ! {
    let t0 = Instant::now();
    let is_ndjson = base_path.ends_with(".ndjson") || {
        let mut b = [0u8; 1];
        std::fs::File::open(base_path).and_then(|mut f| f.read_exact(&mut b)).is_ok() && b[0] == b'{'
    };
    let mut seg_starts = Vec::new();
    let raw_vec: Vec<u8> = if is_ndjson {
        let opts = susz::pack::Options { index: false, threads: workers };
        match susz::pack::pack_to_vec_segs(base_path, &opts) {
            Ok((v, _, ss)) => {
                seg_starts = ss;
                v
            }
            Err(e) => {
                println!("{{\"ready\":false,\"leg\":\"gruszka\",\"error\":{}}}", json_escape(&e.msg));
                std::process::exit(1);
            }
        }
    } else {
        match std::fs::read(base_path) {
            Ok(v) => v,
            Err(e) => {
                println!("{{\"ready\":false,\"leg\":\"gruszka\",\"error\":{}}}", json_escape(&format!("{e}")));
                std::process::exit(1);
            }
        }
    };
    let base_bytes_len = raw_vec.len();
    let (base_bytes_ptr, base_bytes_cap) = unsafe { alloc_bytes_with_tail(&raw_vec) };
    drop(raw_vec);
    let base_bytes: &'static [u8] = unsafe { std::slice::from_raw_parts(base_bytes_ptr, base_bytes_len) };

    env::LOAD_THREADS.store(workers, Ordering::Relaxed);
    let loaded = if !seg_starts.is_empty() {
        env::load_par(base_bytes, &seg_starts, workers).unwrap_or_else(|| env::load_part(base_bytes, None))
    } else {
        env::load_part(base_bytes, None)
    };
    let mut base_env = match loaded {
        Ok(e) => Box::new(e),
        Err(env::LoadError::Reject(m) | env::LoadError::Decline(m) | env::LoadError::IndexInvalid(m)) => {
            println!("{{\"ready\":false,\"leg\":\"gruszka\",\"error\":{}}}", json_escape(&m));
            std::process::exit(1);
        }
    };

    // Verify EVERY declaration of BASE from scratch before accepting any queries!
    let nd = base_env.decl_rows.len();
    let all_decls: Vec<u32> = (0..nd as u32).collect();
    let env_static: &'static Env<'static> = unsafe { &*(&*base_env as *const Env<'static>) };
    if let Err((_, msg)) = check_decl_subset(env_static, &all_decls, workers) {
        println!("{{\"ready\":false,\"leg\":\"gruszka\",\"error\":{}}}", json_escape(&format!("base verification failed: {msg}")));
        std::process::exit(1);
    }

    let bg = build_base_graph(&base_env, base_bytes_ptr, base_bytes_len, base_bytes_cap, workers);
    println!(
        "{{\"ready\":true,\"leg\":\"gruszka\",\"base_consts\":{},\"base_decls\":{},\"ms\":{}}}",
        bg.base_consts_len,
        bg.base_decls_len,
        t0.elapsed().as_millis()
    );
    let _ = std::io::stdout().flush();

    // Parent is now 100% single-threaded: safe to fork() per query!
    let stdin = std::io::stdin();
    let mut line = String::new();
    loop {
        line.clear();
        match stdin.lock().read_line(&mut line) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        let trimmed = line.trim_end_matches(|c| c == '\n' || c == '\r');
        if trimmed.is_empty() {
            continue;
        }
        if trimmed == "QUIT" {
            break;
        }
        let parts: Vec<&str> = trimmed.split('\t').collect();
        let resp = match parts.as_slice() {
            ["CHECK_DELTA", nonce, delta_path] => {
                run_in_forked_child(|| child_check_delta(&mut base_env, &bg, nonce, delta_path, workers))
            }
            ["CHECK_FULL", nonce, full_path] => {
                run_in_forked_child(|| child_check_full(nonce, full_path, workers))
            }
            _ => emit_json("unknown", "error", "unknown command", 0, 0, 0, 0, 0, 0),
        };
        println!("{resp}");
        let _ = std::io::stdout().flush();
    }
    std::process::exit(0);
}
