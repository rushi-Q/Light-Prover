//! expdiff — export-level evidence and kernel-term analysis for proof compression.
//!
//! Reads lean4export NDJSON exports with the parallel loader of kcompare (sources/kcompare, std-only Rust; copied
//! into base.rs with one addition: letE binder names are kept). It is an ANALYSIS tool, not part of any
//! trusted check: its output is evidence and statistics, never a verdict.
//!
//!   expdiff stats [-j N] [--targets FILE|A,B,..] [--base BASE.export] [--tsv OUT.tsv] [--top K] EXPORT
//!   expdiff diff  [-j N] [--targets FILE|A,B,..] [--tsv OUT.tsv] OLD.export NEW.export
//!   expdiff dead  [-j N] [--targets FILE|A,B,..] [--base BASE.export] [--tsv OUT.tsv] EXPORT
//!
//! Equality notions used by `diff` (per declaration, keyed by its full name):
//!   exact  = every field equal, expressions compared structurally INCLUDING binder names / binder infos
//!            (mdata transparent: the parser drops its payload, as LeanExport.parseStream does);
//!   alpha  = every field equal with Expr.eqv semantics (binder names and infos ignored) - the equality the
//!            official comparator uses for the constants it compares;
//!   stmt   = kind + universe parameters + type equal (alpha): "the statement did not change".
//! Equality is decided by 64-bit structural hashes (two independent seeds = 128 bits); a collision would
//! only mislabel a changed declaration as unchanged in this report (no verdict depends on it).

include!("base.rs");

use std::io::Write as IoWrite;
use std::sync::atomic::{AtomicUsize, Ordering};

// ---------------------------------------------------------------------------------------------------
// structural hashes
// ---------------------------------------------------------------------------------------------------

/// --private-modulo: hash `_private.<Module...>.<n>.<rest>` as `_private.<rest>` (the module part of private names
/// changes when modules are merged or split; the rest is the user's name).
static PRIVATE_MODULO: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

struct Hashes {
    hn: Vec<u64>,
    he_alpha: Vec<u64>,
    he_exact: Vec<u64>,
}

fn hashes(env: &Env, seed: u64) -> Hashes {
    let nn = env.names.len();
    let mut hn = vec![0u64; nn];
    hn[0] = hparts(seed, 1, &[]);
    let pm = PRIVATE_MODULO.load(std::sync::atomic::Ordering::Relaxed);
    // state per name (private-modulo): 0 = ordinary, 1 = inside the module part of a _private name, 2 = after it
    let mut pst = if pm { vec![0u8; nn] } else { Vec::new() };
    for i in 1..nn {
        let r = env.names[i];
        let pre = hn[r.pre as usize];
        let c = env.comp_ref(i as u32);
        if pm {
            let ps = pst[r.pre as usize];
            if r.pre == 0 {
                if let CompRef::Str(b) = &c {
                    if &b[..] == b"_private" {
                        pst[i] = 1;
                        hn[i] = hparts(seed, 4, &[pre]);
                        continue;
                    }
                }
            } else if ps == 1 {
                // skip the module components; the numeric marker ends the module part
                pst[i] = if matches!(c, CompRef::Num(_)) { 2 } else { 1 };
                hn[i] = pre;
                continue;
            } else {
                pst[i] = ps;
            }
        }
        hn[i] = match c {
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
    let mut ha = vec![0u64; ne];
    let mut hx = vec![0u64; ne];
    let mut v: Vec<u64> = Vec::new();
    for i in 0..ne {
        let e = env.exprs[i];
        let (a, x) = match e.kind {
            E_BVAR => {
                let h = hparts(seed, 20, &[e.a as u64 | ((e.b as u64) << 32)]);
                (h, h)
            }
            E_SORT => {
                let h = hparts(seed, 21, &[hl[e.a as usize]]);
                (h, h)
            }
            E_CONST => {
                v.clear();
                v.push(hn[e.a as usize]);
                for k in 0..e.c {
                    v.push(hl[env.pool[(e.b + k) as usize] as usize]);
                }
                let h = hparts(seed, 22, &v);
                (h, h)
            }
            E_APP => (
                hparts(seed, 23, &[ha[e.a as usize], ha[e.b as usize]]),
                hparts(seed, 23, &[hx[e.a as usize], hx[e.b as usize]]),
            ),
            E_LAM | E_PI => {
                let tag = if e.kind == E_LAM { 24 } else { 25 };
                (
                    hparts(seed, tag, &[ha[e.a as usize], ha[e.b as usize]]),
                    hparts(seed, tag, &[hn[e.c as usize], e.flag as u64, hx[e.a as usize], hx[e.b as usize]]),
                )
            }
            E_LET => {
                let ln = env.let_name.get(&(i as u32)).map(|&n| hn[n as usize]).unwrap_or(0);
                (
                    hparts(seed, 26, &[ha[e.a as usize], ha[e.b as usize], ha[e.c as usize], e.flag as u64]),
                    hparts(seed, 26, &[ln, hx[e.a as usize], hx[e.b as usize], hx[e.c as usize], e.flag as u64]),
                )
            }
            E_PROJ => (
                hparts(seed, 27, &[hn[e.a as usize], e.c as u64, ha[e.b as usize]]),
                hparts(seed, 27, &[hn[e.a as usize], e.c as u64, hx[e.b as usize]]),
            ),
            E_NAT => {
                let h = hparts(seed, 28, &[hbytes(seed, env.lit(&e))]);
                (h, h)
            }
            E_STR => {
                let raw = env.lit(&e);
                let b = if e.flag != 0 { decode_json_string(raw) } else { raw.to_vec() };
                let h = hparts(seed, 29, &[hbytes(seed, &b)]);
                (h, h)
            }
            E_MDATA => (ha[e.a as usize], hx[e.a as usize]),
            _ => (0, 0),
        };
        ha[i] = a;
        hx[i] = x;
    }
    Hashes { hn, he_alpha: ha, he_exact: hx }
}

/// Digest of a declaration. `he` = alpha or exact expression hashes; `with_name` = include its own name.
/// `stmt_only` = kind + universe params + type only.
fn decl_digest(h: &Hashes, he: &[u64], d: &Decl, seed: u64, with_name: bool, stmt_only: bool) -> u64 {
    // without its own name: occurrences of the name in `all` (mutual block lists) are masked too
    let own = h.hn[d.name as usize];
    let names = |v: &[u32]| -> Vec<u64> {
        v.iter().map(|&n| h.hn[n as usize]).map(|x| if !with_name && x == own { 0 } else { x }).collect()
    };
    let mut v = vec![if with_name { h.hn[d.name as usize] } else { 0 }, hparts(seed, 40, &names(&d.lparams)), he[d.ty as usize]];
    if stmt_only {
        return hparts(seed, 70 + d.kind as u64, &v);
    }
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
            v.push(h.hn[d.induct as usize]);
            v.extend(d.nums[..3].iter().copied());
            v.push(d.is_unsafe as u64);
        }
        D_REC => {
            v.push(hparts(seed, 41, &names(&d.all)));
            v.extend(d.nums.iter().copied());
            v.extend([d.k as u64, d.is_unsafe as u64]);
            for &(c, nf, rhs) in &d.rules {
                v.push(hparts(seed, 43, &[h.hn[c as usize], nf, he[rhs as usize]]));
            }
        }
        _ => {}
    }
    hparts(seed, 50 + d.kind as u64, &v)
}

const SEED1: u64 = 0x1234_5678_9abc_def1;
const SEED2: u64 = 0x0fed_cba9_8765_4321;

#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct D128(u64, u64);

struct Digests {
    name: Vec<D128>,  // per decl: name hash
    exact: Vec<D128>, // full, binder names included
    alpha: Vec<D128>, // full, Expr.eqv semantics
    stmt: Vec<D128>,  // kind + lparams + type (alpha)
    anon: Vec<D128>,  // full alpha without the declaration's own name (rename detection)
    tyh: Vec<D128>,   // type only (alpha), without name/lparams/kind (same-statement search)
    h1: Hashes,       // per-node hashes (seed 1), kept for --explain
}

fn digests(env: &Env) -> Digests {
    let (h1, h2) = std::thread::scope(|s| {
        let a = s.spawn(|| hashes(env, SEED1));
        let b = s.spawn(|| hashes(env, SEED2));
        (a.join().unwrap(), b.join().unwrap())
    });
    let n = env.decls.len();
    let mut dg = Digests {
        name: Vec::with_capacity(n),
        exact: Vec::with_capacity(n),
        alpha: Vec::with_capacity(n),
        stmt: Vec::with_capacity(n),
        anon: Vec::with_capacity(n),
        tyh: Vec::with_capacity(n),
        h1: Hashes { hn: Vec::new(), he_alpha: Vec::new(), he_exact: Vec::new() },
    };
    for d in &env.decls {
        dg.name.push(D128(h1.hn[d.name as usize], h2.hn[d.name as usize]));
        dg.exact.push(D128(decl_digest(&h1, &h1.he_exact, d, SEED1, true, false), decl_digest(&h2, &h2.he_exact, d, SEED2, true, false)));
        dg.alpha.push(D128(decl_digest(&h1, &h1.he_alpha, d, SEED1, true, false), decl_digest(&h2, &h2.he_alpha, d, SEED2, true, false)));
        dg.stmt.push(D128(decl_digest(&h1, &h1.he_alpha, d, SEED1, true, true), decl_digest(&h2, &h2.he_alpha, d, SEED2, true, true)));
        dg.anon.push(D128(decl_digest(&h1, &h1.he_alpha, d, SEED1, false, false), decl_digest(&h2, &h2.he_alpha, d, SEED2, false, false)));
        dg.tyh.push(D128(h1.he_alpha[d.ty as usize], h2.he_alpha[d.ty as usize]));
    }
    drop(h2);
    dg.h1 = h1;
    dg
}

// ---------------------------------------------------------------------------------------------------
// closure
// ---------------------------------------------------------------------------------------------------

fn parse_targets(spec: &str) -> R<Vec<String>> {
    let text = if std::path::Path::new(spec).is_file() {
        std::fs::read_to_string(spec).map_err(|e| Fail::Decline(format!("cannot read {}: {}", spec, e)))?
    } else {
        spec.replace(',', " ")
    };
    Ok(text.split_whitespace().map(String::from).collect())
}

/// Declarations reachable from the targets (runForUsedConsts edges). Returns (in-closure flags, missing names).
fn closure(env: &Env, targets: &[String]) -> R<(Vec<bool>, Vec<String>)> {
    let mut in_cl = vec![false; env.decls.len()];
    let mut missing = Vec::new();
    let mut work: Vec<u32> = Vec::new();
    for t in targets {
        let path = to_name(t)?;
        match env.decl_by_path(&path) {
            Some(d) => {
                if !in_cl[d as usize] {
                    in_cl[d as usize] = true;
                    work.push(d);
                }
            }
            None => missing.push(t.clone()),
        }
    }
    let mut vis = Bits::new(env.exprs.len());
    let mut stack = Vec::new();
    let mut dangling: FxSet<u32> = FxSet::default();
    while let Some(d) = work.pop() {
        let decl = &env.decls[d as usize];
        let mut found: Vec<u32> = Vec::new();
        decl_consts(env, decl, &mut vis, &mut stack, &mut |n| {
            found.push(n);
            Ok(())
        })?;
        for n in found {
            let r = env.canon[n as usize];
            let di = env.decl_of[r as usize];
            if di == NONE {
                dangling.insert(r);
            } else if !in_cl[di as usize] {
                in_cl[di as usize] = true;
                work.push(di);
            }
        }
    }
    for r in dangling {
        missing.push(format!("(referenced, not declared) {}", env.name_str(r)));
    }
    Ok((in_cl, missing))
}


/// The statement closure ("trusted reading set"): what a reader must understand to know WHAT the targets state —
/// constants reachable from the targets' types through types, definition/opaque values, inductive types with their
/// constructors and recursors, but never through theorem proofs.
fn statement_closure(env: &Env, targets: &[String]) -> R<Vec<bool>> {
    let mut in_cl = vec![false; env.decls.len()];
    let mut work: Vec<u32> = Vec::new();
    for t in targets {
        if let Some(d) = env.decl_by_path(&to_name(t)?) {
            if !in_cl[d as usize] {
                in_cl[d as usize] = true;
                work.push(d);
            }
        }
    }
    let mut vis = Bits::new(env.exprs.len());
    let mut stack = Vec::new();
    while let Some(d) = work.pop() {
        let decl = &env.decls[d as usize];
        let mut found: Vec<u32> = Vec::new();
        let mut f = |n: u32| -> R<()> {
            found.push(n);
            Ok(())
        };
        expr_consts(env, decl.ty, &mut vis, &mut stack, &mut f)?;
        match decl.kind {
            D_DEFN | D_OPAQUE => expr_consts(env, decl.val, &mut vis, &mut stack, &mut f)?,
            D_INDUCT => {
                for &c in decl.ctors.iter().chain(decl.all.iter()) {
                    f(c)?;
                }
            }
            D_CTOR => f(decl.induct)?,
            D_REC => {
                for &(c, _, rhs) in &decl.rules {
                    f(c)?;
                    expr_consts(env, rhs, &mut vis, &mut stack, &mut f)?;
                }
            }
            _ => {}
        }
        for n in found {
            let di = env.decl_of[env.canon[n as usize] as usize];
            if di != NONE && !in_cl[di as usize] {
                in_cl[di as usize] = true;
                work.push(di);
            }
        }
    }
    Ok(in_cl)
}

// ---------------------------------------------------------------------------------------------------
// sizes
// ---------------------------------------------------------------------------------------------------

/// Tree size (sharing expanded, saturating in f64) and depth of every expression, bottom-up.
fn tree_sizes(env: &Env) -> (Vec<f64>, Vec<u32>) {
    let ne = env.exprs.len();
    let mut t = vec![0f64; ne];
    let mut dp = vec![0u32; ne];
    for i in 0..ne {
        let e = env.exprs[i];
        let (s, d) = match e.kind {
            E_APP => (1.0 + t[e.a as usize] + t[e.b as usize], 1 + dp[e.a as usize].max(dp[e.b as usize])),
            E_LAM | E_PI => (1.0 + t[e.a as usize] + t[e.b as usize], 1 + dp[e.a as usize].max(dp[e.b as usize])),
            E_LET => (
                1.0 + t[e.a as usize] + t[e.b as usize] + t[e.c as usize],
                1 + dp[e.a as usize].max(dp[e.b as usize]).max(dp[e.c as usize]),
            ),
            E_PROJ => (1.0 + t[e.b as usize], 1 + dp[e.b as usize]),
            E_MDATA => (t[e.a as usize], dp[e.a as usize]),
            _ => (1.0, 1),
        };
        t[i] = s;
        dp[i] = d;
    }
    (t, dp)
}

fn push_children(env: &Env, e: u32, st: &mut Vec<u32>) {
    let x = env.exprs[e as usize];
    match x.kind {
        E_APP | E_LAM | E_PI => {
            st.push(x.a);
            st.push(x.b);
        }
        E_LET => {
            st.push(x.a);
            st.push(x.b);
            st.push(x.c);
        }
        E_PROJ => st.push(x.b),
        E_MDATA => st.push(x.a),
        _ => {}
    }
}

/// Number of distinct expression nodes reachable from the roots (mdata nodes skipped).
fn dag_size(env: &Env, roots: &[u32], vis: &mut FxSet<u32>, st: &mut Vec<u32>) -> u64 {
    let mut n = 0u64;
    for &r in roots {
        st.push(r);
    }
    while let Some(e) = st.pop() {
        if !vis.insert(e) {
            continue;
        }
        if env.exprs[e as usize].kind != E_MDATA {
            n += 1;
        }
        push_children(env, e, st);
    }
    n
}

fn decl_roots(d: &Decl) -> (Vec<u32>, Vec<u32>) {
    let ty = vec![d.ty];
    let mut val = Vec::new();
    match d.kind {
        D_DEFN | D_THM | D_OPAQUE => val.push(d.val),
        D_REC => {
            for &(_, _, rhs) in &d.rules {
                val.push(rhs);
            }
        }
        _ => {}
    }
    (ty, val)
}

#[derive(Clone, Copy, Default)]
struct DeclSize {
    ty_dag: u64,
    val_dag: u64,
    all_dag: u64,
    ty_tree: f64,
    val_tree: f64,
    depth: u32,
}

fn per_decl_sizes(env: &Env, sel: &[bool], tree: &[f64], depth: &[u32], threads: usize) -> Vec<DeclSize> {
    let n = env.decls.len();
    let out: Vec<std::sync::Mutex<Vec<(usize, DeclSize)>>> = (0..threads).map(|_| std::sync::Mutex::new(Vec::new())).collect();
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for t in 0..threads {
            let out = &out;
            let next = &next;
            s.spawn(move || {
                let mut vis: FxSet<u32> = FxSet::default();
                let mut st = Vec::new();
                let mut mine = Vec::new();
                loop {
                    let i = next.fetch_add(64, Ordering::Relaxed);
                    if i >= n {
                        break;
                    }
                    for j in i..(i + 64).min(n) {
                        if !sel[j] {
                            continue;
                        }
                        let d = &env.decls[j];
                        let (ty, val) = decl_roots(d);
                        vis.clear();
                        let ty_dag = dag_size(env, &ty, &mut vis, &mut st);
                        let extra = dag_size(env, &val, &mut vis, &mut st);
                        vis.clear();
                        let val_dag = dag_size(env, &val, &mut vis, &mut st);
                        let val_tree: f64 = val.iter().map(|&v| tree[v as usize]).sum();
                        let dep = val.iter().map(|&v| depth[v as usize]).max().unwrap_or(0).max(depth[d.ty as usize]);
                        if vis.capacity() > (1 << 22) {
                            vis = FxSet::default();
                        }
                        mine.push((j, DeclSize { ty_dag, val_dag, all_dag: ty_dag + extra, ty_tree: tree[d.ty as usize], val_tree, depth: dep }));
                    }
                }
                out[t].lock().unwrap().append(&mut mine);
            });
        }
    });
    let mut res = vec![DeclSize::default(); n];
    for m in out {
        for (j, s) in m.into_inner().unwrap() {
            res[j] = s;
        }
    }
    res
}

/// Distinct expression nodes reachable from the selected declarations (global sharing).
fn global_dag(env: &Env, sel: &[bool]) -> u64 {
    let mut vis = Bits::new(env.exprs.len());
    let mut st: Vec<u32> = Vec::new();
    let mut n = 0u64;
    for (j, d) in env.decls.iter().enumerate() {
        if !sel[j] {
            continue;
        }
        let (ty, val) = decl_roots(d);
        st.extend(ty);
        st.extend(val);
        while let Some(e) = st.pop() {
            if vis.test_set(e) {
                continue;
            }
            if env.exprs[e as usize].kind != E_MDATA {
                n += 1;
            }
            push_children(env, e, &mut st);
        }
    }
    n
}


// ---------------------------------------------------------------------------------------------------
// sharing and dependency graph: nodes owned by one declaration, in/out degree between declarations
// ---------------------------------------------------------------------------------------------------

struct ABits(Vec<std::sync::atomic::AtomicU64>);
impl ABits {
    fn new(n: usize) -> ABits {
        ABits((0..n / 64 + 1).map(|_| std::sync::atomic::AtomicU64::new(0)).collect())
    }
    /// sets bit i, returns whether it was set before
    #[inline]
    fn set(&self, i: u32) -> bool {
        let m = 1u64 << (i & 63);
        self.0[(i >> 6) as usize].fetch_or(m, Ordering::Relaxed) & m != 0
    }
    #[inline]
    fn get(&self, i: u32) -> bool {
        self.0[(i >> 6) as usize].load(Ordering::Relaxed) >> (i & 63) & 1 == 1
    }
}

struct Graph {
    excl: Vec<u64>,  // per decl: expression nodes reachable from this declaration only (among the selected ones)
    indeg: Vec<u32>, // per decl: number of selected declarations that reference it
    outdeg: Vec<u32>,
    refs: Vec<Vec<u32>>, // per decl: referenced declarations (selected ones only)
}

fn graph(env: &Env, sel: &[bool], threads: usize) -> Graph {
    let n = env.decls.len();
    let once = ABits::new(env.exprs.len());
    let twice = ABits::new(env.exprs.len());
    let indeg: Vec<std::sync::atomic::AtomicU32> = (0..n).map(|_| std::sync::atomic::AtomicU32::new(0)).collect();
    let outs: Vec<std::sync::Mutex<Vec<(usize, Vec<u32>)>>> = (0..threads).map(|_| std::sync::Mutex::new(Vec::new())).collect();
    let next = AtomicUsize::new(0);
    // pass 1: mark nodes seen by >= 1 / >= 2 declarations; collect references
    std::thread::scope(|s| {
        for t in 0..threads {
            let (once, twice, indeg, outs, next) = (&once, &twice, &indeg, &outs, &next);
            s.spawn(move || {
                let mut vis: FxSet<u32> = FxSet::default();
                let mut st: Vec<u32> = Vec::new();
                let mut mine = Vec::new();
                let mut rs: FxSet<u32> = FxSet::default();
                loop {
                    let i = next.fetch_add(64, Ordering::Relaxed);
                    if i >= n {
                        break;
                    }
                    for j in i..(i + 64).min(n) {
                        if !sel[j] {
                            continue;
                        }
                        let d = &env.decls[j];
                        let (ty, val) = decl_roots(d);
                        vis.clear();
                        rs.clear();
                        st.extend(ty);
                        st.extend(val);
                        while let Some(e) = st.pop() {
                            if !vis.insert(e) {
                                continue;
                            }
                            if once.set(e) {
                                twice.set(e);
                            }
                            let x = env.exprs[e as usize];
                            if x.kind == E_CONST || x.kind == E_PROJ {
                                let r = env.canon[x.a as usize];
                                let di = env.decl_of[r as usize];
                                if di != NONE && di as usize != j && sel[di as usize] {
                                    rs.insert(di);
                                }
                            }
                            push_children(env, e, &mut st);
                        }
                        let mut v: Vec<u32> = rs.iter().copied().collect();
                        v.sort();
                        for &di in &v {
                            indeg[di as usize].fetch_add(1, Ordering::Relaxed);
                        }
                        mine.push((j, v));
                        if vis.capacity() > (1 << 22) {
                            vis = FxSet::default();
                        }
                    }
                }
                outs[t].lock().unwrap().append(&mut mine);
            });
        }
    });
    let mut refs: Vec<Vec<u32>> = vec![Vec::new(); n];
    for m in outs {
        for (j, v) in m.into_inner().unwrap() {
            refs[j] = v;
        }
    }
    // pass 2: exclusive nodes per declaration
    let excl: Vec<std::sync::atomic::AtomicU64> = (0..n).map(|_| std::sync::atomic::AtomicU64::new(0)).collect();
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..threads {
            let (twice, excl, next) = (&twice, &excl, &next);
            s.spawn(move || {
                let mut vis: FxSet<u32> = FxSet::default();
                let mut st: Vec<u32> = Vec::new();
                loop {
                    let i = next.fetch_add(64, Ordering::Relaxed);
                    if i >= n {
                        break;
                    }
                    for j in i..(i + 64).min(n) {
                        if !sel[j] {
                            continue;
                        }
                        let (ty, val) = decl_roots(&env.decls[j]);
                        vis.clear();
                        st.extend(ty);
                        st.extend(val);
                        let mut c = 0u64;
                        while let Some(e) = st.pop() {
                            if !vis.insert(e) {
                                continue;
                            }
                            if !twice.get(e) && env.exprs[e as usize].kind != E_MDATA {
                                c += 1;
                            }
                            push_children(env, e, &mut st);
                        }
                        excl[j].store(c, Ordering::Relaxed);
                        if vis.capacity() > (1 << 22) {
                            vis = FxSet::default();
                        }
                    }
                }
            });
        }
    });
    let outdeg = refs.iter().map(|v| v.len() as u32).collect();
    Graph {
        excl: excl.into_iter().map(|a| a.into_inner()).collect(),
        indeg: indeg.into_iter().map(|a| a.into_inner()).collect(),
        outdeg,
        refs,
    }
}

/// Shortest reference distance from the targets (BFS over references), u32::MAX if unreachable.
fn bfs_depth(env: &Env, g: &Graph, roots: &[u32]) -> Vec<u32> {
    let mut d = vec![u32::MAX; env.decls.len()];
    let mut q = std::collections::VecDeque::new();
    for &r in roots {
        if d[r as usize] == u32::MAX {
            d[r as usize] = 0;
            q.push_back(r);
        }
    }
    while let Some(x) = q.pop_front() {
        for &y in &g.refs[x as usize] {
            if d[y as usize] == u32::MAX {
                d[y as usize] = d[x as usize] + 1;
                q.push_back(y);
            }
        }
    }
    d
}

/// Longest reference chain below each declaration (height in the dependency DAG; cycles cannot occur in
/// an environment, a defensive cap stops on malformed input).
fn heights(env: &Env, g: &Graph, sel: &[bool]) -> Vec<u32> {
    let n = env.decls.len();
    let mut h = vec![u32::MAX; n];
    let mut st: Vec<(u32, bool)> = Vec::new();
    for j in 0..n {
        if !sel[j] || h[j] != u32::MAX {
            continue;
        }
        st.push((j as u32, false));
        while let Some((x, done)) = st.pop() {
            let xu = x as usize;
            if done {
                let m = g.refs[xu].iter().map(|&y| h[y as usize]).filter(|&v| v != u32::MAX && v != u32::MAX - 1).max();
                h[xu] = m.map(|v| v + 1).unwrap_or(0);
                continue;
            }
            if h[xu] != u32::MAX {
                continue;
            }
            h[xu] = u32::MAX - 1; // in progress
            st.push((x, true));
            for &y in &g.refs[xu] {
                if h[y as usize] == u32::MAX {
                    st.push((y, false));
                }
            }
        }
    }
    h
}

// ---------------------------------------------------------------------------------------------------
// name classes (auxiliary / generated declarations)
// ---------------------------------------------------------------------------------------------------

fn name_class(s: &str) -> &'static str {
    let last = s.rsplit('.').next().unwrap_or(s);
    if s.starts_with("_private.") {
        // private names: classify by their user part
        if s.contains("._proof_") || s.contains(".proof_") {
            return "private-aux-proof";
        }
        return "private";
    }
    if last.starts_with("_proof_") || last.starts_with("proof_") || s.contains("._proof_") {
        return "aux-proof";
    }
    if last.starts_with("match_") || s.contains(".match_") {
        return "match";
    }
    if last.starts_with("eq_") || last == "eq_def" || last.starts_with("eq_unfold") {
        return "equation";
    }
    if last == "congr_simp" || last.ends_with("_congr_simp") {
        return "congr_simp";
    }
    if matches!(
        last,
        "rec" | "recOn" | "casesOn" | "noConfusion" | "noConfusionType" | "below" | "brecOn" | "binductionOn" | "ibelow" | "mk" | "inj"
            | "injEq" | "sizeOf_spec" | "ctorIdx" | "toCtorIdx"
    ) || last.starts_with("_sizeOf")
        || last.ends_with("_def")
    {
        return "structural";
    }
    if last.starts_with("inst") {
        return "instance";
    }
    if last.starts_with("_") || s.contains("._") {
        return "other-aux";
    }
    "user"
}

// ---------------------------------------------------------------------------------------------------
// loose bound variables (for dead-binder detection)
// ---------------------------------------------------------------------------------------------------

struct Loose {
    lbr: Vec<u32>, // loose bvar range
    lo: Vec<u64>,  // bit i = bvar i occurs loose (i < 64); exact iff ex[e]
    ex: Vec<bool>,
}

fn loose(env: &Env) -> Loose {
    let ne = env.exprs.len();
    let mut lbr = vec![0u32; ne];
    let mut lo = vec![0u64; ne];
    let mut ex = vec![true; ne];
    for i in 0..ne {
        let e = env.exprs[i];
        let (r, l, x) = match e.kind {
            E_BVAR => {
                let idx = e.a as u64 | ((e.b as u64) << 32);
                let r = (idx + 1).min(u32::MAX as u64) as u32;
                (r, if idx < 64 { 1u64 << idx } else { 0 }, true)
            }
            E_APP => {
                let (a, b) = (e.a as usize, e.b as usize);
                (lbr[a].max(lbr[b]), lo[a] | lo[b], ex[a] && ex[b])
            }
            E_LAM | E_PI => {
                let (t, b) = (e.a as usize, e.b as usize);
                let rb = lbr[b].saturating_sub(1);
                // bit 63 of the shifted body set needs body bit 64: exact only if the body has no loose bvar >= 64
                let xb = ex[b] && lbr[b] <= 64;
                (lbr[t].max(rb), lo[t] | (lo[b] >> 1), ex[t] && xb)
            }
            E_LET => {
                let (t, v, b) = (e.a as usize, e.b as usize, e.c as usize);
                let rb = lbr[b].saturating_sub(1);
                let xb = ex[b] && lbr[b] <= 64;
                (lbr[t].max(lbr[v]).max(rb), lo[t] | lo[v] | (lo[b] >> 1), ex[t] && ex[v] && xb)
            }
            E_PROJ => {
                let b = e.b as usize;
                (lbr[b], lo[b], ex[b])
            }
            E_MDATA => {
                let a = e.a as usize;
                (lbr[a], lo[a], ex[a])
            }
            _ => (0, 0, true),
        };
        lbr[i] = r;
        lo[i] = l;
        ex[i] = x || r <= 64;
    }
    Loose { lbr, lo, ex }
}

/// Does expression e contain loose bvar k?
fn has_loose(env: &Env, lz: &Loose, e: u32, k: u32, memo: &mut FxSet<(u32, u32)>, st: &mut Vec<(u32, u32)>) -> bool {
    memo.clear();
    st.clear();
    st.push((e, k));
    while let Some((e, k)) = st.pop() {
        let eu = e as usize;
        if lz.lbr[eu] <= k {
            continue;
        }
        if k < 64 && lz.ex[eu] {
            if lz.lo[eu] >> k & 1 == 1 {
                return true;
            }
            continue;
        }
        if !memo.insert((e, k)) {
            continue;
        }
        let x = env.exprs[eu];
        match x.kind {
            E_BVAR => {
                let idx = x.a as u64 | ((x.b as u64) << 32);
                if idx == k as u64 {
                    return true;
                }
            }
            E_APP => {
                st.push((x.a, k));
                st.push((x.b, k));
            }
            E_LAM | E_PI => {
                st.push((x.a, k));
                st.push((x.b, k + 1));
            }
            E_LET => {
                st.push((x.a, k));
                st.push((x.b, k));
                st.push((x.c, k + 1));
            }
            E_PROJ => st.push((x.b, k)),
            E_MDATA => st.push((x.a, k)),
            _ => {}
        }
    }
    false
}

fn strip_mdata(env: &Env, mut e: u32) -> u32 {
    while env.exprs[e as usize].kind == E_MDATA {
        e = env.exprs[e as usize].a;
    }
    e
}

/// Application spine: head and arguments (outermost last).
fn spine(env: &Env, mut e: u32, args: &mut Vec<u32>) -> u32 {
    args.clear();
    loop {
        e = strip_mdata(env, e);
        let x = env.exprs[e as usize];
        if x.kind != E_APP {
            break;
        }
        args.push(x.b);
        e = x.a;
    }
    args.reverse();
    e
}

const DK_LET: u8 = 0; // let x := v; b  with x unused (have/let, nondep or not)
const DK_LETFUN: u8 = 1; // letFun v (fun x => b) with x unused (Lean's `have` encoding)
const DK_BETA: u8 = 2; // (fun x => b) v with x unused
const DK_HYP: u8 = 3; // leading hypothesis of a theorem/definition used neither in the rest of the type nor the value
const DK_NAMES: [&str; 4] = ["let", "letFun", "beta", "hyp"];

#[derive(Clone)]
struct Dead {
    decl: u32,
    kind: u8,
    expr: u32,  // the redex / let node (hyp: the lambda node)
    dval: u32,  // the dead value (hyp: the binder type)
    bname: u32, // binder name index (NONE if unknown)
    binfo: u8,
    pos: u32, // hyp: 0-based binder position
}

fn find_dead(env: &Env, lz: &Loose, sel: &[bool], letfun: Option<u32>, threads: usize) -> Vec<Dead> {
    let n = env.decls.len();
    let out: Vec<std::sync::Mutex<Vec<Dead>>> = (0..threads).map(|_| std::sync::Mutex::new(Vec::new())).collect();
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for t in 0..threads {
            let out = &out;
            let next = &next;
            s.spawn(move || {
                let mut vis: FxSet<u32> = FxSet::default();
                let mut memo: FxSet<(u32, u32)> = FxSet::default();
                let mut st: Vec<u32> = Vec::new();
                let mut st2: Vec<(u32, u32)> = Vec::new();
                let mut args: Vec<u32> = Vec::new();
                let mut mine = Vec::new();
                loop {
                    let i = next.fetch_add(16, Ordering::Relaxed);
                    if i >= n {
                        break;
                    }
                    for j in i..(i + 16).min(n) {
                        if !sel[j] {
                            continue;
                        }
                        let d = &env.decls[j];
                        if !matches!(d.kind, D_DEFN | D_THM | D_OPAQUE) {
                            continue;
                        }
                        // (1) leading hypotheses
                        let mut ty = strip_mdata(env, d.ty);
                        let mut val = strip_mdata(env, d.val);
                        let mut pos = 0u32;
                        loop {
                            let tx = env.exprs[ty as usize];
                            let vx = env.exprs[val as usize];
                            if tx.kind != E_PI || vx.kind != E_LAM {
                                break;
                            }
                            if !has_loose(env, lz, vx.b, 0, &mut memo, &mut st2) && !has_loose(env, lz, tx.b, 0, &mut memo, &mut st2) {
                                mine.push(Dead { decl: j as u32, kind: DK_HYP, expr: val, dval: vx.a, bname: vx.c, binfo: vx.flag, pos });
                            }
                            ty = strip_mdata(env, tx.b);
                            val = strip_mdata(env, vx.b);
                            pos += 1;
                        }
                        // (2) dead let / letFun / beta redexes anywhere in the value
                        vis.clear();
                        st.clear();
                        st.push(d.val);
                        while let Some(e) = st.pop() {
                            if !vis.insert(e) {
                                continue;
                            }
                            let x = env.exprs[e as usize];
                            match x.kind {
                                E_LET => {
                                    if !has_loose(env, lz, x.c, 0, &mut memo, &mut st2) {
                                        let bn = env.let_name.get(&e).copied().unwrap_or(NONE);
                                        mine.push(Dead { decl: j as u32, kind: DK_LET, expr: e, dval: x.b, bname: bn, binfo: x.flag, pos: 0 });
                                    }
                                }
                                E_APP => {
                                    let f = strip_mdata(env, x.a);
                                    let fx = env.exprs[f as usize];
                                    if fx.kind == E_LAM {
                                        if !has_loose(env, lz, fx.b, 0, &mut memo, &mut st2) {
                                            mine.push(Dead { decl: j as u32, kind: DK_BETA, expr: e, dval: x.b, bname: fx.c, binfo: fx.flag, pos: 0 });
                                        }
                                    } else if let Some(lf) = letfun {
                                        // letFun α β v f  (we test at the outermost application only)
                                        let head = spine(env, e, &mut args);
                                        let hx = env.exprs[head as usize];
                                        if hx.kind == E_CONST && env.canon[hx.a as usize] == lf && args.len() == 4 {
                                            let fl = strip_mdata(env, args[3]);
                                            let flx = env.exprs[fl as usize];
                                            if flx.kind == E_LAM && !has_loose(env, lz, flx.b, 0, &mut memo, &mut st2) {
                                                mine.push(Dead { decl: j as u32, kind: DK_LETFUN, expr: e, dval: args[2], bname: flx.c, binfo: flx.flag, pos: 0 });
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                            push_children(env, e, &mut st);
                        }
                        if vis.capacity() > (1 << 22) {
                            vis = FxSet::default();
                        }
                        if memo.capacity() > (1 << 20) {
                            memo = FxSet::default();
                        }
                    }
                }
                out[t].lock().unwrap().append(&mut mine);
            });
        }
    });
    let mut res = Vec::new();
    for m in out {
        res.append(&mut m.into_inner().unwrap());
    }
    res.sort_by_key(|d| (d.decl, d.kind, d.expr, d.pos));
    res
}

// ---------------------------------------------------------------------------------------------------
// output helpers
// ---------------------------------------------------------------------------------------------------

fn kind_name(k: u8) -> &'static str {
    match k {
        D_AXIOM => "axiom",
        D_DEFN => "def",
        D_THM => "thm",
        D_OPAQUE => "opaque",
        D_QUOT => "quot",
        D_INDUCT => "induct",
        D_CTOR => "ctor",
        D_REC => "rec",
        _ => "?",
    }
}

fn tsv_name(s: &str) -> String {
    s.replace('\t', "\\t").replace('\n', "\\n")
}

fn open_out(path: &Option<String>) -> Option<std::io::BufWriter<File>> {
    path.as_ref().map(|p| std::io::BufWriter::with_capacity(1 << 20, File::create(p).unwrap_or_else(|e| panic!("cannot create {}: {}", p, e))))
}

fn binfo_name(b: u8) -> &'static str {
    match b {
        0 => "default",
        1 => "implicit",
        2 => "strictImplicit",
        3 => "instImplicit",
        _ => "?",
    }
}

/// Base classification: decl j of env is "base" if the base export declares the same name with the same
/// alpha digest; "base-changed" if the name exists there with another digest.
fn base_class(env: &Env, dg: &Digests, base: &Option<(Env, Digests)>) -> Vec<u8> {
    let mut cls = vec![0u8; env.decls.len()];
    if let Some((b, bd)) = base {
        let mut idx: FxMap<(u64, u64), u32> = FxMap::default();
        idx.reserve(b.decls.len());
        for (i, n) in bd.name.iter().enumerate() {
            idx.insert((n.0, n.1), i as u32);
        }
        for (j, n) in dg.name.iter().enumerate() {
            if let Some(&i) = idx.get(&(n.0, n.1)) {
                cls[j] = if bd.alpha[i as usize] == dg.alpha[j] { 1 } else { 2 };
            }
        }
        let _ = env;
    }
    cls
}

const BASE_NAMES: [&str; 3] = ["project", "base", "base-changed"];


// ---------------------------------------------------------------------------------------------------
// pretty printer (compact, explicit; bvars shown by binder name) and first-difference search
// ---------------------------------------------------------------------------------------------------

fn pp_level(env: &Env, l: u32, out: &mut String) {
    let mut k = 0u32;
    let mut x = l;
    while env.levels[x as usize].kind == L_SUCC {
        k += 1;
        x = env.levels[x as usize].a;
    }
    let r = env.levels[x as usize];
    let base = match r.kind {
        L_ZERO => None,
        L_PARAM => Some(env.name_str(r.a)),
        L_MAX | L_IMAX => {
            let mut s = String::new();
            s.push_str(if r.kind == L_MAX { "max (" } else { "imax (" });
            pp_level(env, r.a, &mut s);
            s.push_str(") (");
            pp_level(env, r.b, &mut s);
            s.push(')');
            Some(s)
        }
        _ => None,
    };
    match base {
        None => out.push_str(&k.to_string()),
        Some(b) => {
            out.push_str(&b);
            if k > 0 {
                out.push_str(&format!("+{}", k));
            }
        }
    }
}

struct Pp<'a> {
    env: &'a Env,
    out: String,
    budget: isize,
    names: Vec<String>,
}

impl<'a> Pp<'a> {
    fn new(env: &'a Env, budget: isize, names: Vec<String>) -> Pp<'a> {
        Pp { env, out: String::new(), budget, names }
    }
    fn bname(&self, n: u32) -> String {
        if n == NONE {
            return "_".into();
        }
        let s = self.env.name_str(n);
        // hygienic names: keep the user part
        match s.find("._@.") {
            Some(i) => s[..i].to_string(),
            None => s,
        }
    }
    fn expr(&mut self, e: u32) {
        if self.budget <= 0 {
            self.out.push('…');
            return;
        }
        self.budget -= 1;
        let env = self.env;
        let x = env.exprs[e as usize];
        match x.kind {
            E_BVAR => {
                let i = x.a as usize | ((x.b as usize) << 32);
                if i < self.names.len() {
                    let n = self.names[self.names.len() - 1 - i].clone();
                    self.out.push_str(&n);
                } else {
                    self.out.push_str(&format!("#{}", i));
                }
            }
            E_SORT => {
                let l = x.a;
                if env.levels[l as usize].kind == L_ZERO {
                    self.out.push_str("Prop");
                } else {
                    self.out.push_str("Sort (");
                    pp_level(env, l, &mut self.out);
                    self.out.push(')');
                }
            }
            E_CONST => {
                self.out.push_str(&env.name_str(x.a));
                if x.c > 0 {
                    self.out.push_str(".{");
                    for k in 0..x.c {
                        if k > 0 {
                            self.out.push_str(", ");
                        }
                        pp_level(env, env.pool[(x.b + k) as usize], &mut self.out);
                    }
                    self.out.push('}');
                }
            }
            E_APP => {
                let mut args = Vec::new();
                let h = spine(env, e, &mut args);
                self.out.push('(');
                self.expr(h);
                for a in args {
                    self.out.push(' ');
                    if self.budget <= 0 {
                        self.out.push('…');
                        break;
                    }
                    self.expr(a);
                }
                self.out.push(')');
            }
            E_LAM | E_PI => {
                let (l, r) = match x.flag {
                    1 => ("{", "}"),
                    2 => ("⦃", "⦄"),
                    3 => ("[", "]"),
                    _ => ("(", ")"),
                };
                let n = self.bname(x.c);
                self.out.push_str(if x.kind == E_LAM { "(fun " } else { "(∀ " });
                self.out.push_str(&format!("{}{} : ", l, n));
                self.expr(x.a);
                self.out.push_str(r);
                self.out.push_str(if x.kind == E_LAM { " => " } else { ", " });
                self.names.push(n);
                self.expr(x.b);
                self.names.pop();
                self.out.push(')');
            }
            E_LET => {
                let n = self.bname(env.let_name.get(&e).copied().unwrap_or(NONE));
                self.out.push_str(if x.flag != 0 { "(have " } else { "(let " });
                self.out.push_str(&format!("{} : ", n));
                self.expr(x.a);
                self.out.push_str(" := ");
                self.expr(x.b);
                self.out.push_str("; ");
                self.names.push(n);
                self.expr(x.c);
                self.names.pop();
                self.out.push(')');
            }
            E_PROJ => {
                self.out.push('(');
                self.expr(x.b);
                self.out.push_str(&format!(").{}#{}", env.name_str(x.a), x.c + 1));
            }
            E_NAT => self.out.push_str(&String::from_utf8_lossy(env.lit(&x))),
            E_STR => {
                self.out.push('"');
                self.out.push_str(&String::from_utf8_lossy(env.lit(&x)));
                self.out.push('"');
            }
            E_MDATA => self.expr(x.a),
            _ => self.out.push('?'),
        }
    }
}

fn pp(env: &Env, e: u32, budget: isize, names: &[String]) -> String {
    let mut p = Pp::new(env, budget, names.to_vec());
    p.expr(e);
    p.out
}

/// Local description of a node (kind and its own fields, not its children); equal descriptions + equal
/// child hashes = equal nodes.
fn node_local(env: &Env, e: u32, exact: bool) -> String {
    let x = env.exprs[e as usize];
    match x.kind {
        E_BVAR => format!("bvar {}", x.a as u64 | ((x.b as u64) << 32)),
        E_SORT => {
            let mut s = String::from("sort ");
            pp_level(env, x.a, &mut s);
            s
        }
        E_CONST => {
            let mut s = format!("const {}", env.name_str(x.a));
            for k in 0..x.c {
                s.push(' ');
                pp_level(env, env.pool[(x.b + k) as usize], &mut s);
            }
            s
        }
        E_APP => "app".into(),
        E_LAM | E_PI => {
            let k = if x.kind == E_LAM { "lam" } else { "pi" };
            if exact {
                format!("{} {} {}", k, env.name_str(x.c), binfo_name(x.flag))
            } else {
                k.into()
            }
        }
        E_LET => {
            if exact {
                format!("let {} nondep={}", env.let_name.get(&e).map(|&n| env.name_str(n)).unwrap_or_default(), x.flag)
            } else {
                format!("let nondep={}", x.flag)
            }
        }
        E_PROJ => format!("proj {} {}", env.name_str(x.a), x.c),
        E_NAT => format!("nat {}", String::from_utf8_lossy(env.lit(&x))),
        E_STR => format!("str {:?}", String::from_utf8_lossy(env.lit(&x))),
        _ => "?".into(),
    }
}

fn children(env: &Env, e: u32) -> Vec<(&'static str, u32, Option<u32>)> {
    // (step label, child, binder name pushed when descending: Some(name idx) for bodies)
    let x = env.exprs[e as usize];
    match x.kind {
        E_APP => vec![("fn", x.a, None), ("arg", x.b, None)],
        E_LAM | E_PI => vec![("type", x.a, None), ("body", x.b, Some(x.c))],
        E_LET => vec![("type", x.a, None), ("value", x.b, None), ("body", x.c, Some(env.let_name.get(&e).copied().unwrap_or(NONE)))],
        E_PROJ => vec![("struct", x.b, None)],
        _ => vec![],
    }
}

/// First structural difference between expression a (in A) and b (in B), following the first child pair
/// whose hashes differ. Returns (path, node in A, node in B, binder names in scope in A, in B).
fn first_diff(
    a: &Env,
    ha: &[u64],
    b: &Env,
    hb: &[u64],
    mut ea: u32,
    mut eb: u32,
    exact: bool,
) -> Option<(String, u32, u32, Vec<String>, Vec<String>)> {
    let mut path = String::new();
    let mut na: Vec<String> = Vec::new();
    let mut nb: Vec<String> = Vec::new();
    loop {
        ea = strip_mdata(a, ea);
        eb = strip_mdata(b, eb);
        if ha[ea as usize] == hb[eb as usize] {
            return None;
        }
        if node_local(a, ea, exact) != node_local(b, eb, exact) {
            return Some((path, ea, eb, na, nb));
        }
        let ca = children(a, ea);
        let cb = children(b, eb);
        let mut moved = false;
        for (x, y) in ca.iter().zip(cb.iter()) {
            let (xa, ya) = (strip_mdata(a, x.1), strip_mdata(b, y.1));
            if ha[xa as usize] != hb[ya as usize] {
                if !path.is_empty() {
                    path.push('.');
                }
                path.push_str(x.0);
                if let Some(n) = x.2 {
                    na.push(if n == NONE { "_".into() } else { a.name_str(n) });
                }
                if let Some(n) = y.2 {
                    nb.push(if n == NONE { "_".into() } else { b.name_str(n) });
                }
                ea = xa;
                eb = ya;
                moved = true;
                break;
            }
        }
        if !moved {
            // hashes differ but no child differs: the difference is in this node's own fields
            return Some((path, ea, eb, na, nb));
        }
    }
}

fn explain_decl(a: &Env, da: &Digests, i: usize, b: &Env, db: &Digests, j: usize, exact: bool, budget: isize) -> String {
    let (ha, hb) = if exact { (&da.h1.he_exact, &db.h1.he_exact) } else { (&da.h1.he_alpha, &db.h1.he_alpha) };
    let x = &a.decls[i];
    let y = &b.decls[j];
    let short = |n: &[String]| -> Vec<String> {
        n.iter().map(|s| match s.find("._@.") { Some(k) => s[..k].to_string(), None => s.clone() }).collect()
    };
    let mut parts: Vec<(&str, u32, u32)> = vec![("type", x.ty, y.ty)];
    if matches!(x.kind, D_DEFN | D_THM | D_OPAQUE) && matches!(y.kind, D_DEFN | D_THM | D_OPAQUE) {
        parts.push(("value", x.val, y.val));
    }
    if x.kind == D_REC && y.kind == D_REC {
        for (k, (r1, r2)) in x.rules.iter().zip(y.rules.iter()).enumerate() {
            let _ = k;
            parts.push(("rule", r1.2, r2.2));
        }
    }
    for (lbl, ea, eb) in parts {
        if let Some((path, pa, pb, na, nb)) = first_diff(a, ha, b, hb, ea, eb, exact) {
            let na = short(&na);
            let nb = short(&nb);
            return format!(
                "{}{}{}\told: {}\tnew: {}",
                lbl,
                if path.is_empty() { "" } else { "." },
                path,
                pp(a, pa, budget, &na),
                pp(b, pb, budget, &nb)
            );
        }
    }
    let lp = |e: &Env, d: &Decl| d.lparams.iter().map(|&n| e.name_str(n)).collect::<Vec<_>>().join(",");
    format!(
        "metadata\told: kind={} lparams=[{}] hints={}/{} all={}\tnew: kind={} lparams=[{}] hints={}/{} all={}",
        kind_name(x.kind),
        lp(a, x),
        x.hints_kind,
        x.hints_val,
        x.all.len(),
        kind_name(y.kind),
        lp(b, y),
        y.hints_kind,
        y.hints_val,
        y.all.len()
    )
}

fn cmd_show(o: &Opts) -> R<()> {
    let env = load(&o.files[0], o.threads, o.verbose)?;
    for nm in &o.files[1..] {
        let path = to_name(nm)?;
        match env.decl_by_path(&path) {
            None => println!("{}: not declared", nm),
            Some(d) => {
                let d = &env.decls[d as usize];
                let lp = d.lparams.iter().map(|&n| env.name_str(n)).collect::<Vec<_>>().join(", ");
                println!("{} {}.{{{}}}", kind_name(d.kind), nm, lp);
                println!("  type:  {}", pp(&env, d.ty, o.budget, &[]));
                if matches!(d.kind, D_DEFN | D_THM | D_OPAQUE) {
                    println!("  value: {}", pp(&env, d.val, o.budget, &[]));
                }
            }
        }
    }
    std::mem::forget(env);
    Ok(())
}

// ---------------------------------------------------------------------------------------------------
// commands
// ---------------------------------------------------------------------------------------------------

struct Opts {
    threads: usize,
    targets: Option<String>,
    targets_new: Option<String>,
    base: Option<String>,
    tsv: Option<String>,
    top: usize,
    verbose: bool,
    files: Vec<String>,
    explain: usize,
    budget: isize,
    dead_lets: bool,
    private_modulo: bool,
}

fn sel_closure(env: &Env, o: &Opts, label: &str) -> R<Vec<bool>> {
    let spec = if label == "new" && o.targets_new.is_some() { &o.targets_new } else { &o.targets };
    match spec {
        Some(t) => {
            let ts = parse_targets(t)?;
            let (cl, missing) = closure(env, &ts)?;
            let ncl = cl.iter().filter(|&&b| b).count();
            println!("{}.closure_targets\t{}", label, ts.len());
            println!("{}.closure_decls\t{}", label, ncl);
            println!("{}.closure_missing\t{}", label, missing.len());
            for m in missing.iter().take(20) {
                println!("{}.closure_missing_name\t{}", label, m);
            }
            Ok(cl)
        }
        None => Ok(vec![true; env.decls.len()]),
    }
}

fn load_base(o: &Opts) -> R<Option<(Env, Digests)>> {
    match &o.base {
        Some(p) => {
            let b = load(p, o.threads, o.verbose)?;
            let d = digests(&b);
            Ok(Some((b, d)))
        }
        None => Ok(None),
    }
}

fn cmd_stats(o: &Opts) -> R<()> {
    let t0 = Instant::now();
    let path = &o.files[0];
    let (env, base) = std::thread::scope(|s| {
        let hb = s.spawn(|| load_base(o));
        let e = load(path, o.threads, o.verbose);
        (e, hb.join().unwrap())
    });
    let env = env?;
    let base = base?;
    let flen = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    println!("file\t{}", path);
    println!("file_bytes\t{}", flen);
    println!("names\t{}", env.names.len());
    println!("levels\t{}", env.levels.len());
    println!("exprs\t{}", env.exprs.len());
    println!("decls\t{}", env.decls.len());
    let cl = sel_closure(&env, o, "stats")?;
    let dg = digests(&env);
    let bcls = base_class(&env, &dg, &base);
    let (tree, depth) = tree_sizes(&env);
    let sizes = per_decl_sizes(&env, &cl, &tree, &depth, o.threads);
    let t1 = Instant::now();
    // aggregate by (base class, kind) and by (base class, name class)
    let mut agg: std::collections::BTreeMap<(String, String), (u64, u64, u64, f64)> = Default::default();
    let mut agg_nc: std::collections::BTreeMap<(String, String), (u64, u64, f64)> = Default::default();
    let mut names_str: Vec<String> = Vec::with_capacity(env.decls.len());
    for (j, d) in env.decls.iter().enumerate() {
        let s = env.name_str(d.name);
        if cl[j] {
            let b = BASE_NAMES[bcls[j] as usize].to_string();
            let k = kind_name(d.kind).to_string();
            let z = &sizes[j];
            let a = agg.entry((b.clone(), k)).or_default();
            a.0 += 1;
            a.1 += z.ty_dag;
            a.2 += z.val_dag;
            a.3 += z.val_tree;
            let c = agg_nc.entry((b, name_class(&s).to_string())).or_default();
            c.0 += 1;
            c.1 += z.all_dag;
            c.2 += z.val_tree;
        }
        names_str.push(s);
    }
    println!("# by (origin, kind): count, sum type-DAG, sum value-DAG, sum value-tree");
    for ((b, k), (c, td, vd, vt)) in &agg {
        println!("by_kind\t{}\t{}\t{}\t{}\t{}\t{:.4e}", b, k, c, td, vd, vt);
    }
    println!("# by (origin, name class): count, sum DAG (type+value per decl), sum value-tree");
    for ((b, k), (c, ad, vt)) in &agg_nc {
        println!("by_class\t{}\t{}\t{}\t{}\t{:.4e}", b, k, c, ad, vt);
    }
    // global DAG per origin
    for b in 0..3u8 {
        let sel: Vec<bool> = (0..env.decls.len()).map(|j| cl[j] && bcls[j] == b).collect();
        let cnt = sel.iter().filter(|&&x| x).count();
        if cnt == 0 {
            continue;
        }
        println!("global_dag\t{}\t{}\t{}", BASE_NAMES[b as usize], cnt, global_dag(&env, &sel));
    }
    println!("global_dag\tall-closure\t{}\t{}", cl.iter().filter(|&&x| x).count(), global_dag(&env, &cl));
    // same-statement theorems (different names, alpha-equal type and universe params) in the closure
    let mut by_stmt: FxMap<(u64, u64, usize), Vec<u32>> = FxMap::default();
    for (j, d) in env.decls.iter().enumerate() {
        if cl[j] && d.kind == D_THM {
            by_stmt.entry((dg.tyh[j].0, dg.tyh[j].1, d.lparams.len())).or_default().push(j as u32);
        }
    }
    let mut groups = 0u64;
    let mut members = 0u64;
    let mut proj_groups = 0u64;
    let mut proj_extra = 0u64;
    let mut saved_dag = 0u64;
    let mut identical_val = 0u64;
    let mut grp_rows: Vec<(u64, Vec<u32>)> = Vec::new();
    for (_, v) in by_stmt.iter() {
        if v.len() < 2 {
            continue;
        }
        groups += 1;
        members += v.len() as u64;
        let nproj = v.iter().filter(|&&j| bcls[j as usize] != 1).count();
        if nproj > 0 {
            proj_groups += 1;
            proj_extra += (v.len() - 1) as u64;
            // keeping the smallest proof: the others' value DAGs are saved (upper bound; sharing ignored)
            let mut vd: Vec<u64> = v.iter().map(|&j| sizes[j as usize].val_dag).collect();
            vd.sort();
            saved_dag += vd[1..].iter().sum::<u64>();
            let mut av: Vec<D128> = v.iter().map(|&j| dg.anon[j as usize]).collect();
            av.sort_by_key(|d| (d.0, d.1));
            av.dedup();
            identical_val += (v.len() - av.len()) as u64;
            grp_rows.push((vd[1..].iter().sum::<u64>(), v.clone()));
        }
    }
    println!("same_statement_thm_groups\t{}\t(members {})", groups, members);
    println!("same_statement_thm_groups_with_project_member\t{}\t(redundant members {}, of which identical proofs {}; value-DAG of the non-smallest proofs {})", proj_groups, proj_extra, identical_val, saved_dag);
    // identical declarations under different names (anon digest), any kind with a value
    let mut by_anon: FxMap<(u64, u64), u32> = FxMap::default();
    for (j, d) in env.decls.iter().enumerate() {
        if cl[j] && matches!(d.kind, D_THM | D_DEFN) {
            *by_anon.entry((dg.anon[j].0, dg.anon[j].1)).or_default() += 1;
        }
    }
    let dup_anon: u64 = by_anon.values().filter(|&&c| c > 1).map(|&c| (c - 1) as u64).sum();
    println!("identical_content_other_name\t{}\t(declarations that equal another one except for their own name)", dup_anon);
    {
        // breakdown: (origin, name class) of the non-first members of identical-content groups
        let mut first: FxSet<(u64, u64)> = FxSet::default();
        let mut br: std::collections::BTreeMap<(String, String), (u64, u64)> = Default::default();
        for (j, d) in env.decls.iter().enumerate() {
            if cl[j] && matches!(d.kind, D_THM | D_DEFN) && by_anon.get(&(dg.anon[j].0, dg.anon[j].1)).copied().unwrap_or(0) > 1 {
                if !first.insert((dg.anon[j].0, dg.anon[j].1)) {
                    let e = br.entry((BASE_NAMES[bcls[j] as usize].to_string(), name_class(&env.name_str(d.name)).to_string())).or_default();
                    e.0 += 1;
                    e.1 += sizes[j].val_dag;
                }
            }
        }
        for ((b, c), (n, v)) in &br {
            println!("identical_copy\t{}\t{}\t{}\tvalue_dag_of_copies\t{}", b, c, n, v);
        }
    }
    // sharing and dependency graph
    if let Some(t) = &o.targets {
        // statement closure of the THEOREM targets only (the export targets also list primitives/axioms)
        let ts: Vec<String> = parse_targets(t)?
            .into_iter()
            .filter(|x| to_name(x).ok().and_then(|p| env.decl_by_path(&p)).map(|d| env.decls[d as usize].kind == D_THM).unwrap_or(false))
            .collect();
        let sc = statement_closure(&env, &ts)?;
        let mut by: std::collections::BTreeMap<(&str, &str), u64> = Default::default();
        for (j, d) in env.decls.iter().enumerate() {
            if sc[j] {
                *by.entry((BASE_NAMES[bcls[j] as usize], kind_name(d.kind))).or_default() += 1;
            }
        }
        let n = sc.iter().filter(|&&x| x).count();
        let dag = global_dag(&env, &sc);
        println!("statement_closure\t{} theorem targets\t{} declarations\tglobal DAG {}\t(the trusted reading set: types + definition bodies, no proofs)", ts.len(), n, dag);
        for ((b, k), c) in &by {
            println!("statement_closure_by\t{}\t{}\t{}", b, k, c);
        }
    }
    let g = graph(&env, &cl, o.threads);
    let roots: Vec<u32> = match &o.targets {
        Some(t) => parse_targets(t)?.iter().filter_map(|x| to_name(x).ok()).filter_map(|p| env.decl_by_path(&p)).collect(),
        None => vec![],
    };
    let depth_bfs = bfs_depth(&env, &g, &roots);
    let height = heights(&env, &g, &cl);
    {
        let mut ex_proj = 0u64;
        let mut ex_base = 0u64;
        let mut ex_thm = 0u64;
        for j in 0..env.decls.len() {
            if cl[j] {
                if bcls[j] == 1 {
                    ex_base += g.excl[j];
                } else {
                    ex_proj += g.excl[j];
                    if env.decls[j].kind == D_THM {
                        ex_thm += g.excl[j];
                    }
                }
            }
        }
        println!("exclusive_nodes\tproject\t{}\tproject_thm\t{}\tbase\t{}\t(nodes reachable from exactly one closure declaration; the rest is shared by >= 2)", ex_proj, ex_thm, ex_base);
        let mut ord: Vec<usize> = (0..env.decls.len()).filter(|&j| cl[j] && bcls[j] != 1).collect();
        ord.sort_by(|&a, &b| g.excl[b].cmp(&g.excl[a]));
        let mut cum = 0u64;
        let mut marks = vec![100usize, 1000, 10000, 100000];
        for (k, &j) in ord.iter().enumerate() {
            cum += g.excl[j];
            if marks.first() == Some(&(k + 1)) {
                println!("exclusive_nodes_top\t{}\t{}\t(cumulative exclusive nodes of the top-k project declarations)", k + 1, cum);
                marks.remove(0);
            }
        }
        for &j in ord.iter().take(o.top) {
            println!("top_exclusive\t{}\t{}\t{}\tindeg\t{}", names_str[j], kind_name(env.decls[j].kind), g.excl[j], g.indeg[j]);
        }
        // in-degree distribution of project theorems (reuse)
        let mut hist = [0u64; 6];
        let mut sum_in = 0u64;
        let mut nthm = 0u64;
        for j in 0..env.decls.len() {
            if cl[j] && bcls[j] != 1 && env.decls[j].kind == D_THM {
                let k = match g.indeg[j] {
                    0 => 0,
                    1 => 1,
                    2 => 2,
                    3..=5 => 3,
                    6..=20 => 4,
                    _ => 5,
                };
                hist[k] += 1;
                sum_in += g.indeg[j] as u64;
                nthm += 1;
            }
        }
        println!("project_thm_indeg\t0:{}\t1:{}\t2:{}\t3-5:{}\t6-20:{}\t>20:{}\tmean:{:.2}", hist[0], hist[1], hist[2], hist[3], hist[4], hist[5], sum_in as f64 / nthm.max(1) as f64);
        let maxd = (0..env.decls.len()).filter(|&j| cl[j] && bcls[j] != 1 && depth_bfs[j] != u32::MAX).map(|j| depth_bfs[j]).max().unwrap_or(0);
        let mut dh = vec![0u64; maxd as usize + 1];
        for j in 0..env.decls.len() {
            if cl[j] && bcls[j] != 1 && depth_bfs[j] != u32::MAX {
                dh[depth_bfs[j] as usize] += 1;
            }
        }
        println!("project_bfs_depth_from_targets\tmax={}\t{}", maxd, dh.iter().enumerate().map(|(k, c)| format!("{}:{}", k, c)).collect::<Vec<_>>().join(" "));
        for &r in roots.iter().filter(|&&r| env.decls[r as usize].kind == D_THM) {
            println!("target_height\t{}\t{}\t(longest reference chain below the target)", names_str[r as usize], height[r as usize]);
        }
    }
    // top proofs by value DAG among project decls
    let mut order: Vec<usize> = (0..env.decls.len()).filter(|&j| cl[j] && bcls[j] != 1).collect();
    order.sort_by(|&a, &b| sizes[b].val_dag.cmp(&sizes[a].val_dag));
    println!("# top {} project declarations by value DAG: name, kind, value DAG, value tree, type DAG, depth", o.top);
    for &j in order.iter().take(o.top) {
        let z = &sizes[j];
        println!("top\t{}\t{}\t{}\t{:.3e}\t{}\t{}", names_str[j], kind_name(env.decls[j].kind), z.val_dag, z.val_tree, z.ty_dag, z.depth);
    }
    // distribution of project theorem value DAG sizes
    let mut thm_sizes: Vec<u64> = (0..env.decls.len())
        .filter(|&j| cl[j] && bcls[j] != 1 && env.decls[j].kind == D_THM)
        .map(|j| sizes[j].val_dag)
        .collect();
    thm_sizes.sort();
    if !thm_sizes.is_empty() {
        let q = |p: f64| thm_sizes[((thm_sizes.len() - 1) as f64 * p) as usize];
        println!(
            "project_thm_value_dag_quantiles\tn={}\tp10={}\tp50={}\tp90={}\tp99={}\tmax={}\tsum={}",
            thm_sizes.len(),
            q(0.1),
            q(0.5),
            q(0.9),
            q(0.99),
            thm_sizes[thm_sizes.len() - 1],
            thm_sizes.iter().sum::<u64>()
        );
    }
    if let Some(mut w) = open_out(&o.tsv) {
        writeln!(w, "name\tkind\torigin\tname_class\tin_closure\ttype_dag\tvalue_dag\tall_dag\ttype_tree\tvalue_tree\tdepth\texclusive\tindeg\toutdeg\tbfs_depth\theight").unwrap();
        for (j, d) in env.decls.iter().enumerate() {
            let z = &sizes[j];
            writeln!(
                w,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.6e}\t{:.6e}\t{}\t{}\t{}\t{}\t{}\t{}",
                tsv_name(&names_str[j]),
                kind_name(d.kind),
                BASE_NAMES[bcls[j] as usize],
                name_class(&names_str[j]),
                cl[j] as u8,
                z.ty_dag,
                z.val_dag,
                z.all_dag,
                z.ty_tree,
                z.val_tree,
                z.depth,
                g.excl[j],
                g.indeg[j],
                g.outdeg[j],
                if depth_bfs[j] == u32::MAX { -1i64 } else { depth_bfs[j] as i64 },
                if height[j] >= u32::MAX - 1 { -1i64 } else { height[j] as i64 }
            )
            .unwrap();
        }
        // same-statement groups
        if let Some(p) = &o.tsv {
            let mut g = std::io::BufWriter::new(File::create(format!("{}.samestmt.tsv", p)).unwrap());
            writeln!(g, "group\tsaved_value_dag\tname\torigin\tvalue_dag").unwrap();
            grp_rows.sort_by(|a, b| b.0.cmp(&a.0));
            for (gi, (sv, v)) in grp_rows.iter().enumerate() {
                for &j in v {
                    writeln!(g, "{}\t{}\t{}\t{}\t{}", gi, sv, tsv_name(&names_str[j as usize]), BASE_NAMES[bcls[j as usize] as usize], sizes[j as usize].val_dag).unwrap();
                }
            }
        }
    }
    println!("time_s\t{:.1}\t(analysis {:.1})", t0.elapsed().as_secs_f64(), (Instant::now() - t1).as_secs_f64());
    std::mem::forget(env);
    std::mem::forget(base);
    Ok(())
}


// ---------------------------------------------------------------------------------------------------
// equality modulo dead lets: an alpha hash in which every unused `let` is skipped (its body is hashed in its place,
// de Bruijn indices counting only the remaining binders); mdata transparent. Equal to the alpha hash on every subterm
// that contains no dead let and whose loose variables do not cross a skipped binder (fast path).
// ---------------------------------------------------------------------------------------------------

struct DeadSkip<'a> {
    env: &'a Env,
    lz: &'a Loose,
    ha: &'a [u64],    // alpha hashes (seed 1)
    hn: &'a [u64],    // name hashes (seed 1)
    dl: &'a [bool],   // node contains a dead let
    stack_dead: Vec<u32>, // absolute depths of skipped binders (ascending)
    depth: u32,
    memo: FxMap<(u32, u64), u64>,
}

fn dead_let_flags(env: &Env, lz: &Loose) -> Vec<bool> {
    let ne = env.exprs.len();
    let mut dl = vec![false; ne];
    for i in 0..ne {
        let e = env.exprs[i];
        dl[i] = match e.kind {
            E_APP | E_LAM | E_PI => dl[e.a as usize] || dl[e.b as usize],
            E_LET => {
                // dead iff the body has no loose bvar 0: lbr(body) == 0, or the exact mask says so
                let b = e.c as usize;
                let dead = lz.lbr[b] == 0 || (lz.ex[b] && lz.lo[b] & 1 == 0);
                dead || dl[e.a as usize] || dl[e.b as usize] || dl[e.c as usize]
            }
            E_PROJ => dl[e.b as usize],
            E_MDATA => dl[e.a as usize],
            _ => false,
        };
    }
    dl
}

impl<'a> DeadSkip<'a> {
    /// relative offsets of skipped binders inside the loose range of e (pattern key; 0 = none)
    fn pattern(&self, e: u32) -> u64 {
        let r = self.lz.lbr[e as usize];
        if r == 0 || self.stack_dead.is_empty() {
            return 0;
        }
        let lo = self.depth.saturating_sub(r);
        let mut h = 0u64;
        for &p in self.stack_dead.iter().rev() {
            if p < lo {
                break;
            }
            h = hmix(h ^ 0x51, (self.depth - 1 - p) as u64 + 1);
        }
        h
    }
    fn is_dead_let(&self, e: u32, mut memo_has: &mut FxSet<(u32, u32)>, st: &mut Vec<(u32, u32)>) -> bool {
        let x = self.env.exprs[e as usize];
        x.kind == E_LET && !has_loose(self.env, self.lz, x.c, 0, &mut memo_has, st)
    }
    fn h(&mut self, e: u32, mh: &mut FxSet<(u32, u32)>, st: &mut Vec<(u32, u32)>) -> u64 {
        let pat = self.pattern(e);
        if pat == 0 && !self.dl[e as usize] {
            return self.ha[e as usize];
        }
        if let Some(&v) = self.memo.get(&(e, pat)) {
            return v;
        }
        let x = self.env.exprs[e as usize];
        let v = match x.kind {
            E_BVAR => {
                let i = x.a as u64 | ((x.b as u64) << 32);
                let p = self.depth as i64 - 1 - i as i64;
                let skipped = self.stack_dead.iter().rev().take_while(|&&q| q as i64 > p).count() as u64;
                hparts(SEED1, 20, &[i - skipped])
            }
            E_APP => {
                let f = self.h(x.a, mh, st);
                let g = self.h(x.b, mh, st);
                hparts(SEED1, 23, &[f, g])
            }
            E_LAM | E_PI => {
                let t = self.h(x.a, mh, st);
                self.depth += 1;
                let b = self.h(x.b, mh, st);
                self.depth -= 1;
                hparts(SEED1, if x.kind == E_LAM { 24 } else { 25 }, &[t, b])
            }
            E_LET => {
                if self.is_dead_let(e, mh, st) {
                    self.stack_dead.push(self.depth);
                    self.depth += 1;
                    let b = self.h(x.c, mh, st);
                    self.depth -= 1;
                    self.stack_dead.pop();
                    b
                } else {
                    let t = self.h(x.a, mh, st);
                    let v = self.h(x.b, mh, st);
                    self.depth += 1;
                    let b = self.h(x.c, mh, st);
                    self.depth -= 1;
                    hparts(SEED1, 26, &[t, v, b, x.flag as u64])
                }
            }
            E_PROJ => {
                let b = self.h(x.b, mh, st);
                hparts(SEED1, 27, &[self.hn[x.a as usize], x.c as u64, b])
            }
            E_MDATA => self.h(x.a, mh, st),
            _ => self.ha[e as usize],
        };
        self.memo.insert((e, pat), v);
        v
    }
}

/// For each (old decl, new decl) pair: are the values equal modulo dead lets (both sides)? Runs on threads with big
/// stacks (kernel terms are thousands of binders deep).
fn modulo_dead_lets(a: &Env, da: &Digests, b: &Env, db: &Digests, pairs: &[(usize, usize)], threads: usize) -> Vec<bool> {
    if pairs.is_empty() {
        return Vec::new();
    }
    let (lza, lzb) = std::thread::scope(|s| {
        let h = s.spawn(|| loose(a));
        (h.join().unwrap(), loose(b))
    });
    let dla = dead_let_flags(a, &lza);
    let dlb = dead_let_flags(b, &lzb);
    let res: Vec<std::sync::atomic::AtomicBool> = (0..pairs.len()).map(|_| std::sync::atomic::AtomicBool::new(false)).collect();
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..threads.max(1) {
            let (res, next, lza, lzb, dla, dlb) = (&res, &next, &lza, &lzb, &dla, &dlb);
            std::thread::Builder::new()
                .stack_size(1 << 32)
                .spawn_scoped(s, move || {
                    let mut mh: FxSet<(u32, u32)> = FxSet::default();
                    let mut st: Vec<(u32, u32)> = Vec::new();
                    loop {
                        let k = next.fetch_add(1, Ordering::Relaxed);
                        if k >= pairs.len() {
                            break;
                        }
                        let (i, j) = pairs[k];
                        let mut x = DeadSkip { env: a, lz: lza, ha: &da.h1.he_alpha, hn: &da.h1.hn, dl: dla, stack_dead: Vec::new(), depth: 0, memo: FxMap::default() };
                        let mut y = DeadSkip { env: b, lz: lzb, ha: &db.h1.he_alpha, hn: &db.h1.hn, dl: dlb, stack_dead: Vec::new(), depth: 0, memo: FxMap::default() };
                        let (vi, vj) = (a.decls[i].val, b.decls[j].val);
                        let eq = x.h(vi, &mut mh, &mut st) == y.h(vj, &mut mh, &mut st);
                        res[k].store(eq, Ordering::Relaxed);
                    }
                })
                .unwrap();
        }
    });
    res.into_iter().map(|x| x.into_inner()).collect()
}

fn cmd_diff(o: &Opts) -> R<()> {
    let t0 = Instant::now();
    let (a, b) = std::thread::scope(|s| {
        let ha = s.spawn(|| load(&o.files[0], o.threads / 2 + 1, o.verbose));
        let b = load(&o.files[1], o.threads / 2 + 1, o.verbose);
        (ha.join().unwrap(), b)
    });
    let (a, b) = (a?, b?);
    for (lbl, env, p) in [("old", &a, &o.files[0]), ("new", &b, &o.files[1])] {
        println!("{}.file\t{}", lbl, p);
        println!("{}.file_bytes\t{}", lbl, std::fs::metadata(p).map(|m| m.len()).unwrap_or(0));
        println!("{}.exprs\t{}", lbl, env.exprs.len());
        println!("{}.decls\t{}", lbl, env.decls.len());
    }
    let ca = sel_closure(&a, o, "old")?;
    let cb = sel_closure(&b, o, "new")?;
    let (da, db) = std::thread::scope(|s| {
        let h = s.spawn(|| digests(&a));
        let y = digests(&b);
        (h.join().unwrap(), y)
    });
    let (ta, pa) = tree_sizes(&a);
    let (tb, pb) = tree_sizes(&b);
    let sa = per_decl_sizes(&a, &ca, &ta, &pa, o.threads);
    let sb = per_decl_sizes(&b, &cb, &tb, &pb, o.threads);
    println!("old.closure_global_dag\t{}", global_dag(&a, &ca));
    println!("new.closure_global_dag\t{}", global_dag(&b, &cb));
    let sum_val = |env: &Env, cl: &[bool], sz: &[DeclSize]| -> (u64, f64) {
        let mut d = 0u64;
        let mut t = 0f64;
        for j in 0..env.decls.len() {
            if cl[j] {
                d += sz[j].all_dag;
                t += sz[j].ty_tree + sz[j].val_tree;
            }
        }
        (d, t)
    };
    let (ad, at) = sum_val(&a, &ca, &sa);
    let (bd, bt) = sum_val(&b, &cb, &sb);
    println!("old.closure_sum_decl_dag\t{}\told.closure_sum_tree\t{:.4e}", ad, at);
    println!("new.closure_sum_decl_dag\t{}\tnew.closure_sum_tree\t{:.4e}", bd, bt);
    // match by name
    let mut idx: FxMap<(u64, u64), u32> = FxMap::default();
    idx.reserve(b.decls.len());
    // keys that occur more than once on a side (only possible with --private-modulo: the same private name in two
    // modules) are ambiguous and not compared
    let mut amb: FxSet<(u64, u64)> = FxSet::default();
    for (i, n) in db.name.iter().enumerate() {
        if idx.insert((n.0, n.1), i as u32).is_some() {
            amb.insert((n.0, n.1));
        }
    }
    {
        let mut seen: FxSet<(u64, u64)> = FxSet::default();
        for n in da.name.iter() {
            if !seen.insert((n.0, n.1)) {
                amb.insert((n.0, n.1));
            }
        }
    }
    if o.private_modulo {
        println!("private_modulo_ambiguous_names\t{}", amb.len());
    }
    #[derive(Default)]
    struct Cnt {
        by: std::collections::BTreeMap<&'static str, u64>,
    }
    let mut cnt = Cnt::default();
    let mut rows: Vec<(&'static str, usize, Option<usize>)> = Vec::new();
    let mut matched_new = vec![false; b.decls.len()];
    let mut stmt_changed_names: Vec<String> = Vec::new();
    for (i, n) in da.name.iter().enumerate() {
        let st: &'static str;
        let mut other = None;
        if !ca[i] {
            continue;
        }
        if amb.contains(&(n.0, n.1)) {
            *cnt.by.entry("ambiguous (same private name in several modules)").or_default() += 1;
            continue;
        }
        match idx.get(&(n.0, n.1)) {
            Some(&jj) => {
                let j = jj as usize;
                matched_new[j] = true;
                other = Some(j);
                if !cb[j] {
                    st = "dropped-from-closure";
                } else if da.exact[i] == db.exact[j] {
                    st = "identical";
                } else if da.alpha[i] == db.alpha[j] {
                    st = "alpha-equal (binder names/infos differ)";
                } else if a.decls[i].kind != b.decls[j].kind {
                    st = "kind-changed";
                    stmt_changed_names.push(a.name_str(a.decls[i].name));
                } else if da.stmt[i] == db.stmt[j] {
                    st = "value-changed, statement equal";
                } else {
                    st = "STATEMENT-CHANGED";
                    stmt_changed_names.push(a.name_str(a.decls[i].name));
                }
            }
            None => st = "removed",
        }
        *cnt.by.entry(st).or_default() += 1;
        if st != "identical" {
            rows.push((st, i, other));
        }
    }
    if o.dead_lets {
        let pairs: Vec<(usize, usize)> = rows
            .iter()
            .filter(|r| r.0 == "value-changed, statement equal" && matches!(a.decls[r.1].kind, D_DEFN | D_THM | D_OPAQUE))
            .map(|r| (r.1, r.2.unwrap()))
            .collect();
        let t = Instant::now();
        let eq = modulo_dead_lets(&a, &da, &b, &db, &pairs, o.threads);
        let mut k = 0usize;
        let mut nmod = 0u64;
        for r in rows.iter_mut() {
            if r.0 == "value-changed, statement equal" && matches!(a.decls[r.1].kind, D_DEFN | D_THM | D_OPAQUE) {
                if eq[k] {
                    r.0 = "value-equal modulo dead lets";
                    nmod += 1;
                }
                k += 1;
            }
        }
        *cnt.by.entry("value-changed, statement equal").or_default() -= nmod;
        *cnt.by.entry("value-equal modulo dead lets").or_default() += nmod;
        println!("dead_lets_check\t{} value-changed pairs, {} equal modulo dead lets ({:.1} s)", pairs.len(), nmod, t.elapsed().as_secs_f64());
    }
    let mut added: Vec<usize> = Vec::new();
    for j in 0..b.decls.len() {
        if cb[j] && !matched_new[j] && !amb.contains(&(db.name[j].0, db.name[j].1)) {
            added.push(j);
        } else if cb[j] && matched_new[j] {
            // matched by name but not in old closure
        }
    }
    // names in the new closure matched to old decls outside the old closure
    let mut entered = 0u64;
    {
        let mut idxa: FxMap<(u64, u64), u32> = FxMap::default();
        for (i, n) in da.name.iter().enumerate() {
            idxa.insert((n.0, n.1), i as u32);
        }
        for j in 0..b.decls.len() {
            if cb[j] && matched_new[j] {
                if let Some(&i) = idxa.get(&(db.name[j].0, db.name[j].1)) {
                    if !ca[i as usize] {
                        entered += 1;
                    }
                }
            }
        }
    }
    // rename detection: removed (old) vs added (new) with equal anonymous digest
    let mut anon_new: FxMap<(u64, u64), Vec<usize>> = FxMap::default();
    for &j in &added {
        anon_new.entry((db.anon[j].0, db.anon[j].1)).or_default().push(j);
    }
    let mut renamed = 0u64;
    let mut rename_rows: Vec<(usize, usize)> = Vec::new();
    for r in rows.iter() {
        if r.0 == "removed" {
            if let Some(v) = anon_new.get_mut(&(da.anon[r.1].0, da.anon[r.1].1)) {
                if let Some(j) = v.pop() {
                    renamed += 1;
                    rename_rows.push((r.1, j));
                }
            }
        }
    }
    *cnt.by.entry("added").or_default() += added.len() as u64;
    println!("# per-name status of the OLD closure (and declarations added in the NEW closure)");
    for (k, v) in &cnt.by {
        println!("status\t{}\t{}", k, v);
    }
    println!("status\tentered-closure (in new closure, declared but outside the old closure)\t{}", entered);
    println!("status\trenamed (removed+added pairs with identical content except own name)\t{}", renamed);
    println!("statement_changed_count\t{}", stmt_changed_names.len());
    for s in stmt_changed_names.iter().take(50) {
        println!("statement_changed\t{}", s);
    }
    // explanations: first structural difference, up to o.explain per status (statement changes first)
    let mut per: FxMap<&'static str, usize> = FxMap::default();
    let mut ordered: Vec<&(&'static str, usize, Option<usize>)> = rows.iter().filter(|r| r.2.is_some() && r.0 != "dropped-from-closure").collect();
    ordered.sort_by_key(|r| match r.0 { "STATEMENT-CHANGED" => 0, "kind-changed" => 1, "value-changed, statement equal" => 2, _ => 3 });
    for r in ordered {
        let c = per.entry(r.0).or_default();
        if *c >= o.explain {
            continue;
        }
        *c += 1;
        let exact = r.0.starts_with("alpha-equal");
        println!("explain\t{}\t{}\t{}", r.0, a.name_str(a.decls[r.1].name), explain_decl(&a, &da, r.1, &b, &db, r.2.unwrap(), exact, o.budget));
    }
    if let Some(mut w) = open_out(&o.tsv) {
        writeln!(w, "status\tname\tkind\told_all_dag\tnew_all_dag\told_value_tree\tnew_value_tree\tnew_name").unwrap();
        let mut ren: FxMap<usize, usize> = FxMap::default();
        for &(i, j) in &rename_rows {
            ren.insert(i, j);
        }
        for (st, i, other) in &rows {
            let (nd, nt, nn) = match other {
                Some(j) => (sb[*j].all_dag.to_string(), format!("{:.4e}", sb[*j].val_tree), String::new()),
                None => match ren.get(i) {
                    Some(&j) => (sb[j].all_dag.to_string(), format!("{:.4e}", sb[j].val_tree), b.name_str(b.decls[j].name)),
                    None => ("".into(), "".into(), String::new()),
                },
            };
            writeln!(
                w,
                "{}\t{}\t{}\t{}\t{}\t{:.4e}\t{}\t{}",
                st,
                tsv_name(&a.name_str(a.decls[*i].name)),
                kind_name(a.decls[*i].kind),
                sa[*i].all_dag,
                nd,
                sa[*i].val_tree,
                nt,
                tsv_name(&nn)
            )
            .unwrap();
        }
        for &j in &added {
            writeln!(w, "added\t{}\t{}\t\t{}\t\t{:.4e}\t", tsv_name(&b.name_str(b.decls[j].name)), kind_name(b.decls[j].kind), sb[j].all_dag, sb[j].val_tree).unwrap();
        }
    }
    println!("time_s\t{:.1}", t0.elapsed().as_secs_f64());
    let code_changed = !stmt_changed_names.is_empty();
    std::mem::forget(a);
    std::mem::forget(b);
    if code_changed {
        println!("RESULT\tstatements changed in the compared closure (see statement_changed lines)");
    } else {
        println!("RESULT\tno statement changed in the compared closure");
    }
    Ok(())
}

fn cmd_dead(o: &Opts) -> R<()> {
    let t0 = Instant::now();
    let path = &o.files[0];
    let (env, base) = std::thread::scope(|s| {
        let hb = s.spawn(|| load_base(o));
        let e = load(path, o.threads, o.verbose);
        (e, hb.join().unwrap())
    });
    let env = env?;
    let base = base?;
    let cl = sel_closure(&env, o, "dead")?;
    let dg = digests(&env);
    let bcls = base_class(&env, &dg, &base);
    let lz = loose(&env);
    let letfun = env.lookup(&[Comp::Str(b"letFun".to_vec())]).map(|r| env.canon[r as usize]);
    let dead = find_dead(&env, &lz, &cl, letfun, o.threads);
    let (tree, depth) = tree_sizes(&env);
    let sizes = per_decl_sizes(&env, &cl, &tree, &depth, o.threads);
    // aggregate: per (origin, dead kind): count, distinct exprs, dead value DAG (sum), decls affected
    let mut vis: FxSet<u32> = FxSet::default();
    let mut st = Vec::new();
    let mut agg: std::collections::BTreeMap<(u8, u8, u8), (u64, u64, u64)> = Default::default();
    let mut decls_aff: FxSet<(u8, u32)> = FxSet::default();
    let mut seen_expr: FxSet<(u8, u32, u32)> = FxSet::default();
    let mut rows: Vec<(Dead, u64)> = Vec::new();
    for dd in &dead {
        let b = bcls[dd.decl as usize];
        vis.clear();
        let dsz = dag_size(&env, &[dd.dval], &mut vis, &mut st);
        let sub = if dd.kind == DK_HYP { dd.binfo } else { 0 };
        let a = agg.entry((b, dd.kind, sub)).or_default();
        a.0 += 1;
        if seen_expr.insert((dd.kind, dd.expr, dd.pos)) {
            a.1 += 1;
        }
        a.2 += dsz;
        decls_aff.insert((dd.kind, dd.decl));
        rows.push((dd.clone(), dsz));
    }
    let mut tot: std::collections::BTreeMap<u8, (u64, u64)> = Default::default();
    for (j, d) in env.decls.iter().enumerate() {
        if cl[j] && matches!(d.kind, D_DEFN | D_THM | D_OPAQUE) {
            let t = tot.entry(bcls[j]).or_default();
            t.0 += 1;
            t.1 += sizes[j].val_dag;
        }
    }
    for (b, (n, v)) in &tot {
        println!("decls_with_value\t{}\t{}\tsum_value_dag\t{}", BASE_NAMES[*b as usize], n, v);
    }
    println!("# dead binders: origin, kind, (hyp: binder info), occurrences (per decl), distinct nodes, sum DAG of the dead values/binder types");
    for ((b, k, sub), (c, dist, dsz)) in &agg {
        let sk = if *k == DK_HYP { binfo_name(*sub) } else { "-" };
        println!("dead\t{}\t{}\t{}\t{}\t{}\t{}", BASE_NAMES[*b as usize], DK_NAMES[*k as usize], sk, c, dist, dsz);
    }
    for k in 0..4u8 {
        let n = decls_aff.iter().filter(|x| x.0 == k).count();
        println!("decls_affected\t{}\t{}", DK_NAMES[k as usize], n);
    }
    if let Some(mut w) = open_out(&o.tsv) {
        writeln!(w, "decl\torigin\tdecl_kind\tdead_kind\tbinder\tbinder_info\tposition\tdead_value_dag\tdecl_value_dag\tnondep").unwrap();
        for (dd, dsz) in &rows {
            let d = &env.decls[dd.decl as usize];
            let bn = if dd.bname == NONE { "?".to_string() } else { env.name_str(dd.bname) };
            writeln!(
                w,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                tsv_name(&env.name_str(d.name)),
                BASE_NAMES[bcls[dd.decl as usize] as usize],
                kind_name(d.kind),
                DK_NAMES[dd.kind as usize],
                tsv_name(&bn),
                if dd.kind == DK_LET { "-" } else { binfo_name(dd.binfo) },
                dd.pos,
                dsz,
                sizes[dd.decl as usize].val_dag,
                if dd.kind == DK_LET { dd.binfo.to_string() } else { "-".into() }
            )
            .unwrap();
        }
    }
    println!("time_s\t{:.1}", t0.elapsed().as_secs_f64());
    std::mem::forget(env);
    std::mem::forget(base);
    Ok(())
}

fn usage() -> ! {
    eprintln!(
        "usage:\n  expdiff stats [-j N] [-v] [--targets FILE|A,B] [--base BASE.export] [--tsv OUT] [--top K] EXPORT\n  \
         expdiff diff  [-j N] [-v] [--targets FILE|A,B] [--targets-new FILE|A,B] [--explain K] [--budget NODES] [--dead-lets] [--private-modulo] [--tsv OUT] OLD.export NEW.export\n  \
         expdiff dead  [-j N] [-v] [--targets FILE|A,B] [--base BASE.export] [--tsv OUT] EXPORT\n  \
         expdiff show  [--budget NODES] EXPORT NAME...\n\
         diff: --explain K prints the first structural difference of the first K changed declarations per status"
    );
    std::process::exit(2)
}

fn run() -> R<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        usage();
    }
    let cmd = args[0].clone();
    let mut o = Opts {
        threads: std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8),
        targets: None,
        targets_new: None,
        base: None,
        tsv: None,
        top: 30,
        verbose: false,
        files: Vec::new(),
        explain: 20,
        budget: 60,
        dead_lets: false,
        private_modulo: false,
    };
    let mut i = 1;
    while i < args.len() {
        let a = args[i].clone();
        let mut val = || -> String {
            i += 1;
            args.get(i).cloned().unwrap_or_else(|| usage())
        };
        match a.as_str() {
            "-j" => o.threads = val().parse().unwrap_or_else(|_| usage()),
            "-v" => o.verbose = true,
            "--targets" => o.targets = Some(val()),
            "--targets-new" => o.targets_new = Some(val()),
            "--base" => o.base = Some(val()),
            "--tsv" => o.tsv = Some(val()),
            "--top" => o.top = val().parse().unwrap_or_else(|_| usage()),
            "--explain" => o.explain = val().parse().unwrap_or_else(|_| usage()),
            "--dead-lets" => o.dead_lets = true,
            "--private-modulo" => o.private_modulo = true,
            "--budget" => o.budget = val().parse().unwrap_or_else(|_| usage()),
            _ if a.starts_with('-') => usage(),
            _ => o.files.push(a),
        }
        i += 1;
    }
    o.threads = o.threads.max(1);
    PRIVATE_MODULO.store(o.private_modulo, std::sync::atomic::Ordering::Relaxed);
    match (cmd.as_str(), o.files.len()) {
        ("stats", 1) => cmd_stats(&o),
        ("diff", 2) => cmd_diff(&o),
        ("dead", 1) => cmd_dead(&o),
        ("show", n) if n >= 2 => cmd_show(&o),
        _ => usage(),
    }
}

fn main() {
    match run() {
        Ok(()) => std::process::exit(0),
        Err(Fail::Reject(m)) | Err(Fail::Decline(m)) => {
            eprintln!("expdiff: cannot read input: {}", m);
            std::process::exit(2)
        }
    }
}
