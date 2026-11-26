//! The type checker: normalization by evaluation over Susz terms.
//!
//! Terms are never built. A term is a Susz id read from MAIN or from the
//! worker's block arena (proof blocks decoded at ids above MAIN). Everything
//! the checker makes is a *value* in the worker's arena:
//!
//! - `Clo { term, env, ls }`: a lambda or Pi term with an environment of
//!   values for its loose bound variables and a universe substitution `ls`.
//!   `infer = true` on a lambda term means "the type of this lambda": a Pi
//!   whose codomain is the inferred type of the body.
//! - `Thunk { term, env, ls }`: an argument, evaluated on demand, memoized.
//! - `Neu { head, spine }`: a free variable, constant or stuck value applied
//!   to a spine of arguments and projections.
//! - `Sort`, `Lit`.
//!
//! Inference is value-typed: `infer(term, env, ls)` returns a value, the
//! type of a bound variable is the type of its environment value, and
//! applying a Pi type to an argument evaluates (or infers) the codomain in
//! an extended environment. Definitional equality follows Lean's
//! `is_def_eq_core` on values, with lazy delta by definitional height.

use crate::env::*;
use crate::level::{Levels, ZERO};
use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};

mod frames;
mod ground;
mod names;
mod region;
mod spines;
use region::Undo;
use spines::Spines;

/// Facts shared by all workers (kept across declarations, stamped with
/// the declaration that made them and used only after it).
pub struct Shared {
    /// MAIN term -> `(u32::MAX - d) << 32 | g`: a check-mode inference of the
    /// closed term at ls = 0 succeeded in safe declaration `d` under the
    /// level parameter list with global id `g`; 0: none. Milestone 29: an
    /// open MAIN term (loose bound variables) -> `row + 1` (high half 0):
    /// the term is the body of safe definition `row`'s value under its
    /// lambdas, or its type's codomain under as many Pis, and that
    /// definition was checked (`open_fact`).
    checked: Vec<AtomicU64>,
    /// level parameter lists (sorted canonical names), interned
    lps: Mutex<(Vec<Box<[u32]>>, FxHashMap<Box<[u32]>, u32>)>,
    /// Milestone 37: properties of the file per constant row, found by
    /// whichever worker asks first (each was a per-worker array: 26 bytes
    /// per constant and worker, `unused` written in full at start):
    /// a definition's leading lambdas + 1 (0 unknown, 255 none) and the
    /// positions its body never reads (`unused_args`);
    unused_l: Vec<std::sync::atomic::AtomicU8>,
    unused_m: Vec<AtomicU64>,
    /// the explicit-binder mask of the type (`explicit_mask`, 0 unknown);
    explicit: Vec<AtomicU64>,
    /// `abbr_shape_of` (0 unknown); the SH_* bits of `cases_shape` and
    /// `match_shape`
    abbr: Vec<std::sync::atomic::AtomicU8>,
    shape: Vec<std::sync::atomic::AtomicU8>,
}

/// A vector of zeroed atomics from zeroed memory (pages mapped when first
/// written).
fn zeroed<A, T: Copy + Default>(n: usize) -> Vec<A> {
    assert_eq!(std::mem::size_of::<A>(), std::mem::size_of::<T>());
    let mut v = std::mem::ManuallyDrop::new(vec![T::default(); n]);
    unsafe { Vec::from_raw_parts(v.as_mut_ptr() as *mut A, v.len(), v.capacity()) }
}

impl Shared {
    pub fn new(main_len: usize, consts: usize) -> Shared {
        Shared {
            checked: zeroed::<AtomicU64, u64>(main_len),
            lps: Mutex::new((Vec::new(), FxHashMap::default())),
            unused_l: zeroed::<std::sync::atomic::AtomicU8, u8>(consts),
            unused_m: zeroed::<AtomicU64, u64>(consts),
            explicit: zeroed::<AtomicU64, u64>(consts),
            abbr: zeroed::<std::sync::atomic::AtomicU8, u8>(consts),
            shape: zeroed::<std::sync::atomic::AtomicU8, u8>(consts),
        }
    }
}

/// Why a check stopped. Milestone 14: one byte, the message kept aside
/// (`stop_msg`), so `R<V>` fits in registers: with the message inside, every
/// `R<_>` was a 32-byte value returned through memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stop {
    Reject,
    Decline,
    Cancel,
    /// milestone 17: an argument probe ran out of its step budget (caught
    /// by the probe; never leaves it)
    Budget,
    /// milestone 38: a whnf too deeply nested in other whnfs, handed up to
    /// the outermost (`deep_v`; caught there, never leaves it)
    Deep,
    /// milestone 39: the ground machine gives a comparison or a whnf back
    /// to the kernel (caught where the run began; never leaves it)
    Ground,
    /// milestone 45: a closed term's inference too deeply nested in other
    /// inferences, handed up to the outermost (`deep_inf`; caught there,
    /// never leaves it)
    DeepInfer,
    /// milestone 45: a comparison of closed values too deeply nested in
    /// other comparisons, handed up to the outermost (`deep_eq`; caught
    /// there, never leaves it)
    DeepDefeq,
}
pub type R<T> = Result<T, Stop>;

thread_local! {
    /// The message of the latest reject or decline made on this thread.
    static STOP_MSG: std::cell::RefCell<String> = const { std::cell::RefCell::new(String::new()) };
}
#[cold]
#[inline(never)]
fn stop_with(k: Stop, s: String) -> Stop {
    STOP_MSG.with(|m| *m.borrow_mut() = s);
    k
}
/// The message of the latest reject or decline on this thread.
pub fn stop_msg() -> String {
    STOP_MSG.with(|m| std::mem::take(&mut *m.borrow_mut()))
}
#[cold]
pub fn reject<T>(s: impl Into<String>) -> R<T> {
    Err(stop_with(Stop::Reject, s.into()))
}
#[cold]
pub fn decline<T>(s: impl Into<String>) -> R<T> {
    Err(stop_with(Stop::Decline, s.into()))
}

/// Per-declaration tables keep their room for the next declaration, up to
/// this many bytes each: past it a worker that met one heavy declaration
/// would hold its memory to the end of the run. Milestone 37: 4 MiB (half
/// a session, `SESSION_MIB`), was 16 MiB; mathlib w4 (knobs) 16 / 4 / 1 /
/// 0.25 MiB: 419.5 / 419.4 / 421.5 / 434.0 G.
const KEEP_BYTES: usize = 4 << 20;
fn keep_bytes() -> usize {
    static K: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *K.get_or_init(|| {
        let k = if KNOBS {
            std::env::var("SK_KEEP_KIB").ok().and_then(|s| s.parse::<usize>().ok()).map_or(KEEP_BYTES, |k| k << 10)
        } else {
            KEEP_BYTES
        };
        // not divided by `capped`: room is not kept knowledge, and a
        // worker's tables grew again at every session (mathlib w4 with the
        // caps of 64 workers: +3.5% with this room divided, +1.4% without)
        k
    })
}

/// Milestone 37: the worker count the caps of per-worker tables were set
/// at. With more workers each worker's caps are divided by `workers /
/// CAP_WORKERS`, so the memory all workers keep across declarations does
/// not grow past what CAP_WORKERS workers keep (FLT on AWS: 28.7 GB at 16
/// workers, 73.8 GB at 192); never below 1/64 of a cap.
const CAP_WORKERS: usize = 4;
static CAP_DIV: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(1);
/// Called once before the workers start.
pub fn set_workers(n: usize) {
    // K02: K02_CAPW=n sets the worker count the caps were set at (default CAP_WORKERS)
    let capw = std::env::var("K02_CAPW").ok().and_then(|s| s.parse::<usize>().ok()).filter(|&c| c >= 1).unwrap_or(CAP_WORKERS);
    let mut d = n.div_ceil(capw).clamp(1, 64);
    if KNOBS {
        if let Some(x) = std::env::var("SK_CAP_DIV").ok().and_then(|s| s.parse::<usize>().ok()) {
            d = x.clamp(1, 64);
        }
    }
    CAP_DIV.store(d, Ordering::Relaxed);
}
/// A per-worker cap, divided as `set_workers` says.
fn capped(c: usize) -> usize {
    c / CAP_DIV.load(Ordering::Relaxed)
}

/// A per-declaration table that can be emptied and shrunk.
trait Table {
    fn t_len(&self) -> usize;
    fn t_cap(&self) -> usize;
    fn t_entry(&self) -> usize;
    fn t_clear(&mut self);
    fn t_shrink(&mut self, n: usize);
}
impl<K: Eq + std::hash::Hash, W, S: std::hash::BuildHasher> Table for std::collections::HashMap<K, W, S> {
    fn t_len(&self) -> usize { self.len() }
    fn t_cap(&self) -> usize { self.capacity() }
    fn t_entry(&self) -> usize { std::mem::size_of::<(K, W)>() + 1 }
    fn t_clear(&mut self) { self.clear() }
    fn t_shrink(&mut self, n: usize) { self.shrink_to(n) }
}
impl<K: Eq + std::hash::Hash, S: std::hash::BuildHasher> Table for std::collections::HashSet<K, S> {
    fn t_len(&self) -> usize { self.len() }
    fn t_cap(&self) -> usize { self.capacity() }
    fn t_entry(&self) -> usize { std::mem::size_of::<K>() + 1 }
    fn t_clear(&mut self) { self.clear() }
    fn t_shrink(&mut self, n: usize) { self.shrink_to(n) }
}

/// Clears a hash map without paying for its capacity every time: `clear` is
/// proportional to capacity, so an empty map is left alone and one that
/// grew far beyond what it held is shrunk; any map is brought back under
/// `keep_bytes`.
fn clear_table<M: Table>(m: &mut M) {
    let n = m.t_len();
    if n > 0 {
        m.t_clear();
        if m.t_cap() > (1 << 16) && m.t_cap() > 8 * n {
            m.t_shrink(n.max(1024));
        }
    }
    let max = keep_bytes() / m.t_entry();
    if m.t_cap() > max {
        m.t_clear();
        m.t_shrink(max / 2);
    }
}
macro_rules! clear_map {
    ($m:expr) => {
        clear_table(&mut $m)
    };
}

/// Empties a per-declaration vector, keeping at most `keep_bytes` of room.
fn clear_vec<T>(v: &mut Vec<T>) {
    v.clear();
    let max = keep_bytes() / std::mem::size_of::<T>().max(1);
    if v.capacity() > max {
        v.shrink_to(max / 2);
    }
}

/// Milestone 19: empties a per-session slab, keeping at most `keep_bytes`
/// of its pages (as `clear_vec`).
fn clear_slab<T: Copy>(v: &mut Slab<T>) {
    v.clear();
    v.shrink(keep_bytes());
}
/// Room of a worker's value arena (10 GiB of address space at 40 bytes a
/// value), environments (2 GiB each for runs and masks) and environment
/// slots (8 GiB); far past what the memory limits let one session reach.
thread_local! {
    /// knobs, SK_UNFOLD_HIST=1: unfoldings per constant row (diagnostics)
    pub static UHIST: std::cell::RefCell<Option<FxHashMap<u32, u64>>> = std::cell::RefCell::new(
        if KNOBS && std::env::var_os("SK_UNFOLD_HIST").is_some() { Some(FxHashMap::default()) } else { None });
    static TRACE: std::cell::Cell<u32> = std::cell::Cell::new(std::env::var("SK_TRACE").ok().and_then(|s| s.parse().ok()).unwrap_or(0));
    static TDEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    /// milestone 41, knobs SK_DSTACK=1: the conversions and whnfs in
    /// progress (kind, sides, ticks at entry), printed with SK_DIAG_SECS
    pub(crate) static DSTACK_ON: bool = std::env::var_os("SK_DSTACK").is_some();
    pub(crate) static DSTACK: std::cell::RefCell<Vec<(u8, V, V, u32)>> = const { std::cell::RefCell::new(Vec::new()) };
}
#[inline(always)]
pub(crate) fn dstack_on() -> bool {
    KNOBS && DSTACK_ON.with(|x| *x)
}
pub(crate) fn dstack_push(k: u8, a: V, b: V, t: u32) {
    DSTACK.with(|d| d.borrow_mut().push((k, a, b, t)));
}
pub(crate) fn dstack_pop() {
    DSTACK.with(|d| {
        d.borrow_mut().pop();
    });
}
const VALS_CAP: usize = 1 << 28;
const VALS_FULL: &str = "value arena limit (2^28 values per declaration)";
const ENVS_CAP: usize = 1 << 28;
const SLOTS_CAP: usize = 1 << 31;
/// Milestone 36: regions (region.rs) open once a session's arena holds
/// this many values, and roll back only past `REGION_MIN` values made.
const REGION_AT: usize = 1 << 22;
const REGION_MIN: usize = 1 << 8;
const REGION_REACH8: usize = 2;
const REGION_LIT_KEEP: usize = 512;
const REGION_LIT_AT: usize = 64;
/// milestone 37: see `reg_fwd`
const REGION_FWD: u8 = 1;
const REGION_FRONT: u8 = 0;
const REGION_PIN: bool = true;
/// milestone 29/37: entries of the per-worker memos of MAIN terms'
/// variables (`wide_main`, `uses_main`) before they start over
const WIDE_CAP: usize = 1 << 20;
const REGION_LOGK: usize = 0;
const REGION_GROW: usize = 2;
/// Milestone 38: a whnf miss nested in other whnfs past this fraction of
/// the worker's stack is handed up to the outermost whnf (`whnf_outer`),
/// which has the rest of the stack to work it out
const DEEP_DIV: usize = 2;
/// milestone 39: a ground machine run's first step budget (a declaration
/// doubles it at every run that runs out)
const GROUND_FUEL: u64 = 1 << 20;
/// milestone 39: session values past which closed computations go to the
/// ground machine (16 x REGION_AT)
const GROUND_AT: usize = 1 << 26;
/// milestone 40: what a memo lookup of the ground machine costs, in steps
/// of the machine (a hash of the key and a probe, about the time of a few
/// steps); a delayed term is looked up when its forcings save more
const MEMO_COST: u64 = 4;

const DEEP_WHNF: u32 = 8192;
/// milestone 46: see `redo_cut`
const REDO_CUT: u64 = 2;
/// milestone 45: most comparisons or inferences an outermost call keeps
/// waiting while it works out handed-up ones (a bound, not a tuning: a
/// chain deeper than this many slices of half the stack is declined)
const DEEP_PEND_CAP: usize = 1 << 24;
/// Milestone 38: ticks per level past which a handed-up attempt doubles the
/// bound (a quarter of `GHOST_TICKS`, a rollback's own cost)
const DEEP_TICKS: u32 = region::GHOST_TICKS / 4;
/// milestone 36: `args_refuted` on, and its budget per argument pair
const ARGS_REFUTE: bool = true;
const REFUTE_TICKS: u32 = 256;
/// knobs builds: SK_TABLE_CAP=n caps every slab at n entries (to test the
/// full path: the declaration declines, the run goes on)
fn slab_cap(c: usize) -> usize {
    if KNOBS {
        if let Some(n) = std::env::var("SK_TABLE_CAP").ok().and_then(|s| s.parse::<usize>().ok()) {
            return n.min(c);
        }
    }
    c
}


/// milestone 21: undecided walk nodes per declaration before same-head
/// neutral pairs stop being walked at a comparison's entry
const WALK_WASTE: u64 = 400_000;
/// slots of `cll_dm` minus one (2^12 slots, 64 KiB per worker)
const CLL_MASK: usize = (1 << 12) - 1;
/// milestone 23: slots of `lsub_dm` minus one (2^12 slots, 64 KiB per worker)
const LSUB_MASK: usize = (1 << 12) - 1;
/// milestone 25: an argument a binder body never reads is not made a value
const ARG_SKIP: bool = true;
const PF_HOLE: bool = true;
/// Milestone 34: values the walks through environments and spines
/// (`over_let`, `mentions_fv`) visit before they give up.
const MENTION_FUEL: u32 = 256;
/// Milestone 34: ticks the arguments of a literal fold over a let value
/// may take before the fold is skipped (`let_skip_fold`).
const LET_PROBE: u32 = 1024;
/// Milestone 41: the budget of CommonHeadFirst in ticks (a lazy delta loop
/// past it tries a common head). Sweep (con-leche / Init w1, G): off
/// 45.72 / 22.49, 256: 50.59 / 24.93, 1024: 46.47 / 22.57, 4096: 45.40 /
/// 22.47, 16384: 45.47 / 22.48; CFSG's three walls pass at each.
const HEAD_PROBE: u32 = 4096;
/// Milestone 48: the budget in ticks of comparing two applications of the
/// same regular definition by unfolding both, before their arguments
/// (knobs SK_DOVETAIL, 0: off); args_refuted's, the other way round
const DOVETAIL: u32 = 256;
const LS_IDENT: bool = true;
const LS_CLASS: bool = true;

pub type V = u32;
static BIG_ZERO: BigUint = BigUint::ZERO;
/// Milestone 37: the content key of a big Nat literal: its length and a
/// few digits (both ends and the middle). Equal contents, equal keys;
/// numbers that differ only elsewhere share a key.
fn lit_key(n: &BigUint) -> u64 {
    let mut d = n.iter_u64_digits();
    let len = d.len();
    let mid = n.iter_u64_digits().nth(len / 2).unwrap_or(0);
    let (a, b) = (d.next().unwrap_or(0), d.next_back().unwrap_or(0));
    hmix(hmix(hmix(hmix(n.bits(), len as u64), a), b), mid)
}
/// Milestone 47: Lean's bound on the Nat numerals the kernel takes in or
/// computes (`LEAN_NAT_MAX_SIZE`, default 128 MiB, kernel v4.34 on): past
/// it the declaration is refused (a kernel exception), the operation is
/// not unfolded from its definition.
const NAT_MAX_BYTES: u64 = 128 << 20;
const NAT_SIZE_MSG: &str = "the kernel refused a `Nat` numeral because its size exceeds the maximum; increase the LEAN_NAT_MAX_SIZE environment variable to allow it";
/// The size of `n` as Lean counts it: whole 64-bit limbs, one at least.
fn nat_bytes(n: &BigUint) -> u64 {
    n.bits().div_ceil(64).max(1) * 8
}
fn nat_sized(n: BigUint) -> Result<BigUint, &'static str> {
    if nat_bytes(&n) > NAT_MAX_BYTES {
        Err(NAT_SIZE_MSG)
    } else {
        Ok(n)
    }
}
/// Milestone 37: `x * y` skipping the zero 64-bit digits of the shorter
/// operand (CFSG's bit-sliced tables multiply a long, mostly zero number
/// by a short one); num-bigint's product otherwise.
fn nat_mul(x: &BigUint, y: &BigUint) -> BigUint {
    let (l, s) = if x.bits() >= y.bits() { (x, y) } else { (y, x) };
    let sd: Vec<u64> = s.iter_u64_digits().collect();
    // only worth it for a short factor of a long one
    if sd.len() > 4 || l.bits() < 64 * 32 {
        return x * y;
    }
    let ld: Vec<u64> = l.iter_u64_digits().collect();
    let mut out = vec![0u64; ld.len() + sd.len()];
    for (j, &b) in sd.iter().enumerate() {
        if b == 0 {
            continue;
        }
        let mut carry = 0u128;
        for (i, &a) in ld.iter().enumerate() {
            if a == 0 && carry == 0 {
                continue;
            }
            let t = a as u128 * b as u128 + out[i + j] as u128 + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        let mut k = ld.len() + j;
        while carry != 0 {
            let t = out[k] as u128 + carry;
            out[k] = t as u64;
            carry = t >> 64;
            k += 1;
        }
    }
    let mut bytes = Vec::with_capacity(out.len() * 8);
    for d in &out {
        bytes.extend_from_slice(&d.to_le_bytes());
    }
    BigUint::from_bytes_le(&bytes)
}
/// Spines and argument lists on the stack while short (no allocation).
pub type SpineVec = smallvec::SmallVec<[u32; 8]>;
pub type ArgVec = smallvec::SmallVec<[V; 8]>;
macro_rules! cn {
    ($i:expr) => {
        #[cfg(feature = "cnt")]
        THUNK_KINDS[$i].fetch_add(1, Ordering::Relaxed);
    };
}
type SmallVec16 = smallvec::SmallVec<[u32; 16]>;
/// Milestone 14: the worker's hash maps hash through this builder, which
/// under feature `cnt` counts every hash (one per get/insert/entry probe,
/// and one per entry moved when a table grows) in slot `P_BASE + I`.
#[derive(Clone, Copy, Default)]
pub struct CntB<const I: usize>;
impl<const I: usize> std::hash::BuildHasher for CntB<I> {
    type Hasher = rustc_hash::FxHasher;
    #[inline(always)]
    fn build_hasher(&self) -> rustc_hash::FxHasher {
        cn!(P_BASE + I);
        rustc_hash::FxHasher::default()
    }
}
type CMap<K, W, const I: usize> = std::collections::HashMap<K, W, CntB<I>>;
type CSet<K, const I: usize> = std::collections::HashSet<K, CntB<I>>;
/// counter slots of the probe census (feature `cnt`)
pub const P_BASE: usize = 1100;
pub const P_SPINE: usize = P_BASE + 40;
pub const P_FTAB: usize = P_BASE + 41;
pub const P_PDM: usize = P_BASE + 42;
pub const P_CDM: usize = P_BASE + 43;
pub const P_UDM: usize = P_BASE + 44;
pub const P_KTAB: usize = P_BASE + 45;
pub const P_STAB: usize = P_BASE + 46;
pub const P_MADE: usize = P_BASE + 47;
pub const P_LVL: usize = P_BASE + 48;
pub const P_NAMES: usize = P_BASE + 49;
pub const P_SPINE_GROW: usize = P_BASE + 50;
pub const P_INTERN_CALLS: usize = P_BASE + 51;
pub const P_NAMES_LIST: [&str; 52] = [
    "vmap", "env_map", "infer_cache", "infer_u", "uenv_map", "cll_memo", "lsub_memo", "ll_map", "ls_map", "ll_term_map",
    "eq_cache", "fail_cache", "same_no", "term_memo", "unfold_memo", "lam_var", "var_slots", "shash_memo", "proj_map", "nat_map",
    "uses0_memo", "uses_main", "lp_ok", "prop_pos", "canon_memo", "eqp", "block_roots", "prop_ind", "cases", "matchers",
    "lp_list_map", "-", "-", "-", "-", "-", "-", "-", "-", "-",
    "spines(neu)", "frames", "pdm(direct)", "cdm(direct)", "udm(direct)", "ktab(direct)", "stab(direct)", "VALUES MADE", "levels", "names",
    "spines grow (moved)", "intern calls",
];
/// milestone 15: configuration switches read at start (feature `knobs`);
/// without it every switch is its default as a constant
pub const KNOBS: bool = cfg!(feature = "knobs");
/// milestone 27: the diagnostic hit/miss counters of `Stats` (SUSZ_STATS,
/// SK_DECL_INSTR) are kept in knobs and cnt builds only; release counts
/// unfoldings and values (thresholds read them), the rest stays 0
pub const STATS: bool = cfg!(any(feature = "knobs", feature = "cnt"));
pub const EMPTY: u32 = u32::MAX;
const PROJ_BIT: u32 = 0x8000_0000;
pub const LL_POOL: u32 = 0x8000_0000;
pub const LL_EMPTY: u32 = LL_POOL;
/// milestone 16: a canonical level list that occurs in MAIN is the offset
/// of its content in the environment's side table (`Env::ll_canon`) with
/// these two bits; the worker's pool holds only lists MAIN lacks
pub const LL_SIDE: u32 = 0xC000_0000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Head {
    FVar(u32),
    /// Constant row and level list reference.
    Const(u32, u32),
    Stuck(V),
}

#[derive(Clone, Copy, Debug)]
pub enum Val {
    Sort(u32),
    Lit(u32),
    Clo { term: u32, env: u32, ls: u32 },
    /// milestone 22: a closure with `infer = true` (its own variant, so a
    /// `Val` is 16 bytes and a `Rec` 32)
    CloI { term: u32, env: u32, ls: u32 },
    Neu { head: Head, spine: u32 },
    Thunk { term: u32, env: u32, ls: u32 },
}

#[inline(always)]
fn vkey(v: &Val) -> (u64, u64) {
    let (k, a, b, c) = vkey4(v);
    // two words: two rounds of the hash instead of four
    (((k as u64) << 32) | a as u64, ((b as u64) << 32) | c as u64)
}
#[inline(always)]
fn vkey4(v: &Val) -> (u8, u32, u32, u32) {
    match *v {
        Val::Sort(l) => (0u8, l, 0, 0),
        Val::Lit(i) => (1, i, 0, 0),
        Val::Clo { term, env, ls } => (2, term, env, ls),
        Val::CloI { term, env, ls } => (3, term, env, ls),
        Val::Neu { head: Head::FVar(i), spine } => (4, i, spine, 0),
        Val::Neu { head: Head::Const(r, l), spine } => (5, r, l, spine),
        Val::Neu { head: Head::Stuck(x), spine } => (6, x, spine, 0),
        Val::Thunk { term, env, ls } => (7, term, env, ls),
    }
}
/// Milestone 23: the inference caches keyed without the mode. The entry
/// holds the result and, for a check-mode result, the declaration's
/// level-parameter list it was checked under (NONE: inferred only). A
/// check-mode result answers an infer-only query (as the second probe did
/// before); an infer-only one never answers a check query. One probe per
/// query instead of two on an infer-only miss.
#[inline(always)]
fn ikey2(t: u32, env: u32, ls: u32) -> (u64, u64) {
    (((t as u64) << 32) | env as u64, ls as u64)
}
#[inline(always)]
fn icache_hit(e: Option<&(V, u32)>, check: bool, lp: u32) -> Option<V> {
    match e {
        Some(&(v, c)) if !check || c == lp => Some(v),
        _ => None,
    }
}
#[inline(always)]
fn icache_put<S: std::hash::BuildHasher>(m: &mut std::collections::HashMap<(u64, u64), (V, u32), S>, k: (u64, u64), r: V, check: bool, lp: u32) {
    debug_assert!(lp != NONE);
    if check {
        m.insert(k, (r, lp));
    } else {
        // an infer-only result never replaces a checked one
        m.entry(k).or_insert((r, NONE));
    }
}
#[derive(Clone, Copy)]
/// One step of lazy delta.
enum DStep {
    /// the same regular definition with equal arguments
    Equal,
    /// unfolded (one side or both), then `whnf_core` (cheap)
    Next(V, V),
    /// neither side unfolds
    Stuck,
    /// milestone 48: both sides unfolded and compared: not equal
    Differ,
}

#[derive(Clone, Copy)]
struct Memo {
    /// a thunk's forced value, or (any other value) its whnf: whnf and
    /// whnf_core force first, so a thunk never has the others
    whnf: u32,
    /// milestone 22: `whnf_core` and its cheap-projection form in one word:
    /// NONE unknown, else the result, with `CORE_FULL` when it is the full
    /// `whnf_core`. A full result also answers a cheap query (it is the
    /// same value reduced further: definitionally equal, and the cheap
    /// form exists only to save work); a cheap one never answers a full
    /// query.
    core: u32,
    infer: u32,
    /// milestone 15: `unfold` in the record instead of a map by value id;
    /// milestone 22: bits 0..29 the unfolding (`UF_NONE` unknown, `UF_NO`
    /// does not unfold), bits 30..31 `has_fvar` (2 unknown). Value ids are
    /// below 2^28 (`VALS_CAP`: the slab declines past it), so they fit.
    uf: u32,
}
/// milestone 23: slots of `tnp_dm` minus one
const TNP_MASK: usize = (1 << 12) - 1;
const SH_CASES_KNOWN: u8 = 1;
const SH_CASES_SOME: u8 = 2;
const SH_MATCH_KNOWN: u8 = 4;
const SH_MATCH_SOME: u8 = 8;
const EQ_KNOWN: u8 = 1;
const EQ_TRUE: u8 = 2;
const EQ_SAME_NO: u8 = 4;
/// milestone 31: the pair was being compared when an argument probe ran out
/// of budget; a later probe that reaches it stops at once (it would only
/// spend its budget on the same walk). Only probes read it: a probe's stop
/// is never an answer (both sides unfold, as after any exhausted probe).
const EQ_PDEAD: u8 = 8;
const CORE_FULL: u32 = 1 << 30;
const UF_MASK: u32 = (1 << 30) - 1;
const UF_NONE: u32 = UF_MASK;
const UF_NO: u32 = UF_MASK - 1;
const _: () = assert!(VALS_CAP <= 1 << 28);
impl Memo {
    const NEW: Memo = Memo { whnf: NONE, core: NONE, infer: NONE, uf: (2 << 30) | UF_NONE };
    #[inline(always)]
    fn core_get(&self, cheap: bool) -> u32 {
        let c = self.core;
        if c == NONE || (!cheap && c & CORE_FULL == 0) { NONE } else { c & !CORE_FULL }
    }
    #[inline(always)]
    fn core_set(&mut self, cheap: bool, r: u32) {
        debug_assert!(r < 1 << 28);
        if !cheap {
            self.core = r | CORE_FULL;
        } else if self.core == NONE {
            self.core = r;
        }
    }
    #[inline(always)]
    fn fvar(&self) -> u32 {
        self.uf >> 30
    }
    #[inline(always)]
    fn set_fvar(&mut self, r: bool) {
        self.uf = (self.uf & UF_MASK) | ((r as u32) << 30);
    }
    #[inline(always)]
    fn unfold(&self) -> u32 {
        self.uf & UF_MASK
    }
    #[inline(always)]
    fn set_unfold(&mut self, r: u32) {
        debug_assert!(r <= UF_MASK);
        self.uf = (self.uf & !UF_MASK) | r;
    }
}
const _: () = assert!(std::mem::size_of::<Rec>() == 32);
/// Milestone 15: a value and its memos in one record (one index, one
/// cache line for `force`/`whnf` after a `val` read), as nano-lean keeps
/// its memo in the value.
#[derive(Clone, Copy)]
pub struct Rec {
    pub v: Val,
    m: Memo,
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    /// milestone 17: argument probes under non-regular heads (made, equal, out of budget, ticks)
    pub probe: [u64; 5],
    pub values: u64,
    pub infer_hits: u64,
    pub infer_misses: u64,
    pub whnf_hits: u64,
    pub whnf_misses: u64,
    pub defeq_calls: u64,
    pub defeq_cache_hits: u64,
    pub unfolds: u64,
    pub iota: u64,
    pub blocks_foreign: u64,
    pub max_values: u64,
    /// check-mode inference of a closed MAIN term skipped: checked in an
    /// earlier declaration of this worker
    pub checked_hits: u64,
    pub checked_misses: u64,
    /// milestone 29: open facts used (`open_fact`)
    pub open_hits: u64,
    /// closed-pair definitional equalities found true in an earlier
    /// declaration of this worker
    pub eqp_hits: u64,
    pub infer_u_hits: u64,
    pub unfold_memo_hits: u64,
    pub eqp_stored: u64,
    pub eqp_flushes: u64,
    pub lvl_flushes: u64,
    pub memo_flushes: u64,
    /// per-declaration equality cache hits by key band: MAIN terms, other
    pub eq_hits_main: u64,
    pub eq_hits_arena: u64,
    pub cases_direct: u64,
    pub match_direct: u64,
    pub proj_calls: u64,
    pub proj_true: u64,
    pub proj_unfolds: u64,
    pub proj_fallback_none: u64,
    /// built-in readings (Bool, Nat constructors) met before declared
    pub known_miss: u64,
    pub sess_resets: u64,
    /// milestone 35: declarations run again in the overflow arenas
    pub big_runs: u64,
    pub scratch_decls: u64,
    pub evals: u64,
    pub interns: u64,
    pub infer_calls: u64,
    /// milestone 36: regions opened, rolled back, kept (the result reached
    /// too much), values dropped by rollbacks, values copied out
    pub reg: [u64; 5],
    /// milestone 37: regions opened on work found done again; rollbacks
    /// refused because pinned work did not fit
    pub reg_redo: u64,
    pub reg_pin_kept: u64,
    /// milestone 37: attempts skipped (`reg_grow`)
    pub reg_skip: u64,
    /// milestone 38: whnfs handed up to the outermost (`Stop::Deep`)
    pub deep_up: u64,
    pub ckpts: u64,
    pub late: u64,
    pub late_ld: u64,
    /// milestone 37: log entries read by attempts
    pub reg_seg: u64,
    /// milestone 39: ground machine runs, answered true, handed to the
    /// kernel, steps handed to the kernel, machine steps, pairs compared by
    /// the kernel, values imported, values exported
    pub gr: [u64; 10],
    /// milestone 41: pairs with a side that is a proof by its recursor's
    /// motive, compared by their types before whnf_core (taken, equal)
    pub pfirst: [u64; 2],
    /// milestone 41, knobs (SK_KTRAP): K-like recursor checks on a closed
    /// major whose type is not the constructor's syntactically (count,
    /// kernel ticks spent in their comparisons)
    pub ktrap: [u64; 2],
    /// milestone 41: NatFoldWaits (same operation compared, equal by
    /// operands, other side unfolded)
    pub natwait: [u64; 3],
    /// milestone 41: CommonHeadFirst (lazy delta past its budget, decided
    /// by a common head)
    pub headprobe: [u64; 6],
    /// milestone 48: same-head comparisons unfolded first (runs, arguments
    /// after, -, decided by unfolding, ticks)
    pub dovetail: [u64; 5],
}

pub(crate) enum NatWait {
    Fold,
    Equal,
    Next(V, V),
}

pub struct Worker {
    pub env: &'static Env<'static>,
    pub m: u32,
    /// milestone 18: every term node at `nb + t`, its used mask at `ub + t`
    /// (`env::Region`); MAIN is ids [0, mlen), the current arena's block
    /// nodes ids [m, m + blk.len()) (m = blk.base, mlen <= m)
    nb: *const crate::env::Node,
    ub: *const u64,
    /// milestone 51: the used masks' high words (#63 to #125), at `hb + t`
    /// for terms of range past 63
    hb: *const u64,
    mlen: u32,
    /// `env.consts`, `env.row_of_name` without going through `env`
    consts: &'static [ConstInfo],
    rows: &'static [u32],
    pub lv: Levels<'static>,
    ll: Vec<u32>,
    ll_map: CMap<Box<[u32]>, u32, 7>,
    lss: Vec<(u32, u32)>,
    ls_map: CMap<(u32, u32), u32, 8>,
    lsub_memo: CMap<(u32, u32), u32, 6>,
    lsub_scratch: FxHashMap<u32, u32>,
    // per declaration
    pub blk: Cols,
    pub blk_side: Side,
    pub wlits: Vec<LitVal>,
    /// values with their memos (milestone 15: one record per value)
    pub vals: Slab<Rec>,
    /// spines as hash-consed slices (flags: a projection in it, an argument
    /// with a free variable once known)
    sp: Spines,
    projs: Vec<(u32, u32)>,
    /// milestone 13: each environment as a run of `eslots` (start, length),
    /// oldest entry first: `env_get` is one load
    eloc: Slab<(u32, u32, u64)>,
    eslots: Slab<u32>,
    /// per environment: the mask of entries a frame (a cut environment)
    /// holds, 0 for environments made by pushes
    /// frames by content
    ftab: frames::FrameTab,
    /// (environment, mask) -> frame, direct-mapped, stamped by generation
    pdm: Vec<[u32; 5]>,
    pbuf: Vec<u32>,
    pub fv_ty: Vec<V>,
    /// argument terms of the applications being evaluated (see `eval`)
    argstack: Vec<u32>,
    /// milestone 34: values of the `let`s whose bodies are being inferred
    /// (Lean's let variables in the local context; see `over_let`)
    let_vals: Vec<V>,
    /// milestone 34: `let_vals` below this index skip the fold without a
    /// probe: one over them ran out of budget in their scope
    let_skip: usize,
    /// free variables in scope (bound by a check or by a reuse below)
    fv_busy: Vec<bool>,
    /// the variable a lambda `(term, env, ls)` was checked under: comparing
    /// its type (an `infer` closure) under the same variable finds the body
    /// type in the inference cache instead of inferring the body again
    lam_var: CMap<(u32, u32, u32), V, 15>,
    // ---- kept across declarations (position-monotone: a fact made while
    // checking declaration d is used only at declarations after d)
    /// MAIN term -> (declaration + 1, level parameter list) of a successful
    /// check-mode inference at ls = 0 in a safe declaration
    shared: &'static Shared,
    /// definitional equalities found true between closed MAIN terms
    /// (thunks and closures, any level substitution) -> declaration
    eqp: CMap<[u32; 6], u32, 25>,
    /// level parameter lists by global id (`Shared::lps`), copied on demand
    lp_lists: Vec<Option<Box<[u32]>>>,
    lp_list_map: CMap<Box<[u32]>, u32, 30>,
    /// level tables (pool, substitutions, their memos, worker levels) are
    /// flushed between declarations past this many entries (SK_LVL_FLUSH)
    lvl_flush: usize,
    /// `cll_memo` and `lsub_memo` are dropped past this many entries (SK_MEMO_FLUSH)
    cur_lp_list: u32,
    poison: bool,
    infer_cache: CMap<(u64, u64), (V, u32), 2>,
    /// milestone 8: inference by (term, entries read, ls, check)
    infer_u: CMap<(u64, u64), (V, u32), 3>,
    uenv_map: CMap<smallvec::SmallVec<[u32; 8]>, u32, 4>,
    /// milestone 12: (used mask, environment) -> used-entries id, direct-mapped
    udm: Vec<[u32; 5]>,
    /// milestone 34: lambdas' closed body types (`lam_type_record`),
    /// direct-mapped: (lambda, environment, levels, generation, type,
    /// variable)
    lam_dm: Vec<[u32; 6]>,
    unfold_memo: CMap<V, V, 14>,
    /// both outcomes, keyed by the ordered pair of value ids (hash-consing
    /// makes a thunk's or closure's id stand for its (term, env, ls))
    eq_cache: CMap<u64, u8, 10>,
    fail_cache: CSet<(V, V), 11>,
    uses0_memo: CMap<(u32, u32), bool, 20>,
    /// `uses_var` beyond the mask for MAIN terms: a property of the file, kept
    uses_main: CMap<(u32, u32), bool, 20>,
    /// milestone 29: MAIN term -> its loose variables when its range is
    /// past 63 and there are at most WIDE_K of them (`wide_vars`)
    wide_main: FxHashMap<u32, Option<SmallVec16>>,
    /// the same for the session's block terms (emptied with the session;
    /// not used in the scratch arena, whose block ids are its own)
    wide_blk: FxHashMap<u32, Option<SmallVec16>>,
    /// `ticks` when the declaration started
    decl_ticks0: u32,
    block_roots: CMap<u32, Option<u32>, 26>,
    vmap: CMap<(u64, u64), V, 0>,
    env_map: CMap<u64, u32, 1>,
    /// constants without spine by row: `gen << 32 | value`, and the level list
    ktab: Vec<u64>,
    ktab_ll: Vec<u32>,
    /// closed MAIN thunks and closures at `ls = 0`, indexed by term:
    /// `gen << 32 | value`
    ctab: Vec<u64>,
    cgen: u32,
    proj_map: CMap<(u32, u32), u32, 18>,
    nat_map: CMap<u64, V, 19>,
    /// milestone 37: big Nat literals by a hash of all their digits (equal
    /// contents are one value: shared thunks and memos, one copy kept)
    big_map: CMap<u64, V, 19>,
    ll_term_map: CMap<u32, u32, 9>,
    prop_ind: CMap<u32, bool, 27>,
    // context
    pub cur_decl: u32,
    pub self_vis: u8,
    pub safety: u8,
    /// `stats.known_miss` when the declaration began
    known_miss0: u64,
    pub cur_lparams: Vec<u32>,
    lp_ok: CMap<u32, bool, 22>,
    // control
    first_fail: &'static AtomicU32,
    pub ticks: u32,
    /// milestone 17: `tick` takes its slow path when `ticks` reaches this
    /// (the next multiple of 4096: cancellation; or the end of a probe's budget)
    tick_alarm: u32,
    /// an argument probe under a non-regular head is running; it ends at `probe_end`
    probe_on: bool,
    probe_end: u32,
    stack_base: usize,
    stack_limit: usize,
    pub stats: Stats,
    cll_memo: CMap<u64, u32, 5>,
    /// milestone 19: `const_ll` of MAIN terms at a substitution, direct-mapped
    /// (CLL_MASK + 1 slots of side offset, substitution, level epoch, list)
    cll_dm: Vec<[u32; 4]>,
    /// milestone 23: `lsub` results direct-mapped in front of `lsub_memo`
    /// (level, substitution, level epoch, result)
    lsub_dm: Vec<[u32; 4]>,
    /// bumped by `flush_levels` (never 0: an empty slot never matches)
    lvl_epoch: u32,
    /// casesOn shapes by row (`cases_shape`); a property of the file
    cases: CMap<u32, Option<(u32, u32)>, 28>,
    /// milestone 23: `tele_not_proof` of constant heads by (row, arguments)
    /// (row, n, 0 empty / 1 false / 2 true); in cells, `surely_not_proof`
    /// takes &self
    tnp_dm: Vec<std::cell::Cell<[u32; 3]>>,
    /// milestone 41: per recursor row, the level of the sort its motive
    /// ends in (a term of the recursor's type), NONE when not read
    rec_msort: FxHashMap<u32, u32>,
    /// milestone 41: ProofsComparedBeforeReduced on (knobs SK_PFIRST=0:
    /// off); SK_KTRAP=1 counts closed non-syntactic K checks, =2 aborts at
    /// the first
    pfirst: bool,
    ktrap: u8,
    /// milestone 41: NatFoldWaits on (knobs SK_NATWAIT=0: off)
    nat_wait: bool,
    /// milestone 41: CommonHeadFirst's budget in ticks, also NatFoldWaits'
    /// congruence (HEAD_PROBE; knobs SK_HEAD_PROBE, 0: off / unbudgeted)
    head_probe: u32,
    /// milestone 48: the budget of unfolding first (DOVETAIL)
    dovetail: u32,
    /// milestone 48: unfolding first runs: EQ_PDEAD is not read (a mark
    /// left by an earlier probe would end it at once)
    pdead_off: bool,
    /// milestone 48: unfolding first came past `deep_at` bytes of stack,
    /// where a probe does not hand comparisons up: it stops and the
    /// arguments are compared as before, outside any budget
    dove_deep: bool,
    matchers: CMap<u32, Option<(u32, u32, u32)>, 29>,
    /// (type, k) -> the k-th variable of that type (`open_var`); per declaration
    var_slots: CMap<u64, V, 16>,
    /// milestone 21: nodes the structural walks of this declaration spent
    /// on pairs they did not find equal
    walk_wasted: u64,
    vdepth: u32,
    /// release-da: the variables of the open binders, outermost first
    #[cfg(debug_assertions)]
    vstack: Vec<V>,
    /// sorts by level: `gen << 32 | value`
    stab: Vec<u64>,
    /// milestone 28: the inductive check's walks, memoized for one block
    pub ind_memo: Box<crate::induct::IndMemo>,
    /// milestone 25: per row, the class of its parameter list + 1 (0 unknown)
    pclass: Vec<u32>,
    pclass_map: FxHashMap<Box<[u32]>, u32>,
    /// (row, level list) -> argument positions whose domain is surely a
    /// proposition at those levels
    prop_pos: CMap<(u32, u32), u64, 23>,
    term_memo: CMap<(u64, u64, u64), bool, 13>,
    /// node budget of one structural comparison (SK_SAME_FUEL)
    same_fuel: u32,
    shash_memo: CMap<V, u64, 17>,
    /// SK_PROBE=1: milestone 5 counters (no behaviour change)
    /// SK_P1 (proposal 1, canonical first-order thunks): 0 off, 1 constant
    /// applications whose arguments are all atomic, 2 any arguments within
    /// SK_P1_CAP nodes; SK_P1_CLOSED=1 also for closed terms
    canon_memo: CMap<(u32, u32, u32), V, 24>,
    /// direct-mapped canonical-application memo: (term, env, ls, generation, value)
    cdm: Vec<[u32; 5]>,
    /// milestone 17: same_term's pairs, direct-mapped (TDM_MASK + 1 slots)
    tdm: Vec<[u32; 8]>,
    /// on for the declaration (not in inductive groups or the quotient)
    p1_active: bool,
    p1_left: u32,
    p1_nest: u32,
    p2_on: bool,
    p2_unfolds0: u64,
    nm: names::Names,
    /// p2 threshold base: values in the session when the declaration began
    p2_vals0: u64,
    // ---- milestone 10: sessions (see STATUS.md)
    /// SK_SESSION_DECLS=n (testing): also end it every n declarations
    sess_decls: u32,
    /// K02: session size in bytes (K02_SESS_MIB, default SESSION_MIB)
    sess_max: usize,
    sess_len: u32,
    /// the declaration checked last in this session (u32::MAX: none)
    sess_last: u32,
    /// the session must end before the next declaration
    sess_end: bool,
    /// the current declaration runs in the scratch arena
    scratch: bool,
    /// milestone 29: the declaration type whose Pi telescope is about to be
    /// opened (`kb_root`), then that telescope (`kb_tele`) and the
    /// environment of its body (`kb_env`); NONE outside `check_type`
    kb_root: u32,
    kb_tele: u32,
    kb_env: u32,
    stash: Box<Stash>,
    /// generation of the session's direct-table stamps while in scratch
    stash_gen: u32,
    stash_p2_vals0: u64,
    gen_top: u32,
    /// bytes of big Nat literals made in the session (heap of `wlits`)
    wlit_bytes: usize,
    /// the interned level-parameter list of the current declaration, part
    /// of the key of check-mode inference results
    cur_lp: u32,
    /// milestone 35: the lambda term being inferred as the head of an
    /// application (`lam_type_record` keeps only such lambdas' types)
    lam_head: u32,
    /// milestone 35: a type was kept in `lam_dm` in this session (else
    /// `bind_body` does not look)
    lam_any: bool,
    /// milestone 35: a block of the current declaration did not fit the
    /// arena (the declaration runs again in the overflow arenas)
    pub arena_full: bool,
    /// milestone 36 (region.rs): the innermost open region's value mark,
    /// 0 when none is open
    reg_vm: u32,
    /// regions open once the arena holds this many values (SK_REGION_AT;
    /// usize::MAX: never)
    reg_at: usize,
    /// a region rolls back only past this many values (SK_REGION_MIN)
    reg_min: usize,
    /// a rollback copies out at most `reg_reach8` eighths of the values the
    /// region made (SK_REGION_REACH8)
    reg_reach8: usize,
    /// big-literal memos stop surviving rollbacks past this many bytes of
    /// big literals in the session (SK_REGION_LIT_KEEP, MiB)
    reg_lit_keep: usize,
    /// SK_REGION_POISON=1 (knobs): dead ids are marked, not reused; =2
    /// also checks after every rollback that no table names a dead id
    reg_poison: bool,
    reg_check: bool,
    /// rollbacks so far (opaque name leaves carry it)
    reg_epoch: u32,
    /// writes of the open regions that may name their ids
    undo: Vec<Undo>,
    /// closed thunks a rollback keeps forced (thunk, forced value)
    reg_pairs: Vec<(V, V)>,
    /// SK_REGION_CLOSED=0 (knobs): no closed thunk kept
    reg_closed: bool,
    /// milestone 38: a whnf loop that began without a region opens one
    /// once the session wants regions (SK_REGION_LATE=0: off; 1: only at
    /// whnf's delta steps, not inside whnf_core's loop or lazy delta)
    reg_late: bool,
    reg_late2: bool,
    reg_lategate: bool,
    /// milestone 39: the ground machine (SK_GROUND=0: off), and whether a
    /// run of it is in progress (the kernel's own steps inside it do not
    /// start another)
    ground: bool,
    ground_busy: bool,
    /// knobs, gates (SK_GROUND=2): every closed pair with a side that
    /// reduces and every closed whnf goes to the ground machine
    ground_all: bool,
    /// milestone 39: machine steps a run may take before it gives the work
    /// back to the kernel; doubles per declaration at every run that ran
    /// out (`GROUND_FUEL`, SK_GROUND_FUEL)
    ground_fuel: u64,
    ground_fuel0: u64,
    ground_at: usize,
    /// ticks when a run last ran out: the next run waits until the kernel
    /// has done as much work as that run's budget (the machine's waste
    /// stays below the kernel's own work)
    ground_out_at: Option<u64>,
    /// milestone 40: the machine's heap kept from one run to the next
    /// (a declaration's runs share what they import twice and the
    /// constants they force), and the lowest marks of the rollbacks since
    /// the last run ended (vals, environments, literals): a rollback below
    /// what the heap may name drops it
    gm: Option<Box<ground::Gm>>,
    ground_cut: (u32, u32, u32),
    /// milestone 40: memo of forced delayed terms in the machine
    /// (SK_GROUND_MEMO=0: off), and what a lookup costs in machine steps
    /// (`MEMO_COST`, SK_MEMO_COST)
    ground_memo: bool,
    memo_cost: u64,
    /// milestone 38: whnf calls nested in this one (0: none running)
    wdepth: u32,
    /// past this many bytes of stack a nested whnf miss is handed up
    /// (stack limit / SK_DEEP_DIV; 0: never)
    deep_at: usize,
    /// the value handed up with `Stop::Deep`
    deep_v: V,
    /// milestone 45: the closed term (term, level substitution, check)
    /// handed up with `Stop::DeepInfer`, the pair with `Stop::DeepDefeq`
    deep_inf: (u32, u32, bool),
    deep_eq: (V, V),
    /// past `deep_at` when the stack was last measured (tick_slow)
    deep_zone: bool,
    /// milestone 38: an outermost attempt that handed up is rolled back (SK_DEEP_ROLL=1)
    deep_roll: bool,
    /// milestone 38: past this many nested whnfs a miss is handed up (SK_DEEP_WHNF)
    deep_n: u32,
    /// the declaration's hand-up bound (doubles after costly hand-ups)
    deep_cur: u32,
    /// SK_DEEP_TICKS
    deep_ticks: u32,
    /// ticks when the running attempt first reached half the bound (0: not yet)
    deep_half: u32,
    /// milestone 38: a checkpoint's next region opens at its marks
    /// (SK_REGION_CKSAME=0: after the copies, as in milestone 37)
    reg_ckpt_same: bool,
    pub(super) reg_ckpt_req: bool,
    reg_ckpt_new: Option<region::Reg>,
    /// milestone 37: a rollback keeps the forced values of the thunks
    /// (whnf memos of the values) its copies reach (SK_REGION_FWD: 0 off,
    /// 1 on, the region kept when one does not fit; 2 on, the memo dropped)
    reg_fwd: u8,
    /// milestone 37: values of a region made of older parts keep their
    /// whnf memos (SK_REGION_FRONT: 0 off, 1 on and the region kept when
    /// one does not fit, 2 on and the memo dropped)
    reg_front: u8,
    /// milestone 37: `uses_main` is dropped past this many entries
    /// (SK_USES_CAP; WIDE_CAP by default)
    uses_cap: usize,
    /// milestone 37: `eqp` and `cll_memo`/`lsub_memo` caps (`capped`)
    eqp_cap: usize,
    memo_cap: usize,
    /// milestone 37: checkpoints in whnf's loop (SK_REGION_CKPT=0 off)
    reg_ckpt: bool,
    /// a checkpoint after `reg_at / reg_ckdiv` values (SK_REGION_CKDIV)
    reg_ckdiv: usize,
    /// milestone 37: big Nat results shared by content (SK_BIG_SHARE=0 off)
    big_share: bool,
    /// SK_REGION_REBUILD=1 (knobs): milestone 36's rebuild of the spine
    /// and frame tables after a growth instead of deletion by key
    reg_rebuild: bool,
    reg_delall: bool,
    /// milestone 37: the largest region kept after an attempt inside the
    /// innermost open region (values made); see `reg_grow`
    reg_kmax: usize,
    /// an attempt needs this many times `reg_kmax` values made
    /// (SK_REGION_GROW; 0: always attempt)
    reg_grow: usize,
    /// milestone 37: a region whose log holds more than this many entries
    /// per value it made is kept without an attempt (SK_REGION_LOGK; 0 off)
    reg_logk: usize,
    /// milestone 37 (region.rs, redone work): content keys of values and
    /// environments (`mkey`), by id, 0 unknown; cut with the arena
    mkv: Vec<u64>,
    mke: Vec<u64>,
    /// keys of the roots of rolled-back regions that cost at least
    /// `GHOST_TICKS`; a region opened on a value with one of these keys is
    /// work done again, and its key goes to `pinned`
    ghost: FxHashSet<u64>,
    pinned: FxHashSet<u64>,
    ghost_shape: FxHashSet<u64>,
    /// milestone 46: keys of ghost work redone once and not pinned;
    /// SK_PIN_FIRST=1 (knobs): every key pinned at its first redo, as before
    redo_seen: FxHashSet<u64>,
    reg_pin_first: bool,
    /// milestone 46: the sampled keys' first and second redos (the
    /// worker's run: a property of the workload, not of a session's ids)
    redo_n: [u64; 2],
    /// pinned at the first redo while `redo_cut` x second redos >= first
    /// ones in the sample (REDO_CUT; SK_REDO_CUT in knobs)
    redo_cut: u64,
    /// milestone 46: a rollback must give back `reg_min` values or
    /// REGION_MIN_LIT_BYTES of literals (SK_REGION_BENEFIT=0, knobs: off)
    reg_benefit: bool,
    /// milestone 43: content keys (`lit_key`) of big literals whose memos a
    /// rollback dropped, and of those among them made again after the drop
    /// (work done again: their memos are kept from then on)
    lit_dropped: FxHashSet<u64>,
    lit_redo: FxHashSet<u64>,
    /// SK_LIT_REDO=0 (knobs): every big literal's memo dropped, as before
    lit_redo_on: bool,
    /// `GHOST_TICKS` (SK_GHOST_TICKS in knobs)
    ghost_ticks: u32,
    /// `KEY_FUEL` (SK_KEY_FUEL in knobs)
    key_fuel: u32,
    /// closed regions (root, cost in ticks) whose roots may die in an
    /// enclosing rollback (then their keys go to `ghost`)
    reg_done: Vec<(V, u32)>,
    /// roots of pinned regions an enclosing rollback must keep, with their
    /// whnf memos
    pin_ids: Vec<V>,
    /// SK_REGION_PIN (knobs): 0 off, 1 on (default)
    reg_pin: bool,
    /// milestone 36: `args_refuted` on (SK_ARGS_REFUTE=0 in knobs: off)
    args_refute: bool,
    /// regions open past this many bytes of big literals (SK_REGION_LIT_AT, MiB)
    reg_lit_at: usize,
    /// SK_REGION_MEMO_ALL=0 (knobs): memos of older values may be dropped
    /// past a small budget (milestone 36's first policy)
    reg_memo_all: bool,
    /// SK_REGION_OLDENV=1 (knobs): also thunks over older environments
    reg_oldenv: bool,
    /// milestone 36: the next used-entries id (`uenv_map` entries leave
    /// it at a rollback, so its length is no id)
    uenv_next: u32,
}

/// The session's tables while a scratch declaration runs (and the scratch
/// tables' room between scratch declarations).
#[derive(Default)]
struct Stash {
    blk: Cols,
    blk_side: Side,
    wlits: Vec<LitVal>,
    vals: Slab<Rec>,
    sp: Spines,
    projs: Vec<(u32, u32)>,
    eloc: Slab<(u32, u32, u64)>,
    eslots: Slab<u32>,
    ftab: frames::FrameTab,
    fv_ty: Vec<V>,
    fv_busy: Vec<bool>,
    lam_var: CMap<(u32, u32, u32), V, 15>,
    var_slots: CMap<u64, V, 16>,
    shash_memo: CMap<V, u64, 17>,
    term_memo: CMap<(u64, u64, u64), bool, 13>,
    infer_cache: CMap<(u64, u64), (V, u32), 2>,
    infer_u: CMap<(u64, u64), (V, u32), 3>,
    unfold_memo: CMap<V, V, 14>,
    uenv_map: CMap<smallvec::SmallVec<[u32; 8]>, u32, 4>,
    eq_cache: CMap<u64, u8, 10>,
    fail_cache: CSet<(V, V), 11>,
    uses0_memo: CMap<(u32, u32), bool, 20>,
    block_roots: CMap<u32, Option<u32>, 26>,
    vmap: CMap<(u64, u64), V, 0>,
    env_map: CMap<u64, u32, 1>,
    proj_map: CMap<(u32, u32), u32, 18>,
    nat_map: CMap<u64, V, 19>,
    /// milestone 37: big Nat literals by a hash of all their digits (equal
    /// contents are one value: shared thunks and memos, one copy kept)
    big_map: CMap<u64, V, 19>,
    prop_ind: CMap<u32, bool, 27>,
    canon_memo: CMap<(u32, u32, u32), V, 24>,
    stab: Vec<u64>,
    ctab: Vec<u64>,
    wlit_bytes: usize,
    uenv_next: u32,
}

macro_rules! sess_tables {
    ($m:ident) => {
        $m!(blk, blk_side, wlits, vals, sp, projs, eloc, eslots, ftab, fv_ty, fv_busy, lam_var, var_slots, shash_memo, term_memo, infer_cache, infer_u, unfold_memo, uenv_map, eq_cache, fail_cache, uses0_memo, block_roots, vmap, env_map, proj_map, nat_map, big_map, prop_ind, canon_memo, stab, ctab, wlit_bytes, uenv_next)
    };
}

impl Worker {
    pub fn new(env: &'static Env<'static>, shared: &'static Shared, first_fail: &'static AtomicU32, stack_limit: usize) -> Worker {
        let x = 0u8;
        // milestone 18: the session's and the scratch arena's slabs
        let blk = crate::env::region().take();
        let stash_blk = crate::env::region().take();
        Worker {
            env,
            m: blk.base,
            nb: crate::env::region().nodes(),
            ub: crate::env::region().used(),
            hb: crate::env::region().used_hi(),
            mlen: env.main.len() as u32,
            consts: &env.consts,
            rows: &env.row_of_name,
            lv: Levels::new(&env.lvl, &env.lvl_intern).with_names(&env.st.canon, env.bytes),
            ll: vec![0],
            ll_map: Default::default(),
            lss: vec![(NONE, 0)],
            ls_map: Default::default(),
            lsub_memo: Default::default(),
            lsub_scratch: FxHashMap::default(),
            blk,
            blk_side: Side::new(),
            wlits: Vec::new(),
            vals: Slab::new(slab_cap(VALS_CAP)),
            sp: Spines::new(slab_cap(spines::SPINE_WORDS)),
            projs: Vec::new(),
            eloc: Slab::new(slab_cap(ENVS_CAP)),
            eslots: Slab::new(slab_cap(SLOTS_CAP)),
            ftab: frames::FrameTab::default(),
            pdm: vec![[0; 5]; dm_bits(0) + 1],
            pbuf: Vec::new(),
            fv_ty: Vec::new(),
            argstack: Vec::new(),
            let_vals: Vec::new(),
            let_skip: 0,
            fv_busy: Vec::new(),
            lam_var: Default::default(),
            lam_dm: vec![[0; 6]; LAM_DM_MASK + 1],
            shared,
            lvl_flush: capped(std::env::var("SK_LVL_FLUSH").ok().and_then(|s| s.parse().ok()).unwrap_or(1 << 22)),
            eqp: Default::default(),
            lp_lists: Vec::new(),
            lp_list_map: Default::default(),
            cur_lp_list: NONE,
            poison: std::env::var_os("SK_POISON").is_some(),
            infer_cache: Default::default(),
            infer_u: Default::default(),
            uenv_map: Default::default(),
            unfold_memo: Default::default(),
            udm: vec![[0; 5]; dm_bits(1) + 1],
            eq_cache: Default::default(),
            fail_cache: Default::default(),
            uses0_memo: Default::default(),
            uses_main: Default::default(),
            wide_main: FxHashMap::default(),
            wide_blk: FxHashMap::default(),
            decl_ticks0: 0,
            block_roots: Default::default(),
            vmap: Default::default(),
            env_map: Default::default(),
            ktab: vec![0; env.consts.len()],
            ktab_ll: vec![0; env.consts.len()],
            ctab: Vec::new(),
            cgen: 1,
            proj_map: Default::default(),
            nat_map: Default::default(),
            big_map: Default::default(),
            ll_term_map: Default::default(),
            prop_ind: Default::default(),
            cur_decl: 0,
            self_vis: 0,
            safety: 0,
            known_miss0: 0,
            cur_lparams: Vec::new(),
            lp_ok: Default::default(),
            first_fail,
            ticks: 0,
            tick_alarm: 0x1000,
            probe_on: false,
            probe_end: 0,
            stack_base: &x as *const u8 as usize,
            stack_limit,
            stats: Stats::default(),
            term_memo: Default::default(),
            same_fuel: 4096,

            shash_memo: Default::default(),
            canon_memo: Default::default(),
            cdm: vec![[0; 5]; 1usize << CDM_BITS],
            tdm: vec![[0; 8]; dm_bits(2) + 1],
            p1_active: false,
            p1_left: 0,
            p1_nest: 0,
            p2_on: false,
            p2_unfolds0: 0,
            nm: names::Names::default(),
            cll_memo: Default::default(),
            cll_dm: vec![[0; 4]; CLL_MASK + 1],
            lsub_dm: vec![[0; 4]; LSUB_MASK + 1],
            lvl_epoch: 1,
            cases: Default::default(),
            tnp_dm: vec![std::cell::Cell::new([0; 3]); TNP_MASK + 1],
            rec_msort: FxHashMap::default(),
            pfirst: !(KNOBS && std::env::var("SK_PFIRST").is_ok_and(|s| s == "0")),
            head_probe: if KNOBS { std::env::var("SK_HEAD_PROBE").ok().and_then(|s| s.parse().ok()).unwrap_or(HEAD_PROBE) } else { HEAD_PROBE },
            dovetail: if KNOBS { std::env::var("SK_DOVETAIL").ok().and_then(|s| s.parse().ok()).unwrap_or(DOVETAIL) } else { DOVETAIL },
            pdead_off: false,
            dove_deep: false,
            nat_wait: !(KNOBS && std::env::var("SK_NATWAIT").is_ok_and(|s| s == "0")),
            ktrap: if KNOBS { std::env::var("SK_KTRAP").ok().and_then(|s| s.parse().ok()).unwrap_or(0) } else { 0 },
            matchers: Default::default(),
            var_slots: Default::default(),
            walk_wasted: 0,
            vdepth: 0,
            #[cfg(debug_assertions)]
            vstack: Vec::new(),
            stab: Vec::new(),
            ind_memo: Default::default(),
            pclass: vec![0; env.consts.len()],
            pclass_map: FxHashMap::default(),
            prop_pos: Default::default(),
            p2_vals0: 0,
            sess_decls: std::env::var("SK_SESSION_DECLS").ok().and_then(|s| s.parse().ok()).unwrap_or(0),
            sess_max: std::env::var("K02_SESS_MIB").ok().and_then(|s| s.parse::<usize>().ok()).filter(|&m| (1..=4096).contains(&m)).unwrap_or(SESSION_MIB) << 20,
            sess_len: 0,
            sess_last: u32::MAX,
            sess_end: true,
            arena_full: false,
            lam_head: NONE,
            lam_any: false,
            scratch: false,
            kb_root: NONE,
            kb_tele: NONE,
            kb_env: NONE,
            stash: Box::new(Stash {
                blk: stash_blk,
                blk_side: Side::new(),
                vals: Slab::new(slab_cap(VALS_CAP)),
                sp: Spines::new(slab_cap(spines::SPINE_WORDS)),
                eloc: Slab::new(slab_cap(ENVS_CAP)),
                eslots: Slab::new(slab_cap(SLOTS_CAP)),
                ctab: Vec::new(), ..Default::default() }),
            stash_gen: 0,
            stash_p2_vals0: 0,
            gen_top: 1,
            wlit_bytes: 0,
            cur_lp: 0,
            reg_vm: 0,
            reg_at: if KNOBS {
                match std::env::var("SK_REGION_AT").ok().and_then(|s| s.parse::<usize>().ok()) {
                    Some(0) => usize::MAX,
                    Some(n) => n,
                    None => REGION_AT,
                }
            } else {
                REGION_AT
            },
            reg_lit_keep: (if KNOBS { std::env::var("SK_REGION_LIT_KEEP").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_LIT_KEEP) } else { REGION_LIT_KEEP }) << 20,
            reg_reach8: if KNOBS { std::env::var("SK_REGION_REACH8").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_REACH8) } else { REGION_REACH8 },
            reg_min: if KNOBS { std::env::var("SK_REGION_MIN").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_MIN) } else { REGION_MIN },
            reg_poison: KNOBS && std::env::var("SK_REGION_POISON").is_ok_and(|s| s == "1" || s == "2"),
            reg_check: KNOBS && std::env::var("SK_REGION_POISON").is_ok_and(|s| s == "2"),
            reg_epoch: 0,
            undo: Vec::new(),
            reg_pairs: Vec::new(),
            reg_oldenv: KNOBS && std::env::var("SK_REGION_OLDENV").is_ok_and(|s| s == "1"),
            reg_memo_all: !(KNOBS && std::env::var("SK_REGION_MEMO_ALL").is_ok_and(|s| s == "0")),
            args_refute: ARGS_REFUTE && !(KNOBS && std::env::var("SK_ARGS_REFUTE").is_ok_and(|s| s == "0")),
            reg_lit_at: (if KNOBS { std::env::var("SK_REGION_LIT_AT").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_LIT_AT) } else { REGION_LIT_AT }) << 20,
            reg_fwd: if KNOBS { std::env::var("SK_REGION_FWD").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_FWD) } else { REGION_FWD },
            reg_front: if KNOBS { std::env::var("SK_REGION_FRONT").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_FRONT) } else { REGION_FRONT },
            mkv: Vec::new(),
            mke: Vec::new(),
            ghost: FxHashSet::default(),
            pinned: FxHashSet::default(),
            ghost_shape: FxHashSet::default(),
            redo_seen: FxHashSet::default(),
            reg_pin_first: KNOBS && std::env::var("SK_PIN_FIRST").is_ok_and(|s| s == "1"),
            redo_n: [0, 0],
            redo_cut: if KNOBS { std::env::var("SK_REDO_CUT").ok().and_then(|s| s.parse().ok()).unwrap_or(REDO_CUT) } else { REDO_CUT },
            reg_benefit: !(KNOBS && std::env::var("SK_REGION_BENEFIT").is_ok_and(|s| s == "0")),
            lit_dropped: FxHashSet::default(),
            lit_redo: FxHashSet::default(),
            lit_redo_on: !(KNOBS && std::env::var("SK_LIT_REDO").is_ok_and(|s| s == "0")),
            key_fuel: if KNOBS { std::env::var("SK_KEY_FUEL").ok().and_then(|s| s.parse().ok()).unwrap_or(region::KEY_FUEL) } else { region::KEY_FUEL },
            ghost_ticks: if KNOBS { std::env::var("SK_GHOST_TICKS").ok().and_then(|s| s.parse().ok()).unwrap_or(region::GHOST_TICKS) } else { region::GHOST_TICKS },
            reg_done: Vec::new(),
            pin_ids: Vec::new(),
            reg_pin: REGION_PIN && !(KNOBS && std::env::var("SK_REGION_PIN").is_ok_and(|s| s == "0")),
            reg_logk: if KNOBS { std::env::var("SK_REGION_LOGK").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_LOGK) } else { REGION_LOGK },
            reg_kmax: 0,
            reg_grow: if KNOBS { std::env::var("SK_REGION_GROW").ok().and_then(|s| s.parse().ok()).unwrap_or(REGION_GROW) } else { REGION_GROW },
            reg_delall: KNOBS && std::env::var("SK_REGION_DELALL").is_ok_and(|s| s == "1"),
            reg_rebuild: KNOBS && std::env::var("SK_REGION_REBUILD").is_ok_and(|s| s == "1"),
            big_share: !(KNOBS && std::env::var("SK_BIG_SHARE").is_ok_and(|s| s == "0")),
            reg_ckpt: !(KNOBS && std::env::var("SK_REGION_CKPT").is_ok_and(|s| s == "0")),
            reg_ckdiv: if KNOBS { std::env::var("SK_REGION_CKDIV").ok().and_then(|s| s.parse().ok()).unwrap_or(2) } else { 2 },
            uses_cap: capped(if KNOBS { std::env::var("SK_USES_CAP").ok().and_then(|s| s.parse().ok()).unwrap_or(WIDE_CAP) } else { WIDE_CAP }),
            eqp_cap: capped(1 << 22),
            memo_cap: capped(MEMO_FLUSH),
            reg_closed: !(KNOBS && std::env::var("SK_REGION_CLOSED").is_ok_and(|s| s == "0")),
            reg_ckpt_same: !(KNOBS && std::env::var("SK_REGION_CKSAME").is_ok_and(|s| s == "0")),
            reg_ckpt_req: false,
            reg_ckpt_new: None,
            wdepth: 0,
            deep_at: match if KNOBS { std::env::var("SK_DEEP_DIV").ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(DEEP_DIV) } else { DEEP_DIV } {
                0 => 0,
                d => stack_limit / d,
            },
            deep_v: NONE,
            deep_inf: (NONE, 0, false),
            deep_eq: (NONE, NONE),
            deep_zone: false,
            deep_n: if KNOBS { std::env::var("SK_DEEP_WHNF").ok().and_then(|s| s.parse().ok()).unwrap_or(DEEP_WHNF) } else { DEEP_WHNF },
            deep_cur: u32::MAX,
            deep_half: 0,
            deep_ticks: if KNOBS { std::env::var("SK_DEEP_TICKS").ok().and_then(|s| s.parse().ok()).unwrap_or(DEEP_TICKS) } else { DEEP_TICKS },
            deep_roll: !(KNOBS && std::env::var("SK_DEEP_ROLL").is_ok_and(|s| s == "0")),
            reg_late: !(KNOBS && std::env::var("SK_REGION_LATE").is_ok_and(|s| s == "0")),
            reg_late2: !(KNOBS && std::env::var("SK_REGION_LATE").is_ok_and(|s| s == "0" || s == "1")),
            reg_lategate: KNOBS && std::env::var("SK_REGION_LATEGATE").is_ok_and(|s| s == "1"),
            ground: !(KNOBS && std::env::var("SK_GROUND").is_ok_and(|s| s == "0")),
            ground_all: KNOBS && std::env::var("SK_GROUND").is_ok_and(|s| s == "2"),
            ground_fuel: GROUND_FUEL,
            ground_at: if KNOBS { std::env::var("SK_GROUND_AT").ok().and_then(|s| s.parse().ok()).unwrap_or(GROUND_AT) } else { GROUND_AT },
            ground_out_at: None,
            gm: None,
            ground_cut: (u32::MAX, u32::MAX, u32::MAX),
            ground_memo: !(KNOBS && std::env::var("SK_GROUND_MEMO").is_ok_and(|s| s == "0")),
            memo_cost: if KNOBS { std::env::var("SK_MEMO_COST").ok().and_then(|s| s.parse().ok()).unwrap_or(MEMO_COST) } else { MEMO_COST },
            ground_fuel0: if KNOBS { std::env::var("SK_GROUND_FUEL").ok().and_then(|s| s.parse().ok()).unwrap_or(GROUND_FUEL) } else { GROUND_FUEL },
            ground_busy: false,
            uenv_next: 0,
        }
    }

    // ---- milestone 15: configuration knobs. Without feature `knobs` each one
    // is its default as a constant (the switch is not read), so the hot paths
    // test nothing; `cargo build --features knobs` reads them as before.

    /// Bytes used by the session's tables (entries, not room: tables keep
    /// their room across sessions).
    fn sess_bytes(&self) -> usize {
        fn vb<T>(v: &[T]) -> usize {
            std::mem::size_of_val(v)
        }
        fn mb<K, W, S>(m: &std::collections::HashMap<K, W, S>) -> usize {
            // a hash table holds about 8/7 slots per entry, plus control bytes
            m.len() * (std::mem::size_of::<(K, W)>() + 1) * 8 / 7
        }
        fn sb<K, S>(m: &std::collections::HashSet<K, S>) -> usize {
            m.len() * (std::mem::size_of::<K>() + 1) * 8 / 7
        }
        self.blk.len() * 23
            + self.wlit_bytes
            + vb(&self.blk_side.lets)
            + vb(&self.blk_side.lvls)
            + vb(&self.wlits)
            + vb(&self.vals)
            + self.sp.bytes()
            + vb(&self.projs)
            + vb(&self.eloc)
            + vb(&self.eslots)
            + self.ftab.bytes()
            + vb(&self.fv_ty)
            + vb(&self.fv_busy)
            + mb(&self.lam_var)
            + mb(&self.var_slots)
            + mb(&self.shash_memo)
            + mb(&self.term_memo)
            + mb(&self.infer_cache)
            + mb(&self.infer_u)
            + mb(&self.unfold_memo)
            + mb(&self.uenv_map)
            + mb(&self.eq_cache)
            + sb(&self.fail_cache)
            + mb(&self.uses0_memo)
            + mb(&self.block_roots)
            + mb(&self.vmap)
            + mb(&self.env_map)
            + mb(&self.proj_map)
            + mb(&self.nat_map)
            + mb(&self.big_map)
            + mb(&self.prop_ind)
            + mb(&self.canon_memo)
    }


    /// Milestone 37: bytes this worker holds, by group: per-constant
    /// arrays, direct-mapped tables, tables kept across sessions, the
    /// session's tables (room included), the scratch arena's.
    pub fn mem_report(&self) -> String {
        fn v<T>(x: &Vec<T>) -> usize {
            x.capacity() * std::mem::size_of::<T>()
        }
        fn h<K, W, S>(m: &std::collections::HashMap<K, W, S>) -> usize {
            m.capacity() * (std::mem::size_of::<(K, W)>() + 1)
        }
        fn hs<K, S>(m: &std::collections::HashSet<K, S>) -> usize {
            m.capacity() * (std::mem::size_of::<K>() + 1)
        }
        let percon = v(&self.ktab) + v(&self.ktab_ll) + v(&self.pclass);
        let dm = v(&self.pdm) + v(&self.lam_dm) + v(&self.udm) + v(&self.cdm) + v(&self.tdm) + v(&self.cll_dm)
            + v(&self.lsub_dm) + self.tnp_dm.capacity() * 12 + v(&self.stab);
        let lv = v(&self.ll) + h(&self.ll_map) + v(&self.lss) + h(&self.ls_map) + h(&self.lsub_memo) + h(&self.cll_memo)
            + h(&self.ll_term_map) + h(&self.prop_pos) + h(&self.lp_list_map) + self.lv.held_bytes();
        let kept = h(&self.eqp) + h(&self.uses_main) + h(&self.wide_main) + h(&self.cases) + h(&self.matchers)
            + h(&self.pclass_map) + h(&self.lp_ok) + self.ind_memo.held_bytes();
        let names = self.nm.held_bytes();
        macro_rules! sess {
            ($o:expr) => {{
                let o = $o;
                o.blk.bytes() + v(&o.wlits) + o.wlit_bytes + o.vals.held_bytes() + o.sp.held_bytes() + v(&o.projs)
                    + o.eloc.held_bytes() + o.eslots.held_bytes() + o.ftab.held_bytes() + v(&o.fv_ty) + v(&o.fv_busy)
                    + h(&o.lam_var) + h(&o.var_slots) + h(&o.shash_memo) + h(&o.term_memo) + h(&o.infer_cache)
                    + h(&o.infer_u) + h(&o.unfold_memo) + h(&o.uenv_map) + h(&o.eq_cache) + hs(&o.fail_cache)
                    + h(&o.uses0_memo) + h(&o.block_roots) + h(&o.vmap) + h(&o.env_map) + h(&o.proj_map)
                    + h(&o.nat_map) + h(&o.big_map) + h(&o.prop_ind) + h(&o.canon_memo)
            }};
        }
        let sess = sess!(self) + h(&self.wide_blk) + v(&self.undo) + v(&self.argstack);
        let stash = sess!(&*self.stash);
        let mb = |x: usize| x >> 20;
        format!(
            "mem percon {} dm {} lv {} kept {} [eqp {} uses_main {}/{} wide_main {} cases {} matchers {} ind {}] names {} sess {} stash {} (MiB; vals {} sp {} eloc {} eslots {} lits {} vmap {} env_map {})",
            mb(percon), mb(dm), mb(lv), mb(kept), mb(h(&self.eqp)), mb(h(&self.uses_main)), self.uses_main.len(), mb(h(&self.wide_main)),
            mb(h(&self.cases)), mb(h(&self.matchers)), mb(self.ind_memo.held_bytes()), mb(names), mb(sess), mb(stash),
            mb(self.vals.held_bytes()), mb(self.sp.held_bytes()), mb(self.eloc.held_bytes()), mb(self.eslots.held_bytes()),
            mb(self.wlit_bytes + v(&self.wlits)), mb(h(&self.vmap)), mb(h(&self.env_map))
        )
    }

    /// knobs, SK_DIAG_SECS=N: every 2^24 ticks past N seconds of the run,
    /// the tables, memory and (SK_UNFOLD_HIST) unfold counts; past 2N the
    /// process ends with status 3 (diagnostics of runs that would be killed)
    #[cold]
    fn diag_dump(&mut self) {
        thread_local! {
            static T0: std::time::Instant = std::time::Instant::now();
            static SECS: u64 = std::env::var("SK_DIAG_SECS").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
        }
        let secs = SECS.with(|s| *s);
        if secs == 0 {
            return;
        }
        let el = T0.with(|t| t.elapsed().as_secs());
        thread_local! { static LAST: std::cell::Cell<u64> = const { std::cell::Cell::new(0) }; }
        if el < secs || LAST.with(|l| l.get()) == el {
            return;
        }
        LAST.with(|l| l.set(el));
        eprintln!("DIAG {el} s ticks {} unfolds {} {}", self.ticks, self.stats.unfolds, self.table_report());
        if dstack_on() {
            let st: Vec<(u8, V, V, u32)> = DSTACK.with(|d| d.borrow().clone());
            let n = st.len();
            eprintln!("DSTACK decl {} depth {n}", self.cur_decl);
            for (i, &(k, a, b, t)) in st.iter().enumerate() {
                if i >= 30 && i + 8 < n {
                    continue;
                }
                let age = self.ticks.wrapping_sub(t);
                let mut sa = self.vshow(a, 5);
                sa.truncate(600);
                if b == NONE {
                    eprintln!("DS {i:>4} {} age {age:>11} {sa}", k as char);
                } else {
                    let mut sb = self.vshow(b, 5);
                    sb.truncate(600);
                    eprintln!("DS {i:>4} {} age {age:>11} {sa}\n            =?= {sb}", k as char);
                }
            }
        }
        eprintln!("DIAG {}", self.mem_report());
        eprintln!("DIAG ground live {:?}", ground::LIVE.with(|l| l.get()));
        self.ground_made_report();
        self.dump_unfold_hist();
        if el >= 2 * secs {
            std::process::exit(3);
        }
    }

    /// knobs, SK_UNFOLD_HIST: the most unfolded constants of this thread
    pub fn dump_unfold_hist(&self) {
        UHIST.with(|h| {
            if let Some(h) = h.borrow().as_ref() {
                let mut v: Vec<(u64, u32)> = h.iter().map(|(&r, &c)| (c, r)).collect();
                v.sort_unstable_by(|a, b| b.cmp(a));
                for (c, r) in v.into_iter().take(40) {
                    eprintln!("UH {c:>12} {}", self.env.name_str(self.consts[r as usize].name));
                }
            }
        });
    }

    /// Milestone 36 (SK_DECL_INSTR): the sizes of the session's tables.
    pub fn table_report(&self) -> String {
        format!(
            "redo_n {:?} gr {:?} pfirst {:?} ktrap {:?} natwait {:?} headprobe {:?} reg {:?} redo {} pinkept {} skip {} seg {} undo {} vals {} eloc {} eslots {} sp_b {} ftab_b {} wlits {} wlit_b {} blk {} vmap {} env_map {} eq {} fail {} icache {} iu {} unf {} uenv {} fv {} sess_b {}",
            self.redo_n, self.stats.gr, self.stats.pfirst, self.stats.ktrap, self.stats.natwait, self.stats.headprobe, self.stats.reg, self.stats.reg_redo, self.stats.reg_pin_kept, self.stats.reg_skip, self.stats.reg_seg, self.undo.len(), self.vals.len(), self.eloc.len(), self.eslots.len(), self.sp.bytes(), self.ftab.bytes(),
            self.wlits.len(), self.wlit_bytes, self.blk.len(), self.vmap.len(), self.env_map.len(),
            self.eq_cache.len(), self.fail_cache.len(), self.infer_cache.len(), self.infer_u.len(),
            self.unfold_memo.len(), self.uenv_map.len(), self.fv_ty.len(), self.sess_bytes()
        )
    }

    /// Swaps the session's tables with the stash (scratch declarations).
    fn swap_stash(&mut self) {
        macro_rules! sw {
            ($($f:ident),*) => { $( std::mem::swap(&mut self.$f, &mut self.stash.$f); )* };
        }
        sess_tables!(sw);
        self.m = self.blk.base;
    }

    /// Runs the current declaration in the scratch arena: the session's
    /// tables are put aside and the declaration starts from empty tables.
    fn enter_scratch(&mut self) {
        debug_assert!(!self.scratch);
        self.mkv.clear();
        self.mke.clear();
        self.swap_stash();
        self.scratch = true;
        self.stats.scratch_decls += 1;
        // the names threshold counts this arena's values
        std::mem::swap(&mut self.p2_vals0, &mut self.stash_p2_vals0);
        self.p2_vals0 = 0;
        self.stash_gen = self.cgen;
        // a generation never used before or after (`cgen_bump` takes the
        // next unused one): what the scratch stamps in the direct tables is
        // never read back by the session
        self.cgen_bump();
        self.poison_shift(self.cur_decl);
    }
    /// Back to the session; the scratch tables are emptied (their room kept
    /// for the next scratch declaration).
    fn leave_scratch(&mut self) {
        if !self.scratch {
            return;
        }
        self.count_values();
        self.clear_sess_tables();
        self.swap_stash();
        self.scratch = false;
        self.mkv.clear();
        self.mke.clear();
        self.p2_vals0 = self.stash_p2_vals0;
        // the session's generation again (scratch entries carry a newer one,
        // never handed out again)
        self.cgen = self.stash_gen;
    }

    fn count_values(&mut self) {
        self.stats.max_values = self.stats.max_values.max(self.vals.len() as u64);
        self.stats.values += self.vals.len() as u64;
    }

    /// Empties the session's tables (a new session).
    fn clear_sess_tables(&mut self) {
        self.blk.clear();
        self.blk.shrink(keep_bytes());
        self.blk_side.clear();
        clear_vec(&mut self.blk_side.lets);
        clear_vec(&mut self.blk_side.lvls);
        self.blk_side.lvls.push(0);
        clear_vec(&mut self.wlits);
        self.wlit_bytes = 0;
        clear_slab(&mut self.vals);
        self.sp.clear(keep_bytes());
        clear_vec(&mut self.projs);
        clear_slab(&mut self.eloc);
        clear_slab(&mut self.eslots);
        self.ftab.clear(keep_bytes());
        clear_vec(&mut self.fv_ty);
        clear_vec(&mut self.argstack);
        clear_vec(&mut self.fv_busy);
        clear_map!(self.lam_var);
        clear_map!(self.var_slots);
        clear_map!(self.shash_memo);
        clear_map!(self.term_memo);
        clear_map!(self.infer_cache);
        clear_map!(self.infer_u);
        clear_map!(self.unfold_memo);
        clear_map!(self.uenv_map);
        self.uenv_next = 0;
        clear_map!(self.eq_cache);
        clear_map!(self.fail_cache);
        clear_map!(self.uses0_memo);
        clear_map!(self.block_roots);
        clear_map!(self.vmap);
        clear_map!(self.env_map);
        clear_map!(self.proj_map);
        clear_map!(self.nat_map);
        clear_map!(self.big_map);
        clear_map!(self.prop_ind);
        clear_map!(self.canon_memo);
        clear_map!(self.wide_blk);
    }

    /// debugging (SK_POISON=1): shift every id space of the arena by a
    /// varying amount, so an id that survived a reset points elsewhere
    fn poison_shift(&mut self, d: u32) {
        if self.poison && d != u32::MAX {
            for _ in 0..(d % 7) + 1 {
                let _ = self.mk(Val::Sort(ZERO));
                self.eloc.push((self.eslots.len() as u32, 1, 0));
                self.eslots.push(0);
                self.sp.poison();
                self.fv_ty.push(0);
                self.fv_busy.push(true);
                self.blk.push(SORT, 0, 0, ZERO, 0, 0);
                self.wlits.push(LitVal::Nat(BigUint::zero()));
            }
        }
    }

    /// Ends the session: every table keyed by arena ids is emptied.
    fn new_session(&mut self, d: u32) {
        self.gm = None;
        self.count_values();
        self.clear_sess_tables();
        self.reg_forget();
        self.cgen_bump();
        self.stats.sess_resets += 1;
        self.lam_any = false;
        self.sess_len = 0;
        if self.ll.len() + self.lss.len() + self.lv.len() > self.lvl_flush {
            self.flush_levels();
        }
        self.poison_shift(d);
    }

    /// Clears everything that depends on the declaration being checked.
    pub fn reset(&mut self, d: u32) {
        self.arena_full = false;
        // milestone 36: no region is open between declarations
        self.reg_vm = 0;
        self.reg_kmax = 0;
        self.undo.clear();
        self.let_vals.clear();
        self.let_skip = 0;
        // milestone 10: the arena and its tables live for a session
        let lvl_big = self.ll.len() + self.lss.len() + self.lv.len() > self.lvl_flush;
        let end = d == u32::MAX
            || self.sess_end
            || (self.sess_last != u32::MAX && d <= self.sess_last)
            || (self.sess_decls != 0 && self.sess_len >= self.sess_decls)
            || lvl_big
            || self.sess_bytes() > self.sess_max;
        if end {
            self.new_session(d);
            self.sess_end = false;
        }
        self.sess_last = d;
        self.sess_len += 1;
        self.argstack.clear();
        // milestone 38: the hand-up bound starts over with each declaration
        // (and no whnf is running: a panic may have left the count)
        self.deep_cur = self.deep_n;
        self.wdepth = 0;
        clear_map!(self.lp_ok);
        if self.eqp.len() > self.eqp_cap {
            self.eqp = Default::default();
            self.stats.eqp_flushes += 1;
        }
        // pure memos (their values stay valid): dropped past a size
        if self.cll_memo.len() > self.memo_cap {
            self.cll_memo = Default::default();
            self.stats.memo_flushes += 1;
        }
        if self.lsub_memo.len() > self.memo_cap {
            self.lsub_memo = Default::default();
            self.stats.memo_flushes += 1;
        }
        self.cur_lp_list = NONE;
        // no binder is open between declarations
        self.vdepth = 0;
        self.kb_root = NONE;
        self.kb_tele = NONE;
        self.kb_env = NONE;
        self.decl_ticks0 = self.ticks;
        #[cfg(debug_assertions)]
        self.vstack.clear();
        self.cur_decl = d;
        self.self_vis = 0;
        self.safety = 0;
        self.cur_lparams.clear();
        self.cur_lp = self.lp_list();
        self.known_miss0 = self.stats.known_miss;
        self.walk_wasted = 0;
        self.p1_active = false;
        self.p1_nest = 0;
        if self.p2_on {
        }
        if self.nm.dirty {
            self.nm.reset();
        }
        self.p2_on = false;
        self.p2_unfolds0 = self.stats.unfolds;
        self.p2_vals0 = self.vals.len() as u64;
    }

    /// Forgets every table keyed by worker level ids, level-list pool
    /// references or level substitutions (between declarations only: the
    /// values that held such ids were cleared with the arena). Facts kept
    /// across declarations that name them (closed-pair equalities, the
    /// level lists of constants, proposition positions) go too.
    fn flush_levels(&mut self) {
        self.stats.lvl_flushes += 1;
        self.ll = vec![0];
        self.ll_map = Default::default();
        self.lss = vec![(NONE, 0)];
        self.ls_map = Default::default();
        self.lsub_memo = Default::default();
        self.cll_memo = Default::default();
        self.lvl_epoch = self.lvl_epoch.wrapping_add(1);
        if self.lvl_epoch == 0 {
            self.cll_dm.iter_mut().for_each(|s| *s = [0; 4]);
            self.lsub_dm.iter_mut().for_each(|s| *s = [0; 4]);
            self.lvl_epoch = 1;
        }
        self.ll_term_map = Default::default();
        self.prop_pos = Default::default();
        self.eqp = Default::default();
        self.nm.flush_persistent();
        self.lv = Levels::new(&self.env.lvl, &self.env.lvl_intern).with_names(&self.env.st.canon, self.env.bytes);
        // ktab_ll entries are read only together with a current stamp
        self.cgen_bump();
    }
    /// After a panic inside a declaration: the tables kept across
    /// declarations may be half-written, so they go.
    pub fn after_panic(&mut self) {
        // milestone 24: a panic inside an argument probe left the probe on,
        // and the worker's next declaration declined ("probe budget escaped")
        self.probe_on = false;
        self.ground_busy = false;
        // milestone 28: an inductive block's memo names its scratch ids
        self.ind_memo = Default::default();
        self.set_alarm();
        self.leave_scratch();
        self.new_session(u32::MAX);
        self.sess_last = u32::MAX;
        self.flush_levels();
    }
    /// Milestone 35: swaps the worker's two block arenas with the overflow
    /// arenas `big` (to run a declaration whose blocks did not fit, and
    /// back after it). Both sides start from a new session: no table keeps
    /// an id of the arenas left; the overflow arenas give their pages back.
    pub fn swap_big(&mut self, big: &mut (crate::env::Cols, crate::env::Cols)) {
        self.leave_scratch();
        self.ind_memo = Default::default();
        self.new_session(u32::MAX);
        self.sess_last = u32::MAX;
        std::mem::swap(&mut self.blk, &mut big.0);
        std::mem::swap(&mut self.stash.blk, &mut big.1);
        self.m = self.blk.base;
        for c in [&mut big.0, &mut big.1] {
            c.clear();
            c.shrink(0);
        }
    }
    /// A new generation for the direct tables: the next one never used
    /// (generations only grow; a scratch declaration takes one and the
    /// session returns to its own afterwards).
    fn cgen_bump(&mut self) {
        if self.gen_top == u32::MAX {
            self.ctab.iter_mut().for_each(|s| *s = 0);
            self.ktab.iter_mut().for_each(|s| *s = 0);
            self.stab.iter_mut().for_each(|s| *s = 0);
            self.cdm.iter_mut().for_each(|s| *s = [0; 5]);
            self.tdm.iter_mut().for_each(|s| *s = [0; 8]);
            self.pdm.iter_mut().for_each(|s| *s = [0; 5]);
            self.udm.iter_mut().for_each(|s| *s = [0; 5]);
            self.lam_dm.iter_mut().for_each(|s| *s = [0; 6]);
            self.gen_top = 1;
            // the stashed session's stamps are gone too: it must end
            self.sess_end = true;
        }
        self.gen_top += 1;
        self.cgen = self.gen_top;
    }

    /// The current declaration's level parameters as an interned list.
    fn lp_list(&mut self) -> u32 {
        if self.cur_lp_list == NONE {
            let mut v = self.cur_lparams.clone();
            v.sort_unstable();
            v.dedup();
            let b: Box<[u32]> = v.into();
            self.cur_lp_list = match self.lp_list_map.get(&b) {
                Some(&i) => i,
                None => {
                    let i = {
                        let mut g = self.shared.lps.lock().unwrap();
                        match g.1.get(&b) {
                            Some(&i) => i,
                            None => {
                                let i = g.0.len() as u32;
                                g.0.push(b.clone());
                                g.1.insert(b.clone(), i);
                                i
                            }
                        }
                    };
                    self.lp_list_map.insert(b, i);
                    i
                }
            };
        }
        self.cur_lp_list
    }
    fn lp_list_get(&mut self, g: u32) -> &[u32] {
        let i = g as usize;
        if i >= self.lp_lists.len() {
            self.lp_lists.resize(i + 1, None);
        }
        if self.lp_lists[i].is_none() {
            let l = self.shared.lps.lock().unwrap().0[i].clone();
            self.lp_lists[i] = Some(l);
        }
        self.lp_lists[i].as_deref().unwrap()
    }

    /// Was closed MAIN term `t` checked (at ls = 0) in an earlier
    /// declaration whose level parameters the current one has too? Typing
    /// is preserved when the environment grows, so the check is not redone.
    fn checked_before(&mut self, t: u32) -> bool {
        let x = self.shared.checked[t as usize].load(Ordering::Relaxed);
        if x == 0 {
            return false;
        }
        let (d, l) = (u32::MAX - (x >> 32) as u32, x as u32);
        if d >= self.cur_decl {
            return false;
        }
        let cur = self.lp_list();
        if l == cur {
            return true;
        }
        let a = self.lp_list_get(l).to_vec();
        let b = self.lp_list_get(cur);
        a.iter().all(|x| b.binary_search(x).is_ok())
    }



    #[inline(always)]
    pub fn tick(&mut self) -> R<()> {
        self.ticks = self.ticks.wrapping_add(1);
        if self.ticks == self.tick_alarm {
            return self.tick_slow();
        }
        Ok(())
    }
    /// Every 4096 ticks: cancellation. Under an argument probe also its
    /// budget: past `probe_end` every tick stops (`Stop::Budget`) until the
    /// probe returns, so a caller that swallows one error still stops.
    #[cold]
    #[inline(never)]
    fn tick_slow(&mut self) -> R<()> {
        // milestone 27: the stack measured every TICK_STACK ticks, not at
        // every tick: each recursive step ticks, so at most TICK_STACK
        // frames are pushed between two checks, far inside the 64 MiB
        // margin below the limit
        let x = 0u8;
        let sp = std::hint::black_box(&x) as *const u8 as usize;
        let used = self.stack_base.saturating_sub(sp);
        // milestone 45: inferences and comparisons hand up past `deep_at`
        // (read here, every TICK_STACK ticks: they tick)
        self.deep_zone = self.deep_at != 0 && used > self.deep_at && !self.scratch;
        if used > self.stack_limit {
            // while too deep, every tick measures again (a caller that
            // swallows the decline still stops), as before
            self.tick_alarm = self.ticks.wrapping_add(1);
            return decline("recursion too deep (stack limit)");
        }
        // milestone 47: a worker table near its room declines here, before
        // a push past the room panics
        if self.vals.over_soft() || self.eloc.over_soft() || self.eslots.over_soft() || self.sp.over_soft() {
            return decline("a worker table is full");
        }
        let t = self.ticks;
        if self.probe_on && t == self.probe_end {
            self.probe_end = t.wrapping_add(1);
            self.tick_alarm = self.probe_end;
            return Err(Stop::Budget);
        }
        self.set_alarm();
        if KNOBS && t & 0xf_ffff == 0 {
            self.diag_dump();
        }
        if t & 0xfff == 0 && self.first_fail.load(Ordering::Relaxed) < self.cur_decl {
            return Err(Stop::Cancel);
        }
        Ok(())
    }
    #[inline]
    fn set_alarm(&mut self) {
        let t = self.ticks;
        let next = (t | (TICK_STACK - 1)).wrapping_add(1);
        self.tick_alarm = if self.probe_on && self.probe_end.wrapping_sub(t) < next.wrapping_sub(t) { self.probe_end } else { next };
    }

    // -----------------------------------------------------------------------
    // Terms

    /// milestone 17: the whole 16-byte node, read once. Milestone 18: one
    /// load from the region's base (no MAIN-or-block test, no bounds check).
    #[inline(always)]
    pub fn node(&self, t: u32) -> Node {
        debug_assert!(self.term_live(t), "term {t} read outside MAIN and the current arena");
        // SAFETY: the region maps 16 bytes at every u32 id
        unsafe { *self.nb.add(t as usize) }
    }
    #[inline(always)]
    pub fn tk(&self, t: u32) -> u8 {
        self.node(t).kind
    }
    #[inline(always)]
    pub fn ta(&self, t: u32) -> u32 {
        self.node(t).a
    }
    #[inline(always)]
    pub fn tb(&self, t: u32) -> u32 {
        self.node(t).b
    }
    #[inline(always)]
    pub fn tp(&self, t: u32) -> u32 {
        self.node(t).p
    }
    #[inline(always)]
    pub fn trng(&self, t: u32) -> u32 {
        self.node(t).rng as u32
    }
    /// A MAIN id or one of the current arena's nodes.
    #[inline(always)]
    pub fn term_live(&self, t: u32) -> bool {
        debug_assert!(self.m == self.blk.base, "block ids not those of the current arena");
        t < self.mlen || (t >= self.blk.base && ((t - self.blk.base) as usize) < self.blk.len())
    }
    /// LET body.
    pub fn let_body(&self, t: u32) -> u32 {
        let i = self.tp(t) as usize;
        if t < self.mlen { self.env.side.lets[i].1 } else { self.blk_side.lets[i].1 }
    }

    /// Level list of a CONST term or a pool entry.
    pub fn ll_get(&self, r: u32) -> &[u32] {
        if r & LL_POOL != 0 {
            if r & LL_SIDE == LL_SIDE {
                let o = (r & !LL_SIDE) as usize;
                let side = &self.env.side.lvls;
                let n = side[o] as usize;
                return &side[o + 1..o + 1 + n];
            }
            let o = (r & !LL_POOL) as usize;
            let n = self.ll[o] as usize;
            &self.ll[o + 1..o + 1 + n]
        } else {
            let o = self.tp(r) as usize;
            let side = if r < self.mlen { &self.env.side.lvls } else { &self.blk_side.lvls };
            let n = side[o] as usize;
            if o == 0 { &[] } else { &side[o + 1..o + 1 + n] }
        }
    }
    pub fn ll_intern(&mut self, xs: &[u32]) -> u32 {
        if xs.is_empty() {
            // one form of the empty list (the pool's entry 0)
            return LL_EMPTY;
        }
        if let Some(&o) = self.ll_map.get(xs) {
            return o;
        }
        // a list MAIN has is named by its side offset; only others are pooled
        let r = match self.env.ll_canon.get(xs) {
            Some(&o) => o | LL_SIDE,
            None => {
                let o = self.ll.len() as u32;
                assert!(o < 0x4000_0000, "level-list pool past 2^30 words");
                self.ll.push(xs.len() as u32);
                self.ll.extend_from_slice(xs);
                o | LL_POOL
            }
        };
        self.ll_map.insert(xs.into(), r);
        r
    }
    /// Level substitution for constant `row` at level list `llr`.
    pub fn mk_ls(&mut self, row: u32, llr: u32) -> u32 {
        if self.consts[row as usize].lparams.is_empty() {
            return 0;
        }
        let llr = if llr & LL_POOL != 0 {
            llr
        } else {
            let v = self.ll_get(llr).to_vec();
            self.ll_intern(&v)
        };
        // milestone 25: keyed by the constant's parameter names (a class
        // per list of canonical names), not its row: constants with the
        // same parameters at the same levels share one substitution
        let pc = if LS_CLASS { self.pclass_of(row) } else { row };
        let key = (pc, llr);
        cn!(967);
        if let Some(&x) = self.ls_map.get(&key) {
            cn!(968);
            return x;
        }
        // milestone 25: the identity substitution (the constant's own
        // parameters, in order) is ls = 0, so its terms evaluate as they
        // are, and share what is known about them at ls = 0
        let ps = &self.consts[row as usize].lparams;
        let xs = self.ll_get(llr);
        let ident = LS_IDENT && xs.len() == ps.len() && xs.iter().zip(ps.iter()).all(|(&l, &p)| self.lv.get(l) == (crate::level::K_PARAM, self.env.canon(p), 0));
        if ident {
            self.ls_map.insert(key, 0);
            return 0;
        }
        let id = self.lss.len() as u32;
        self.lss.push((row, llr));
        self.ls_map.insert(key, id);
        id
    }
    /// Milestone 25: the class of constant `row`'s parameter list (equal
    /// lists of canonical names, one class); a property of the file.
    #[inline(always)]
    fn pclass_of(&mut self, row: u32) -> u32 {
        // class + 1, 0 unknown (a zeroed vector: pages made only when used)
        let c = self.pclass[row as usize];
        if c != 0 {
            return c - 1;
        }
        let ps: Box<[u32]> = self.consts[row as usize].lparams.iter().map(|&n| self.env.canon(n)).collect();
        let n = self.pclass_map.len() as u32;
        let c = *self.pclass_map.entry(ps).or_insert(n);
        self.pclass[row as usize] = c + 1;
        c
    }
    #[inline(always)]
    pub fn lsub(&mut self, l: u32, ls: u32) -> u32 {
        if ls == 0 {
            return l;
        }
        self.lsub_some(l, ls)
    }
    #[inline(never)]
    fn lsub_some(&mut self, l: u32, ls: u32) -> u32 {
        // milestone 23: a direct-mapped table first, stamped with the level
        // epoch like `cll_dm` (level ids and substitution ids are reset
        // together by `flush_levels`); the result is a function of (l, ls)
        // within an epoch, so a lost slot is only a probe of the map
        let i = (hmix(l as u64, ls as u64) >> 20) as usize & LSUB_MASK;
        cn!(960);
        let e = self.lsub_dm[i];
        if e[0] == l && e[1] == ls && e[2] == self.lvl_epoch {
            cn!(961);
            return e[3];
        }
        if let Some(&r) = self.lsub_memo.get(&(l, ls)) {
            cn!(962);
            self.lsub_dm[i] = [l, ls, self.lvl_epoch, r];
            return r;
        }
        cn!(963);
        let (row, llr) = self.lss[ls as usize];
        // milestone 14: no allocation on a miss (parameter names and levels
        // on the stack, the subst memo kept by the worker)
        let ps: smallvec::SmallVec<[u32; 8]> = self.consts[row as usize].lparams.iter().map(|&n| self.env.canon(n)).collect();
        let lvls: smallvec::SmallVec<[u32; 8]> = smallvec::SmallVec::from_slice(self.ll_get(llr));
        let f = move |n: u32| -> Option<u32> { ps.iter().position(|&p| p == n).and_then(|i| lvls.get(i).copied()) };
        let mut budget = 32u32;
        let r = match self.lv.subst_small(l, &f, &mut budget) {
            Some(r) => r,
            None => {
                let mut memo = std::mem::take(&mut self.lsub_scratch);
                memo.clear();
                let r = self.lv.subst(l, &f, &mut memo);
                self.lsub_scratch = memo;
                r
            }
        };
        self.lsub_memo.insert((l, ls), r);
        self.lsub_dm[i] = [l, ls, self.lvl_epoch, r];
        r
    }
    pub fn lsub_ll(&mut self, llr: u32, ls: u32) -> u32 {
        if ls == 0 {
            return llr;
        }
        // milestone 25: the list read in place; lsub writes no level list
        // (only levels and its memos), so the pool does not move under it
        let xs = self.ll_get(llr);
        if xs.is_empty() {
            return llr;
        }
        // SAFETY: see above
        let xs: &[u32] = unsafe { std::slice::from_raw_parts(xs.as_ptr(), xs.len()) };
        cn!(965);
        let ys: smallvec::SmallVec<[u32; 8]> = xs.iter().map(|&l| self.lsub(l, ls)).collect();
        if ys[..] == xs[..] { cn!(966); llr } else { self.ll_intern(&ys) }
    }

    pub fn lit(&self, i: u32) -> &LitVal {
        let g = self.env.lits.len() as u32;
        let l = if i < g { &self.env.lits[i as usize] } else { &self.wlits[(i - g) as usize] };
        debug_assert!(!matches!(l, LitVal::Str(s) if s.starts_with('\u{0}')), "literal {i} read after its region was rolled back");
        l
    }

    // -----------------------------------------------------------------------
    // Values

    // ---- milestone 15: arena reads without bounds checks.
    // Invariant (A): every value id `v` held anywhere in the worker was
    // returned by `mk`/`intern`/`neu` (a push onto `vals`) in the current session, and `vals` only grows within
    // a session (it is cleared or swapped, `sess_tables!`, at a
    // session boundary, after which no old id is read: SK_POISON shifts the
    // id spaces to catch one). So `v < vals.len()`. Debug
    // builds assert it. Milestone 36: a region's rollback cuts `vals`
    // (and the environment, spine and literal tables) back to its marks
    // after every table and memo that could name a cut id has dropped it
    // (region.rs); SK_REGION_POISON marks the cut ids instead, and debug
    // builds assert no marked value is read.
    #[inline(always)]
    pub fn val(&self, v: V) -> Val {
        debug_assert!((v as usize) < self.vals.len(), "value id {v} out of the arena ({})", self.vals.len());
        // SAFETY: invariant (A)
        let x = unsafe { self.vals.get_unchecked(v as usize).v };
        debug_assert!(!matches!(x, Val::Sort(region::DEAD_LVL)), "value {v} read after its region was rolled back");
        x
    }
    #[inline(always)]
    fn memo_at(&self, v: V) -> &Memo {
        debug_assert!((v as usize) < self.vals.len());
        // SAFETY: invariant (A)
        unsafe { &self.vals.get_unchecked(v as usize).m }
    }
    #[inline(always)]
    fn memo_mut(&mut self, v: V) -> &mut Memo {
        debug_assert!((v as usize) < self.vals.len());
        // SAFETY: invariant (A)
        unsafe { &mut self.vals.get_unchecked_mut(v as usize).m }
    }
    /// The run (start, length) of environment `env` (not EMPTY).
    /// Invariant (E): environment ids are made by `push_env`/`prune_build`
    /// in the current session (pushes onto `eloc`, cleared together with
    /// `eslots` at a session boundary), and every run lies inside `eslots`
    /// (a run is pushed only after its slots are). Debug builds assert both.
    #[inline(always)]
    fn eloc_of(&self, env: u32) -> (u32, u32) {
        debug_assert!((env as usize) < self.eloc.len(), "environment id {env} out of range ({})", self.eloc.len());
        // SAFETY: invariant (E)
        let r = unsafe { *self.eloc.get_unchecked(env as usize) };
        debug_assert!(r.0 != region::DEAD_RUN, "environment {env} read after its region was rolled back");
        debug_assert!((r.0 + r.1) as usize <= self.eslots.len());
        (r.0, r.1)
    }
    /// Slot `k` of `eslots`, `k` inside a run (invariant (E)).
    #[inline(always)]
    fn eslot(&self, k: u32) -> u32 {
        debug_assert!((k as usize) < self.eslots.len());
        // SAFETY: invariant (E), callers index inside a run
        unsafe { *self.eslots.get_unchecked(k as usize) }
    }
    #[inline(always)]
    pub fn mk(&mut self, v: Val) -> R<V> {
        let id = self.vals.len();
        // milestone 47: the slab's own room (2^28), not 2^31: past it the
        // slab panicked ("a worker table is full", CFSG's archiveGiantBytes)
        if id >= self.vals.cap() {
            return decline(VALS_FULL);
        }
        cn!(P_MADE);
        self.vals.push(Rec { v, m: Memo::NEW });
        Ok(id as u32)
    }
    /// Hash-consed values: equal structure (same term, environment, level
    /// substitution, head, spine) gives the same id, so the identity fast
    /// path of definitional equality and the per-value memos are shared.
    /// Milestone 15: inlined at every call site, so the dispatch on the
    /// kind (known there) folds away; the table probes stay out of line.
    #[inline(always)]
    pub fn intern(&mut self, v: Val) -> R<V> {
        if let Val::Neu { head, spine } = v {
            if spine != EMPTY {
                return self.neu(head, spine, &[]);
            }
        }
        let key = vkey(&v);
        cn!(P_INTERN_CALLS);
        #[cfg(feature = "cnt")]
        { self.stats.interns += 1; }
        // sorts: indexed by level
        if let Val::Sort(l) = v {
            let i = l as usize;
            if i >= self.stab.len() {
                self.stab.resize(i + 1024, 0);
            }
            cn!(P_STAB);
            let s = self.stab[i];
            if (s >> 32) as u32 == self.cgen {
                return Ok(s as u32);
            }
            return self.intern_sort_miss(v, i);
        }
        // constants without arguments: indexed by row
        if let Val::Neu { head: Head::Const(row, llr), spine: EMPTY } = v {
            cn!(P_KTAB);
            let s = self.ktab[row as usize];
            if (s >> 32) as u32 == self.cgen && self.ktab_ll[row as usize] == llr {
                return Ok(s as u32);
            }
            return self.intern_const_miss(v, key, row, llr);
        }
        self.intern_vmap(v, key)
    }
    #[inline(never)]
    fn intern_sort_miss(&mut self, v: Val, i: usize) -> R<V> {
        // milestone 36: through `vmap`, so a sort keeps its id when the
        // direct table is dropped (a region's rollback bumps the generation)
        let id = self.intern_vmap(v, vkey(&v))?;
        self.stab[i] = ((self.cgen as u64) << 32) | id as u64;
        Ok(id)
    }
    #[inline(never)]
    fn intern_const_miss(&mut self, v: Val, key: (u64, u64), row: u32, llr: u32) -> R<V> {
        let id = match self.vmap.get(&key) {
            Some(&x) => x,
            None => {
                let id = self.mk(v)?;
                self.vmap.insert(key, id);
                id
            }
        };
        self.ktab[row as usize] = ((self.cgen as u64) << 32) | id as u64;
        self.ktab_ll[row as usize] = llr;
        Ok(id)
    }
    #[inline(never)]
    fn intern_vmap(&mut self, v: Val, key: (u64, u64)) -> R<V> {
        // one probe: the entry is found or made in place
        let n = self.vals.len();
        cn!(974);
        cn!(980 + (key.0 >> 32) as usize);
        match self.vmap.entry(key) {
            std::collections::hash_map::Entry::Occupied(e) => {
                cn!(975);
                cn!(988 + (key.0 >> 32) as usize);
                Ok(*e.get())
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                if n >= self.vals.cap() {
                    return decline(VALS_FULL);
                }
                e.insert(n as u32);
                cn!(P_MADE);
                self.vals.push(Rec { v, m: Memo::NEW });
                Ok(n as u32)
            }
        }
    }

    /// Milestone 23: the environment of binder body `body` with `v` pushed
    /// on `env`; a body with no loose variable reads no environment, so it
    /// gets EMPTY (what every table keys a closed term under) and no push.
    #[inline(always)]
    pub fn push_for(&mut self, v: V, env: u32, body: u32) -> u32 {
        if self.trng(body) == 0 {
            EMPTY
        } else if PF_HOLE && self.used_mask(body) & 1 == 0 {
            // milestone 25: an entry the body never reads is a HOLE, so
            // environments that differ only there are one
            self.push_env(HOLE, env)
        } else {
            self.push_env(v, env)
        }
    }
    /// Milestone 25: the environment of binder body `body` with the value
    /// of argument term `a` (in `aenv`, `ls`) pushed on `env`, the value
    /// made only when `body` reads entry 0: a body that never reads it
    /// gets a HOLE there (bit 0 of the used mask is exact: no subterm of
    /// `body` reads that entry), a closed body no push at all.
    #[inline(always)]
    fn push_arg(&mut self, a: u32, aenv: u32, ls: u32, env: u32, body: u32) -> R<u32> {
        if self.trng(body) == 0 {
            return Ok(EMPTY);
        }
        if ARG_SKIP && self.used_mask(body) & 1 == 0 {
            return Ok(self.push_env(HOLE, env));
        }
        let av = self.thunk(a, aenv, ls)?;
        Ok(self.push_env(av, env))
    }
    pub fn push_env(&mut self, v: V, env: u32) -> u32 {
        let key = ((v as u64) << 32) | env as u64;
        let n = self.eloc.len() as u32;
        cn!(972);
        let e = *self.env_map.entry(key).or_insert(n);
        if e != n { cn!(973); }
        if e == n {
            self.push_loc(v, env);
            self.ulog(Undo::EnvMap(key));
        }
        e
    }
    /// The run of a new environment: the parent's run extended in place
    /// when it ends the slots, else copied to the end first.
    #[inline(always)]
    fn push_loc(&mut self, v: V, env: u32) {
        let top = self.eslots.len() as u32;
        if env == EMPTY {
            self.eloc.push((top, 1, 0));
        } else {
            let (s, l) = self.eloc_of(env);
            if s + l == top {
                self.eloc.push((s, l + 1, 0));
            } else {
                cn!(1019);
                #[cfg(feature = "cnt")]
                THUNK_KINDS[1020].fetch_add(l as u64, Ordering::Relaxed);
                if l <= 8 {
                    // short runs word by word (no memmove call)
                    self.eslots.reserve(l as usize + 1);
                    for k in s..s + l {
                        let x = self.eslots[k as usize];
                        self.eslots.push(x);
                    }
                } else {
                    self.eslots.extend_from_within(s as usize..(s + l) as usize);
                }
                self.eloc.push((top, l + 1, 0));
            }
        }
        self.eslots.push(v);
    }
    /// Entry `i` of environment `env` (HOLE in a frame where the term never
    /// reads), None past its end.
    #[inline(always)]
    fn env_at(&self, env: u32, i: u32) -> Option<u32> {
        if env == EMPTY {
            return None;
        }
        let (s, l) = self.eloc_of(env);
        if i >= l { None } else { Some(self.eslot(s + l - 1 - i)) }
    }
    /// The run (start, length) of `env`, None for EMPTY.
    #[inline(always)]
    fn env_run(&self, env: u32) -> Option<(u32, u32)> {
        if env == EMPTY { None } else { Some(self.eloc_of(env)) }
    }
    #[inline(always)]
    fn used_mask(&self, t: u32) -> u64 {
        debug_assert!(self.term_live(t), "term {t} read outside MAIN and the current arena");
        // SAFETY: the region maps 8 bytes at every u32 id
        unsafe { *self.ub.add(t as usize) }
    }
    /// Milestone 51: the used mask's high word of a term of range past 63:
    /// bit j for #(63 + j), j < 63 (exact), bit 63 for any index of 126 or
    /// more.
    #[inline(always)]
    fn used_hi(&self, t: u32) -> u64 {
        debug_assert!(self.term_live(t) && self.trng(t) > 63, "high mask word of term {t}");
        // SAFETY: as used_mask; written for every term of range past 63
        unsafe { *self.hb.add(t as usize) }
    }
    /// Milestone 13: environment `env` cut to the entries term `t` reads,
    /// as a frame hash-consed by content (unread entries HOLE, ending at
    /// the last read one): environments that agree on what `t` reads give
    /// one id. Exact below 63 entries (the used mask is exact there);
    /// wider ranges, or an environment shorter than the range (left for
    /// `env_get` to reject), keep `env`.
    #[inline(always)]
    pub fn prune(&mut self, t: u32, env: u32) -> u32 {
        let r = self.trng(t);
        if r == 0 || env == EMPTY {
            return EMPTY;
        }
        if r > 63 {
            return env;
        }
        let u = self.used_mask(t) & ((1u64 << r) - 1);
        debug_assert!((env as usize) < self.eloc.len());
        // SAFETY: invariant (E); milestone 22: the frame mask is the third
        // word of the environment's record (0 for pushes), read with its run
        if unsafe { self.eloc.get_unchecked(env as usize).2 } == u {
            // milestone 23: release-da checks the frame against its content
            // (length r, real slots exactly at u's bits), not against the
            // stored word the fast path trusted
            #[cfg(debug_assertions)]
            self.check_frame(env, r, u);
            return env;
        }
        let (s, l) = self.eloc_of(env);
        if l < r {
            return env;
        }
        if l == r && u == (1u64 << r) - 1 {
            // every entry read: the environment as it is (not the frame of
            // the same content, if one exists)
            cn!(1018);
            return env;
        }
        let h = (hmix(env as u64, u) >> 20) as usize & PDM_MASK;
        cn!(P_PDM);
        let sl = self.pdm[h];
        if sl[0] == env && sl[1] == u as u32 && sl[2] == (u >> 32) as u32 && sl[3] == self.cgen {
            cn!(1015);
            return sl[4];
        }
        let out = self.prune_build(s, l, r, u);
        #[cfg(debug_assertions)]
        self.check_frame(out, r, u);
        self.pdm[h] = [env, u as u32, (u >> 32) as u32, self.cgen, out];
        out
    }
    /// Milestone 23 (release-da): frame `e` is the cut of some environment
    /// to mask `u` over `r` entries: its run has length r, its slots are
    /// real values exactly at u's bits (HOLE elsewhere), and the mask word
    /// stored with it is the mask of that content. Catches a wrong stored
    /// mask (it would let a term that reads a HOLE take the fast path) and
    /// a fast path that returns a frame of another mask.
    #[cfg(debug_assertions)]
    fn check_frame(&self, e: u32, r: u32, u: u64) {
        let (s, l, m) = self.eloc[e as usize];
        assert_eq!(l, r, "frame {e}: length {l}, range {r}");
        let mut cm = 0u64;
        for j in 0..l {
            if self.eslots[(s + l - 1 - j) as usize] != HOLE {
                cm |= 1u64 << j;
            }
        }
        assert_eq!(m, cm, "frame {e}: stored mask {m:#x}, content mask {cm:#x}");
        assert_eq!(cm, u, "frame {e}: content mask {cm:#x}, term mask {u:#x}");
    }
    #[inline(never)]
    fn prune_build(&mut self, s: u32, l: u32, r: u32, u: u64) -> u32 {
        cn!(1016);
        let mut c = std::mem::take(&mut self.pbuf);
        c.clear();
        // oldest first: entry r-1 down to entry 0
        let top = (s + l) as usize;
        for j in (0..r).rev() {
            c.push(if u & (1u64 << j) != 0 { self.eslots[top - 1 - j as usize] } else { HOLE });
        }
        let h = frames::fhash(&c);
        let (eloc, eslots) = (&self.eloc, &self.eslots);
        let run = |e: u32| {
            let (s, l, _) = eloc[e as usize];
            &eslots[s as usize..(s + l) as usize]
        };
        cn!(P_FTAB);
        let out = match self.ftab.find(h, &c, run) {
            Ok(e) => {
                cn!(1017);
                e
            }
            Err(slot) => {
                let e = self.eloc.len() as u32;
                self.eloc.push((self.eslots.len() as u32, r, u));
                self.eslots.extend_from_slice(&c);
                self.ft_insert(h, slot, e);
                e
            }
        };
        self.pbuf = c;
        out
    }
    #[inline(always)]
    pub fn env_get(&self, env: u32, i: u32) -> R<V> {
        #[cfg(feature = "cnt")]
        THUNK_KINDS[900 + (i.min(31) as usize)].fetch_add(1, Ordering::Relaxed);
        if env == EMPTY {
            return reject("loose bound variable");
        }
        let (s, l) = self.eloc_of(env);
        if i >= l {
            return reject("loose bound variable");
        }
        // i < l: inside the run
        Ok(self.eslot(s + l - 1 - i))
    }
    /// The neutral value `head` applied to spine `base` and then `extra`,
    /// hash-consed as a whole (milestone 12: one probe, not one per cell).
    #[inline(always)]
    pub fn neu(&mut self, head: Head, base: u32, extra: &[u32]) -> R<V> {
        if base == EMPTY && extra.is_empty() {
            return self.intern(Val::Neu { head, spine: EMPTY });
        }
        self.neu_spine(head, base, extra)
    }
    #[inline(never)]
    fn neu_spine(&mut self, head: Head, base: u32, extra: &[u32]) -> R<V> {
        cn!(970);
        cn!(P_SPINE);
        match self.sp.find(&self.vals, head, base, extra) {
            Ok(v) => {
                cn!(971);
                Ok(v)
            }
            Err(slot) => {
                if self.vals.len() >= self.vals.cap() {
                    return decline(VALS_FULL);
                }
                let s = self.sp.make(base, extra);
                let v = self.mk(Val::Neu { head, spine: s })?;
                let j = self.sp.add(slot, v);
                self.ulog(Undo::Sp(j as u32));
                Ok(v)
            }
        }
    }
    /// The neutral value `head` applied to the first `p` elims of `spine`.
    fn neu_prefix(&mut self, head: Head, spine: u32, p: usize) -> R<V> {
        if p >= self.sp.len(spine) {
            return self.neu(head, spine, &[]);
        }
        let xs = SpineVec::from_slice(&self.sp.args(spine)[..p]);
        self.neu(head, EMPTY, &xs)
    }

    /// Does the spine contain a projection?
    #[inline(always)]
    pub fn spine_has_proj(&self, s: u32) -> bool {
        self.sp.flags(s) & spines::F_PROJ != 0
    }

    /// The level list of CONST term `t` under `ls`, canonical (a side or
    /// pool reference). Milestone 16: a MAIN term at ls = 0 is its side
    /// offset (no memo); under ls != 0 memoized per worker by (side offset,
    /// ls), one entry per list content, the memo dropped between
    /// declarations past `memo_flush` entries.
    pub fn const_ll(&mut self, t: u32, ls: u32) -> u32 {
        if t >= self.mlen {
            #[cfg(feature = "cnt")]
            THUNK_KINDS[1013].fetch_add(1, Ordering::Relaxed);
            let l = self.lsub_ll(t, ls);
            return self.canon_ll(l);
        }
        if self.tp(t) == 0 {
            return LL_EMPTY;
        }
        if ls == 0 {
            // milestone 16: MAIN's lists are canonical by side offset
            return self.tp(t) | LL_SIDE;
        }
        #[cfg(feature = "cnt")]
        THUNK_KINDS[1010].fetch_add(1, Ordering::Relaxed);
        // milestone 19: a direct-mapped table stamped with the level epoch
        // (the pool and substitution ids it names are reset together)
        let off = self.tp(t);
        let i = (hmix(off as u64, ls as u64) >> 20) as usize & CLL_MASK;
        let e = self.cll_dm[i];
        if e[0] == off && e[1] == ls && e[2] == self.lvl_epoch {
            return e[3];
        }
        #[cfg(feature = "cnt")]
        THUNK_KINDS[1012].fetch_add(1, Ordering::Relaxed);
        let l = self.lsub_ll(t, ls);
        let r = self.canon_ll(l);
        self.cll_dm[i] = [off, ls, self.lvl_epoch, r];
        r
    }

    /// Level list of a CONST term as a pool reference (one canonical form).
    pub fn canon_ll(&mut self, t: u32) -> u32 {
        if t & LL_POOL != 0 {
            return t;
        }
        if t < self.mlen {
            return if self.tp(t) == 0 { LL_EMPTY } else { self.tp(t) | LL_SIDE };
        }
        // a block term's list, by content
        let xs: smallvec::SmallVec<[u32; 8]> = smallvec::SmallVec::from_slice(self.ll_get(t));
        self.ll_intern(&xs)
    }
    /// Spine elims in order (first applied first), with their node ids;
    /// `spine_in`, milestone 25: read in place, not copied. A spine's words never
    /// change once made and the spine slab never moves (a reserved range,
    /// invariant (S)); it is cleared or swapped only between declarations,
    /// so the slice stays valid for the call that asked for it.
    pub fn spine(&self, s: u32) -> SpineVec {
        SpineVec::from_slice(self.sp.args(s))
    }
    fn spine_in(&self, s: u32) -> &'static [u32] {
        let a = self.sp.args(s);
        // SAFETY: see above
        unsafe { std::slice::from_raw_parts(a.as_ptr(), a.len()) }
    }
    pub fn app_args(&self, s: u32) -> Option<&'static [u32]> {
        if self.spine_has_proj(s) {
            return None;
        }
        Some(self.spine_in(s))
    }
    pub fn fresh(&mut self, ty: V) -> R<V> {
        let id = self.fv_ty.len() as u32;
        self.fv_ty.push(ty);
        self.fv_busy.push(false);
        self.intern(Val::Neu { head: Head::FVar(id), spine: EMPTY })
    }
    /// A variable of type `ty` for a binder being opened (Pestka's counted
    /// variables): the first variable of that type not in scope, so a
    /// binder opened again (or another binder of the same type at the same
    /// depth of its kind) gets the same variable and the caches keyed under
    /// it hit again. A variable stands for nothing but its type, so what was
    /// found about it holds wherever it is reused; two binders in scope at
    /// once never share one (the variable is marked in scope; `close_var`
    /// releases it).
    fn open_var(&mut self, ty: V) -> R<V> {
        let x = self.pick_var(ty)?;
        self.bind_open(x, ty);
        Ok(x)
    }
    /// Milestone 20: a binder opens with variable `x` (from `open_var` or
    /// `reuse_var`). The invariant (asserted in release-da): no two open
    /// binders share a variable, and a variable has one type. `vdepth`
    /// counts the open binders; `vstack` (release-da) lists their
    /// variables, outermost first.
    #[inline(always)]
    fn bind_open(&mut self, x: V, _ty: V) {
        #[cfg(debug_assertions)]
        {
            assert_eq!(self.vstack.len(), self.vdepth as usize, "open binders and depth");
            assert!(!self.vstack.contains(&x), "a variable bound by two open binders");
            let Val::Neu { head: Head::FVar(i), .. } = self.val(x) else { unreachable!() };
            assert_eq!(self.fv_ty[i as usize], _ty, "variable's type");
            self.vstack.push(x);
        }
        self.vdepth += 1;
    }
    fn pick_var(&mut self, ty: V) -> R<V> {
        // slots by the type value; with SK_VARS_BY_TERM=1 (experiment) by
        // the type as a term (Pestka's CountedVariables keys), found by a
        // structural hash and confirmed by structural equality: Init +4.4%,
        // std +8% (the hashing costs more than the sharing it finds)
        let h = if false {
            let mut fuel = 4096u32;
            self.shash(ty, &mut fuel)
        } else {
            ty as u64
        };
        let mut k = 0u32;
        loop {
            let key = h.wrapping_add((k as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            match self.var_slots.get(&key) {
                Some(&x) => {
                    let Val::Neu { head: Head::FVar(i), .. } = self.val(x) else { unreachable!() };
                    let same = {
                        let t0 = self.fv_ty[i as usize];
                        t0 == ty || (false && {
                            let mut fuel = 4096u32;
                            self.same_val(t0, ty, &mut fuel)
                        })
                    };
                    if same && !self.fv_busy[i as usize] {
                        self.fv_busy[i as usize] = true;
                        return Ok(x);
                    }
                    k += 1;
                }
                None => {
                    let x = self.fresh(ty)?;
                    self.var_slots.insert(key, x);
                    self.ulog(Undo::VarSlot(key));
                    self.set_busy(x, true);
                    return Ok(x);
                }
            }
        }
    }

    /// A hash of the term a value stands for, equal for values that
    /// `same_val` finds equal through terms, environments and spines (a
    /// variable's entry hashed where it stands, a constant term as the
    /// constant's neutral value). Out of fuel: the value's own id.
    fn shash(&mut self, v: V, fuel: &mut u32) -> u64 {
        if let Some(&h) = self.shash_memo.get(&v) {
            return h;
        }
        let h = match self.val(v) {
            Val::Thunk { term, env, ls } => self.shash_term(term, env, ls, 0, fuel),
            Val::Clo { term, env, ls } => self.shash_term(term, env, ls, 0, fuel),
            Val::CloI { term, env, ls } => hmix(self.shash_term(term, env, ls, 0, fuel), 0x1F),
            Val::Neu { head, spine } => {
                let mut h = match head {
                    Head::Const(r, l) => hmix(hmix(3, self.canon_of_row(r) as u64), l as u64),
                    Head::FVar(i) => hmix(5, i as u64),
                    Head::Stuck(x) => hmix(7, self.shash(x, fuel)),
                };
                for e in self.spine(spine) {
                    h = if e & PROJ_BIT != 0 {
                        hmix(hmix(h, 11), self.projs[(e & !PROJ_BIT) as usize].1 as u64)
                    } else {
                        hmix(hmix(h, 13), self.shash(e, fuel))
                    };
                }
                h
            }
            Val::Sort(l) => hmix(17, l as u64),
            Val::Lit(i) => match self.lit(i) {
                LitVal::Nat(n) => hmix(19, n.to_u64().unwrap_or(u64::MAX)),
                LitVal::Str(st) => hmix(23, st.len() as u64),
            },
        };
        self.shash_memo.insert(v, h);
        self.ulog(Undo::Shash(v));
        h
    }

    #[allow(clippy::too_many_arguments)]
    fn shash_term(&mut self, t: u32, env: u32, ls: u32, depth: u32, fuel: &mut u32) -> u64 {
        if *fuel == 0 {
            return hmix(0xDEAD, ((t as u64) << 32) ^ env as u64 ^ ((ls as u64) << 17));
        }
        *fuel -= 1;
        match self.tk(t) {
            BVAR => {
                let i = self.tp(t);
                if i < depth {
                    hmix(29, i as u64)
                } else {
                    match self.env_get(env, i - depth) {
                        Ok(x) => self.shash(x, fuel),
                        Err(_) => hmix(31, i as u64),
                    }
                }
            }
            SORT => hmix(17, self.lsub(self.tp(t), ls) as u64),
            CONST => {
                let c = self.env.canon(self.ta(t));
                let l = self.const_ll(t, ls);
                hmix(hmix(3, c as u64), l as u64)
            }
            APP => {
                let f = self.shash_term(self.ta(t), env, ls, depth, fuel);
                let a = self.shash_term(self.tb(t), env, ls, depth, fuel);
                hmix(hmix(f, 13), a)
            }
            NAT | STR => match self.lit(self.tp(t)) {
                LitVal::Nat(n) => hmix(19, n.to_u64().unwrap_or(u64::MAX)),
                LitVal::Str(st) => hmix(23, st.len() as u64),
            },
            PROJ => {
                let x = self.shash_term(self.ta(t), env, ls, depth, fuel);
                hmix(hmix(x, 11), self.tb(t) as u64)
            }
            LET => {
                let a = self.shash_term(self.ta(t), env, ls, depth, fuel);
                let b = self.shash_term(self.tb(t), env, ls, depth, fuel);
                let c = self.shash_term(self.let_body(t), env, ls, depth + 1, fuel);
                hmix(hmix(hmix(37, a), b), c)
            }
            k => {
                let a = self.shash_term(self.ta(t), env, ls, depth, fuel);
                let b = self.shash_term(self.tb(t), env, ls, depth + 1, fuel);
                hmix(hmix(hmix(41, is_lam(k) as u64), a), b)
            }
        }
    }
    /// Milestone 20: back to `d` open binders (after a scope, or after a
    /// probe whose budget ended inside binders).
    fn vdepth_to(&mut self, d: u32) {
        debug_assert!(d <= self.vdepth);
        self.vdepth = d;
        #[cfg(debug_assertions)]
        self.vstack.truncate(d as usize);
    }
    /// Closes the scope of a binder that opened `x` when `d0` binders were
    /// open: `x` is out of scope again, and so is whatever an error left
    /// open inside the scope (back to `d0` open binders).
    fn close_var(&mut self, x: V, d0: u32) {
        #[cfg(debug_assertions)]
        assert_eq!(self.vstack.get(d0 as usize), Some(&x), "binder closed at its depth");
        self.set_busy(x, false);
        self.vdepth_to(d0);
    }

    fn set_busy(&mut self, x: V, b: bool) {
        if let Val::Neu { head: Head::FVar(i), .. } = self.val(x) {
            self.fv_busy[i as usize] = b;
        }
    }
    /// The variable the lambda was checked under, when `v` is that
    /// lambda's type (an `infer` closure), the variable has type `dom` and
    /// is not in scope. It is marked in scope; the caller releases it.
    fn reuse_var(&mut self, v: V, dom: V) -> Option<V> {
        if let Val::CloI { term, env, ls } = self.val(v) {
            if let Some(&x) = self.lam_var.get(&(term, env, ls)) {
                if let Val::Neu { head: Head::FVar(i), .. } = self.val(x) {
                    if !self.fv_busy[i as usize] && self.fv_ty[i as usize] == dom {
                        self.fv_busy[i as usize] = true;
                        self.bind_open(x, dom);
                        return Some(x);
                    }
                }
            }
        }
        None
    }

    pub fn mk_const(&mut self, row: u32, llr: u32) -> R<V> {
        self.intern(Val::Neu { head: Head::Const(row, llr), spine: EMPTY })
    }
    pub fn mk_app(&mut self, f: V, args: &[V]) -> R<V> {
        let mut f = f;
        for (i, &a) in args.iter().enumerate() {
            let fv = self.force(f)?;
            if let Val::Neu { head, spine } = self.val(fv) {
                return self.neu(head, spine, &args[i..]);
            }
            f = self.apply(fv, a)?;
        }
        Ok(f)
    }
    pub fn mk_nat(&mut self, n: BigUint) -> R<V> {
        let small = n.to_u64();
        if let Some(k) = small {
            if let Some(&v) = self.nat_map.get(&k) {
                return Ok(v);
            }
        }
        let i = self.env.lits.len() as u32 + self.wlits.len() as u32;
        let mut bk = 0;
        if small.is_none() {
            // milestone 37: one value per content, found by a hash of the
            // length and a few digits (both ends and the middle) and
            // confirmed by comparing the contents; numbers that differ only
            // elsewhere share a slot (the later one takes it: less sharing,
            // never a wrong value)
            bk = lit_key(&n);
            if let Some(&v) = self.big_map.get(&bk) {
                if self.nat_ref(v) == Some(&n) {
                    return Ok(v);
                }
            }
            // milestone 43: a literal whose memo a rollback dropped is made
            // again: the work that made it was done again
            if !self.lit_dropped.is_empty() && self.lit_dropped.contains(&bk) {
                if self.lit_redo.len() >= region::LIT_KEYS_CAP {
                    self.lit_redo.clear();
                }
                self.lit_redo.insert(bk);
            }
            self.wlit_bytes += (n.bits() / 8) as usize;
        }
        self.wlits.push(LitVal::Nat(n));
        let v = self.intern(Val::Lit(i))?;
        if let Some(k) = small {
            self.nat_map.insert(k, v);
            self.ulog(Undo::Nat(k));
        } else if self.big_share {
            self.big_map.insert(bk, v);
            self.ulog(Undo::BigNat(bk));
        }
        Ok(v)
    }

    /// A literal of the file as a value; small Nats are shared by value.
    fn lit_value(&mut self, i: u32) -> R<V> {
        if let LitVal::Nat(n) = self.lit(i) {
            if let Some(k) = n.to_u64() {
                if let Some(&v) = self.nat_map.get(&k) {
                    return Ok(v);
                }
                let v = self.intern(Val::Lit(i))?;
                self.nat_map.insert(k, v);
                self.ulog(Undo::Nat(k));
                return Ok(v);
            }
        }
        self.intern(Val::Lit(i))
    }

    #[inline(always)]
    pub fn row_of(&self, name: u32) -> u32 {
        self.rows.get(name as usize).copied().unwrap_or(NONE)
    }
    #[inline(always)]
    pub fn visible(&self, row: u32) -> bool {
        let c = &self.consts[row as usize];
        c.decl < self.cur_decl || (c.decl == self.cur_decl && c.group < self.self_vis)
    }

    /// Evaluates term `t` in environment `env` under level substitution `ls`.
    #[inline(always)]
    pub fn eval(&mut self, t: u32, env: u32, ls: u32) -> R<V> {
        let n = self.node(t);
        if n.kind == BVAR {
            return self.env_get(env, n.p);
        }
        self.eval_loop(t, env, ls)
    }
    #[inline(never)]
    fn eval_loop(&mut self, t: u32, env: u32, ls: u32) -> R<V> {
        let (mut t, mut env, mut ls) = (t, env, ls);
        // tail positions (let bodies, the last beta step) loop instead of recursing
        loop {
            self.tick()?;
            #[cfg(feature = "cnt")]
            { self.stats.evals += 1; }
            match self.tk(t) {
                LET => {
                    let lb = self.let_body(t);
                    env = self.push_arg(self.tb(t), env, ls, env, lb)?;
                    t = lb;
                }
                APP => {
                    // the arguments on a shared stack (no allocation per node)
                    let base = self.argstack.len();
                    let mut f = t;
                    loop {
                        let n = self.node(f);
                        if n.kind != APP {
                            break;
                        }
                        self.argstack.push(n.b);
                        f = n.a;
                    }
                    // milestone 23: arguments last first on the stack,
                    // read from the end (no reversal)
                    let n = self.argstack.len() - base;
                    let top = base + n - 1;
                    // the head is no application: eval is eval_node unless it is a let
                    let mut fv = if self.tk(f) == LET { self.eval(f, env, ls)? } else { self.eval_node(f, env, ls)? };
                    let mut i = 0;
                    let mut tail = None;
                    while i < n {
                        fv = self.force(fv)?;
                        match self.val(fv) {
                            Val::Clo { term, env: cenv, ls: cls } if is_lam(self.tk(term)) => {
                                // the lambdas under it walked as (term, env)
                                // pairs, not made values (see `beta`)
                                let (mut term, mut cenv) = (term, cenv);
                                loop {
                                    let body = self.tb(term);
                                    let e2 = self.push_arg(self.argstack[top - i], env, ls, cenv, body)?;
                                    i += 1;
                                    if i == n {
                                        tail = Some((body, e2, cls));
                                        break;
                                    }
                                    if is_lam(self.tk(body)) {
                                        term = body;
                                        cenv = if self.trng(body) == 0 { EMPTY } else { e2 };
                                        continue;
                                    }
                                    fv = self.eval(body, e2, cls)?;
                                    break;
                                }
                                if tail.is_some() {
                                    break;
                                }
                            }
                            Val::Neu { head, spine } => {
                                // the rest of the arguments at once: one value
                                let mut xs = ArgVec::new();
                                for j in i..n {
                                    xs.push(self.thunk(self.argstack[top - j], env, ls)?);
                                }
                                self.argstack.truncate(base);
                                return self.neu(head, spine, &xs);
                            }
                            _ => {
                                let av = self.thunk(self.argstack[top - i], env, ls)?;
                                fv = self.apply(fv, av)?;
                                i += 1;
                            }
                        }
                    }
                    self.argstack.truncate(base);
                    match tail {
                        Some((b, e2, cls)) => {
                            t = b;
                            env = e2;
                            ls = cls;
                        }
                        None => return Ok(fv),
                    }
                }
                BVAR => return self.env_get(env, self.tp(t)),
                _ => return self.eval_node(t, env, ls),
            }
        }
    }

    fn eval_node(&mut self, t: u32, env: u32, ls: u32) -> R<V> {
        let nd = self.node(t);
        let k = nd.kind;
        match k {
            BVAR => self.env_get(env, nd.p),
            SORT => {
                let l = self.lsub(nd.p, ls);
                self.intern(Val::Sort(l))
            }
            CONST => {
                let row = self.row_of(nd.a);
                if row == NONE || !self.visible(row) {
                    return decline(format!(
                        "reduction reached constant {} that is not declared before this declaration",
                        self.env.name_str(self.ta(t))
                    ));
                }
                let llr = self.const_ll(t, ls);
                self.intern(Val::Neu { head: Head::Const(row, llr), spine: EMPTY })
            }
            APP => {
                let mut args = Vec::new();
                let mut f = t;
                loop {
                    let n = self.node(f);
                    if n.kind != APP {
                        break;
                    }
                    args.push(n.b);
                    f = n.a;
                }
                let mut fv = self.eval(f, env, ls)?;
                for &a in args.iter().rev() {
                    let av = self.thunk(a, env, ls)?;
                    fv = self.apply(fv, av)?;
                }
                Ok(fv)
            }
            LET => {
                let lb = self.let_body(t);
                let e = self.push_arg(self.tb(t), env, ls, env, lb)?;
                self.eval(lb, e, ls)
            }
            NAT | STR => self.lit_value(self.tp(t)),
            PROJ => {
                let s = self.eval(self.ta(t), env, ls)?;
                self.proj_val(s, self.tb(t), self.tp(t))
            }
            _ => {
                // LAM / PI
                let env = self.prune(t, env);
                self.intern(Val::Clo { term: t, env, ls })
            }
        }
    }

    /// A lazy value for term `t`.
    /// Milestone 15: a variable is read inline at every call site.
    #[inline(always)]
    pub fn thunk(&mut self, t: u32, env: u32, ls: u32) -> R<V> {
        let n = self.node(t);
        let k = n.kind;
        if k == BVAR {
            return self.env_get(env, n.p);
        }
        if k == APP && self.p1_active {
            // the canonical-application memo probed inline (see canon_app)
            let e2 = if n.rng == 0 { EMPTY } else { env };
            let h = hmix(hmix(t as u64, e2 as u64), ls as u64);
            let i = (h >> 20) as usize & ((1 << CDM_BITS) - 1);
            let e = self.cdm[i];
            if e[0] == t && e[1] == e2 && e[2] == ls && e[3] == self.cgen {
                return Ok(e[4]);
            }
            // milestone 23: canon_app does not probe the slot again
            return self.thunk_nv(t, env, ls, i);
        }
        self.thunk_nv(t, env, ls, usize::MAX)
    }
    /// `cdm_slot`: the canonical-application slot `thunk` probed and missed
    /// (usize::MAX: not probed).
    #[inline(never)]
    fn thunk_nv(&mut self, t: u32, env: u32, ls: u32, cdm_slot: usize) -> R<V> {
        let nd = self.node(t);
        match nd.kind {
            // leaves and binders: eval is eval_node (no loop, no recursion)
            BVAR => self.env_get(env, nd.p),
            SORT | CONST | NAT | STR => self.eval_node(t, env, ls),
            k if is_lam(k) || is_pi(k) => self.eval_node(t, env, ls),
            _ => {
                if self.p1_active && nd.kind == APP {
                    if let Some(v) = self.canon_app(t, env, ls, cdm_slot)? {
                        return Ok(v);
                    }
                } else if self.p1_active && self.tk(t) == APP {
                    if self.p1_nest == 0 {
                        self.p1_left = 16;
                    }
                    self.p1_nest += 1;
                    let r = self.thunk_canon(t, env, ls);
                    self.p1_nest -= 1;
                    if let Some(v) = r? {
                        return Ok(v);
                    }
                }
                let env = self.prune(t, env);
                #[cfg(feature = "cnt")]
                {
                    let mut f = t;
                    while self.tk(f) == APP { f = self.ta(f); }
                    let hk = self.tk(f) as usize;
                    let extra = if self.tk(f) == BVAR {
                        match self.env_get(env, self.tp(f)).map(|x| self.val(x)) {
                            Ok(Val::Thunk { .. }) => 1, Ok(Val::Clo { .. } | Val::CloI { .. }) => 2, Ok(Val::Neu { .. }) => 3, _ => 4,
                        }
                    } else { 0 };
                    let i = (self.tk(t) as usize) * 64 + hk * 5 + extra;
                    THUNK_KINDS[i.min(1023)].fetch_add(1, Ordering::Relaxed);
                }
                self.intern(Val::Thunk { term: t, env, ls })
            }
        }
    }

    /// Milestone 11: an application whose head is a visible constant or a
    /// variable bound to a neutral value is made the neutral value it
    /// evaluates to (no reduction happens: eval of such a term is exactly
    /// this), its arguments made in turn the same way, memoized by (term,
    /// environment, level substitution) for the session. Equal terms reached
    /// through different bodies or environments become one value, as in a
    /// call-by-value kernel. Any doubt (a constant not visible, a loose
    /// variable, a head that is not neutral) leaves the lazy thunk.
    fn canon_app(&mut self, t: u32, env: u32, ls: u32, cdm_slot: usize) -> R<Option<V>> {
        let env = if self.trng(t) == 0 { EMPTY } else { env };
        let key = (t, env, ls);
        #[cfg(feature = "cnt")]
        {
            THUNK_KINDS[1000].fetch_add(1, Ordering::Relaxed);
            if env == EMPTY { THUNK_KINDS[1001].fetch_add(1, Ordering::Relaxed); }
            if env == EMPTY && ls == 0 { THUNK_KINDS[1002].fetch_add(1, Ordering::Relaxed); }
            if t >= self.mlen { THUNK_KINDS[1003].fetch_add(1, Ordering::Relaxed); }
        }
        let slot = if cdm_slot != usize::MAX {
            // probed by `thunk` with this key (prune bit 4 off there), a miss
            cdm_slot
        } else {
            let h = hmix(hmix(t as u64, env as u64), ls as u64);
            let i = (h >> 20) as usize & ((1 << CDM_BITS) - 1);
            cn!(P_CDM);
            let e = self.cdm[i];
            if e[0] == t && e[1] == env && e[2] == ls && e[3] == self.cgen {
                #[cfg(feature = "cnt")]
                THUNK_KINDS[1004].fetch_add(1, Ordering::Relaxed);
                return Ok(Some(e[4]));
            }
            i
        };
        // milestone 45: each argument is made canonical inside this call,
        // one Rust frame chain per level and no tick: CFSG's RG.chars (a
        // 913 K-element list literal) overflowed a 64 MiB stack here (an
        // abort of the whole run). Past half the stack a closed term is
        // left the lazy thunk (as for any doubt; it has no environment to
        // hold); past the limit, as a tick, a decline. (The lazy thunk for
        // open terms too turned the deep vector lets_bad, 300 K nested
        // lets, from a decline into 7 GB of thunks over their
        // environments.)
        {
            let x = 0u8;
            let sp = std::hint::black_box(&x) as *const u8 as usize;
            let used = self.stack_base.saturating_sub(sp);
            if used > self.stack_limit / 2 {
                if env == EMPTY {
                    return Ok(None);
                }
                if used > self.stack_limit {
                    return decline("recursion too deep (stack limit)");
                }
            }
        }
        let base = self.argstack.len();
        let mut f = t;
        loop {
            let n = self.node(f);
            if n.kind != APP {
                break;
            }
            self.argstack.push(n.b);
            f = n.a;
        }
        let (head, sp0) = match self.tk(f) {
            CONST => {
                let row = self.row_of(self.ta(f));
                if row == NONE || !self.visible(row) {
                    self.argstack.truncate(base);
                    return Ok(None);
                }
                (Head::Const(row, self.const_ll(f, ls)), EMPTY)
            }
            BVAR => match self.env_get(env, self.tp(f)) {
                Ok(x) => match self.val(x) {
                    Val::Neu { head, spine } => (head, spine),
                    _ => {
                        self.argstack.truncate(base);
                        return Ok(None);
                    }
                },
                Err(_) => {
                    self.argstack.truncate(base);
                    return Ok(None);
                }
            },
            _ => {
                self.argstack.truncate(base);
                return Ok(None);
            }
        };
        let n = self.argstack.len() - base;
        cn!(976);
        for _ in 0..n { cn!(977); }
        let mut xs = smallvec::SmallVec::<[V; 16]>::new();
        for j in (0..n).rev() {
            let a = self.argstack[base + j];
            let na = self.node(a);
            let av = match na.kind {
                BVAR => self.env_get(env, na.p).ok(),
                CONST => {
                    let r = self.row_of(na.a);
                    if r == NONE || !self.visible(r) {
                        None
                    } else {
                        // what eval makes of it (eval_node's CONST case)
                        let llr = self.const_ll(a, ls);
                        Some(self.intern(Val::Neu { head: Head::Const(r, llr), spine: EMPTY })?)
                    }
                }
                _ => match self.thunk(a, env, ls) {
                    Ok(x) => Some(x),
                    Err(e) => {
                        self.argstack.truncate(base);
                        return Err(e);
                    }
                },
            };
            let Some(av) = av else {
                self.argstack.truncate(base);
                return Ok(None);
            };
            xs.push(av);
        }
        self.argstack.truncate(base);
        let v = self.neu(head, sp0, &xs)?;
        if true {
            self.cdm[slot] = [t, env, ls, self.cgen, v];
        } else {
            self.canon_memo.insert(key, v);
            self.ulog(Undo::Canon(key));
        }
        Ok(Some(v))
    }

    /// Proposal 1: an application of a constant made the neutral value it
    /// evaluates to (no reduction: eval of such a term is exactly this), its
    /// arguments thunked in turn, so the same substituted term under two
    /// environments is one value. Declines to (the lazy thunk is made) when
    /// a constant is unknown or not visible yet, or a variable is loose, so
    /// no error happens earlier than it would.
    fn thunk_canon(&mut self, t: u32, env: u32, ls: u32) -> R<Option<V>> {
        if self.p1_left == 0 || self.trng(t) == 0 {
            return Ok(None);
        }
        let mut f = t;
        while self.tk(f) == APP {
            let a = self.tb(f);
            match self.tk(a) {
                BVAR => {
                    if self.env_get(env, self.tp(a)).is_err() {
                        return Ok(None);
                    }
                }
                CONST => {
                    let r = self.row_of(self.ta(a));
                    if r == NONE || !self.visible(r) {
                        return Ok(None);
                    }
                }
                SORT | NAT | STR => {}
                _ => {}
            }
            f = self.ta(f);
        }
        let mkey = (t, if self.trng(t) == 0 { EMPTY } else { env }, ls);
        if let Some(&v) = self.canon_memo.get(&mkey) {
            return Ok(Some(v));
        }
        let (head, sp0) = match self.tk(f) {
            CONST => {
                let row = self.row_of(self.ta(f));
                if row == NONE || !self.visible(row) {
                    return Ok(None);
                }
                (Head::Const(row, self.const_ll(f, ls)), EMPTY)
            }
            BVAR => {
                let Ok(x) = self.env_get(env, self.tp(f)) else { return Ok(None) };
                match self.val(x) {
                    Val::Neu { head, spine } => (head, spine),
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        self.p1_left -= 1;
        let base = self.argstack.len();
        let mut g = t;
        while self.tk(g) == APP {
            self.argstack.push(self.tb(g));
            g = self.ta(g);
        }
        let n = self.argstack.len() - base;
        let mut xs = ArgVec::new();
        for j in (0..n).rev() {
            let a = self.argstack[base + j];
            let av = match self.thunk(a, env, ls) {
                Ok(x) => x,
                Err(e) => {
                    self.argstack.truncate(base);
                    return Err(e);
                }
            };
            xs.push(av);
        }
        self.argstack.truncate(base);
        let v = self.neu(head, sp0, &xs)?;
        self.canon_memo.insert(mkey, v);
        self.ulog(Undo::Canon(mkey));
        Ok(Some(v))
    }

    /// Milestone 15: the forced or non-thunk case inlined, evaluation out of line.
    #[inline(always)]
    pub fn force(&mut self, v: V) -> R<V> {
        if let Val::Thunk { .. } = self.val(v) {
            let f = self.memo_at(v).whnf;
            if f != NONE {
                return Ok(f);
            }
            self.force_eval(v)
        } else {
            Ok(v)
        }
    }
    #[inline(never)]
    fn force_eval(&mut self, v: V) -> R<V> {
        if let Val::Thunk { term, env, ls } = self.val(v) {
            let r = self.eval(term, env, ls)?;
            let r = self.force(r)?;
            self.memo_w(v).whnf = r;
            Ok(r)
        } else {
            Ok(v)
        }
    }

    pub fn apply(&mut self, f: V, a: V) -> R<V> {
        let f = self.force(f)?;
        match self.val(f) {
            Val::Clo { term, env, ls } if is_lam(self.tk(term)) => {
                let b = self.tb(term);
                let e = self.push_for(a, env, b);
                self.eval(b, e, ls)
            }
            Val::Neu { head, spine } => self.neu(head, spine, &[a]),
            _ => self.neu(Head::Stuck(f), EMPTY, &[a]),
        }
    }

    /// `term` (in `env`, `ls`) applied to `args`. The lambdas met on the way
    /// are walked as (term, environment) pairs and never made values: only
    /// the result is (Pestka's RuleLambdasAtOnce: one closure per call, not
    /// one per argument).
    pub fn beta(&mut self, term: u32, env: u32, ls: u32, args: &[V]) -> R<V> {
        if args.is_empty() || !is_lam(self.tk(term)) {
            let f = self.eval(term, env, ls)?;
            return self.apply_many(f, args);
        }
        let env = if self.trng(term) == 0 { EMPTY } else { env };
        self.beta_from(term, env, ls, args)
    }
    /// `f` applied to `args`; see `beta`.
    pub fn apply_many(&mut self, f: V, args: &[V]) -> R<V> {
        let mut fv = f;
        let mut i = 0;
        while i < args.len() {
            fv = self.force(fv)?;
            match self.val(fv) {
                Val::Clo { term, env, ls } if is_lam(self.tk(term)) && true => {
                    return self.beta_from(term, env, ls, &args[i..]);
                }
                Val::Neu { head, spine } => {
                    return self.neu(head, spine, &args[i..]);
                }
                _ => {
                    fv = self.apply(fv, args[i])?;
                    i += 1;
                }
            }
        }
        Ok(fv)
    }
    /// The lambda `term` (in `env`, `ls`) applied to the non-empty `args`.
    fn beta_from(&mut self, mut term: u32, mut env: u32, mut ls: u32, args: &[V]) -> R<V> {
        let n = args.len();
        let mut i = 0;
        loop {
            let body = self.tb(term);
            let e2 = self.push_for(args[i], env, body);
            i += 1;
            if i == n {
                return self.eval(body, e2, ls);
            }
            if is_lam(self.tk(body)) {
                term = body;
                env = if self.trng(body) == 0 { EMPTY } else { e2 };
                continue;
            }
            let f = self.eval(body, e2, ls)?;
            let f = self.force(f)?;
            match self.val(f) {
                Val::Clo { term: t2, env: e3, ls: l3 } if is_lam(self.tk(t2)) => {
                    term = t2;
                    env = e3;
                    ls = l3;
                }
                _ => return self.apply_many(f, &args[i..]),
            }
        }
    }

    pub fn proj_val(&mut self, s: V, idx: u32, sname: u32) -> R<V> {
        let s = self.force(s)?;
        let e = match self.proj_map.get(&(sname, idx)) {
            Some(&e) => e,
            None => {
                self.projs.push((sname, idx));
                let e = PROJ_BIT | (self.projs.len() as u32 - 1);
                self.proj_map.insert((sname, idx), e);
                e
            }
        };
        match self.val(s) {
            Val::Neu { head, spine } => self.neu(head, spine, &[e]),
            _ => self.neu(Head::Stuck(s), EMPTY, &[e]),
        }
    }

    /// Re-applies spine elims to a value.
    fn apply_elims(&mut self, mut v: V, elims: &[u32]) -> R<V> {
        let mut k = 0;
        while k < elims.len() {
            let e = elims[k];
            if e & PROJ_BIT != 0 {
                let (sn, i) = self.projs[(e & !PROJ_BIT) as usize];
                v = self.proj_val(v, i, sn)?;
                k += 1;
            } else {
                let mut j = k;
                while j < elims.len() && elims[j] & PROJ_BIT == 0 {
                    j += 1;
                }
                v = self.apply_many(v, &elims[k..j])?;
                k = j;
            }
        }
        Ok(v)
    }

    pub fn is_lam_val(&self, v: V) -> bool {
        matches!(self.val(v), Val::Clo { term, .. } if is_lam(self.tk(term)))
    }
    pub fn is_pi_val(&self, v: V) -> bool {
        match self.val(v) {
            Val::Clo { term, .. } => is_pi(self.tk(term)),
            Val::CloI { term, .. } => is_lam(self.tk(term)),
            _ => false,
        }
    }
    /// Domain of a lambda or Pi value.
    pub fn bind_dom(&mut self, v: V) -> R<V> {
        match self.val(v) {
            Val::Clo { term, env, ls } | Val::CloI { term, env, ls } => self.thunk(self.ta(term), env, ls),
            _ => reject("binder expected"),
        }
    }
    /// Body of a lambda (applied) or codomain of a Pi at `x`.
    pub fn bind_body(&mut self, v: V, x: V) -> R<V> {
        match self.val(v) {
            Val::Clo { term, env, ls } => {
                let b = self.tb(term);
                let e = self.push_for(x, env, b);
                self.eval(b, e, ls)
            }
            Val::CloI { term, env, ls } => {
                let b = self.tb(term);
                if self.lam_any {
                    if let Some(r) = self.lam_type_at(term, env, ls, x)? {
                        return Ok(r);
                    }
                }
                let e = self.push_for(x, env, b);
                self.infer(b, e, ls, false)
            }
            _ => reject("binder expected"),
        }
    }

    /// Milestone 34: the codomain of a lambda's type at argument `a`
    /// without inferring the body again. When the lambda was checked, its
    /// body got type `r` under its variable `y`; if `r` does not mention
    /// `y` (`lam_type_record`), `r` is the body's type at any argument of
    /// the domain (substitution: y : A ⊢ b : r with y not in r gives
    /// b[a/y] : r), as Lean instantiates the inferred Pi. Without it a
    /// ladder of n redexes, each body inferred again at its argument, costs
    /// n² (beta-ladder). release-da infers the body at `a` too and asserts
    /// the types equal.
    fn lam_type_at(&mut self, term: u32, env: u32, ls: u32, a: V) -> R<Option<V>> {
        let i = (hmix(hmix(term as u64, env as u64), ls as u64) >> 20) as usize & LAM_DM_MASK;
        let x = self.lam_dm[i];
        if x[0] != term || x[1] != env || x[2] != ls || x[3] != self.cgen {
            return Ok(None);
        }
        let (r, _y) = (x[4], x[5]);
        #[cfg(debug_assertions)]
        {
            // y was not in scope when the lambda was checked (`open_var`),
            // so the lambda's environment does not mention it (as
            // `reuse_var` relies on): an entry holding y would be
            // substituted too in the fact
            let Val::Neu { head: Head::FVar(yi), .. } = self.val(_y) else { unreachable!() };
            let mut f = u32::MAX;
            assert_eq!(self.mentions_te(term, env, yi, &mut f), Some(false), "lambda type at an argument: the environment mentions the lambda's variable");
            let b = self.tb(term);
            let e2 = self.push_for(a, env, b);
            let w = self.infer(b, e2, ls, false)?;
            assert!(self.defeq(r, w)?, "lambda type at an argument: term {term} in {env}: the recorded type is not the inferred one");
        }
        let _ = a;
        Ok(Some(r))
    }
    /// Milestone 34: lambda `lam` (in pruned environment `ek`, levels
    /// `ls`), checked with variable `y`: its body `b` has type `r`. Kept
    /// for `lam_type_at` when the body reads `y` (else one environment
    /// serves every argument already), `r` has no free variable at all
    /// (so not `y`), and the lambda's environment surely does not mention
    /// `y`: an entry holding `y` would make the fact one about the body
    /// with that entry and the argument equal, not the body at any
    /// argument. `y` was not in scope when the lambda was checked, so by
    /// milestone 20's invariant no entry holds it; this condition is
    /// conservative and costs beta_ladder 86 -> 178 M. (An earlier
    /// release-da check said "could not tell" on cedar and con-leche, read
    /// at first as such an entry; a conclusive walk of every checked
    /// lambda found none on init, std, cedar and con-leche.) Types that mention only
    /// other variables were measured too (a walk per checked lambda, Init
    /// +0.6% instructions): their records were not used enough to pay.
    fn lam_type_record(&mut self, lam: u32, ek: u32, ls: u32, b: u32, r: V, y: V) {
        if lam == NONE || self.trng(b) == 0 || self.used_mask(self.tb(lam)) & 1 == 0 || self.has_fvar(r) {
            return;
        }
        let Val::Neu { head: Head::FVar(yi), .. } = self.val(y) else { return };
        // the entries the lambda reads (its used mask); in a wide context
        // every entry (no used-variable walk there). Each must be closed
        // or a variable other than y; anything else is not walked (a walk
        // of MENTION_FUEL values per entry cost con-leche +3%) and the
        // type is not kept.
        let mut fuel = 0;
        let rng = self.trng(lam);
        if rng <= 63 {
            let mut m = self.used_mask(lam) & ((1u64 << rng) - 1);
            while m != 0 {
                let i = m.trailing_zeros();
                m &= m - 1;
                let Some(x) = self.env_at(ek, i) else { break };
                if self.mentions_fv(x, yi, &mut fuel) != Some(false) {
                    return;
                }
            }
        } else if let Some((st, len)) = self.env_run(ek) {
            for k in st..st + len {
                let x = self.eslot(k);
                if self.mentions_fv(x, yi, &mut fuel) != Some(false) {
                    return;
                }
            }
        }
        let i = (hmix(hmix(lam as u64, ek as u64), ls as u64) >> 20) as usize & LAM_DM_MASK;
        self.lam_dm[i] = [lam, ek, ls, self.cgen, r, y];
        self.lam_any = true;
    }

    /// Does value `v` mention variable `fv` (an `fv_ty` index)? Walks the
    /// entries terms read and spines; None when `fuel` runs out.
    fn mentions_fv(&mut self, v: V, fv: u32, fuel: &mut u32) -> Option<bool> {
        if v == HOLE || !self.has_fvar(v) {
            return Some(false);
        }
        if let Val::Neu { head: Head::FVar(i), spine: EMPTY } = self.val(v) {
            return Some(i == fv);
        }
        if *fuel == 0 {
            return None;
        }
        *fuel -= 1;
        match self.val(v) {
            Val::Sort(_) | Val::Lit(_) => Some(false),
            Val::Thunk { term, env, .. } | Val::Clo { term, env, .. } | Val::CloI { term, env, .. } => self.mentions_te(term, env, fv, fuel),
            Val::Neu { head, spine } => {
                match head {
                    Head::FVar(i) => {
                        if i == fv {
                            return Some(true);
                        }
                    }
                    Head::Const(..) => {}
                    Head::Stuck(x) => {
                        if self.mentions_fv(x, fv, fuel)? {
                            return Some(true);
                        }
                    }
                }
                for i in 0..self.sp.len(spine) {
                    let e = self.sp.args(spine)[i];
                    if e & PROJ_BIT == 0 && self.mentions_fv(e, fv, fuel)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
        }
    }
    /// Does an entry of `env` that `term` reads mention variable `fv`?
    fn mentions_te(&mut self, term: u32, env: u32, fv: u32, fuel: &mut u32) -> Option<bool> {
        for i in 0..self.trng(term) {
            if !self.uses_var(term, i) {
                continue;
            }
            let Some(x) = self.env_at(env, i) else { break };
            if self.mentions_fv(x, fv, fuel)? {
                return Some(true);
            }
        }
        Some(false)
    }

    pub fn const_head(&self, v: V) -> Option<(u32, u32, u32)> {
        match self.val(v) {
            Val::Neu { head: Head::Const(r, l), spine } => Some((r, l, spine)),
            _ => None,
        }
    }
    pub fn canon_of_row(&self, row: u32) -> u32 {
        self.env.canon(self.consts[row as usize].name)
    }

    // -----------------------------------------------------------------------
    // Literals

    /// Milestone 37: a Nat literal (or `Nat.zero`) in place.
    pub fn nat_ref(&self, v: V) -> Option<&BigUint> {
        match self.val(v) {
            Val::Lit(i) => match self.lit(i) {
                LitVal::Nat(n) => Some(n),
                _ => None,
            },
            Val::Neu { head: Head::Const(r, _), spine: EMPTY } if self.canon_of_row(r) == self.env.known.nat_zero => {
                Some(&BIG_ZERO)
            }
            _ => None,
        }
    }
    pub fn nat_of(&mut self, v: V) -> Option<BigUint> {
        match self.val(v) {
            Val::Lit(i) => match self.lit(i) {
                LitVal::Nat(n) => Some(n.clone()),
                _ => None,
            },
            Val::Neu { head: Head::Const(r, _), spine: EMPTY } if self.canon_of_row(r) == self.env.known.nat_zero => {
                Some(BigUint::zero())
            }
            _ => None,
        }
    }
    fn known_visible(&self, canon: u32) -> u32 {
        let r = self.env.known_row(canon);
        if r != NONE && self.visible(r) { r } else { NONE }
    }
    /// A built-in reading (Bool or Nat constructors) is not available yet:
    /// a `false` found now may be `true` once it is, so the declaration
    /// keeps no `false` across declarations from now on.
    #[cold]
    #[inline(never)]
    fn known_missing(&mut self) {
        self.stats.known_miss += 1;
    }
    pub fn mk_bool(&mut self, b: bool) -> R<Option<V>> {
        let r = self.known_visible(if b { self.env.known.bool_true } else { self.env.known.bool_false });
        if r == NONE {
            self.known_missing();
            return Ok(None);
        }
        Ok(Some(self.mk_const(r, LL_EMPTY)?))
    }
    /// Nat literal to constructor form.
    pub fn nat_lit_ctor(&mut self, n: &BigUint) -> R<Option<V>> {
        if n.is_zero() {
            let r = self.known_visible(self.env.known.nat_zero);
            if r == NONE {
                self.known_missing();
                return Ok(None);
            }
            Ok(Some(self.mk_const(r, LL_EMPTY)?))
        } else {
            let r = self.known_visible(self.env.known.nat_succ);
            if r == NONE {
                self.known_missing();
                return Ok(None);
            }
            let f = self.mk_const(r, LL_EMPTY)?;
            let p = self.mk_nat(n - 1u32)?;
            Ok(Some(self.apply(f, p)?))
        }
    }
    /// String literal to `String.ofList [Char.ofNat c, ...]`.
    pub fn str_lit_expand(&mut self, s: &str) -> R<Option<V>> {
        let k = self.env.known;
        let (ol, nil, cons, ch, chn) = (
            self.known_visible(k.string_of_list),
            self.known_visible(k.list_nil),
            self.known_visible(k.list_cons),
            self.known_visible(k.char_),
            self.known_visible(k.char_of_nat),
        );
        if [ol, nil, cons, ch, chn].contains(&NONE) {
            return decline("string literal expansion needs String.ofList, List, Char and Char.ofNat declared before");
        }
        let l0 = self.ll_intern(&[ZERO]);
        let chv = self.mk_const(ch, LL_EMPTY)?;
        let nilc = self.mk_const(nil, l0)?;
        let mut acc = self.apply(nilc, chv)?;
        let chars: Vec<char> = s.chars().collect();
        for c in chars.iter().rev() {
            let consc = self.mk_const(cons, l0)?;
            let x = self.mk_nat(BigUint::from(*c as u32))?;
            let cn = self.mk_const(chn, LL_EMPTY)?;
            let cv = self.apply(cn, x)?;
            acc = self.mk_app(consc, &[chv, cv, acc])?;
        }
        let f = self.mk_const(ol, LL_EMPTY)?;
        Ok(Some(self.apply(f, acc)?))
    }

    /// Does the value (as the term it stands for) contain a free variable?
    #[inline(always)]
    pub fn has_fvar(&mut self, v: V) -> bool {
        let m = self.memo_at(v).fvar();
        if m != 2 {
            return m == 1;
        }
        self.has_fvar_miss(v)
    }
    /// Milestone 42: past half the stack limit. The walks that do not tick
    /// (has_fvar, uses_var) go on with an explicit stack from there.
    #[inline(always)]
    pub(super) fn stack_half(&self) -> bool {
        let x = 0u8;
        let sp = std::hint::black_box(&x) as *const u8 as usize;
        self.stack_base.saturating_sub(sp) > self.stack_limit / 2
    }
    #[inline(never)]
    fn has_fvar_miss(&mut self, v: V) -> bool {
        // milestone 42: a value's entries can nest as deep as a loop ran (a
        // lazy accumulator: each step's closure holds the one before), one
        // Rust frame per level here: past half the stack, an explicit stack
        if self.stack_half() {
            return self.has_fvar_iter(v);
        }
        let r = match self.val(v) {
            Val::Sort(_) | Val::Lit(_) => false,
            Val::Thunk { term, env, .. } | Val::Clo { term, env, .. } | Val::CloI { term, env, .. } => {
                let n = self.trng(term);
                let mut found = false;
                for i in 0..n {
                    // only the entries the term actually uses (Lean asks the
                    // instantiated term)
                    if !self.uses_var(term, i) {
                        continue;
                    }
                    let Some(x) = self.env_at(env, i) else { break };
                    if self.has_fvar(x) {
                        found = true;
                        break;
                    }
                }
                found
            }
            Val::Neu { head, spine } => {
                let h = match head {
                    Head::FVar(_) => true,
                    Head::Const(..) => false,
                    Head::Stuck(x) => self.has_fvar(x),
                };
                h || self.spine_fvar(spine)
            }
        };
        self.memo_mut(v).set_fvar(r);
        r
    }

    /// has_fvar_miss with an explicit stack: the same walk (the same
    /// entries and spine arguments, in the same order, stopping at the
    /// first one found) and the same memos (per value, per spine node).
    #[inline(never)]
    fn has_fvar_iter(&mut self, v: V) -> bool {
        struct Fr {
            v: V,
            // what is left to look at, last first; the first `nspine` are
            // `spine`'s arguments (looked at last)
            kids: Vec<V>,
            nspine: usize,
            spine: u32,
            from_spine: bool,
        }
        // Ok: known at once; Err: a frame to walk
        let open = |s: &mut Self, v: V| -> Result<bool, Fr> {
            let m = s.memo_at(v).fvar();
            if m != 2 {
                return Ok(m == 1);
            }
            let mut kids = Vec::new();
            let (mut spine, mut nspine) = (EMPTY, 0);
            match s.val(v) {
                Val::Sort(_) | Val::Lit(_) => {}
                Val::Thunk { term, env, .. } | Val::Clo { term, env, .. } | Val::CloI { term, env, .. } => {
                    for i in 0..s.trng(term) {
                        if !s.uses_var(term, i) {
                            continue;
                        }
                        let Some(x) = s.env_at(env, i) else { break };
                        kids.push(x);
                    }
                }
                Val::Neu { head, spine: sp } => {
                    match head {
                        Head::FVar(_) => {
                            s.memo_mut(v).set_fvar(true);
                            return Ok(true);
                        }
                        Head::Const(..) => {}
                        Head::Stuck(x) => kids.push(x),
                    }
                    if sp != EMPTY {
                        let f = s.sp.flags(sp);
                        if f & spines::F_FV_KNOWN != 0 {
                            if f & spines::F_FV != 0 && kids.is_empty() {
                                s.memo_mut(v).set_fvar(true);
                                return Ok(true);
                            }
                            if f & spines::F_FV != 0 {
                                // the stuck head first, then the spine's answer
                                kids.push(NONE);
                            }
                        } else {
                            spine = sp;
                            for i in 0..s.sp.len(sp) {
                                let e = s.sp.args(sp)[i];
                                if e & PROJ_BIT == 0 {
                                    kids.push(e);
                                    nspine += 1;
                                }
                            }
                        }
                    }
                }
            }
            if kids.is_empty() {
                s.memo_mut(v).set_fvar(false);
                if spine != EMPTY {
                    s.sp.set_flags(spine, spines::F_FV_KNOWN);
                }
                return Ok(false);
            }
            kids.reverse();
            Err(Fr { v, kids, nspine, spine, from_spine: false })
        };
        let mut st: Vec<Fr> = match open(self, v) {
            Ok(b) => return b,
            Err(f) => vec![f],
        };
        let mut done: Option<bool> = None;
        loop {
            let top = st.last_mut().unwrap();
            let r = match done.take() {
                Some(true) => Some(true),
                _ => match top.kids.pop() {
                    None => Some(false),
                    // a spine already known to have one (after the stuck head)
                    Some(NONE) => Some(true),
                    Some(k) => {
                        top.from_spine = top.kids.len() < top.nspine;
                        match open(self, k) {
                            Ok(b) => {
                                done = Some(b);
                                None
                            }
                            Err(f) => {
                                st.push(f);
                                None
                            }
                        }
                    }
                },
            };
            let Some(r) = r else { continue };
            let f = st.pop().unwrap();
            self.memo_mut(f.v).set_fvar(r);
            if f.spine != EMPTY && (!r || f.from_spine) {
                self.sp.set_flags(f.spine, spines::F_FV_KNOWN | if r { spines::F_FV } else { 0 });
            }
            if st.is_empty() {
                return r;
            }
            done = Some(r);
        }
    }

    /// Does an argument of spine `s` have a free variable? Remembered per
    /// spine node (a spine is its last elimination and the spine before it).
    fn spine_fvar(&mut self, s: u32) -> bool {
        if s == EMPTY {
            return false;
        }
        let f = self.sp.flags(s);
        if f & spines::F_FV_KNOWN != 0 {
            return f & spines::F_FV != 0;
        }
        let mut r = false;
        for i in 0..self.sp.len(s) {
            let e = self.sp.args(s)[i];
            if e & PROJ_BIT == 0 && self.has_fvar(e) {
                r = true;
                break;
            }
        }
        self.sp.set_flags(s, spines::F_FV_KNOWN | if r { spines::F_FV } else { 0 });
        r
    }

    fn reduce_nat(&mut self, v: V) -> R<Option<V>> {
        let Some((row, _, spine)) = self.const_head(v) else { return Ok(None) };
        if spine == EMPTY || self.env.nat_op[row as usize] == 0 {
            return Ok(None);
        }
        // Lean asks for no free variables here. whnf does not (Pestka's
        // natGo): an argument that comes to a literal is a literal, wherever
        // a free variable sits in a part the value does not use, and the
        // operation on literals is the kernel's own extension. Lazy delta
        // keeps Lean's guard (it checks before calling).
        let c = self.canon_of_row(row);
        let k = self.env.known;
        let Some(args) = self.app_args(spine) else { return Ok(None) };
        if args.len() == 1 {
            if c == k.nat_succ || c == k.nat_log2 {
                let a = self.whnf(args[0])?;
                let Some(n) = self.nat_of(a) else { return Ok(None) };
                let r = if c == k.nat_succ {
                    match nat_sized(n + 1u32) {
                        Ok(r) => r,
                        Err(why) => return reject(why),
                    }
                } else if n.is_zero() {
                    BigUint::zero()
                } else {
                    BigUint::from(n.bits() - 1)
                };
                return Ok(Some(self.mk_nat(r)?));
            }
            return Ok(None);
        }
        if args.len() != 2 {
            return Ok(None);
        }
        let Some(op) = k.nat_ops.iter().position(|&x| x == c && x != NONE) else { return Ok(None) };
        let a = self.whnf(args[0])?;
        if self.nat_ref(a).is_none() {
            return Ok(None);
        }
        let b = self.whnf(args[1])?;
        // milestone 37: the operands are read in place (they were cloned:
        // two copies of up to tens of KB per operation on CFSG's bit-sliced
        // tables)
        let (Some(x), Some(y)) = (self.nat_ref(a), self.nat_ref(b)) else { return Ok(None) };
        let r = match ground::nat_fold(op, x, y) {
            Ok(ground::NatR::N(r)) => r,
            Ok(ground::NatR::B(e)) => return self.mk_bool(e),
            Err(why) => return reject(why),
        };
        Ok(Some(self.mk_nat(r)?))
    }

    // -----------------------------------------------------------------------
    // Weak head normal form

    /// Projections, recursors and quotients (no delta).
    pub fn whnf_core(&mut self, v: V) -> R<V> {
        self.whnf_core_c(v, false)
    }

    /// `cheap`: Lean's `cheap_proj`, a projection's structure is reduced by
    /// `whnf_core` only (used first by definitional equality).
    #[inline(always)]
    pub fn whnf_core_c(&mut self, v: V, cheap: bool) -> R<V> {
        let v0 = self.force(v)?;
        let m = self.memo_at(v0).core_get(cheap);
        if m != NONE {
            return Ok(m);
        }
        self.whnf_core_miss(v0, cheap)
    }
    #[inline(never)]
    fn whnf_core_miss(&mut self, v0: V, cheap: bool) -> R<V> {
        let memo = |w: &Self, x: V| w.memo_at(x).core_get(cheap);
        let m = memo(self, v0);
        if m != NONE {
            return Ok(m);
        }
        // consecutive head reductions loop instead of recursing
        let mut cur = v0;
        loop {
            let (r, again) = self.whnf_core_step(cur, cheap)?;
            let r = self.force(r)?;
            if !again {
                cur = r;
                break;
            }
            let m = memo(self, r);
            if m != NONE {
                cur = m;
                break;
            }
            cur = r;
        }
        self.memo_w(v0).core_set(cheap, cur);
        Ok(cur)
    }

    /// Milestone 38: `whnf_core` for whnf's own loop, which may pause it:
    /// Err(current term) when a checkpoint of the loop's region `g` is due,
    /// or (no region) when the session wants regions. Recursors over a
    /// literal (`go n b`, Nat.rec all the way) reduce without a delta step,
    /// so a loop of a million steps never came back to whnf's loop, where
    /// checkpoints and late regions are. Paused, `t`'s memo is not set (it
    /// may not outlive the checkpoint).
    #[inline(always)]
    fn whnf_core_ck(&mut self, t: V, g: Option<region::Reg>) -> R<Result<V, V>> {
        let v0 = self.force(t)?;
        let m = self.memo_at(v0).core_get(false);
        if m != NONE {
            return Ok(Ok(m));
        }
        self.whnf_core_ck_miss(v0, g)
    }
    #[inline(never)]
    fn whnf_core_ck_miss(&mut self, v0: V, g: Option<region::Reg>) -> R<Result<V, V>> {
        let mut cur = v0;
        loop {
            let (r, again) = self.whnf_core_step(cur, false)?;
            let r = self.force(r)?;
            if !again {
                cur = r;
                break;
            }
            let m = self.memo_at(r).core_get(false);
            if m != NONE {
                cur = m;
                break;
            }
            cur = r;
            let pause = match &g {
                Some(g) => self.reg_ckpt && self.reg_due(g),
                None => self.reg_late2 && self.reg_wanted(),
            };
            if pause {
                return Ok(Err(cur));
            }
        }
        self.memo_w(v0).core_set(false, cur);
        Ok(Ok(cur))
    }

    /// One step: `(value, true)` when it reduced and may reduce further.
    fn whnf_core_step(&mut self, v: V, cheap: bool) -> R<(V, bool)> {
        self.tick()?;
        let Val::Neu { head, spine } = self.val(v) else { return Ok((v, false)) };
        if spine == EMPTY {
            return Ok((v, false));
        }
        if !self.spine_has_proj(spine) {
            // without projections only recursors and quotients reduce here
            match head {
                Head::Const(row, _) => match self.consts[row as usize].kind {
                    CKind::Rec { .. } | CKind::Quot { kind: 2 | 3 } => {}
                    _ => return Ok((v, false)),
                },
                _ => return Ok((v, false)),
            }
        }
        let elims = self.spine_in(spine);
        if let Some(pi) = elims.iter().position(|&e| e & PROJ_BIT != 0) {
            let base = match head {
                Head::Stuck(x) if pi == 0 => x,
                _ => self.neu_prefix(head, spine, pi)?,
            };
            let b = if cheap { self.whnf_core_c(base, true)? } else { self.whnf(base)? };
            let (sname, idx) = self.projs[(elims[pi] & !PROJ_BIT) as usize];
            let _ = sname;
            if let Some(f) = self.ctor_field(b, idx)? {
                let r = self.apply_elims(f, &elims[pi + 1..])?;
                return Ok((r, true));
            }
            // milestone 49: a structure that comes to no constructor leaves
            // the projection as it was (Lean's reduce_proj gives none,
            // Pestka keeps the term); the projection over the reduced
            // structure turned `(forIn l s f).1` into the loop run to its
            // first stuck step, compared step by step (CFSG's
            // KernelRouteP.wordG_treeWord_of)
            return Ok((v, false));
        }
        if let Head::Const(row, llr) = head {
            match &self.consts[row as usize].kind {
                CKind::Rec { .. } => {
                    if let Some(r) = self.iota(row, llr, &elims)? {
                        if STATS { self.stats.iota += 1; }
                        return Ok((r, true));
                    }
                }
                CKind::Quot { kind: qk @ (2 | 3) } => {
                    let qk = *qk;
                    if let Some(r) = self.quot_reduce(qk, &elims)? {
                        return Ok((r, true));
                    }
                }
                _ => {}
            }
        }
        Ok((v, false))
    }

    /// Field `idx` of a constructor application.
    fn ctor_field(&mut self, b: V, idx: u32) -> R<Option<V>> {
        let b = if let Val::Lit(i) = self.val(b) {
            match self.lit(i).clone() {
                LitVal::Str(s) => match self.str_lit_expand(&s)? {
                    Some(x) => self.whnf(x)?,
                    None => return Ok(None),
                },
                _ => return Ok(None),
            }
        } else {
            b
        };
        let Some((row, _, spine)) = self.const_head(b) else { return Ok(None) };
        let CKind::Ctor { nparams, .. } = self.consts[row as usize].kind else { return Ok(None) };
        let Some(args) = self.app_args(spine) else { return Ok(None) };
        let i = nparams as usize + idx as usize;
        Ok(args.get(i).copied())
    }

    fn quot_reduce(&mut self, qk: u8, elims: &[u32]) -> R<Option<V>> {
        let (mk_pos, arg_pos) = if qk == 2 { (5usize, 3usize) } else { (4, 3) };
        if elims.len() <= mk_pos || elims[..=mk_pos].iter().any(|&e| e & PROJ_BIT != 0) {
            return Ok(None);
        }
        let mk = self.whnf(elims[mk_pos])?;
        let Some((row, _, spine)) = self.const_head(mk) else { return Ok(None) };
        if !matches!(self.consts[row as usize].kind, CKind::Quot { kind: 1 }) {
            return Ok(None);
        }
        let Some(margs) = self.app_args(spine) else { return Ok(None) };
        if margs.len() != 3 {
            return Ok(None);
        }
        let r = self.apply(elims[arg_pos], margs[2])?;
        Ok(Some(self.apply_elims(r, &elims[mk_pos + 1..])?))
    }

    fn iota(&mut self, row: u32, llr: u32, elims: &[u32]) -> R<Option<V>> {
        let env = self.env;
        let CKind::Rec { nparams, nindices, nmotives, nminors, .. } = &env.consts[row as usize].kind else {
            return Ok(None);
        };
        let major_idx = *nparams as usize + *nmotives as usize + *nminors as usize + *nindices as usize;
        if elims.len() <= major_idx {
            return Ok(None);
        }
        if self.ll_get(llr).len() != env.consts[row as usize].lparams.len() {
            return Ok(None);
        }
        let Some((ri, fields)) = self.rec_rule(row, elims[major_idx])? else { return Ok(None) };
        let CKind::Rec { rules, .. } = &env.consts[row as usize].kind else { unreachable!() };
        let rhs = rules[ri].2;
        let ls = self.mk_ls(row, llr);
        let pre = *nparams as usize + *nmotives as usize + *nminors as usize;
        let mut args: Vec<V> = Vec::with_capacity(pre + fields.len() + elims.len() - major_idx);
        args.extend_from_slice(&elims[..pre]);
        args.extend_from_slice(&fields);
        // the arguments after the major premise too, up to a projection
        let mut k = major_idx + 1;
        while k < elims.len() && elims[k] & PROJ_BIT == 0 {
            args.push(elims[k]);
            k += 1;
        }
        let r = self.beta(rhs, EMPTY, ls, &args)?;
        Ok(Some(self.apply_elims(r, &elims[k..])?))
    }

    /// The rule recursor `row` takes on major premise `major` and the
    /// constructor's fields: the major premise brought to a constructor as
    /// the recursor reduces it (K, structure eta, literals).
    ///
    /// Structure eta comes before the major is reduced (lean4#15351, with
    /// lean4#15371's condition): a major with no weak head normal form, such
    /// as a proof built from Coquand's paradox, then never stops the
    /// recursor. Literals keep their own expansion (String is a structure).
    fn rec_rule(&mut self, row: u32, major: V) -> R<Option<(usize, ArgVec)>> {
        let env = self.env;
        let CKind::Rec { rules, k, .. } = &env.consts[row as usize].kind else { return Ok(None) };
        let mut major = major;
        if *k {
            major = self.to_ctor_when_k(row, major)?;
        }
        major = self.force(major)?;
        if !matches!(self.val(major), Val::Lit(_)) && !self.is_ctor_app_only(major) {
            if let Some(&ind) = env.rec_major.get(&row) {
                major = self.to_ctor_when_structure(row, ind, major)?;
            }
        }
        major = self.whnf(major)?;
        if let Val::Lit(i) = self.val(major) {
            match self.lit(i).clone() {
                LitVal::Nat(n) => match self.nat_lit_ctor(&n)? {
                    Some(x) => major = x,
                    None => return Ok(None),
                },
                LitVal::Str(s) => match self.str_lit_expand(&s)? {
                    Some(x) => major = self.whnf(x)?,
                    None => return Ok(None),
                },
            }
        }
        let Some((crow, _, mspine)) = self.const_head(major) else { return Ok(None) };
        let ccanon = self.canon_of_row(crow);
        let Some(ri) = rules.iter().position(|r| env.canon(r.0) == ccanon) else { return Ok(None) };
        let (_, nfields, rhs) = rules[ri];
        let Some(margs) = self.app_args(mspine) else { return Ok(None) };
        if nfields as usize > margs.len() || (rhs as usize) >= env.main.len() || env.main.n()[rhs as usize].rng != 0 {
            return Ok(None);
        }
        Ok(Some((ri, ArgVec::from_slice(&margs[margs.len() - nfields as usize..]))))
    }

    /// Is definition `row` a casesOn: lambdas over params, motive, indices,
    /// major premise and minor premises, whose body is its recursor (one
    /// motive, at the definition's own levels) applied to them in recursor
    /// order, each minor premise wrapped in lambdas over the fields and the
    /// induction hypotheses that pass the fields on? Then `(recursor row,
    /// number of lambdas)`. Read from the value, not the name.
    fn cases_shape(&mut self, row: u32) -> Option<(u32, u32)> {
        // milestone 23: a byte per row says whether the shape is known and
        // whether there is one; only rows with a shape probe the map
        let f = self.shape_flag(row);
        if f & SH_CASES_KNOWN != 0 {
            if f & SH_CASES_SOME == 0 {
                return None;
            }
            if let Some(&r) = self.cases.get(&row) {
                return r;
            }
        }
        let r = self.cases_shape_of(row);
        self.shared.shape[row as usize].fetch_or(SH_CASES_KNOWN | if r.is_some() { SH_CASES_SOME } else { 0 }, Ordering::Relaxed);
        if r.is_some() {
            self.cases.insert(row, r);
        }
        r
    }
    #[inline(always)]
    fn shape_flag(&mut self, row: u32) -> u8 {
        self.shared.shape[row as usize].load(Ordering::Relaxed)
    }
    fn cases_shape_of(&mut self, row: u32) -> Option<(u32, u32)> {
        let c = &self.consts[row as usize];
        let CKind::Defn { value, .. } = c.kind else { return None };
        if value >= self.mlen {
            return None;
        }
        let mut b = value;
        let mut l = 0u32;
        while is_lam(self.tk(b)) {
            b = self.tb(b);
            l += 1;
        }
        let mut args: SmallVec16 = SmallVec16::new();
        let mut f = b;
        loop {
            let n = self.node(f);
            if n.kind != APP {
                break;
            }
            args.push(n.b);
            f = n.a;
        }
        args.reverse();
        if self.tk(f) != CONST {
            return None;
        }
        let rrow = self.row_of(self.ta(f));
        if rrow == NONE {
            return None;
        }
        let CKind::Rec { nparams, nindices, nmotives: 1, nminors, ref rules, .. } = self.consts[rrow as usize].kind else {
            return None;
        };
        let (np, ni, nm) = (nparams, nindices, nminors);
        if l != np + 1 + ni + 1 + nm || args.len() as u32 != np + 1 + nm + ni + 1 || rules.len() as u32 != nm {
            return None;
        }
        // the recursor at the definition's own levels, in order
        let ps: Vec<u32> = c.lparams.iter().map(|&n| self.env.canon(n)).collect();
        let lv: Vec<u32> = self.ll_get(f).to_vec();
        if lv.len() != ps.len() || self.consts[rrow as usize].lparams.len() != ps.len() {
            return None;
        }
        for (i, &x) in lv.iter().enumerate() {
            let (k, a, _) = self.lv.get(x);
            if k != crate::level::K_PARAM || self.env.canon(a) != ps[i] {
                return None;
            }
        }
        let bv = |w: &Self, t: u32, i: u32| w.tk(t) == BVAR && w.tp(t) == i;
        // binder positions (outermost 0): params, motive, indices, major, minors
        let var = |pos: u32| l - 1 - pos;
        for i in 0..np {
            if !bv(self, args[i as usize], var(i)) {
                return None;
            }
        }
        if !bv(self, args[np as usize], var(np)) {
            return None;
        }
        for k in 0..ni {
            if !bv(self, args[(np + 1 + nm + k) as usize], var(np + 1 + k)) {
                return None;
            }
        }
        if !bv(self, args[(np + 1 + nm + ni) as usize], var(np + 1 + ni)) {
            return None;
        }
        let rules: Vec<u32> = rules.iter().map(|r| r.1).collect();
        for j in 0..nm {
            // λ fields ihs. minor_j fields
            let mut a = args[(np + 1 + j) as usize];
            let mut k = 0u32;
            while is_lam(self.tk(a)) {
                a = self.tb(a);
                k += 1;
            }
            let nf = rules[j as usize];
            if k < nf {
                return None;
            }
            let mut g = a;
            let mut fs: SmallVec16 = SmallVec16::new();
            while self.tk(g) == APP {
                fs.push(self.tb(g));
                g = self.ta(g);
            }
            fs.reverse();
            if fs.len() as u32 != nf || !bv(self, g, var(np + 1 + ni + 1 + j) + k) {
                return None;
            }
            for (i, &x) in fs.iter().enumerate() {
                if !bv(self, x, k - 1 - i as u32) {
                    return None;
                }
            }
        }
        Some((rrow, l))
    }

    /// Is definition `row` a matcher-like function: lambdas over a casesOn
    /// application (any argument terms)? Then `(casesOn row, number of
    /// lambdas, the casesOn term)`.
    fn match_shape(&mut self, row: u32) -> Option<(u32, u32, u32)> {
        let f = self.shape_flag(row);
        if f & SH_MATCH_KNOWN != 0 {
            if f & SH_MATCH_SOME == 0 {
                return None;
            }
            if let Some(&r) = self.matchers.get(&row) {
                return r;
            }
        }
        let r = self.match_shape_of(row);
        self.shared.shape[row as usize].fetch_or(SH_MATCH_KNOWN | if r.is_some() { SH_MATCH_SOME } else { 0 }, Ordering::Relaxed);
        if r.is_some() {
            self.matchers.insert(row, r);
        }
        r
    }
    fn match_shape_of(&mut self, row: u32) -> Option<(u32, u32, u32)> {
        let CKind::Defn { value, .. } = self.consts[row as usize].kind else { return None };
        if value >= self.mlen {
            return None;
        }
        let mut b = value;
        let mut l = 0u32;
        while is_lam(self.tk(b)) {
            b = self.tb(b);
            l += 1;
        }
        let mut f = b;
        let mut n = 0u32;
        while self.tk(f) == APP {
            f = self.ta(f);
            n += 1;
        }
        if self.tk(f) != CONST {
            return None;
        }
        let crow = self.row_of(self.ta(f));
        if crow == NONE || crow == row {
            return None;
        }
        let (_, cl) = self.cases_shape(crow)?;
        if n < cl {
            return None;
        }
        Some((crow, l, b))
    }

    /// A matcher-like function applied to at least its arguments: the
    /// casesOn in its body has only its major premise evaluated, and the
    /// minor premise it picks; the motive and the other minor premises are
    /// never made values (Pestka's MatchersInlined, read off the value).
    fn match_direct(&mut self, row: u32, llr: u32, args: &[V]) -> R<Option<V>> {
        let Some((crow, l, body)) = self.match_shape(row) else { return Ok(None) };
        if (args.len() as u32) < l {
            return Ok(None);
        }
        let (rrow, cl) = self.cases_shape(crow).unwrap();
        let CKind::Rec { nparams, nindices, k, .. } = self.consts[rrow as usize].kind else { return Ok(None) };
        if k {
            return Ok(None);
        }
        // the casesOn's argument terms
        let mut cargs: SmallVec16 = SmallVec16::new();
        let mut f = body;
        loop {
            let n = self.node(f);
            if n.kind != APP {
                break;
            }
            cargs.push(n.b);
            f = n.a;
        }
        cargs.reverse();
        let ls = self.mk_ls(row, llr);
        let cllr = self.const_ll(f, ls);
        if self.ll_get(cllr).len() != self.consts[rrow as usize].lparams.len() {
            return Ok(None);
        }
        if !self.visible(crow) {
            return Ok(None);
        }
        let mut env = EMPTY;
        if self.trng(body) != 0 {
            for &a in &args[..l as usize] {
                env = self.push_env(a, env);
            }
        }
        let mi = (nparams + 1 + nindices) as usize;
        let major = self.thunk(cargs[mi], env, ls)?;
        let Some((ri, fields)) = self.rec_rule(rrow, major)? else { return Ok(None) };
        let minor = self.thunk(cargs[mi + 1 + ri], env, ls)?;
        let mut xs: ArgVec = fields;
        for &t in &cargs[cl as usize..] {
            let a = self.thunk(t, env, ls)?;
            xs.push(a);
        }
        xs.extend_from_slice(&args[l as usize..]);
        self.stats.match_direct += 1;
        Ok(Some(self.apply_many(minor, &xs)?))
    }

    /// A casesOn applied to at least its arguments, its major premise
    /// brought to a constructor: that constructor's minor premise applied
    /// to the fields and the arguments after (Pestka's CasesOnDirect: what
    /// unfolding, the recursor's rule and beta give, without them).
    fn cases_direct(&mut self, row: u32, llr: u32, args: &[V]) -> R<Option<V>> {
        let Some((rrow, l)) = self.cases_shape(row) else { return Ok(None) };
        if (args.len() as u32) < l || self.ll_get(llr).len() != self.consts[rrow as usize].lparams.len() {
            return Ok(None);
        }
        let CKind::Rec { nparams, nindices, .. } = self.consts[rrow as usize].kind else { return Ok(None) };
        let mi = (nparams + 1 + nindices) as usize;
        if matches!(self.consts[rrow as usize].kind, CKind::Rec { k: true, .. }) {
            // K: the recursor builds the constructor from the major's type
            // and its parameters; let it do so
            return Ok(None);
        }
        let Some((ri, fields)) = self.rec_rule(rrow, args[mi])? else { return Ok(None) };
        let minor = args[mi + 1 + ri];
        let mut xs: ArgVec = fields;
        xs.extend_from_slice(&args[l as usize..]);
        self.stats.cases_direct += 1;
        Ok(Some(self.apply_many(minor, &xs)?))
    }

    pub fn is_ctor_app(&self, v: V) -> bool {
        match self.const_head(v) {
            Some((r, _, _)) => matches!(self.consts[r as usize].kind, CKind::Ctor { .. }),
            None => false,
        }
    }

    /// A constructor applied to arguments only: no projection in the
    /// spine. `is_ctor_app` also takes `(mk a b).0`, a projection that
    /// whnf still reduces, which is right after whnf but not before it
    /// (Lean's is_constructor_app does not see through Expr.proj).
    pub fn is_ctor_app_only(&self, v: V) -> bool {
        match self.const_head(v) {
            Some((r, _, sp)) => matches!(self.consts[r as usize].kind, CKind::Ctor { .. }) && self.app_args(sp).is_some(),
            None => false,
        }
    }

    pub fn ind_info(&self, row: u32) -> Option<(u32, u32, &[u32], bool)> {
        match &self.consts[row as usize].kind {
            CKind::Induct { nparams, nindices, ctors, is_rec, .. } => Some((*nparams, *nindices, ctors, *is_rec)),
            _ => None,
        }
    }
    /// One constructor, no indices, not recursive.
    pub fn structure_like(&self, row: u32) -> bool {
        matches!(self.ind_info(row), Some((_, 0, ctors, false)) if ctors.len() == 1)
    }
    /// K06: inductive `row`'s declared type, past its parameters, is
    /// syntactically a sort that is never zero at any levels (its values
    /// are never proofs). False when unknown.
    pub fn struct_sort_never_zero(&self, row: u32) -> bool {
        let Some((np, ni, _, _)) = self.ind_info(row) else { return false };
        let mut t = self.consts[row as usize].ty;
        for _ in 0..(np + ni) {
            if !is_pi(self.tk(t)) {
                return false;
            }
            t = self.tb(t);
        }
        self.tk(t) == SORT && self.lv.is_not_zero(self.tp(t))
    }

    fn to_ctor_when_k(&mut self, rec_row: u32, major: V) -> R<V> {
        let Some(&ind) = self.env.rec_major.get(&rec_row) else { return Ok(major) };
        let t = self.infer_val(major)?;
        let t = self.whnf(t)?;
        let Some((irow, illr, ispine)) = self.const_head(t) else { return Ok(major) };
        if self.canon_of_row(irow) != ind {
            return Ok(major);
        }
        let Some((np, _, ctors, _)) = self.ind_info(irow) else { return Ok(major) };
        let Some(&c0) = ctors.first() else { return Ok(major) };
        let crow = self.row_of(c0);
        if crow == NONE || !self.visible(crow) {
            return Ok(major);
        }
        let Some(targs) = self.app_args(ispine) else { return Ok(major) };
        if targs.len() < np as usize {
            return Ok(major);
        }
        let c = self.mk_const(crow, illr)?;
        let capp = self.mk_app(c, &targs[..np as usize])?;
        let nt = self.infer_val(capp)?;
        // knobs, SK_KTRAP: a closed major whose type is not the
        // constructor's syntactically (the comparison may compute)
        if KNOBS && self.ktrap > 0 && t != nt && !self.has_fvar(major) {
            let t0 = self.ticks as u64;
            let r = self.defeq(t, nt)?;
            self.stats.ktrap[0] += 1;
            self.stats.ktrap[1] += self.ticks.wrapping_sub(t0 as u32) as u64;
            if self.ktrap >= 2 {
                eprintln!("KTRAP decl {} rec {} ticks {} result {r}\n  t  = {}\n  nt = {}", self.cur_decl, self.env.name_str(self.consts[rec_row as usize].name), self.ticks.wrapping_sub(t0 as u32) as u64, self.vshow(t, 6), self.vshow(nt, 6));
                std::process::exit(7);
            }
            return if r { Ok(capp) } else { Ok(major) };
        }
        if self.defeq(t, nt)? { Ok(capp) } else { Ok(major) }
    }

    /// `mk params major.0 ... major.(n-1)` when recursor `rec_row`'s major
    /// inductive `ind` is a non-recursive structure (one constructor, no
    /// indices: Gruszka's own checked data) and the recursor eliminates into
    /// every sort; otherwise `major` unchanged. Lean's to_cnstr_when_structure
    /// after lean4#15371: a structure in Prop is expanded only when it
    /// eliminates into every sort (like And): with no indices every field is
    /// then a proof, so its projections are well typed; one that eliminates
    /// only into Prop (like Exists) has no projections and is left alone.
    fn to_ctor_when_structure(&mut self, rec_row: u32, ind: u32, major: V) -> R<V> {
        let irow = self.env.known_row(ind);
        if irow == NONE || !self.visible(irow) || !self.structure_like(irow) || self.is_ctor_app_only(major) {
            return Ok(major);
        }
        if !self.rec_elim_any_sort(rec_row) {
            return Ok(major);
        }
        let t = self.infer_val(major)?;
        let t = self.whnf(t)?;
        let Some((trow, tllr, tspine)) = self.const_head(t) else { return Ok(major) };
        if self.canon_of_row(trow) != ind {
            return Ok(major);
        }
        // K06: the official Lean 4.36.0 kernel never eta-expands a major
        // premise that is a proof (inductive.h to_cnstr_when_structure:
        // `if (is_prop(e_type)) return e;`); lean4#15371, which does it for
        // large-eliminating Prop structures such as And, is only in
        // v4.37.0-rc1. Following 4.36 keeps the verdicts identical.
        if self.is_prop_type(t)? {
            return Ok(major);
        }
        self.expand_eta_struct(irow, tllr, tspine, major)
    }

    /// Does recursor `rec_row` eliminate into every sort? Lean's test
    /// (lean4#15371): it has one more universe parameter, the motive's,
    /// than the first inductive of its block (not the major's inductive,
    /// which for a nested auxiliary recursor is another type). The
    /// recursor's universe parameters were checked against the block's
    /// elimination level when the block was added (induct.rs
    /// check_recursors: equal when it eliminates only into Prop, one fresh
    /// motive universe more otherwise), and its `all` against the block.
    fn rec_elim_any_sort(&self, rec_row: u32) -> bool {
        let env = self.env;
        let c = &env.consts[rec_row as usize];
        let CKind::Rec { all, .. } = &c.kind else { return false };
        let Some(&first) = all.first() else { return false };
        let frow = env.known_row(env.canon(first));
        if frow == NONE || !matches!(env.consts[frow as usize].kind, CKind::Induct { .. }) {
            return false;
        }
        c.lparams.len() == env.consts[frow as usize].lparams.len() + 1
    }

    fn expand_eta_struct(&mut self, irow: u32, tllr: u32, tspine: u32, v: V) -> R<V> {
        let (np, _, ctors, _) = self.ind_info(irow).unwrap();
        let crow = self.row_of(ctors[0]);
        if crow == NONE {
            return Ok(v);
        }
        let CKind::Ctor { nfields, .. } = self.consts[crow as usize].kind else { return Ok(v) };
        let Some(targs) = self.app_args(tspine) else { return Ok(v) };
        if targs.len() < np as usize {
            return Ok(v);
        }
        let c = self.mk_const(crow, tllr)?;
        let mut r = self.mk_app(c, &targs[..np as usize])?;
        let sname = self.consts[irow as usize].name;
        for i in 0..nfields {
            let p = self.proj_val(v, i, sname)?;
            r = self.apply(r, p)?;
        }
        Ok(r)
    }

    /// Value of a theorem's or definition's body, if it can be unfolded.
    fn decl_value(&mut self, row: u32) -> R<Option<u32>> {
        match self.consts[row as usize].kind {
            CKind::Defn { value, .. } => Ok(Some(value)),
            CKind::Thm { value: ThmVal::Main(v), .. } => Ok(Some(v)),
            CKind::Thm { value: ThmVal::Block(bi), .. } => {
                if let Some(&r) = self.block_roots.get(&bi) {
                    return Ok(r);
                }
                self.stats.blocks_foreign += 1;
                let r = self.decode_block(bi).ok();
                let r = r.filter(|&t| self.trng(t) == 0);
                self.block_roots.insert(bi, r);
                Ok(r)
            }
            _ => Ok(None),
        }
    }

    /// Decodes proof block `bi` into the arena; returns its root id.
    pub fn decode_block(&mut self, bi: u32) -> Result<u32, Stop> {
        let env = self.env;
        let b = env.blocks[bi as usize];
        let base = self.m + self.blk.len() as u32;
        let cols_base = self.m;
        let lit_base = env.lits.len() as u32;
        let (blk, side, lits) = (&mut self.blk, &mut self.blk_side, &mut self.wlits);
        let r: Result<(), susz::read::Stop<()>> = susz::read::decode_block(env.bytes, &env.st, b, |_k, e| {
            // milestone 19: past a dropped push the children's ids are not
            // nodes: stop (the arena-full decline below)
            if blk.full {
                return Err(());
            }
            push_expr(blk, side, lits, lit_base, cols_base, base, &env.lvl_map, Some(env.main.n()), Some(env.main.used()), e);
            Ok(())
        });
        if self.blk.too_deep {
            // not sticky: the session's later blocks decode on their own
            self.blk.too_deep = false;
            return decline("a term has 65535 or more loose bound variables");
        }
        if self.blk.full {
            self.arena_full = true;
            return decline("the worker's block arena is full");
        }
        match r {
            Ok(()) => Ok(self.m + self.blk.len() as u32 - 1),
            Err(susz::read::Stop::File(f)) => {
                if f.class.declines() {
                    decline(f.to_string())
                } else {
                    reject(f.to_string())
                }
            }
            Err(susz::read::Stop::Visitor(())) => decline("block decode stopped"),
        }
    }

    /// `(row, hint)` if `v` is a constant application that delta can unfold.
    fn delta_info(&mut self, v: V) -> Option<(u32, Hint)> {
        let (row, llr, spine) = self.const_head(v)?;
        if !self.visible(row) {
            return None;
        }
        let c = &self.consts[row as usize];
        let hint = match &c.kind {
            CKind::Defn { hint, .. } => *hint,
            CKind::Thm { .. } => Hint::Opaque,
            _ => return None,
        };
        if self.ll_get(llr).len() != c.lparams.len() {
            return None;
        }
        if self.spine_has_proj(spine) {
            return None;
        }
        Some((row, hint))
    }

    fn unfold(&mut self, v: V) -> R<Option<V>> {
        if true {
            let r = self.memo_at(v).unfold();
            if r != UF_NONE {
                if STATS { self.stats.unfold_memo_hits += 1; }
                return Ok(if r == UF_NO { None } else { Some(r) });
            }
            let r = self.unfold_raw(v)?;
            self.memo_w(v).set_unfold(r.unwrap_or(UF_NO));
            return Ok(r);
        }
        self.unfold_raw(v)
    }

    fn unfold_raw(&mut self, v: V) -> R<Option<V>> {
        let Some((row, _)) = self.delta_info(v) else { return Ok(None) };
        let (_, llr, spine) = self.const_head(v).unwrap();
        // milestone 48: a Nat operation without free variables is computed,
        // not unfolded (whnf computes it; every unfolding caller, probes
        // too, gets the literal). CFSG's TripleCoverSuz.gen_of_le compared
        // `x + 7` with `n <<< 297`, n a 5901-digit literal: lazy delta does
        // not fold with a free variable on the other side (Lean's guard),
        // so the shift was unfolded and each `2 * m` came to Nat.mul's
        // recursion on m, peeling the literal one by one
        if self.env.nat_op[row as usize] != 0 && !self.has_fvar(v) {
            if let Some(n) = self.reduce_nat(v)? {
                return Ok(Some(n));
            }
        }
        // milestone 50: a Nat operation over a large literal and a free
        // variable is unfolded like any definition (Lean's lazy delta:
        // reduce_nat is a shortcut, never a refusal). It used to stay
        // stuck: `Nat.ble 131072 =?= fun m => Nat.ble 131072 m` unfolded
        // the left side and left the right one, and the two never met
        // (CFSG KernelCensus.Fi22K.T2.walkT2).
        let Some(body) = self.decl_value(row)? else { return Ok(None) };
        if self.trng(body) != 0 {
            return Ok(None);
        }
        Ok(Some(self.unfold_body(v, row, llr, spine, body)?))
    }

    fn unfold_body(&mut self, v: V, row: u32, llr: u32, spine: u32, body: u32) -> R<V> {
        self.stats.unfolds += 1;
        if KNOBS {
            UHIST.with(|h| {
                let mut h = h.borrow_mut();
                if let Some(h) = h.as_mut() {
                    *h.entry(row).or_insert(0) += 1;
                }
            });
        }
        let args = self.app_args(spine).unwrap_or(&[]);
        if true {
            if let Some(r) = self.cases_direct(row, llr, &args)? {
                return Ok(r);
            }
            if true {
                if let Some(r) = self.match_direct(row, llr, &args)? {
                    return Ok(r);
                }
            }
        }
        let ls = self.mk_ls(row, llr);
        self.beta(body, EMPTY, ls, &args)
    }

    /// Milestone 15: values in normal form and memo hits inlined; the rest
    /// out of line (`whnf_miss` checks them again).
    #[inline(always)]
    pub fn whnf(&mut self, v: V) -> R<V> {
        let v = self.force(v)?;
        match self.val(v) {
            Val::Sort(_) | Val::Lit(_) | Val::Clo { .. } | Val::CloI { .. } => return Ok(v),
            Val::Neu { head: Head::FVar(_), spine: EMPTY } => return Ok(v),
            _ => {}
        }
        let m = self.memo_at(v).whnf;
        if m != NONE {
            if STATS { self.stats.whnf_hits += 1; }
            return Ok(m);
        }
        self.whnf_miss(v)
    }
    #[inline(never)]
    fn whnf_miss(&mut self, v: V) -> R<V> {
        if dstack_on() {
            dstack_push(b'W', v, NONE, self.ticks);
            let r = self.whnf_miss1(v);
            dstack_pop();
            return r;
        }
        self.whnf_miss1(v)
    }
    fn whnf_miss1(&mut self, v: V) -> R<V> {
        match self.val(v) {
            Val::Sort(_) | Val::Lit(_) | Val::Clo { .. } | Val::CloI { .. } => return Ok(v),
            Val::Neu { head: Head::FVar(_), spine: EMPTY } => return Ok(v),
            _ => {}
        }
        let m = self.memo_at(v).whnf;
        if m != NONE {
            if STATS { self.stats.whnf_hits += 1; }
            return Ok(m);
        }
        if STATS { self.stats.whnf_misses += 1; }
        if self.deep_at != 0 {
            if self.wdepth == 0 {
                return self.whnf_outer(v);
            }
            let x = 0u8;
            let sp = std::hint::black_box(&x) as *const u8 as usize;
            if self.stack_base.saturating_sub(sp) > self.deep_at || self.wdepth >= self.deep_cur {
                self.deep_v = v;
                return Err(Stop::Deep);
            }
        }
        self.wdepth += 1;
        if self.wdepth == self.deep_cur / 2 && self.deep_half == 0 {
            self.deep_half = self.ticks | 1;
        }
        let r = self.whnf_body(v);
        self.wdepth -= 1;
        r
    }

    /// Milestone 38: the outermost whnf. A nested whnf past `deep_at`
    /// bytes of stack that misses its memo is handed up here (`Stop::Deep`): it is worked
    /// out from this shallow stack (its own deep misses handed up the same
    /// way, so the deepest first), its memo kept, and the call tried again,
    /// finding it. A lazy accumulator (`go n (xor b true)`, a fold whose
    /// state no step looks at) is a chain of thunks as long as the loop,
    /// each one's whnf inside the next one's: a million steps overflowed
    /// the stack; now it is worked out a slice of half the stack at a time.
    /// Handing up is costly where the chain is not one thread (each retry
    /// walks again to the next deep point: CFSG's hD at 8192 levels took
    /// 73 G instead of 19), so it waits for the stack to be at risk.
    #[inline(never)]
    fn whnf_outer(&mut self, v: V) -> R<V> {
        let (a0, l0, d0) = (self.argstack.len(), self.let_vals.len(), self.vdepth);
        let mut pend: Vec<V> = Vec::new();
        let mut x = v;
        loop {
            self.wdepth = 1;
            self.deep_half = 0;
            let r = self.whnf_body(x);
            self.wdepth = 0;
            match r {
                Ok(r) => match pend.pop() {
                    None => return Ok(r),
                    Some(y) => x = y,
                },
                Err(Stop::Deep) => {
                    // the frames between were unwound: their stacks too
                    self.argstack.truncate(a0);
                    self.let_vals.truncate(l0);
                    self.vdepth_to(d0);
                    self.stats.deep_up += 1;
                    // an attempt whose deeper half cost `deep_ticks` or more
                    // per level is costly to try again: the bound doubles
                    // (CFSG's hD, a deep tree of levels of ~84 ticks, took
                    // 3.7x its work at a fixed bound; a lazy accumulator's
                    // levels take ~8 and keep it)
                    let per = if self.deep_half == 0 { 0 } else { self.ticks.wrapping_sub(self.deep_half) / (self.deep_cur / 2).max(1) };
                    if per >= self.deep_ticks {
                        self.deep_cur = self.deep_cur.saturating_mul(2);
                    }
                    pend.push(x);
                    x = self.deep_v;
                }
                Err(e) => return Err(e),
            }
        }
    }

    fn whnf_body(&mut self, v: V) -> R<V> {
        let m = self.memo_at(v).whnf;
        if m != NONE {
            return Ok(m);
        }
        // milestone 39: a closed value of a heavy declaration by the ground machine
        if self.ground && (self.vals.len() >= self.ground_at || self.ground_all) && !self.ground_busy {
            if let Some(r) = self.ground_whnf(v)? {
                self.memo_w(v).whnf = r;
                return Ok(r);
            }
        }
        // milestone 36: past `reg_at` values the call is a region
        // (SK_REGION_LATEGATE=1, knobs, gates: every region opens late)
        let r = if self.reg_wanted() && !self.reg_lategate {
            self.whnf_region(v, v)?
        } else {
            match self.whnf_loop(v)? {
                Ok(r) => r,
                // milestone 38: the session passed `reg_at` while this
                // loop ran: the rest of it is a region (a late region)
                Err(t) => {
                    self.stats.late += 1;
                    self.whnf_region(v, t)?
                }
            }
        };
        self.memo_w(v).whnf = r;
        // only real steps: a value in normal form found again under another
        // id with the same name must come back as itself, or a caller that
        // asks whether anything changed would go round between the two
        Ok(r)
    }

    /// The whnf loop of `v` from its current term `t` as a region (opened
    /// at `v`'s call, or late: at a step of the loop, which keeps only its
    /// current term from one step to the next, as at a checkpoint).
    #[inline(never)]
    fn whnf_region(&mut self, v: V, t: V) -> R<V> {
        Ok({
            let mut g = self.reg_open(v);
            // milestone 37: the loop's current term is all it keeps from
            // one step to the next: past `reg_min` values made since the
            // region (re)opened, the region closes with that term as its
            // result and opens again (a checkpoint). A long tail loop (CPS
            // code over big literals, CFSG's rowOK*: one whnf for the whole
            // check) gave nothing back before it returned.
            let mut t = t;
            loop {
                let step = (|| -> R<Result<V, V>> {
                    self.tick()?;
                    let c = match self.whnf_core_ck(t, Some(g))? {
                        Ok(c) => c,
                        Err(cur) => return Ok(Err(cur)),
                    };
                    if let Some(n) = self.reduce_nat(c)? {
                        return Ok(Ok(n));
                    }
                    Ok(match self.unfold(c)? {
                        Some(u) => Err(u),
                        None => Ok(c),
                    })
                })();
                match step {
                    Ok(Ok(r)) => break self.reg_close(&g, v, r)?,
                    Ok(Err(u)) => {
                        t = u;
                        if self.reg_ckpt && self.reg_due(&g) {
                            (t, g) = self.reg_checkpoint(&g, v, t)?;
                        }
                    }
                    Err(Stop::Deep) if self.wdepth == 1 && self.deep_roll => {
                        // milestone 38: the outermost whnf's attempt ended
                        // at a miss handed up from too deep: what it made is
                        // given back but the handed-up value (it is tried
                        // again after that value is worked out)
                        self.deep_v = self.reg_close(&g, v, self.deep_v)?;
                        return Err(Stop::Deep);
                    }
                    Err(e) => {
                        self.reg_keep(&g);
                        return Err(e);
                    }
                }
            }
        })
    }

    /// The whnf loop without a region: Ok(result), or Err(current term)
    /// once the session wants regions (milestone 38: a loop that began
    /// before the session passed `reg_at` gave nothing back until it
    /// returned; CFSG's Fi24P7.MS.a0 multiplies 42 bit-sliced matrices in
    /// loops entered early, 11 GB of dead literals).
    #[inline(always)]
    fn whnf_loop(&mut self, v: V) -> R<Result<V, V>> {
        let mut t = v;
        Ok(loop {
            self.tick()?;
            let c = match self.whnf_core_ck(t, None)? {
                Ok(c) => c,
                Err(cur) => break Err(cur),
            };
            if let Some(n) = self.reduce_nat(c)? {
                break Ok(n);
            }
            match self.unfold(c)? {
                Some(u) => {
                    t = u;
                    if self.reg_late && self.reg_wanted() {
                        break Err(t);
                    }
                }
                None => break Ok(c),
            }
        })
    }

    // -----------------------------------------------------------------------
    // Type inference

    pub fn sort_of(&mut self, t: V, what: &str) -> R<u32> {
        let w = self.whnf(t)?;
        match self.val(w) {
            Val::Sort(l) => Ok(l),
            _ => reject(format!("type expected ({what})")),
        }
    }

    pub fn is_prop_type(&mut self, t: V) -> R<bool> {
        let s = self.infer_val(t)?;
        let s = self.whnf(s)?;
        Ok(matches!(self.val(s), Val::Sort(l) if self.lv.zeroish(l)))
    }

    fn check_levels(&mut self, l: u32) -> R<()> {
        if let Some(&ok) = self.lp_ok.get(&l) {
            return if ok { Ok(()) } else { reject("undeclared universe parameter") };
        }
        let ps = self.cur_lparams.clone();
        let ok = self.lv.params_in(l, &mut |n| ps.contains(&n));
        self.lp_ok.insert(l, ok);
        if ok { Ok(()) } else { reject("undeclared universe parameter") }
    }

    fn infer_const(&mut self, t: u32, ls: u32, check: bool) -> R<V> {
        let name = self.ta(t);
        let row = self.row_of(name);
        if row == NONE || !self.visible(row) {
            return reject(format!("unknown constant {}", self.env.name_str(name)));
        }
        let c = &self.consts[row as usize];
        if self.ll_get(t).len() != c.lparams.len() {
            return reject(format!("wrong number of universe levels for {}", self.env.name_str(name)));
        }
        if check {
            if c.is_unsafe() && self.safety != 1 {
                return reject(format!("invalid declaration, it uses unsafe declaration {}", self.env.name_str(name)));
            }
            if let CKind::Defn { safety: 2, .. } = c.kind {
                if self.safety == 0 {
                    return reject(format!("safe declaration must not use partial declaration {}", self.env.name_str(name)));
                }
            }
            let lvls = self.ll_get(t).to_vec();
            for l in lvls {
                self.check_levels(l)?;
            }
        }
        let ty = c.ty;
        let llr = self.const_ll(t, ls);
        let cls = self.mk_ls(row, llr);
        self.eval(ty, EMPTY, cls)
    }

    /// Milestone 15: a variable whose value's type is memoized is answered
    /// inline (no tick: nothing recurses), the rest out of line.
    #[inline(always)]
    pub fn infer(&mut self, t: u32, env: u32, ls: u32, check: bool) -> R<V> {
        if self.tk(t) == BVAR {
            if let Ok(v) = self.env_get(env, self.tp(t)) {
                let m = self.memo_at(v).infer;
                if m != NONE {
                    #[cfg(feature = "cnt")]
                    { self.stats.infer_calls += 1; }
                    return Ok(m);
                }
            }
        }
        self.infer_full(t, env, ls, check)
    }
    /// Milestone 45: an inference past `deep_at` bytes of stack of a
    /// closed term that misses its cache is handed up (`Stop::DeepInfer`)
    /// to the declaration (`check_decl`), worked out there from a shallow
    /// stack (its own deep misses handed up the same way, so the deepest
    /// first), cached, and the declaration tried again, finding it. CFSG's
    /// RG.chars is a List Char literal of 913 K conses: each tail's type
    /// was inferred inside its cons's, past the stack limit on AWS
    /// ("recursion too deep", declined, and everything after it in the
    /// file skipped). Pestka hands deep arguments up the same way
    /// (DeepSpinesResumed). (An outermost inference catching them, as
    /// whnf_outer does, cost +1.7% instructions on Init: every inference
    /// went through it.)
    #[inline(never)]
    fn infer_full(&mut self, t: u32, env: u32, ls: u32, check: bool) -> R<V> {
        self.tick()?;
        if self.deep_zone && self.trng(t) == 0 {
            let x = 0u8;
            let sp = std::hint::black_box(&x) as *const u8 as usize;
            if self.stack_base.saturating_sub(sp) > self.deep_at
                && self.tk(t) != BVAR
                && icache_hit(self.infer_cache.get(&ikey2(t, EMPTY, ls)), check, self.cur_lp).is_none()
            {
                self.deep_inf = (t, ls, check);
                return Err(Stop::DeepInfer);
            }
        }
        #[cfg(feature = "cnt")]
        { self.stats.infer_calls += 1; }
        if self.tk(t) == BVAR {
            // milestone 14: a variable's type is its value's (memoized in
            // the value's record), what infer_core returns: no table probes
            let v = self.env_get(env, self.tp(t))?;
            return self.infer_val(v);
        }
        let env = if self.trng(t) == 0 { EMPTY } else { env };
        // milestone 16: one key. Under an environment of at most 63 entries
        // the result is kept only by the entries the term reads (milestone
        // 8's used-entries key, `infer_u`), not also by the environment
        // itself: one table, one probe on a hit, one insert on a miss.
        // Closed terms and wider environments keep `infer_cache`.
        if env != EMPTY {
            if let Some(u) = self.used_env_id(t, env) {
                let ukey = ikey2(t, u, ls);
                if let Some(v) = icache_hit(self.infer_u.get(&ukey), check, self.cur_lp) {
                    if STATS { self.stats.infer_hits += 1; }
                    if STATS { self.stats.infer_u_hits += 1; }
                    return Ok(v);
                }
                if STATS { self.stats.infer_misses += 1; }
                let r = if env == self.kb_env && check && ls == 0 { self.infer_known(t, env)? } else { self.infer_core(t, env, ls, check)? };
                icache_put(&mut self.infer_u, ukey, r, check, self.cur_lp);
                self.ulog(Undo::InferU(ukey));
                return Ok(r);
            }
        }
        if let Some(v) = icache_hit(self.infer_cache.get(&ikey2(t, env, ls)), check, self.cur_lp) {
            if STATS { self.stats.infer_hits += 1; }
            return Ok(v);
        }
        if STATS { self.stats.infer_misses += 1; }
        let mut nkey = u64::MAX;
        // milestone 31: by name only under a wide environment (the used-entry
        // keys did not apply); closed terms keep `infer_cache` alone
        // Names of at most INFER_NAME_FUEL nodes. Past INFER_NAME_CALLS calls
        // the site stays on only while at least 1 in INFER_NAME_HITS calls
        // hits, and past 4x that many only while the ticks its hits saved
        // pay for the name nodes walked (INFER_NAME_PAY nodes a tick):
        // SzemerediRegularity's edgeDensity proof (12% hits) turns it off,
        // FLT's ModularCurve proofs (40-60% hits) keep it.
        // release-da: on for every inference that reaches it (closed terms
        // too, no cost model), so the gates' small files reach name hits
        let mut nm_on = cfg!(debug_assertions)
            || self.nm.icalls < INFER_NAME_CALLS
            || (self.nm.hits[3] * INFER_NAME_HITS >= self.nm.icalls
                && (self.nm.icalls < 4 * INFER_NAME_CALLS || self.nm.ispent <= INFER_NAME_PAY * self.nm.isaved));
        // milestone 32: off is tried again, on a fresh sample, once the
        // declaration has run twice as long as when it went off (the first
        // calls depend on what the session's caches already answer: igusaSep
        // after its own _proof_1_2 hit 22% at first, 54% overall)
        if !nm_on && INFER_REARM != 0 {
            let now = self.ticks.wrapping_sub(self.decl_ticks0).max(1);
            if self.nm.ioff == 0 {
                self.nm.ioff = now;
            } else if now / INFER_REARM >= self.nm.ioff {
                (self.nm.icalls, self.nm.hits[3], self.nm.ispent, self.nm.isaved, self.nm.ioff) = (0, 0, 0, 0, 0);
                nm_on = true;
            }
        }
        if (env != EMPTY || cfg!(debug_assertions)) && nm_on && self.p2() {
            self.nm.icalls += 1;
            let named = self.name_t_f(t, env, ls, INFER_NAME_FUEL);
            self.nm.ispent += (INFER_NAME_FUEL - self.nm.fuel) as u64;
            if let Some(n) = named {
                let k = (n as u64) << 1;
                let hit = match self.nm.infer.get(&(k | check as u64)) {
                    Some(&r) => Some(r),
                    None if !check => self.nm.infer.get(&(k | 1)).copied(),
                    None => None,
                };
                if let Some((r, c)) = hit {
                    self.nm.hits[3] += 1;
                    self.nm.isaved += c as u64;
                    // release-da: every hit inferred again, the types equal
                    #[cfg(debug_assertions)]
                    {
                        let w = self.infer_core(t, env, ls, check)?;
                        assert!(self.defeq(r, w)?, "inference by name: term {t} in {env}: a type not the inferred one");
                    }
                    icache_put(&mut self.infer_cache, ikey2(t, env, ls), r, check, self.cur_lp);
            self.ulog(Undo::Infer(ikey2(t, env, ls)));
                    return Ok(r);
                }
                nkey = k | check as u64;
            }
        }
        let closed_main = check && env == EMPTY && ls == 0 && t < self.mlen;
        if closed_main && self.checked_before(t) {
            if STATS { self.stats.checked_hits += 1; }
            let r = self.infer(t, EMPTY, 0, false)?;
            icache_put(&mut self.infer_cache, ikey2(t, env, ls), r, check, self.cur_lp);
            self.ulog(Undo::Infer(ikey2(t, env, ls)));
            return Ok(r);
        }
        let tk0 = self.ticks;
        let r = if env == self.kb_env && check && ls == 0 { self.infer_known(t, env)? } else { self.infer_core(t, env, ls, check)? };
        if nkey != u64::MAX {
            self.nm.infer.insert(nkey, (r, self.ticks.wrapping_sub(tk0)));
            self.ulog(Undo::NmInfer(nkey));
        }
        if closed_main && self.safety == 0 {
            if STATS { self.stats.checked_misses += 1; }
            let l = self.lp_list();
            let x = ((u32::MAX - self.cur_decl) as u64) << 32 | l as u64;
            // the latest fact replaces the stored one (as with one worker):
            // any stored pair is a true fact, a lost one is only a miss
            self.shared.checked[t as usize].store(x, Ordering::Relaxed);
        }
        icache_put(&mut self.infer_cache, ikey2(t, env, ls), r, check, self.cur_lp);
            self.ulog(Undo::Infer(ikey2(t, env, ls)));
        Ok(r)
    }

    fn infer_core(&mut self, t: u32, env: u32, ls: u32, check: bool) -> R<V> {
        let k = self.tk(t);
        match k {
            BVAR => {
                let v = self.env_get(env, self.tp(t))?;
                self.infer_val(v)
            }
            SORT => {
                let l = self.tp(t);
                if check {
                    self.check_levels(l)?;
                }
                let l = self.lsub(l, ls);
                let s = self.lv.succ(l);
                self.intern(Val::Sort(s))
            }
            CONST => self.infer_const(t, ls, check),
            APP => {
                let base = self.argstack.len();
                let mut f = t;
                loop {
                    let n = self.node(f);
                    if n.kind != APP {
                        break;
                    }
                    self.argstack.push(n.b);
                    f = n.a;
                }
                // milestone 23: read from the end, as in eval_loop
                let n = self.argstack.len() - base;
                let top = base + n - 1;
                if is_lam(self.tk(f)) {
                    self.lam_head = f;
                }
                let mut ft = self.infer(f, env, ls, check)?;
                // the function type walked as a syntactic Pi (term, env, ls)
                // while it is one, without making a value per argument
                let mut cur: Option<(u32, u32, u32)> = None;
                for k in 0..n {
                    let a = self.argstack[top - k];
                    let (pt, pe, pls) = match cur {
                        Some(x) => x,
                        None => {
                            let w = self.whnf(ft)?;
                            match self.val(w) {
                                Val::Clo { term, env: ce, ls: cl } if is_pi(self.tk(term)) => (term, ce, cl),
                                _ => {
                                    if !self.is_pi_val(w) {
                                        return reject("function expected");
                                    }
                                    let av = self.thunk(a, env, ls)?;
                                    if check {
                                        let at = self.infer(a, env, ls, true)?;
                                        let dom = self.bind_dom(w)?;
                                        if !self.defeq(at, dom)? {
                                            return reject("application type mismatch");
                                        }
                                    }
                                    ft = self.bind_body(w, av)?;
                                    continue;
                                }
                            }
                        }
                    };
                    if check {
                        let at = self.infer(a, env, ls, true)?;
                        let dom = self.thunk(self.ta(pt), pe, pls)?;
                        if !self.defeq(at, dom)? {
                            return reject("application type mismatch");
                        }
                    }
                    let b = self.tb(pt);
                    // milestone 25: the argument's value only when the
                    // codomain reads it (nano-lean's uses_arg); else a HOLE
                    // holds its place (the used mask is exact at bit 0, so
                    // no subterm of `b` ever reads it)
                    let e2 = self.push_arg(a, env, ls, pe, b)?;
                    if is_pi(self.tk(b)) {
                        cur = Some((b, e2, pls));
                    } else {
                        cur = None;
                        ft = self.eval(b, e2, pls)?;
                    }
                }
                self.argstack.truncate(base);
                if let Some((pt, pe, pls)) = cur {
                    ft = self.pi_value(pt, pe, pls)?;
                }
                Ok(ft)
            }
            k if is_lam(k) => {
                if check {
                    // milestone 35: a lambda's body type is used at an argument
                    // only when the lambda is an application's head (bind_body
                    // of its inference closure); kept only for those (keeping
                    // it for every checked lambda cost cedar, con-leche +1%)
                    let head = std::mem::replace(&mut self.lam_head, NONE) == t;
                    let mut e = env;
                    let mut b = t;
                    // milestone 23: on the stack (no allocation per lambda)
                    let mut xs: ArgVec = ArgVec::new();
                    let d0 = self.vdepth;
                    let mut last = (NONE, NONE);
                    while is_lam(self.tk(b)) {
                        let d = self.ta(b);
                        let s = self.infer(d, e, ls, true)?;
                        self.sort_of(s, "binder domain")?;
                        let dv = self.thunk(d, e, ls)?;
                        let x = self.open_var(dv)?;
                        let ek = self.prune(b, e);
                        self.lam_var.entry((b, ek, ls)).or_insert(x);
                        self.ulog(Undo::LamVar((b, ek, ls)));
                        last = (b, ek);
                        self.set_busy(x, true);
                        xs.push(x);
                        e = self.push_env(x, e);
                        b = self.tb(b);
                    }
                    let r = self.infer(b, e, ls, true);
                    if let (true, Ok(rv)) = (head, r) {
                        self.lam_type_record(last.0, last.1, ls, b, rv, xs[xs.len() - 1]);
                    }
                    for (j, &x) in xs.iter().enumerate().rev() {
                        self.close_var(x, d0 + j as u32);
                    }
                    r?;
                }
                let env = self.prune(t, env);
                self.intern(Val::CloI { term: t, env, ls })
            }
            k if is_pi(k) => {
                let mut e = env;
                let mut b = t;
                let mut us: smallvec::SmallVec<[u32; 16]> = smallvec::SmallVec::new();
                let mut xs: ArgVec = ArgVec::new();
                let d0 = self.vdepth;
                while is_pi(self.tk(b)) {
                    let d = self.ta(b);
                    let s = self.infer(d, e, ls, check)?;
                    us.push(self.sort_of(s, "binder domain")?);
                    let dv = self.thunk(d, e, ls)?;
                    let x = self.open_var(dv)?;
                    xs.push(x);
                    e = self.push_env(x, e);
                    b = self.tb(b);
                }
                if t == self.kb_root && env == EMPTY && ls == 0 {
                    // milestone 29: the declaration type's telescope, where
                    // open facts are looked up
                    self.kb_root = NONE;
                    self.kb_tele = t;
                    self.kb_env = e;
                }
                let s = self.infer(b, e, ls, check);
                for (j, &x) in xs.iter().enumerate().rev() {
                    self.close_var(x, d0 + j as u32);
                }
                let mut r = self.sort_of(s?, "Pi body")?;
                for &u in us.iter().rev() {
                    r = self.lv.imax(u, r);
                }
                self.intern(Val::Sort(r))
            }
            LET => {
                let (ty, val) = (self.ta(t), self.tb(t));
                if check {
                    let s = self.infer(ty, env, ls, true)?;
                    self.sort_of(s, "let type")?;
                    let vt = self.infer(val, env, ls, true)?;
                    let tv = self.eval(ty, env, ls)?;
                    if !self.defeq(vt, tv)? {
                        return reject("let value type mismatch");
                    }
                }
                let lb = self.let_body(t);
                if self.trng(lb) == 0 || self.used_mask(lb) & 1 == 0 {
                    let e = self.push_arg(val, env, ls, env, lb)?;
                    return self.infer(lb, e, ls, check);
                }
                // milestone 34: Lean checks the body with the variable in
                // the local context; its value is pushed as before and
                // remembered as a let variable's (`over_let`)
                let av = self.thunk(val, env, ls)?;
                let e = self.push_env(av, env);
                let n0 = self.let_vals.len();
                if !matches!(self.val(av), Val::Lit(_) | Val::Sort(_)) {
                    self.let_vals.push(av);
                }
                let r = self.infer(lb, e, ls, check);
                self.let_vals.truncate(n0);
                self.let_skip = self.let_skip.min(n0);
                r
            }
            NAT | STR => {
                // Lean's infer_lit: literals entering the kernel are bounded too
                if let LitVal::Nat(n) = self.lit(self.tp(t)) {
                    if nat_bytes(n) > NAT_MAX_BYTES {
                        return reject(NAT_SIZE_MSG);
                    }
                }
                self.lit_type(k == NAT)
            }
            PROJ => {
                let s = self.ta(t);
                let st = self.infer(s, env, ls, check)?;
                let sv = self.thunk(s, env, ls)?;
                self.proj_type(sv, st, self.tb(t), self.tp(t))
            }
            _ => reject("unknown expression kind"),
        }
    }

    fn lit_type(&mut self, nat: bool) -> R<V> {
        let k = self.env.known;
        let r = self.known_visible(if nat { k.nat } else { k.string });
        if r == NONE {
            return decline("literal used before Nat/String is declared");
        }
        self.mk_const(r, LL_EMPTY)
    }

    /// Does the body of Pi closure `w` use its bound variable?
    fn pi_dependent(&mut self, w: V) -> bool {
        match self.val(w) {
            Val::Clo { term, .. } if is_pi(self.tk(term)) => {
                let b = self.tb(term);
                self.uses_var(b, 0)
            }
            _ => true,
        }
    }
    /// The entries of `env` that term `t` reads, as one id per declaration
    /// (the used mask and the values at its bits); None past 63 entries.
    fn used_env_id(&mut self, t: u32, env: u32) -> Option<u32> {
        let r = self.trng(t);
        if r == 0 {
            return None;
        }
        if r > 63 {
            return self.used_env_id_wide(t, env);
        }
        let u = self.used_mask(t) & ((1u64 << r) - 1);
        // milestone 12: the id depends on (mask, environment) only; a lossy
        // direct-mapped memo of it, stamped by session generation
        let slot = if true {
            let i = (hmix(u, env as u64) >> 20) as usize & UDM_MASK;
            cn!(P_UDM);
            let x = self.udm[i];
            if x[0] == u as u32 && x[1] == (u >> 32) as u32 && x[2] == env && x[3] == self.cgen {
                cn!(978);
                return Some(x[4]);
            }
            i
        } else {
            0
        };
        let mut key: smallvec::SmallVec<[u32; 8]> = smallvec::SmallVec::new();
        key.push(u as u32);
        key.push((u >> 32) as u32);
        let mut m = u;
        while m != 0 {
            let i = m.trailing_zeros();
            key.push(self.env_at(env, i)?);
            m &= m - 1;
        }
        let id = self.uenv_id(key);
        if true {
            self.udm[slot] = [u as u32, (u >> 32) as u32, env, self.cgen, id];
        }
        Some(id)
    }

    /// Milestone 36: the id of used-entries key `key` (counted, not the
    /// map's length: a rollback removes entries).
    fn uenv_id(&mut self, key: smallvec::SmallVec<[u32; 8]>) -> u32 {
        if let Some(&id) = self.uenv_map.get(&key) {
            return id;
        }
        let id = self.uenv_next;
        self.uenv_next += 1;
        if self.reg_vm != 0 {
            self.undo.push(Undo::Uenv(key[..].into()));
        }
        self.uenv_map.insert(key, id);
        id
    }

    /// Milestone 29: `used_env_id` past 63 entries, for a term reading at
    /// most WIDE_K of them (contexts of hundreds of binders, FLT; heavy
    /// declarations only): the key
    /// is the variables read and their entries, after a leading [0, 0] (a
    /// narrow key's mask is never 0).
    #[cold]
    #[inline(never)]
    fn used_env_id_wide(&mut self, t: u32, env: u32) -> Option<u32> {
        // only in very heavy declarations, past WIDE_TICKS: in lighter ones
        // (cedar, con-leche) their results, carrying other contexts'
        // environments, cost more later than they saved (+0.2..0.4%)
        if self.ticks.wrapping_sub(self.decl_ticks0) < WIDE_TICKS {
            return None;
        }
        let vs = self.wide_vars(t)?;
        let mut key: smallvec::SmallVec<[u32; 8]> = smallvec::SmallVec::new();
        key.push(0);
        key.push(0);
        key.push(vs.len() as u32);
        for &i in vs.iter() {
            key.push(i);
        }
        for &i in vs.iter() {
            key.push(self.env_at(env, i)?);
        }
        Some(self.uenv_id(key))
    }

    /// Milestone 29: the loose variables of `t` (range past 63), sorted, if
    /// there are at most WIDE_K and the walk stays within WIDE_NODES nodes;
    /// MAIN terms memoized (block ids are reused across sessions and the
    /// scratch arena, so theirs are walked each time).
    fn wide_vars(&mut self, t: u32) -> Option<SmallVec16> {
        if t < self.mlen {
            if let Some(x) = self.wide_main.get(&t) {
                return x.clone();
            }
        } else if self.scratch {
            return None;
        } else if let Some(x) = self.wide_blk.get(&t) {
            return x.clone();
        }
        let mut out = SmallVec16::new();
        let mut budget = WIDE_NODES;
        let r = if self.wide_walk(t, 0, &mut out, &mut budget) { out.sort_unstable(); out.dedup(); Some(out) } else { None };
        if t < self.mlen {
            if self.wide_main.len() > self.uses_cap {
                self.wide_main = FxHashMap::default();
            }
            self.wide_main.insert(t, r.clone());
        } else {
            self.wide_blk.insert(t, r.clone());
        }
        r
    }

    /// Adds the loose variables of `t` under `depth` binders to `out`;
    /// false past WIDE_K variables or the node budget.
    fn wide_walk(&mut self, t: u32, depth: u32, out: &mut SmallVec16, budget: &mut u32) -> bool {
        let r = self.trng(t);
        if r <= depth {
            return true;
        }
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        if r <= 63 {
            // the used mask (a superset of what is read: sound for a key)
            let mut m = self.used_mask(t) & ((1u64 << r) - 1) & !((1u64 << depth) - 1);
            while m != 0 {
                let i = m.trailing_zeros();
                m &= m - 1;
                if !out.contains(&(i - depth)) {
                    if out.len() >= WIDE_K {
                        return false;
                    }
                    out.push(i - depth);
                }
            }
            return true;
        }
        let k = self.tk(t);
        match k {
            BVAR => {
                let i = self.tp(t) - depth;
                if !out.contains(&i) {
                    if out.len() >= WIDE_K {
                        return false;
                    }
                    out.push(i);
                }
                true
            }
            APP => self.wide_walk(self.ta(t), depth, out, budget) && self.wide_walk(self.tb(t), depth, out, budget),
            LET => {
                let lb = self.let_body(t);
                self.wide_walk(self.ta(t), depth, out, budget) && self.wide_walk(self.tb(t), depth, out, budget) && self.wide_walk(lb, depth + 1, out, budget)
            }
            k if is_lam(k) || is_pi(k) => self.wide_walk(self.ta(t), depth, out, budget) && self.wide_walk(self.tb(t), depth + 1, out, budget),
            PROJ => self.wide_walk(self.ta(t), depth, out, budget),
            _ => false,
        }
    }

    pub fn uses_var(&mut self, t: u32, d: u32) -> bool {
        let r = self.trng(t);
        if r <= d {
            return false;
        }
        if d < 63 {
            let u = self.used_mask(t);
            return u & (1 << d) != 0;
        }
        // milestone 51: exact up to #125 (r > d >= 63)
        if d < 126 {
            return self.used_hi(t) & (1 << (d - 63)) != 0;
        }
        let memo = if t < self.mlen { &self.uses_main } else { &self.uses0_memo };
        if let Some(&x) = memo.get(&(t, d)) {
            return x;
        }
        // milestone 42: one frame per level of the term: past half the
        // stack, an explicit stack (a term nests as deep as the file says)
        if self.stack_half() {
            return self.uses_var_iter(t, d);
        }
        let k = self.tk(t);
        let x = match k {
            BVAR => self.tp(t) == d,
            APP => self.uses_var(self.ta(t), d) || self.uses_var(self.tb(t), d),
            LET => {
                let lb = self.let_body(t);
                self.uses_var(self.ta(t), d) || self.uses_var(self.tb(t), d) || self.uses_var(lb, d + 1)
            }
            PROJ => self.uses_var(self.ta(t), d),
            k if is_lam(k) || is_pi(k) => self.uses_var(self.ta(t), d) || self.uses_var(self.tb(t), d + 1),
            _ => false,
        };
        if t < self.mlen {
            // milestone 37: bounded as `wide_main` is (it grew without
            // bound: 1.5 GB per worker by the end of FLT at 4 workers, and
            // with every worker the same file's terms again)
            if self.uses_main.len() >= self.uses_cap {
                self.uses_main = Default::default();
                self.stats.memo_flushes += 1;
            }
            self.uses_main.insert((t, d), x);
        } else {
            self.uses0_memo.insert((t, d), x);
        }
        x
    }
    /// uses_var with an explicit stack (reads the memos, writes none).
    #[inline(never)]
    fn uses_var_iter(&mut self, t: u32, d: u32) -> bool {
        let mut st: Vec<(u32, u32)> = vec![(t, d)];
        while let Some((t, d)) = st.pop() {
            if self.trng(t) <= d {
                continue;
            }
            if d < 63 {
                if self.used_mask(t) & (1 << d) != 0 {
                    return true;
                }
                continue;
            }
            if d < 126 {
                if self.used_hi(t) & (1 << (d - 63)) != 0 {
                    return true;
                }
                continue;
            }
            let memo = if t < self.mlen { &self.uses_main } else { &self.uses0_memo };
            if let Some(&x) = memo.get(&(t, d)) {
                if x {
                    return true;
                }
                continue;
            }
            match self.tk(t) {
                BVAR => {
                    if self.tp(t) == d {
                        return true;
                    }
                }
                APP => {
                    st.push((self.tb(t), d));
                    st.push((self.ta(t), d));
                }
                LET => {
                    st.push((self.let_body(t), d + 1));
                    st.push((self.tb(t), d));
                    st.push((self.ta(t), d));
                }
                PROJ => st.push((self.ta(t), d)),
                k if is_lam(k) || is_pi(k) => {
                    st.push((self.tb(t), d + 1));
                    st.push((self.ta(t), d));
                }
                _ => {}
            }
        }
        false
    }

    pub fn proj_type(&mut self, sv: V, st: V, idx: u32, sname: u32) -> R<V> {
        let st = self.whnf(st)?;
        let Some((irow, illr, ispine)) = self.const_head(st) else { return reject("projection of non-structure") };
        if self.canon_of_row(irow) != self.env.canon(sname) {
            return reject("projection structure name mismatch");
        }
        let Some((np, ni, ctors, _)) = self.ind_info(irow) else { return reject("projection of non-inductive") };
        if ctors.len() != 1 {
            return reject("projection of a type that is not structure-like");
        }
        let c0 = ctors[0];
        let Some(args) = self.app_args(ispine) else { return reject("projection: bad structure type") };
        if args.len() != np as usize + ni as usize {
            return reject("projection: wrong number of structure type arguments");
        }
        let crow = self.row_of(c0);
        if crow == NONE {
            return reject("projection: missing constructor");
        }
        if self.ll_get(illr).len() != self.consts[crow as usize].lparams.len() {
            return reject("projection: universe levels");
        }
        let cls = self.mk_ls(crow, illr);
        let cty = self.consts[crow as usize].ty;
        let mut r = self.eval(cty, EMPTY, cls)?;
        for i in 0..np as usize {
            let w = self.whnf(r)?;
            if !self.is_pi_val(w) {
                return reject("projection: constructor type");
            }
            r = self.bind_body(w, args[i])?;
        }
        // A structure whose inductive lives in Prop (at generic parameters) is
        // a proposition even when this instance only shows it through a
        // chain of equalities that are not transitive (proof irrelevance).
        let is_prop = self.is_prop_type(st)? || self.ind_in_prop(irow)?;
        for i in 0..idx {
            let w = self.whnf(r)?;
            if !self.is_pi_val(w) {
                return reject("projection index out of range");
            }
            if self.pi_dependent(w) && is_prop {
                let d = self.bind_dom(w)?;
                if !self.is_prop_type(d)? {
                    return reject("projection from a proposition to data a later field depends on");
                }
            }
            let p = self.proj_val(sv, i, sname)?;
            r = self.bind_body(w, p)?;
        }
        let w = self.whnf(r)?;
        if !self.is_pi_val(w) {
            return reject("projection index out of range");
        }
        let res = self.bind_dom(w)?;
        if is_prop && !self.is_prop_type(res)? {
            return reject("projection of data out of a proposition");
        }
        Ok(res)
    }

    /// Does inductive `row` live in Prop, for generic parameters and indices?
    pub fn ind_in_prop(&mut self, row: u32) -> R<bool> {
        if let Some(&b) = self.prop_ind.get(&row) {
            return Ok(b);
        }
        let Some((np, ni, _, _)) = self.ind_info(row) else { return Ok(false) };
        let ty = self.consts[row as usize].ty;
        let ps: Vec<u32> = self.consts[row as usize].lparams.iter().map(|&n| self.env.canon(n)).collect();
        let lv: Vec<u32> = ps.iter().map(|&p| self.lv.param(p)).collect();
        let llr = self.ll_intern(&lv);
        let ls = self.mk_ls(row, llr);
        let mut t = self.eval(ty, EMPTY, ls)?;
        for _ in 0..(np + ni) {
            let w = self.whnf(t)?;
            if !self.is_pi_val(w) {
                self.prop_ind.insert(row, false);
                return Ok(false);
            }
            let d = self.bind_dom(w)?;
            let x = self.fresh(d)?;
            t = self.bind_body(w, x)?;
        }
        let w = self.whnf(t)?;
        let b = matches!(self.val(w), Val::Sort(l) if self.lv.zeroish(l));
        self.prop_ind.insert(row, b);
        Ok(b)
    }

    /// The type of a value.
    #[inline(always)]
    /// The value of Pi term `pt` in (`pe`, `pls`): what eval makes of it.
    fn pi_value(&mut self, pt: u32, pe: u32, pls: u32) -> R<V> {
        let pe = self.prune(pt, pe);
        self.intern(Val::Clo { term: pt, env: pe, ls: pls })
    }
    pub fn infer_val(&mut self, v: V) -> R<V> {
        let m = self.memo_at(v).infer;
        if m != NONE {
            return Ok(m);
        }
        self.infer_val_miss(v)
    }
    #[inline(never)]
    fn infer_val_miss(&mut self, v: V) -> R<V> {
        self.tick()?;
        let r = match self.val(v) {
            Val::Thunk { term, env, ls } => self.infer(term, env, ls, false)?,
            Val::Sort(l) => {
                let s = self.lv.succ(l);
                self.intern(Val::Sort(s))?
            }
            Val::Lit(i) => {
                let nat = matches!(self.lit(i), LitVal::Nat(_));
                self.lit_type(nat)?
            }
            Val::Clo { term, env, ls } => {
                if is_lam(self.tk(term)) {
                    self.intern(Val::CloI { term, env, ls })?
                } else {
                    self.infer(term, env, ls, false)?
                }
            }
            Val::CloI { term, env, ls } => {
                let d = self.thunk(self.ta(term), env, ls)?;
                let ds = self.infer_val(d)?;
                let l1 = self.sort_of(ds, "binder domain")?;
                let d0 = self.vdepth;
                let reused = self.reuse_var(v, d);
                let x = match reused {
                    Some(x) => x,
                    None => self.open_var(d)?,
                };
                let e = self.push_env(x, env);
                let bt = self.infer(self.tb(term), e, ls, false);
                let bs = match bt {
                    Ok(bt) => self.infer_val(bt),
                    Err(e) => Err(e),
                };
                self.close_var(x, d0);
                let bs = bs?;
                let l2 = self.sort_of(bs, "body type")?;
                let l = self.lv.imax(l1, l2);
                self.intern(Val::Sort(l))?
            }
            Val::Neu { head, spine } => {
                let mut t = match head {
                    Head::FVar(i) => self.fv_ty[i as usize],
                    Head::Const(row, llr) => {
                        let ls = self.mk_ls(row, llr);
                        let ty = self.consts[row as usize].ty;
                        self.eval(ty, EMPTY, ls)?
                    }
                    Head::Stuck(x) => self.infer_val(x)?,
                };
                // milestone 23: the type walked as a syntactic Pi (term,
                // environment, levels) while it is one, as infer_core's
                // application case does: no closure value per argument;
                // the elims read in place (a spine never changes)
                let mut cur: Option<(u32, u32, u32)> = None;
                let n = self.sp.len(spine);
                for i in 0..n {
                    let e = self.sp.args(spine)[i];
                    if e & PROJ_BIT != 0 {
                        if let Some((pt, pe, pls)) = cur.take() {
                            t = self.pi_value(pt, pe, pls)?;
                        }
                        let (sname, idx) = self.projs[(e & !PROJ_BIT) as usize];
                        let pv = self.neu_prefix(head, spine, i)?;
                        t = self.proj_type(pv, t, idx, sname)?;
                    } else {
                        let (pt, pe, pls) = match cur {
                            Some(x) => x,
                            None => {
                                let w = self.whnf(t)?;
                                match self.val(w) {
                                    Val::Clo { term, env, ls } if is_pi(self.tk(term)) => (term, env, ls),
                                    _ => {
                                        if !self.is_pi_val(w) {
                                            return reject("function expected (value)");
                                        }
                                        t = self.bind_body(w, e)?;
                                        continue;
                                    }
                                }
                            }
                        };
                        let b = self.tb(pt);
                        let e2 = self.push_for(e, pe, b);
                        if is_pi(self.tk(b)) {
                            cur = Some((b, e2, pls));
                        } else {
                            cur = None;
                            t = self.eval(b, e2, pls)?;
                        }
                    }
                }
                if let Some((pt, pe, pls)) = cur {
                    t = self.pi_value(pt, pe, pls)?;
                }
                t
            }
        };
        self.memo_w(v).infer = r;
        Ok(r)
    }

    // -----------------------------------------------------------------------
    // Definitional equality

    fn ident(&self, v: V) -> [u32; 3] {
        match self.val(v) {
            Val::Thunk { term, env, ls } => [term, env, ls],
            Val::Clo { term, env, ls } => [term, env, ls],
            Val::CloI { term, env, ls } => [term, env, ls | PROJ_BIT],
            _ => [v, NONE, NONE],
        }
    }

    /// Milestone 23: `eq_cache` holds both the definitional equalities
    /// found (EQ_KNOWN, EQ_TRUE) and the pairs `same_val` found
    /// structurally different (EQ_SAME_NO, the old `same_no` set), cleared
    /// together at a session end as the two tables were.
    #[inline(always)]
    fn eq_get(&self, pk: u64) -> Option<bool> {
        match self.eq_cache.get(&pk) {
            Some(&f) if f & EQ_KNOWN != 0 => Some(f & EQ_TRUE != 0),
            _ => None,
        }
    }
    #[inline(always)]
    fn eq_put(&mut self, pk: u64, r: bool) {
        self.ulog(Undo::Eq(pk));
        let f = self.eq_cache.entry(pk).or_insert(0);
        *f = (*f & EQ_SAME_NO) | EQ_KNOWN | if r { EQ_TRUE } else { 0 };
    }
    /// Milestone 15: identity inlined at the call sites.
    #[inline(always)]
    pub fn defeq(&mut self, a: V, b: V) -> R<bool> {
        cn!(952);
        if a == b {
            return Ok(true);
        }
        self.defeq_ne(a, b)
    }
    /// Milestone 45: a comparison past `deep_at` bytes of stack of two
    /// values without free variables whose pair is not cached is handed up
    /// (`Stop::DeepDefeq`) to the declaration, worked out there from a
    /// shallow stack, cached (`eq_cache` keeps both outcomes), and the
    /// declaration tried again. CFSG's RG.eq compares a 913 K-character
    /// string literal with String.ofList of a list literal: one nested
    /// comparison per element (each tail is the last argument of a cons),
    /// ~630 B of stack each on arm64, more on x86 with PGO. Not inside a
    /// probe (its budget belongs to the probe's caller).
    #[inline(never)]
    fn defeq_ne(&mut self, a: V, b: V) -> R<bool> {
        if self.deep_zone && self.probe_on && self.pdead_off {
            let x = 0u8;
            let sp = std::hint::black_box(&x) as *const u8 as usize;
            if self.stack_base.saturating_sub(sp) > self.deep_at {
                self.dove_deep = true;
                self.probe_end = self.ticks.wrapping_add(1);
                self.tick_alarm = self.probe_end;
                return Err(Stop::Budget);
            }
        }
        if self.deep_zone && !self.probe_on {
            let x = 0u8;
            let sp = std::hint::black_box(&x) as *const u8 as usize;
            if self.stack_base.saturating_sub(sp) > self.deep_at {
                let pk = if a < b { (a as u64) << 32 | b as u64 } else { (b as u64) << 32 | a as u64 };
                if self.eq_get(pk).is_none() && !self.has_fvar(a) && !self.has_fvar(b) {
                    self.deep_eq = (a, b);
                    return Err(Stop::DeepDefeq);
                }
            }
        }
        if dstack_on() {
            dstack_push(b'D', a, b, self.ticks);
            let r = self.defeq_ne1(a, b);
            dstack_pop();
            return r;
        }
        self.defeq_ne1(a, b)
    }
    fn defeq_ne1(&mut self, a: V, b: V) -> R<bool> {
        if KNOBS && TRACE.with(|t| t.get()) > 0 {
            let d = TDEPTH.with(|t| { let x = t.get(); t.set(x + 1); x });
            let t0 = self.ticks;
            let lim = TRACE.with(|t| t.get());
            if d < lim {
                eprintln!("{:>2}{} DEQ> {} =?= {}", d, " ".repeat(d as usize), self.vshow(a, 3), self.vshow(b, 3));
            }
            let r = self.defeq_ne0(a, b);
            TDEPTH.with(|t| t.set(d));
            let dt = self.ticks.wrapping_sub(t0);
            if d < lim || dt > 200_000 {
                eprintln!("{:>2}{} DEQ< {:?} ticks {} : {} =?= {}", d, " ".repeat(d as usize), r.as_ref().ok(), dt, self.vshow(a, 3), self.vshow(b, 3));
            }
            return r;
        }
        self.defeq_ne0(a, b)
    }
    /// knobs SK_TRACE: a value as text (depth-limited)
    fn vshow(&self, v: V, d: u32) -> String {
        if d == 0 { return "_".into(); }
        let tn = |w: &Self, t: u32| -> String {
            let mut h = t; let mut n = 0;
            while w.tk(h) == APP { h = w.ta(h); n += 1; }
            let hn = if w.tk(h) == CONST { w.env.name_str(w.ta(h)) } else { format!("k{}", w.tk(h)) };
            format!("{hn}/{n}")
        };
        match self.val(v) {
            Val::Sort(_) => "Sort".into(),
            Val::Lit(i) => match self.lit(i) { LitVal::Nat(n) => { let s = n.to_string(); if s.len() > 12 { format!("{}..({}d)", &s[..6], s.len()) } else { s } }, LitVal::Str(_) => "\"..\"".into() },
            Val::Clo { term, .. } => format!("λ[{}]", tn(self, term)),
            Val::CloI { term, .. } => format!("λI[{}]", tn(self, term)),
            Val::Thunk { term, .. } => format!("T[{}]", tn(self, term)),
            Val::Neu { head, spine } => {
                let h = match head { Head::Const(r, _) => self.env.name_str(self.consts[r as usize].name), Head::FVar(i) => format!("x{i}"), Head::Stuck(x) => format!("({})", self.vshow(x, d - 1)) };
                let args: Vec<String> = self.sp.args(spine).iter().map(|&e| if e & PROJ_BIT != 0 { ".p".into() } else { self.vshow(e, d - 1) }).collect();
                if args.is_empty() { h } else { format!("({} {})", h, args.join(" ")) }
            }
        }
    }
    fn defeq_ne0(&mut self, a: V, b: V) -> R<bool> {
        self.tick()?;
        if STATS { self.stats.defeq_calls += 1; }
        cn!(940);
        let ia = self.ident(a);
        let ib = self.ident(b);
        if ia == ib {
            cn!(941);
            return Ok(true);
        }
        if let (Val::Neu { head: h1, spine: s1 }, Val::Neu { head: h2, spine: s2 }) = (self.val(a), self.val(b)) {
            if h1 == h2 && s1 == s2 {
                cn!(942);
                return Ok(true);
            }
        }
        let key = [ia[0], ia[1], ia[2], ib[0], ib[1], ib[2]];
        let pk = if a < b { (a as u64) << 32 | b as u64 } else { (b as u64) << 32 | a as u64 };
        if self.probe_on && !self.pdead_off {
            if let Some(&f) = self.eq_cache.get(&pk) {
                if f & (EQ_KNOWN | EQ_PDEAD) == EQ_PDEAD {
                    self.stats.probe[4] += 1;
                    // every later tick of this probe stops too
                    self.probe_end = self.ticks.wrapping_add(1);
                    self.tick_alarm = self.probe_end;
                    return Err(Stop::Budget);
                }
            }
        }
        if let Some(r) = self.eq_get(pk) {
            cn!(943);
            if STATS { self.stats.defeq_cache_hits += 1; }
            if ia[0] < self.mlen && ib[0] < self.mlen {
                if STATS { self.stats.eq_hits_main += 1; }
            } else {
                if STATS { self.stats.eq_hits_arena += 1; }
            }
            return Ok(r);
        }
        let closed = ia[1] == EMPTY
            && ib[1] == EMPTY
            && ia[0] < self.mlen
            && ib[0] < self.mlen
            && matches!(self.val(a), Val::Thunk { .. } | Val::Clo { .. } | Val::CloI { .. })
            && matches!(self.val(b), Val::Thunk { .. } | Val::Clo { .. } | Val::CloI { .. });
        if closed {
            cn!(944);
            if let Some(&d) = self.eqp.get(&key) {
                if d < self.cur_decl {
                    cn!(945);
                    self.stats.eqp_hits += 1;
                    self.eq_put(pk, true);
                    return Ok(true);
                }
            }
        }
        // milestone 12 (SK_ENTRY_FIRST): the structural walk before the
        // names machinery; a pair it finds equal needs no names
        let walked = true;
        if walked {
            let r = self.closure_congr(a, b);
            if r? {
                cn!(950);
                if closed && self.cur_decl != u32::MAX {
                    self.stats.eqp_stored += 1;
                    self.eqp.insert(key, self.cur_decl);
                    self.eqp.insert([ib[0], ib[1], ib[2], ia[0], ia[1], ia[2]], self.cur_decl);
                }
                self.eq_put(pk, true);
                return Ok(true);
            }
        }
        let mut nkey = u64::MAX;
        let mut pkey2 = u64::MAX;
        let p2 = self.p2();
        // milestone 8: closed values are named in every declaration, and
        // what was found about a pair of closed names is kept across
        // declarations (Pestka's closed pairs, both outcomes)
        // Outside heavy declarations a pair is named only when a pair with
        // the same heads was kept (`peq_heads`), and kept only when it cost
        // `peq_min` unfoldings or more.
        // both closed first (remembered per value): most pairs have a
        // free variable, and their heads are never looked at
        let both_closed = !self.has_fvar(a) && !self.has_fvar(b);
        cn!(946);
        if both_closed { cn!(947); }
        let hk = if both_closed { self.head_pair(a, b) } else { u64::MAX };
        let pn = !p2 && hk != u64::MAX && self.nm.peq_heads.contains(&hk);
        if p2 || pn {
            cn!(948);
            if let (Some(na), Some(nb)) = (self.name_v(a), self.name_v(b)) {
                if na == nb {
                    // one term: equal
                    self.nm.hits[4] += 1;
                    cn!(949);
                    self.eq_put(pk, true);
                    return Ok(true);
                }
                let k = if na < nb { ((na as u64) << 32) | nb as u64 } else { ((nb as u64) << 32) | na as u64 };
                if p2 {
                    if let Some(&r) = self.nm.eq.get(&k) {
                        self.nm.hits[4] += 1;
                        cn!(949);
                        self.eq_put(pk, r);
                        return Ok(r);
                    }
                    nkey = k;
                }
                if self.nm.closed(na) && self.nm.closed(nb) {
                    if let Some(&x) = self.nm.peq.get(&k) {
                        if ((x >> 1) as u32) < self.cur_decl {
                            self.nm.phits += 1;
                            cn!(949);
                            let r = x & 1 != 0;
                            self.eq_put(pk, r);
                            return Ok(r);
                        }
                    }
                    pkey2 = k;
                }
            }
        }
        let u0 = self.stats.unfolds;
        let r = if walked { Ok(false) } else { self.closure_congr(a, b) };
        let r = match r {
            Ok(true) => { cn!(950); Ok(true) }
            Ok(false) => {
                cn!(951);
                self.defeq_core(a, b)
            }
            Err(e) => Err(e),
        };
        if self.probe_on && matches!(r, Err(Stop::Budget)) {
            self.ulog(Undo::Eq(pk));
            *self.eq_cache.entry(pk).or_insert(0) |= EQ_PDEAD;
        }
        let r = r?;
        if closed && r && self.cur_decl != u32::MAX {
            // definitional equality is preserved when the environment grows
            self.stats.eqp_stored += 1;
            self.eqp.insert(key, self.cur_decl);
            self.eqp.insert([ib[0], ib[1], ib[2], ia[0], ia[1], ia[2]], self.cur_decl);
        }
        // both outcomes: within a declaration the answer is deterministic
        self.eq_put(pk, r);

        if nkey != u64::MAX {
            self.nm.eq.insert(nkey, r);
        }
        if hk != u64::MAX && pkey2 == u64::MAX && !p2 && !pn && self.stats.unfolds - u0 >= 1 && self.cur_decl != u32::MAX && self.safety == 0 {
            if let (Some(na), Some(nb)) = (self.name_v(a), self.name_v(b)) {
                if self.nm.closed(na) && self.nm.closed(nb) && na != nb {
                    pkey2 = if na < nb { ((na as u64) << 32) | nb as u64 } else { ((nb as u64) << 32) | na as u64 };
                }
            }
        }
        if pkey2 != u64::MAX && self.cur_decl != u32::MAX && self.safety == 0 && !self.scratch && (r || self.stats.known_miss == self.known_miss0) && self.stats.unfolds - u0 >= 1 {
            self.nm.pstored += 1;
            self.nm.peq.insert(pkey2, ((self.cur_decl as u64) << 1) | r as u64);
            self.nm.peq_heads.insert(hk);
        }
        Ok(r)
    }

    /// A cheap key of a pair's heads (unordered): constant rows of neutral
    /// values and of the terms of thunks and closures, else kinds.
    fn head_pair(&self, a: V, b: V) -> u64 {
        let neu_only = false;
        let h = |w: &Self, v: V| -> u32 {
            match w.val(v) {
                Val::Neu { head: Head::Const(r, _), .. } => r,
                _ if neu_only => u32::MAX,
                Val::Thunk { term, .. } | Val::Clo { term, .. } | Val::CloI { term, .. } => {
                    let mut f = term;
                    while w.tk(f) == APP {
                        f = w.ta(f);
                    }
                    if w.tk(f) == CONST { w.env.row(w.ta(f)) } else { 0xFFFF_FF00 | w.tk(f) as u32 }
                }
                Val::Neu { .. } => 0xFFFF_FE00,
                Val::Sort(_) => 0xFFFF_FD00,
                Val::Lit(_) => 0xFFFF_FC00,
            }
        };
        let (x, y) = (h(self, a), h(self, b));
        if x == u32::MAX || y == u32::MAX {
            return u64::MAX;
        }
        if x < y { ((x as u64) << 32) | y as u64 } else { ((y as u64) << 32) | x as u64 }
    }

    /// Two closures or thunks of the same term (same level substitution):
    /// equal when the environment entries the term uses are congruent
    /// (congruence of substitution). Only a shortcut: `false` decides
    /// nothing. Like Pestka's quickParts (CongruenceAfterSteps), the
    /// entries are compared by identity and by equalities already found,
    /// never by a definitional equality check of their own: an entry that
    /// is a proof would otherwise have its proposition compared with the
    /// other's, work the comparison after it (which skips proof arguments)
    /// never needs.
    fn closure_congr(&mut self, a: V, b: V) -> R<bool> {
        // at the entry of every comparison: a short walk only
        // Milestone 20: not between two lambdas of different terms.
        // They go to binder_defeq (`quick`) at once, which evaluates
        // both bodies under one variable into canonical values;
        // walking them first (bodies at different term ids,
        // environments of 30-40 entries) cost 0.4..0.75% of all
        // instructions on every corpus and decided little (data/m20).
        // Two pis are still walked (SK_CLO_PI=1 skips them too: etale,
        // std, con-leche gain 0.4..0.6% more, cedar loses 0.7%), and
        // closures of one term (their environments' entries in step).
        // Leaving a shortcut out never changes an answer.
        if let (Val::Clo { term: ta, .. } | Val::CloI { term: ta, .. }, Val::Clo { term: tb, .. } | Val::CloI { term: tb, .. }) = (self.val(a), self.val(b)) {
            if ta != tb && is_lam(self.tk(ta)) {
                return Ok(false);
            }
        }
        // milestone 21: once the declaration's structural walks have
        // spent walk_waste nodes on pairs they did not find equal, two
        // neutral values of one head constant and spine length go to
        // lazy delta at once (same head: arguments first, each pair with
        // its own entry walk). colim's heavy declaration walked 1.4 M
        // nodes that decided nothing.
        if self.walk_wasted > WALK_WASTE {
            if let (Val::Neu { head: Head::Const(r1, _), spine: sa }, Val::Neu { head: Head::Const(r2, _), spine: sb }) = (self.val(a), self.val(b)) {
                if r1 == r2 && self.sp.len(sa) == self.sp.len(sb) {
                    return Ok(false);
                }
            }
        }
        let f = self.same_fuel;
        self.same_fuel = 16384;
        let r = self.same_top(a, b);
        self.same_fuel = f;
        Ok(r)
    }

    /// Structural equality of two values (Lean's and Pestka's `==` before
    /// any reduction): the terms of thunks and closures compared node by
    /// node, a bound variable outside the term's own binders standing for
    /// its environment entry; neutral values by head and spine; a forced
    /// thunk by its value. Identical or already found equal parts are equal.
    /// Only a shortcut: `false` decides nothing. `fuel` bounds the walk.
    fn same_val(&mut self, a: V, b: V, fuel: &mut u32) -> bool {
        if a == b {
            return true;
        }
        let pk = if a < b { (a as u64) << 32 | b as u64 } else { (b as u64) << 32 | a as u64 };
        // milestone 23: one probe for both facts; a pair found not
        // definitionally equal is not structurally equal either
        if let Some(&f) = self.eq_cache.get(&pk) {
            if f & EQ_KNOWN != 0 {
                return f & EQ_TRUE != 0;
            }
            if f & EQ_SAME_NO != 0 {
                return false;
            }
        }
        if *fuel == 0 {
            return false;
        }
        let r = self.same_val_walk(a, b, fuel);
        if r {
            // structurally equal: definitionally equal, for the declaration
            self.eq_put(pk, true);
        } else if *fuel > 0 {
            // a decided difference (not one that ran out of fuel)
            self.ulog(Undo::Eq(pk));
            *self.eq_cache.entry(pk).or_insert(0) |= EQ_SAME_NO;
        }
        r
    }

    fn same_val_walk(&mut self, a: V, b: V, fuel: &mut u32) -> bool {
        *fuel -= 1;
        let (va, vb) = (self.val(a), self.val(b));
        match (va, vb) {
            (Val::Thunk { term: ta, env: ea, ls: la }, Val::Thunk { term: tb, env: eb, ls: lb }) => {
                self.same_term(ta, ea, la, tb, eb, lb, 0, fuel)
            }
            (Val::Clo { term: ta, env: ea, ls: la }, Val::Clo { term: tb, env: eb, ls: lb })
            | (Val::CloI { term: ta, env: ea, ls: la }, Val::CloI { term: tb, env: eb, ls: lb }) => self.same_term(ta, ea, la, tb, eb, lb, 0, fuel),
            (Val::Thunk { .. }, _) | (_, Val::Thunk { .. }) => {
                // a forced thunk by its value
                let fa = if let Val::Thunk { .. } = va { self.memo_at(a).whnf } else { a };
                let fb = if let Val::Thunk { .. } = vb { self.memo_at(b).whnf } else { b };
                if fa == NONE || fb == NONE || (fa == a && fb == b) {
                    return false;
                }
                self.same_val(fa, fb, fuel)
            }
            (Val::Neu { head: ha, spine: sa }, Val::Neu { head: hb, spine: sb }) => {
                let heads = match (ha, hb) {
                    (Head::Stuck(x), Head::Stuck(y)) => self.same_val(x, y, fuel),
                    (Head::Const(r1, l1), Head::Const(r2, l2)) => r1 == r2 && self.levels_equiv(l1, l2),
                    _ => ha == hb,
                };
                if !heads {
                    return false;
                }
                if sa == sb {
                    return true;
                }
                let n = self.sp.len(sa);
                if n != self.sp.len(sb) {
                    return false;
                }
                // last elims first
                for i in (0..n).rev() {
                    let (ex, ey) = (self.sp.args(sa)[i], self.sp.args(sb)[i]);
                    if ex != ey {
                        if ex & PROJ_BIT != 0 || ey & PROJ_BIT != 0 {
                            if ex & PROJ_BIT == 0 || ey & PROJ_BIT == 0 {
                                return false;
                            }
                            if self.projs[(ex & !PROJ_BIT) as usize].1 != self.projs[(ey & !PROJ_BIT) as usize].1 {
                                return false;
                            }
                        } else if !self.same_val(ex, ey, fuel) {
                            return false;
                        }
                    }
                }
                true
            }
            (Val::Lit(x), Val::Lit(y)) => x == y || self.lit(x) == self.lit(y),
            _ => false,
        }
    }

    /// Value `v` and term `t` in (`e`, `ls`) structurally equal (no binders
    /// of `t` around).
    fn same_vt(&mut self, v: V, t: u32, e: u32, ls: u32, fuel: &mut u32) -> bool {
        if *fuel == 0 {
            return false;
        }
        *fuel -= 1;
        let k = self.tk(t);
        if k == BVAR {
            let Ok(y) = self.env_get(e, self.tp(t)) else { return false };
            return self.same_val(v, y, fuel);
        }
        if let Val::Neu { head: Head::Const(..), .. } = self.val(v) {
            if true {
                // milestone 29: a value against a term, walked once per pair
                // (same_term's table; depth VT_MARK, never a real depth)
                let h = hmix(hmix(hmix(((t as u64) << 32) | v as u64, e as u64), ls as u64), VT_MARK as u64);
                let i = (h >> 20) as usize & TDM_MASK;
                let x = self.tdm[i];
                if x[0] == t && x[1] == v && x[2] == e && x[4] == ls && x[6] & 0x7fff_ffff == VT_MARK && x[7] == self.cgen {
                    let r = x[6] >> 31 != 0;
                    // release-da: every hit kept true walked again, true
                    // when that walk decides (a kept false only skips a
                    // shortcut: a thunk forced since may make it true)
                    #[cfg(debug_assertions)]
                    if r {
                        let mut f2 = 1u32 << 16;
                        let r2 = self.same_vt_neu(v, t, e, ls, &mut f2);
                        assert!(f2 == 0 || r2, "value-term memo: {v} against term {t} in {e}: kept true, walked false");
                    }
                    return r;
                }
                let r = self.same_vt_neu(v, t, e, ls, fuel);
                if r || *fuel > 0 {
                    self.tdm[i] = [t, v, e, 0, ls, 0, VT_MARK | (r as u32) << 31, self.cgen];
                }
                return r;
            }
            return self.same_vt_neu(v, t, e, ls, fuel);
        }
        match self.val(v) {
            Val::Thunk { term, env, ls: l } => self.same_term(term, env, l, t, e, ls, 0, fuel),
            Val::Clo { term, env, ls: l } => self.same_term(term, env, l, t, e, ls, 0, fuel),
            Val::Sort(l) => k == SORT && {
                let y = self.lsub(self.tp(t), ls);
                l == y || self.lv.equiv(l, y)
            },
            Val::Lit(i) => (k == NAT || k == STR) && self.lit(i) == self.lit(self.tp(t)),
            _ => false,
        }
    }

    /// Milestone 48: term `t` reads none of the `depth` innermost binders.
    fn reads_none_below(&mut self, t: u32, depth: u32) -> bool {
        (0..depth).all(|d| !self.uses_var(t, d))
    }
    /// Milestone 48: `env` with `depth` entries pushed (`v`, never read: the
    /// term evaluated in it reads none of them).
    fn pad_env(&mut self, v: V, env: u32, depth: u32) -> u32 {
        let mut e = env;
        for _ in 0..depth {
            e = self.push_env(v, e);
        }
        e
    }

    /// same_vt for a constant-headed neutral value `v`.
    fn same_vt_neu(&mut self, v: V, t: u32, e: u32, ls: u32, fuel: &mut u32) -> bool {
        let Val::Neu { head: Head::Const(r, l), spine } = self.val(v) else { return false };
        // t must be the constant applied to as many arguments
        let mut f = t;
        let mut args: SmallVec16 = SmallVec16::new();
        loop {
            let n = self.node(f);
            if n.kind != APP {
                break;
            }
            args.push(n.b);
            f = n.a;
        }
        if self.tk(f) != CONST || self.row_of(self.ta(f)) != r {
            return false;
        }
        let l2 = self.const_ll(f, ls);
        if !self.levels_equiv(l, l2) {
            return false;
        }
        // spine from last to first, args collected last first
        let n = self.sp.len(spine);
        if n != args.len() {
            return false;
        }
        for (k, &a) in args.iter().enumerate() {
            let x = self.sp.args(spine)[n - 1 - k];
            if x & PROJ_BIT != 0 || !self.same_vt(x, a, e, ls, fuel) {
                return false;
            }
        }
        true
    }

    /// Term `ta` in (`ea`, `la`) and term `tb` in (`eb`, `lb`) structurally
    /// equal, `depth` binders inside both.
    #[allow(clippy::too_many_arguments)]
    fn same_term(&mut self, ta: u32, ea: u32, la: u32, tb: u32, eb: u32, lb: u32, depth: u32, fuel: &mut u32) -> bool {
        if ta == tb && la == lb && (ea == eb || self.trng(ta) <= depth) {
            return true;
        }
        // a term DAG walked once per pair (Susz terms share subterms).
        // Milestone 17: a direct-mapped table, every field of the pair kept
        // whole and stamped with the generation (a lost entry is a walk
        // again); the hash map below only with SK_TDM=0 (knobs).
        if true {
            let h = hmix(hmix(hmix(((ta as u64) << 32) | tb as u64, ((ea as u64) << 32) | eb as u64), ((la as u64) << 32) | lb as u64), depth as u64);
            let i = (h >> 20) as usize & TDM_MASK;
            let e = self.tdm[i];
            if e[0] == ta && e[1] == tb && e[2] == ea && e[3] == eb && e[4] == la && e[5] == lb && e[6] & 0x7fff_ffff == depth && e[7] == self.cgen {
                return e[6] >> 31 != 0;
            }
            let r = self.same_term_walk(ta, ea, la, tb, eb, lb, depth, fuel);
            if r || *fuel > 0 {
                self.tdm[i] = [ta, tb, ea, eb, la, lb, depth | (r as u32) << 31, self.cgen];
            }
            return r;
        }
        let key = (((ta as u64) << 32) | tb as u64, ((ea as u64) << 32) | eb as u64, ((la as u64) << 40) ^ ((lb as u64) << 8) ^ depth as u64);
        if let Some(&r) = self.term_memo.get(&key) {
            return r;
        }
        let r = self.same_term_walk(ta, ea, la, tb, eb, lb, depth, fuel);
        if r || *fuel > 0 {
            if self.term_memo.len() >= (1 << 18) {
                // bounded: a big declaration starts the memo over
                self.term_memo.clear();
            }
            self.term_memo.insert(key, r);
        }
        r
    }

    #[allow(clippy::too_many_arguments)]
    fn same_term_walk(&mut self, ta: u32, ea: u32, la: u32, tb: u32, eb: u32, lb: u32, depth: u32, fuel: &mut u32) -> bool {
        if ta == tb && la == lb && (ea == eb || self.trng(ta) <= depth) {
            return true;
        }
        if *fuel == 0 {
            return false;
        }
        *fuel -= 1;
        if ta == tb && la == lb && depth == 0 {
            // one term: the entries it can reach, in step
            let n = self.trng(ta);
            if n <= 63 {
                // milestone 23: the used entries by the mask's bits, both
                // runs read once
                let (Some((sx, lx)), Some((sy, ly))) = (self.env_run(ea), self.env_run(eb)) else { return n == 0 };
                let mut m = self.used_mask(ta) & ((1u64 << n) - 1);
                while m != 0 {
                    let i = m.trailing_zeros();
                    m &= m - 1;
                    if i >= lx || i >= ly {
                        return false;
                    }
                    let (vx, vy) = (self.eslot(sx + lx - 1 - i), self.eslot(sy + ly - 1 - i));
                    if vx != vy && !self.same_val(vx, vy, fuel) {
                        return false;
                    }
                }
                return true;
            }
            for i in 0..n {
                if !self.uses_var(ta, i) {
                    continue;
                }
                let (Some(vx), Some(vy)) = (self.env_at(ea, i), self.env_at(eb, i)) else { return false };
                if vx != vy && !self.same_val(vx, vy, fuel) {
                    return false;
                }
            }
            return true;
        }
        let (na, nb) = (self.node(ta), self.node(tb));
        let k = na.kind;
        if k != nb.kind {
            // a variable standing for a value, against a term
            if depth == 0 {
                if k == BVAR {
                    let Ok(x) = self.env_get(ea, na.p) else { return false };
                    return self.same_vt(x, tb, eb, lb, fuel);
                }
                if nb.kind == BVAR {
                    let Ok(y) = self.env_get(eb, nb.p) else { return false };
                    return self.same_vt(y, ta, ea, la, fuel);
                }
                return false;
            }
            // milestone 48: under binders too, when the variable is one of
            // the environment's and the other term reads none of the
            // binders: that term in its environment with `depth` unread
            // entries pushed (CFSG's HNSchreier orbitTreeCheck_certificate:
            // `λ k _, (λ i, body) (0 + k)` against `λ k _, p (lo + k)`, `p`
            // and `lo` standing for those values; before, the two loops
            // were compared step by step, 1 140 000 nested comparisons)
            if k == BVAR && na.p >= depth && self.reads_none_below(tb, depth) {
                let Ok(x) = self.env_get(ea, na.p - depth) else { return false };
                let e2 = self.pad_env(x, eb, depth);
                return self.same_vt(x, tb, e2, lb, fuel);
            }
            if nb.kind == BVAR && nb.p >= depth && self.reads_none_below(ta, depth) {
                let Ok(y) = self.env_get(eb, nb.p - depth) else { return false };
                let e2 = self.pad_env(y, ea, depth);
                return self.same_vt(y, ta, e2, la, fuel);
            }
            return false;
        }
        match k {
            BVAR => {
                let (i, j) = (na.p, nb.p);
                if i < depth || j < depth {
                    return i == j;
                }
                let (Ok(x), Ok(y)) = (self.env_get(ea, i - depth), self.env_get(eb, j - depth)) else { return false };
                self.same_val(x, y, fuel)
            }
            SORT => {
                let (x, y) = (self.lsub(na.p, la), self.lsub(nb.p, lb));
                x == y || self.lv.equiv(x, y)
            }
            CONST => {
                if self.env.canon(na.a) != self.env.canon(nb.a) {
                    return false;
                }
                let (x, y) = (self.const_ll(ta, la), self.const_ll(tb, lb));
                self.levels_equiv(x, y)
            }
            APP => {
                self.same_term(na.a, ea, la, nb.a, eb, lb, depth, fuel)
                    && self.same_term(na.b, ea, la, nb.b, eb, lb, depth, fuel)
            }
            NAT | STR => self.lit(na.p) == self.lit(nb.p),
            PROJ => {
                na.b == nb.b
                    && self.same_term(na.a, ea, la, nb.a, eb, lb, depth, fuel)
            }
            LET => {
                let (ba, bb) = (self.let_body(ta), self.let_body(tb));
                self.same_term(na.a, ea, la, nb.a, eb, lb, depth, fuel)
                    && self.same_term(na.b, ea, la, nb.b, eb, lb, depth, fuel)
                    && self.same_term(ba, ea, la, bb, eb, lb, depth + 1, fuel)
            }
            k if is_lam(k) || is_pi(k) => {
                self.same_term(na.a, ea, la, nb.a, eb, lb, depth, fuel)
                    && self.same_term(na.b, ea, la, nb.b, eb, lb, depth + 1, fuel)
            }
            _ => false,
        }
    }



    fn quick(&mut self, a: V, b: V) -> R<Option<bool>> {
        if a == b {
            return Ok(Some(true));
        }
        match (self.val(a), self.val(b)) {
            (Val::Sort(x), Val::Sort(y)) => {
                let r = self.lv.equiv(x, y);
                Ok(Some(r))
            }
            (Val::Lit(x), Val::Lit(y)) => Ok(Some(x == y || self.lit(x) == self.lit(y))),
            (Val::Clo { .. } | Val::CloI { .. }, Val::Clo { .. } | Val::CloI { .. }) => {
                if (self.is_lam_val(a) && self.is_lam_val(b)) || (self.is_pi_val(a) && self.is_pi_val(b)) {
                    Ok(Some(self.binder_defeq(a, b)?))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    fn binder_defeq(&mut self, a: V, b: V) -> R<bool> {
        let da = self.bind_dom(a)?;
        let db = self.bind_dom(b)?;
        if !self.defeq(da, db)? {
            return Ok(false);
        }
        let d0 = self.vdepth;
        let reused = self.reuse_var(a, da).or_else(|| self.reuse_var(b, da));
        let x = match reused {
            Some(x) => x,
            None => self.open_var(da)?,
        };
        let r = (|| {
            let ba = self.bind_body(a, x)?;
            let bb = self.bind_body(b, x)?;
            self.defeq(ba, bb)
        })();
        self.close_var(x, d0);
        r
    }

    fn defeq_core(&mut self, a: V, b: V) -> R<bool> {
        let a = self.force(a)?;
        let b = self.force(b)?;
        if let Some(r) = self.quick(a, b)? {
            return Ok(r);
        }
        // milestone 41 (Pestka's ProofsComparedBeforeReduced): a side that
        // is a recursor into Prop applied up to its major premise is a proof;
        // whnf_core would reduce it first, and a K-like recursor checks its
        // major's type against the constructor's (a closed computation).
        // Proof irrelevance answers from the two types, which whnf_core
        // keeps up to definitional equality.
        if self.pfirst && (self.proof_by_rec(a) || self.proof_by_rec(b)) {
            self.stats.pfirst[0] += 1;
            let ta = self.infer_val(a)?;
            let tb = self.infer_val(b)?;
            let r = self.defeq(ta, tb)?;
            self.stats.pfirst[1] += r as u64;
            return Ok(r);
        }
        let a1 = self.whnf_core_c(a, true)?;
        let b1 = self.whnf_core_c(b, true)?;
        if a1 != a || b1 != b {
            if let Some(r) = self.quick(a1, b1)? {
                return Ok(r);
            }
            // Pestka's eqCoreWhnf: quickParts after whnfCore
            if self.quick_parts(a1, b1) {
                return Ok(true);
            }
        }
        if let Some(r) = self.proof_irrel(a1, b1)? {
            return Ok(r);
        }
        if self.ground && (self.vals.len() >= self.ground_at || self.ground_all) {
            if let Some(r) = self.ground_try(a1, b1)? {
                return Ok(r);
            }
        }
        let (a2, b2) = match self.lazy_delta(a1, b1)? {
            Ok(r) => return Ok(r),
            Err(p) => p,
        };
        // projections of the same field: the structures by lazy delta
        // first (Lean's lazy_delta_proj_reduction, Pestka's eqProj /
        // eqProjApp); congruence under a projection is never tried
        let proj = match self.proj_eq(a2, b2)? {
            Some(true) => return Ok(true),
            Some(false) => true,
            None => false,
        };
        if !proj && self.defeq_app(a2, b2)? {
            return Ok(true);
        }
        // now reduce projections fully; retry if that changed anything
        let a3 = self.whnf_core(a2)?;
        let b3 = self.whnf_core(b2)?;
        if a3 != a2 || b3 != b2 {
            return self.defeq(a3, b3);
        }
        if self.try_eta(a2, b2)? || self.try_eta(b2, a2)? {
            return Ok(true);
        }
        if self.try_eta_struct(a2, b2)? || self.try_eta_struct(b2, a2)? {
            return Ok(true);
        }
        if let Some(r) = self.string_expansion(a2, b2)? {
            return Ok(r);
        }
        if self.unit_like(a2, b2)? {
            return Ok(true);
        }
        Ok(false)
    }

    /// Values that are surely not proofs, read off declared types without
    /// inference (nano-lean's statically_not_proof; milestone 12 widens it to
    /// Pestka's notProofByHead, `SK_STATIC_NP=1` the milestone 11 test).
    fn surely_not_proof(&self, v: V) -> bool {
        let Val::Neu { head, spine } = self.val(v) else { return false };
        let n = self.sp.len(spine);
        if self.spine_has_proj(spine) {
            // x.i b1 .. bm: the field's type in the structure's constructor
            let el = self.sp.args(spine);
            let p = el.iter().rposition(|&e| e & PROJ_BIT != 0).unwrap();
            let (sname, idx) = self.projs[(el[p] & !PROJ_BIT) as usize];
            return self.proj_not_proof(sname, idx, n - 1 - p);
        }
        match head {
            Head::Const(row, _) => {
                // milestone 23: a function of (row, n) (the constant's
                // declared type read syntactically), direct-mapped for the
                // worker's life; a lost slot is only a walk again
                let i = (hmix(row as u64, n as u64) >> 20) as usize & TNP_MASK;
                let e = self.tnp_dm[i].get();
                if e[0] == row && e[1] == n as u32 && e[2] != 0 {
                    return e[2] == 2;
                }
                let r = self.tele_not_proof(&[], self.consts[row as usize].ty, n);
                self.tnp_dm[i].set([row, n as u32, 1 + r as u32]);
                r
            }
            Head::FVar(i) => {
                let ty = self.fv_ty[i as usize];
                match self.val(ty) {
                    Val::Sort(_) => n == 0,
                    Val::Neu { head: Head::Const(r, _), spine: ts } if n == 0 && !self.spine_has_proj(ts) => {
                        self.const_sort_not_zero(r, self.sp.len(ts))
                    }
                    // a Pi type: its term, variables beyond its own binders unknown
                    Val::Clo { term, .. } if is_pi(self.tk(term)) => self.tele_not_proof(&[], term, n),
                    _ => false,
                }
            }
            Head::Stuck(_) => false,
        }
    }
    /// Constant `r`'s type past `k` pis is a sort never zero at any levels:
    /// `r a1 .. ak` is a type whose elements are not proofs.
    fn const_sort_not_zero(&self, r: u32, k: usize) -> bool {
        let mut u = self.consts[r as usize].ty;
        for _ in 0..k {
            if !is_pi(self.tk(u)) {
                return false;
            }
            u = self.tb(u);
        }
        self.tk(u) == SORT && self.lv.is_not_zero(self.tp(u))
    }
    /// A head of type `ty` (a term under binders whose domains are `ctx`,
    /// outermost first) applied to `n` arguments is surely not a proof:
    /// past `n` pis the type is a sort (a type), or a pi (a function, a
    /// proof exactly when its codomain is one: read on), or a family whose
    /// sort is never zero at any levels: a constant whose type past its
    /// arguments ends in such a sort, or a variable bound by one of the pis
    /// (or by `ctx`) whose domain does (HAdd.hAdd ends in its gamma : Type u).
    /// A variable bound outside is unknown: false.
    fn tele_not_proof(&self, ctx: &[u32], ty: u32, n: usize) -> bool {
        let mut doms: SmallVec16 = SmallVec16::from_slice(ctx);
        let mut t = ty;
        for _ in 0..n {
            if !is_pi(self.tk(t)) {
                return false;
            }
            doms.push(self.ta(t));
            t = self.tb(t);
        }
        while is_pi(self.tk(t)) {
            doms.push(self.ta(t));
            t = self.tb(t);
        }
        if self.tk(t) == SORT {
            return true;
        }
        let mut h = t;
        let mut k = 0usize;
        while self.tk(h) == APP {
            h = self.ta(h);
            k += 1;
        }
        let sort_end = |w: &Self, mut u: u32| -> bool {
            for _ in 0..k {
                if !is_pi(w.tk(u)) {
                    return false;
                }
                u = w.tb(u);
            }
            w.tk(u) == SORT && w.lv.is_not_zero(w.tp(u))
        };
        match self.tk(h) {
            CONST => {
                let r = self.row_of(self.ta(h));
                r != NONE && sort_end(self, self.consts[r as usize].ty)
            }
            BVAR => {
                let j = self.tp(h) as usize;
                j < doms.len() && sort_end(self, doms[doms.len() - 1 - j])
            }
            _ => false,
        }
    }
    /// `x.idx b1 .. bm` with `x` of structure `sname`: the type of field
    /// `idx` in the constructor, past `m` pis (x's levels are unknown, so a
    /// sort must be never zero at any levels).
    fn proj_not_proof(&self, sname: u32, idx: u32, m: usize) -> bool {
        let srow = self.row_of(sname);
        if srow == NONE || !self.visible(srow) {
            return false;
        }
        let Some((np, 0, ctors, _)) = self.ind_info(srow) else { return false };
        if ctors.len() != 1 {
            return false;
        }
        let crow = self.row_of(ctors[0]);
        if crow == NONE || !self.visible(crow) {
            return false;
        }
        let mut ctx: SmallVec16 = SmallVec16::new();
        let mut t = self.consts[crow as usize].ty;
        for _ in 0..(np + idx) {
            if !is_pi(self.tk(t)) {
                return false;
            }
            ctx.push(self.ta(t));
            t = self.tb(t);
        }
        if !is_pi(self.tk(t)) {
            return false;
        }
        self.tele_not_proof(&ctx, self.ta(t), m)
    }

    /// Milestone 41: `v` is a recursor applied at least up to its major
    /// premise (no projection in its spine), at as many levels as the
    /// recursor has parameters, whose motive ends in a sort that is zero at
    /// those levels: its type is the motive applied, a proposition, so `v`
    /// is a proof. Read from the recursor's declared type, no inference.
    fn proof_by_rec(&mut self, v: V) -> bool {
        let Val::Neu { head: Head::Const(row, llr), spine } = self.val(v) else { return false };
        let CKind::Rec { nparams, nmotives, nminors, nindices, .. } = self.consts[row as usize].kind else { return false };
        let major_idx = (nparams + nmotives + nminors + nindices) as usize;
        if spine == EMPTY || self.sp.len(spine) <= major_idx || self.spine_has_proj(spine) {
            return false;
        }
        if self.ll_get(llr).len() != self.consts[row as usize].lparams.len() {
            return false;
        }
        let l = match self.rec_msort.get(&row) {
            Some(&l) => l,
            None => {
                let l = self.rec_motive_sort(row, major_idx + 1);
                self.rec_msort.insert(row, l);
                l
            }
        };
        if l == NONE {
            return false;
        }
        let ls = self.mk_ls(row, llr);
        let l = self.lsub(l, ls);
        self.lv.zeroish(l)
    }

    /// The level (a term of the recursor's type) of the sort its motive
    /// ends in: the recursor's type past `n` pis is a bound variable (one of
    /// those pis) applied to k arguments, and that variable's domain past
    /// k pis is a sort. NONE otherwise.
    fn rec_motive_sort(&self, row: u32, n: usize) -> u32 {
        let mut doms: SmallVec16 = SmallVec16::new();
        let mut t = self.consts[row as usize].ty;
        for _ in 0..n {
            if !is_pi(self.tk(t)) {
                return NONE;
            }
            doms.push(self.ta(t));
            t = self.tb(t);
        }
        let mut h = t;
        let mut k = 0usize;
        while self.tk(h) == APP {
            h = self.ta(h);
            k += 1;
        }
        if self.tk(h) != BVAR {
            return NONE;
        }
        let j = self.tp(h) as usize;
        if j >= doms.len() {
            return NONE;
        }
        let mut u = doms[doms.len() - 1 - j];
        for _ in 0..k {
            if !is_pi(self.tk(u)) {
                return NONE;
            }
            u = self.tb(u);
        }
        if self.tk(u) == SORT { self.tp(u) } else { NONE }
    }

    fn proof_irrel(&mut self, a: V, b: V) -> R<Option<bool>> {
        match self.val(a) {
            Val::Sort(_) | Val::Lit(_) => return Ok(None),
            _ if self.is_pi_val(a) => return Ok(None),
            _ => {}
        }
        if self.surely_not_proof(a) {
            return Ok(None);
        }
        let ta = self.infer_val(a)?;
        if !self.is_prop_type(ta)? {
            return Ok(None);
        }
        let tb = self.infer_val(b)?;
        Ok(Some(self.defeq(ta, tb)?))
    }

    /// `nat_succ_pred(v)` is Some (without making the predecessor).
    fn succ_like(&self, v: V) -> bool {
        match self.val(v) {
            Val::Lit(i) => matches!(self.lit(i), LitVal::Nat(n) if !n.is_zero()),
            Val::Neu { head: Head::Const(r, _), spine } if spine != EMPTY => {
                self.canon_of_row(r) == self.env.known.nat_succ && self.sp.len(spine) == 1 && self.sp.args(spine)[0] & PROJ_BIT == 0
            }
            _ => false,
        }
    }
    fn nat_succ_pred(&mut self, v: V) -> R<Option<V>> {
        match self.val(v) {
            Val::Lit(i) => {
                if let LitVal::Nat(n) = self.lit(i) {
                    if !n.is_zero() {
                        let p = n - BigUint::one();
                        return Ok(Some(self.mk_nat(p)?));
                    }
                }
                Ok(None)
            }
            Val::Neu { head: Head::Const(r, _), spine } if spine != EMPTY => {
                if self.canon_of_row(r) == self.env.known.nat_succ && self.sp.len(spine) == 1 {
                    let e = self.sp.args(spine)[0];
                    if e & PROJ_BIT == 0 {
                        return Ok(Some(e));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }
    fn is_nat_zero(&self, v: V) -> bool {
        match self.val(v) {
            Val::Lit(i) => matches!(self.lit(i), LitVal::Nat(n) if n.is_zero()),
            Val::Neu { head: Head::Const(r, _), spine: EMPTY } => self.canon_of_row(r) == self.env.known.nat_zero,
            _ => false,
        }
    }

    fn hint_cmp(a: Hint, b: Hint) -> i32 {
        match (a, b) {
            (Hint::Regular(x), Hint::Regular(y)) => {
                if x == y {
                    0
                } else if x > y {
                    -1
                } else {
                    1
                }
            }
            (Hint::Opaque, Hint::Opaque) | (Hint::Abbrev, Hint::Abbrev) => 0,
            (Hint::Opaque, _) => 1,
            (_, Hint::Opaque) => -1,
            (Hint::Abbrev, _) => -1,
            (_, Hint::Abbrev) => 1,
        }
    }

    /// A value headed by a projection (a projection in its spine), when
    /// `whnf_core` changes it.
    fn proj_app_step(&mut self, v: V) -> R<Option<V>> {
        let Val::Neu { spine, .. } = self.val(v) else { return Ok(None) };
        if !self.spine_has_proj(spine) {
            return Ok(None);
        }
        let w = self.whnf_core(v)?;
        Ok(if w != v { Some(w) } else { None })
    }

    /// Lean's lazy delta reduction. `Ok(r)` decided, `Err((a, b))` undecided.
    fn lazy_delta(&mut self, a: V, b: V) -> R<Result<bool, (V, V)>> {
        if self.head_probe == 0 || self.probe_on {
            return self.lazy_delta_r(a, b);
        }
        // milestone 41 (CommonHeadFirst): the reference loop under a budget;
        // past it, each side unfolded a step at a time towards the other's
        // head under the same budget; then the reference loop again
        let budget = self.head_probe;
        let t0 = self.ticks;
        let d0 = self.vdepth;
        self.probe_on = true;
        self.probe_end = t0.wrapping_add(budget);
        self.set_alarm();
        let r = self.lazy_delta_r(a, b);
        self.probe_on = false;
        self.set_alarm();
        match r {
            Err(Stop::Budget) => self.vdepth_to(d0),
            r => return r,
        }
        self.stats.headprobe[2] += self.ticks.wrapping_sub(t0) as u64;
        self.stats.headprobe[0] += 1;
        let tl = self.ticks;
        for (x, y) in [(a, b), (b, a)] {
            let t0 = self.ticks;
            let d0 = self.vdepth;
            self.probe_on = true;
            self.probe_end = t0.wrapping_add(budget);
            self.set_alarm();
            let r = self.head_lookahead(x, y);
            self.probe_on = false;
            self.set_alarm();
            match r {
                Ok(true) => {
                    self.stats.headprobe[1] += 1;
                    self.stats.headprobe[3] += self.ticks.wrapping_sub(tl) as u64;
                    return Ok(Ok(true));
                }
                Ok(false) => self.stats.headprobe[5] += 1,
                Err(Stop::Budget) => self.vdepth_to(d0),
                Err(e) => return Err(e),
            }
        }
        self.stats.headprobe[3] += self.ticks.wrapping_sub(tl) as u64;
        let tr = self.ticks;
        let r = self.lazy_delta_r(a, b);
        self.stats.headprobe[4] += self.ticks.wrapping_sub(tr) as u64;
        r
    }

    /// Milestone 41 (CommonHeadFirst): `x` unfolded a step at a time (a
    /// projection application reduced, else delta and cheap whnf_core)
    /// until its head is `y`'s constant; then the two compared by their
    /// arguments (congruence). false: no such head reached, or the
    /// arguments not shown equal.
    fn head_lookahead(&mut self, x: V, y: V) -> R<bool> {
        let Some((ry, ly, sy)) = self.const_head(y) else { return Ok(false) };
        if self.spine_has_proj(sy) {
            return Ok(false);
        }
        let cy = self.canon_of_row(ry);
        let mut x = x;
        loop {
            self.tick()?;
            let w = match self.proj_app_step(x)? {
                Some(w) => w,
                None => {
                    if self.delta_info(x).is_none() {
                        return Ok(false);
                    }
                    let Some(u) = self.unfold(x)? else { return Ok(false) };
                    self.whnf_core_c(u, true)?
                }
            };
            x = w;
            if x == y {
                return Ok(true);
            }
            if let Some((rx, lx, sx)) = self.const_head(x) {
                if self.canon_of_row(rx) == cy {
                    // milestone 48: a constant without arguments on the
                    // other side is reached when x comes to it (an `ite`
                    // whose branch is that constant); before, such a `y`
                    // ended the probe at once and the reference loop
                    // unfolded the constant itself
                    if sx == EMPTY && sy == EMPTY {
                        return Ok(self.levels_equiv(lx, ly));
                    }
                    if sx != EMPTY && sy != EMPTY && !self.spine_has_proj(sx) {
                        return Ok(self.levels_equiv(lx, ly) && self.spines_defeq_skip(sx, sy, rx, lx, true)?);
                    }
                }
            }
        }
    }

    fn lazy_delta_r(&mut self, a: V, b: V) -> R<Result<bool, (V, V)>> {
        let mut reg: Option<region::Reg> = None;
        let r = self.lazy_delta_loop(a, b, &mut reg);
        let Some(g) = reg else { return r };
        // milestone 38: the late region of a long lazy delta (see below)
        match r {
            Ok(Ok(e)) => {
                self.reg_close(&g, a, a)?;
                Ok(Ok(e))
            }
            Ok(Err((x, y))) if self.reg_old(&g, y) => Ok(Err((self.reg_close(&g, a, x)?, y))),
            Ok(Err((x, y))) if self.reg_old(&g, x) => Ok(Err((x, self.reg_close(&g, a, y)?))),
            r => {
                self.reg_keep(&g);
                r
            }
        }
    }
    /// Lazy delta's loop. Milestone 38: once the session wants regions
    /// the rest of the loop is a region (`reg`), with checkpoints when one
    /// side is older than the region (the loop keeps only the pair from one
    /// step to the next). A `decide` over a lazy loop (`go n (xor b true)`
    /// against `true`) unfolds here a step at a time, a million steps with
    /// nothing given back.
    #[inline(always)]
    fn lazy_delta_loop(&mut self, mut a: V, mut b: V, reg: &mut Option<region::Reg>) -> R<Result<bool, (V, V)>> {
        // the region's root: older than it
        let a0 = a;
        loop {
            if self.reg_late2 {
                match reg {
                    None => {
                        if self.reg_wanted() {
                            self.stats.late_ld += 1;
                            *reg = Some(self.reg_open(a0));
                        }
                    }
                    Some(g) => {
                        if self.reg_ckpt && self.reg_due(g) {
                            if self.reg_old(g, b) {
                                (a, *g) = self.reg_checkpoint(g, a0, a)?;
                            } else if self.reg_old(g, a) {
                                (b, *g) = self.reg_checkpoint(g, a0, b)?;
                            }
                        }
                    }
                }
            }
            self.tick()?;
            // offsets
            // milestone 23: both sides' shapes first, so a literal's
            // predecessor is made only when the other side has one too
            if self.succ_like(a) && self.succ_like(b) {
                if let (Some(pa), Some(pb)) = (self.nat_succ_pred(a)?, self.nat_succ_pred(b)?) {
                    return Ok(Ok(self.defeq(pa, pb)?));
                }
            }
            if self.is_nat_zero(a) && self.is_nat_zero(b) {
                return Ok(Ok(true));
            }
            if !self.has_fvar(a) && !self.has_fvar(b) && !self.let_skip_fold(a, b)? {
                // milestone 41: a Nat operation whose operands are not
                // literals yet waits while the other side can unfold or
                // the two are the same operation (NatFoldWaits)
                match self.nat_fold_wait(a, b)? {
                    NatWait::Fold => {}
                    NatWait::Equal => return Ok(Ok(true)),
                    NatWait::Next(x, y) => {
                        a = x;
                        b = y;
                        if let Some(r) = self.quick(a, b)? {
                            return Ok(Ok(r));
                        }
                        if self.quick_parts(a, b) {
                            return Ok(Ok(true));
                        }
                        continue;
                    }
                }
                if let Some(an) = self.reduce_nat(a)? {
                    return Ok(Ok(self.defeq(an, b)?));
                }
                if let Some(bn) = self.reduce_nat(b)? {
                    return Ok(Ok(self.defeq(a, bn)?));
                }
            }
            match self.delta_step(a, b)? {
                DStep::Equal => return Ok(Ok(true)),
                DStep::Differ => return Ok(Ok(false)),
                DStep::Stuck => return Ok(Err((a, b))),
                DStep::Next(x, y) => {
                    a = x;
                    b = y;
                }
            }
            if let Some(r) = self.quick(a, b)? {
                return Ok(Ok(r));
            }
            // Pestka's afterStep: identical, already equal or of such parts
            if self.quick_parts(a, b) {
                return Ok(Ok(true));
            }
            // milestone 39: one side came to data
            if self.ground && (self.vals.len() >= self.ground_at || self.ground_all) {
                if let Some(r) = self.ground_try(a, b)? {
                    return Ok(Ok(r));
                }
            }
        }
    }

    /// Milestone 34: Lean folds `Nat` arithmetic in lazy delta only on
    /// terms without free variables, and a `let` body is checked with the
    /// bound variable free (in the local context, with its value). Here the
    /// value itself is in the environment, so a side built over it looks
    /// closed and the fold evaluates the value (let-fold: `let d := bits 16
    /// 0; d + 0 =?= Nat.add d 0` made 2^16 calls, where Lean unfolds
    /// `HAdd.hAdd`). Is the fold to be skipped? When a side `reduce_nat`
    /// would fold reads the value of a `let` whose body is being inferred,
    /// the fold's arguments are evaluated first as a probe of LET_PROBE
    /// ticks: within it the fold runs as before; past it the fold is
    /// skipped and lazy delta unfolds (complete without the fold; Lean's
    /// order), and so for every later pair over these lets in their scope.
    /// Always skipping costs where folding small values is cheaper than
    /// unfolding: Init's Char.ofOrdinal proofs (lets over 0xD800, unary
    /// unfolding) ran out of memory; delta first as a probe made Mathlib's
    /// Nat.clog_of_one_lt._proof_1_4 16 -> 103 M. Inside another probe the
    /// fold runs (its budget bounds the work). release-da, on a skip, folds
    /// as well and asserts lazy delta's answer after one step the same.
    fn let_skip_fold(&mut self, a: V, b: V) -> R<bool> {
        if self.let_vals.is_empty() || self.probe_on || !(self.nat_fold_head(a) || self.nat_fold_head(b)) {
            return Ok(false);
        }
        let mut fuel = MENTION_FUEL;
        if self.over_let(a, &mut fuel) != Some(true) && self.over_let(b, &mut fuel) != Some(true) {
            return Ok(false);
        }
        let skip = if self.let_skip >= self.let_vals.len() {
            true
        } else {
            let t0 = self.ticks;
            let d0 = self.vdepth;
            self.probe_on = true;
            self.probe_end = t0.wrapping_add(LET_PROBE);
            self.set_alarm();
            let r = self.fold_args_whnf(a).and_then(|_| self.fold_args_whnf(b));
            self.probe_on = false;
            self.set_alarm();
            match r {
                Ok(()) => false,
                Err(Stop::Budget) => {
                    self.vdepth_to(d0);
                    self.let_skip = self.let_vals.len();
                    true
                }
                Err(e) => return Err(e),
            }
        };
        #[cfg(debug_assertions)]
        if skip {
            let n0 = std::mem::take(&mut self.let_vals);
            let folded = match self.reduce_nat(a)? {
                Some(an) => Some(self.defeq(an, b)?),
                None => match self.reduce_nat(b)? {
                    Some(bn) => Some(self.defeq(a, bn)?),
                    None => None,
                },
            };
            self.let_vals = n0;
            let d = match self.delta_step(a, b)? {
                DStep::Equal => Some(true),
                DStep::Differ => Some(false),
                DStep::Next(x, y) => Some(self.defeq(x, y)?),
                DStep::Stuck => None,
            };
            if let (Some(f), Some(d)) = (folded, d) {
                assert_eq!(d, f, "literal folding over a let value: lazy delta and the fold disagree");
            }
        }
        Ok(skip)
    }
    /// The arguments `reduce_nat` brings to weak head normal form for `v`.
    fn fold_args_whnf(&mut self, v: V) -> R<()> {
        if !self.nat_fold_head(v) {
            return Ok(());
        }
        let Some((_, _, spine)) = self.const_head(v) else { return Ok(()) };
        let Some(args) = self.app_args(spine) else { return Ok(()) };
        let args = ArgVec::from_slice(args);
        for &x in args.iter() {
            self.whnf(x)?;
        }
        Ok(())
    }
    /// Milestone 41 (NatFoldWaits). Lean's lazy delta folds a Nat
    /// operation as soon as a side is one, bringing its operands to weak
    /// head normal form: in CFSG's totalC, `List.sum [x, y] =?= x + (y + 0)`
    /// with `x` a closed count over a whole enumeration computed `x`, where
    /// unfolding `List.sum` on the other side reaches the same `x` by
    /// congruence. A side `Nat.op x y` whose operands are not literals
    /// already (no whnf is asked) waits:
    /// - the other side the same operation: the operands are compared
    ///   first (congruence; equal operands give equal results), and fold
    ///   only if they are not shown equal;
    /// - the other side unfolds (a definition, not a Nat operation, or a
    ///   projection application that reduces): it takes one step, and the
    ///   loop goes on;
    /// - otherwise (a literal, a constructor, a stuck term) the fold
    ///   happens as before.
    /// The steps are the kernel's own (delta, whnf_core, congruence) in
    /// another order; a fold is never refused, only delayed while the
    /// other side still unfolds, so the answer is the one lazy delta gives.
    fn nat_fold_wait(&mut self, a: V, b: V) -> R<NatWait> {
        if !self.nat_wait {
            return Ok(NatWait::Fold);
        }
        let (fa, fb) = (self.nat_fold_head(a) && !self.nat_args_lit(a), self.nat_fold_head(b) && !self.nat_args_lit(b));
        if !fa && !fb {
            return Ok(NatWait::Fold);
        }
        if fa && fb || (self.nat_fold_head(a) && self.nat_fold_head(b)) {
            let (ra, la, sa) = self.const_head(a).unwrap();
            let (rb, lb, sb) = self.const_head(b).unwrap();
            if self.canon_of_row(ra) == self.canon_of_row(rb) && !self.fail_cache.contains(&(a, b)) {
                self.stats.natwait[0] += 1;
                // under CommonHeadFirst's budget: two runs of one
                // computation on different inputs agree in shape down to
                // where the inputs differ (CFSG traps' s2bad: `g 19 0`
                // against `g 19 1`, congruence nested 2^19 deep), so a
                // comparison past the budget folds, as the reference does
                let eq = self.levels_equiv(la, lb) && self.budgeted(|w| w.spines_defeq_skip(sa, sb, ra, la, true))? == Some(true);
                if eq {
                    self.stats.natwait[1] += 1;
                    return Ok(NatWait::Equal);
                }
                self.fail_cache.insert((a, b));
                self.ulog(Undo::Fail(a, b));
            }
            return Ok(NatWait::Fold);
        }
        // one side waits; the other unfolds if it can
        let o = if fa { b } else { a };
        if self.nat_fold_head(o) {
            return Ok(NatWait::Fold);
        }
        // a projection application first (as delta_step's
        // try_unfold_proj_app), else one unfolding
        let u = match self.proj_app_step(o)? {
            Some(w) => w,
            None => {
                if self.delta_info(o).is_none() {
                    return Ok(NatWait::Fold);
                }
                let Some(u) = self.unfold(o)? else { return Ok(NatWait::Fold) };
                self.whnf_core_c(u, true)?
            }
        };
        self.stats.natwait[2] += 1;
        Ok(if fa { NatWait::Next(a, u) } else { NatWait::Next(u, b) })
    }
    /// Milestone 41: `f` under a budget of `head_probe` ticks (the argument
    /// probes' machinery); None past it. Inside another probe, `f` shares
    /// that probe's budget.
    fn budgeted<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<Option<T>> {
        if self.probe_on {
            return f(self).map(Some);
        }
        if self.head_probe == 0 {
            return f(self).map(Some);
        }
        let t0 = self.ticks;
        let d0 = self.vdepth;
        self.probe_on = true;
        self.probe_end = t0.wrapping_add(self.head_probe);
        self.set_alarm();
        let r = f(self);
        self.probe_on = false;
        self.set_alarm();
        match r {
            Ok(x) => Ok(Some(x)),
            Err(Stop::Budget) => {
                self.vdepth_to(d0);
                Ok(None)
            }
            Err(e) => Err(e),
        }
    }

    /// Are all of the operation's operands literals already (or values
    /// whose weak head normal form, already known, is one)?
    fn nat_args_lit(&mut self, v: V) -> bool {
        let Some((_, _, spine)) = self.const_head(v) else { return false };
        let Some(args) = self.app_args(spine) else { return false };
        let args = ArgVec::from_slice(args);
        args.iter().all(|&x| {
            if self.nat_ref(x).is_some() {
                return true;
            }
            let w = self.memo_at(x).whnf;
            w != NONE && self.nat_ref(w).is_some()
        })
    }

    /// Is `v` an application `reduce_nat` folds (a `Nat` operation)?
    fn nat_fold_head(&self, v: V) -> bool {
        match self.const_head(v) {
            Some((row, _, spine)) => spine != EMPTY && self.env.nat_op[row as usize] != 0,
            None => false,
        }
    }
    /// Does `v` read one of `let_vals` (entries terms read, spines)? None
    /// when `fuel` runs out.
    fn over_let(&mut self, v: V, fuel: &mut u32) -> Option<bool> {
        if v == HOLE {
            return Some(false);
        }
        if self.let_vals.contains(&v) {
            return Some(true);
        }
        if *fuel == 0 {
            return None;
        }
        *fuel -= 1;
        match self.val(v) {
            Val::Sort(_) | Val::Lit(_) => Some(false),
            Val::Thunk { term, env, .. } | Val::Clo { term, env, .. } | Val::CloI { term, env, .. } => {
                if self.trng(term) > 63 {
                    return None;
                }
                for i in 0..self.trng(term) {
                    if !self.uses_var(term, i) {
                        continue;
                    }
                    let Some(x) = self.env_at(env, i) else { break };
                    if self.over_let(x, fuel)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
            Val::Neu { head, spine } => {
                if let Head::Stuck(x) = head {
                    if self.over_let(x, fuel)? {
                        return Some(true);
                    }
                }
                for i in 0..self.sp.len(spine) {
                    let e = self.sp.args(spine)[i];
                    if e & PROJ_BIT == 0 && self.over_let(e, fuel)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
        }
    }

    /// One step of lazy delta (Pestka's deltaStep): unfold the side that
    /// unfolds, or the higher one, or both; the same regular definition
    /// first tries equal arguments.
    fn delta_step(&mut self, a: V, b: V) -> R<DStep> {
        let (mut a, mut b) = (a, b);
        let da = self.delta_info(a);
        let db = self.delta_info(b);
        match (da, db) {
            (None, None) => return Ok(DStep::Stuck),
            // only one side unfolds: a projection application on the
            // other side is reduced instead when it can be (Lean's
            // try_unfold_proj_app, Pestka's tryUnfoldProjApp)
            (Some(_), None) => match self.proj_app_step(b)? {
                Some(w) => b = w,
                None => match self.unfold(a)? {
                    Some(u) => a = self.whnf_core_c(u, true)?,
                    None => return Ok(DStep::Stuck),
                },
            },
            (None, Some(_)) => match self.proj_app_step(a)? {
                Some(w) => a = w,
                None => match self.unfold(b)? {
                    Some(u) => b = self.whnf_core_c(u, true)?,
                    None => return Ok(DStep::Stuck),
                },
            },
            (Some((ra, ha)), Some((rb, hb))) => {
                let c = Self::hint_cmp(ha, hb);
                // a side whose unfolding is refused (no value to
                // unfold) leaves the other side to unfold
                if c < 0 {
                    match self.unfold(a)? {
                        Some(u) => a = self.whnf_core_c(u, true)?,
                        None => match self.unfold(b)? {
                            Some(u) => b = self.whnf_core_c(u, true)?,
                            None => return Ok(DStep::Stuck),
                        },
                    }
                } else if c > 0 {
                    match self.unfold(b)? {
                        Some(u) => b = self.whnf_core_c(u, true)?,
                        None => match self.unfold(a)? {
                            Some(u) => a = self.whnf_core_c(u, true)?,
                            None => return Ok(DStep::Stuck),
                        },
                    }
                } else {
                    if ra == rb && matches!(ha, Hint::Regular(_)) {
                        let (_, la, sa) = self.const_head(a).unwrap();
                        let (_, lb, sb) = self.const_head(b).unwrap();
                        if sa != EMPTY && sb != EMPTY && !self.fail_cache.contains(&(a, b)) {
                            #[cfg(feature = "cnt")]
                            let tk0 = self.ticks;
                            let same = if !self.levels_equiv(la, lb) || self.args_refuted(sa, sb, ra, la)? {
                                false
                            } else if self.dovetail == 0 || self.probe_on {
                                self.spines_defeq_skip(sa, sb, ra, la, true)?
                            } else {
                                match self.dovetail_args(a, b, sa, sb, ra, la)? {
                                    Some(d) => return Ok(d),
                                    None => false,
                                }
                            };
                            #[cfg(feature = "cnt")]
                            {
                                let d = self.ticks.wrapping_sub(tk0) as u64;
                                THUNK_KINDS[if same { 700 } else { 701 }].fetch_add(1, Ordering::Relaxed);
                                THUNK_KINDS[if same { 702 } else { 703 }].fetch_add(d, Ordering::Relaxed);
                            }
                            if same {
                                return Ok(DStep::Equal);
                            }
                            self.fail_cache.insert((a, b));
                            self.ulog(Undo::Fail(a, b));
                        }
                    }
                    if ra == rb && !matches!(ha, Hint::Regular(_)) {
                        let (_, la, sa) = self.const_head(a).unwrap();
                        let (_, lb, sb) = self.const_head(b).unwrap();
                        if sa != EMPTY && sb != EMPTY && !self.fail_cache.contains(&(a, b)) && self.probe_worth(sa, sb, ra) {
                            if self.levels_equiv(la, lb) && self.probe_args(sa, sb, ra, la)? {
                                return Ok(DStep::Equal);
                            }
                            self.fail_cache.insert((a, b));
                            self.ulog(Undo::Fail(a, b));
                        }
                    }
                    let ua = self.unfold(a)?;
                    let ub = self.unfold(b)?;
                    match (ua, ub) {
                        (Some(x), Some(y)) => {
                            a = self.whnf_core_c(x, true)?;
                            b = self.whnf_core_c(y, true)?;
                        }
                        (Some(x), None) => a = self.whnf_core_c(x, true)?,
                        (None, Some(y)) => b = self.whnf_core_c(y, true)?,
                        (None, None) => return Ok(DStep::Stuck),
                    }
                }
            }
        }
        Ok(DStep::Next(a, b))
    }

    /// milestone 17: the arguments of two applications of the same
    /// non-regular constant (an abbreviation: an instance, a projection
    /// function) compared before both sides unfold, within a step budget
    /// (nano-lean's probe_args). A probe inside a probe shares the outer
    /// budget. Out of budget: not equal (both sides unfold, as without
    /// the probe). Nothing is cached as a false equality: `eq_cache` only
    /// keeps results of comparisons that finished.
    fn probe_worth(&mut self, sa: u32, sb: u32, row: u32) -> bool {
        let c = 6;
        if c == 0 {
            return true;
        }
        if c >= 2 {
            let mut k = self.shared.abbr[row as usize].load(Ordering::Relaxed);
            if k == 0 {
                k = self.abbr_shape_of(row);
                self.shared.abbr[row as usize].store(k, Ordering::Relaxed);
            }
            if c == 2 {
                return k >= 2;
            }
            if c == 4 {
                return k == 2;
            }
            if c == 5 && k >= 2 {
                return true;
            }
            if c == 6 {
                return k != 4 || self.elim_probe_worth(sa, sb);
            }
            if c == 3 && k < 2 {
                return false;
            }
        }
        if self.spine_has_proj(sa) || self.spine_has_proj(sb) {
            return false;
        }
        let ea = self.sp.args(sa);
        let eb = self.sp.args(sb);
        if ea.len() != eb.len() {
            return false;
        }
        let mut m = self.shared.explicit[row as usize].load(Ordering::Relaxed);
        if m == 0 {
            m = self.explicit_mask(row);
            self.shared.explicit[row as usize].store(m, Ordering::Relaxed);
        }
        let ea = self.sp.args(sa);
        let eb = self.sp.args(sb);
        for i in 0..ea.len() {
            if (i >= 63 || m & (1u64 << i) != 0) && ea[i] != eb[i] {
                return false;
            }
        }
        true
    }
    /// milestone 18: an eliminator-like head (shape 4) is probed only when
    /// every differing argument pair is neutral against neutral, or every
    /// one closure against closure (Init's Omega.Constraint.sat' probes:
    /// ~92% equal); a mix, or a thunk among them, is a matcher on different
    /// discriminants (con-leche's List.filter.match_1: ~0% equal).
    fn elim_probe_worth(&self, sa: u32, sb: u32) -> bool {
        if self.spine_has_proj(sa) || self.spine_has_proj(sb) {
            return false;
        }
        let (ea, eb) = (self.sp.args(sa), self.sp.args(sb));
        if ea.len() != eb.len() {
            return false;
        }
        let mut kind = 0u8;
        for i in 0..ea.len() {
            if ea[i] == eb[i] {
                continue;
            }
            let k = match (self.val(ea[i]), self.val(eb[i])) {
                (Val::Neu { .. }, Val::Neu { .. }) => 1,
                (Val::Clo { .. } | Val::CloI { .. }, Val::Clo { .. } | Val::CloI { .. }) => 2,
                _ => return false,
            };
            if kind != 0 && k != kind {
                return false;
            }
            kind = k;
        }
        true
    }
    /// What a non-regular definition's body is past its lambdas: 2 a
    /// projection (a projection function), 3 a constructor application (an
    /// instance), 1 anything else (a matcher, casesOn, recursion helpers).
    fn abbr_shape_of(&self, row: u32) -> u8 {
        self.abbr_shape_d(row, 0)
    }
    /// 4: an eliminator in disguise: the body's head is a recursor, or a
    /// definition of shape 4 (casesOn, matchers), or a projection of one
    /// (brecOn); read at most 4 definitions deep.
    fn abbr_shape_d(&self, row: u32, d: u32) -> u8 {
        let CKind::Defn { value, .. } = self.consts[row as usize].kind else { return 1 };
        if value >= self.mlen {
            return 1;
        }
        let mut b = value;
        while is_lam(self.tk(b)) {
            b = self.tb(b);
        }
        if self.tk(b) == PROJ && self.tk(self.ta(b)) == BVAR {
            return 2;
        }
        while self.tk(b) == PROJ {
            b = self.ta(b);
        }
        let mut h = b;
        while self.tk(h) == APP {
            h = self.ta(h);
        }
        if self.tk(h) == CONST {
            let r = self.row_of(self.ta(h));
            if r != NONE {
                match self.consts[r as usize].kind {
                    CKind::Ctor { .. } => return 3,
                    CKind::Rec { .. } => return 4,
                    CKind::Defn { .. } if d < 4 && r != row => {
                        if self.abbr_shape_d(r, d + 1) == 4 {
                            return 4;
                        }
                    }
                    _ => {}
                }
            }
        }
        1
    }
    /// Bit i: argument i of constant `row` is an explicit binder of its
    /// type (or past the pis read); bit 63 always set (so never 0).
    fn explicit_mask(&self, row: u32) -> u64 {
        let mut t = self.consts[row as usize].ty;
        let mut m = 1u64 << 63;
        let mut i = 0;
        while i < 63 {
            let k = self.tk(t);
            if !is_pi(k) {
                m |= !0u64 << i;
                break;
            }
            if k == PI {
                m |= 1 << i;
            }
            t = self.tb(t);
            i += 1;
        }
        m
    }
    /// Milestone 36: before lazy delta compares the arguments of the same
    /// regular definition left to right, each pair is tried under a small
    /// budget; a pair found different settles it (the arguments are not
    /// all equal), so a later cheap difference (`getD l 2 _` against
    /// `getD l' 0 _`) is found before an earlier argument is evaluated in
    /// full (lyLet_mem: the 111x111 matrices of `aStarList`). A false here
    /// only skips the shortcut: both sides are unfolded as after any
    /// failed argument comparison, so verdicts cannot depend on it.
    fn args_refuted(&mut self, sa: u32, sb: u32, row: u32, llr: u32) -> R<bool> {
        if self.probe_on || !self.args_refute || self.spine_has_proj(sa) || self.spine_has_proj(sb) {
            return Ok(false);
        }
        let n = self.sp.len(sa);
        if n != self.sp.len(sb) || n < 2 {
            return Ok(false);
        }
        let skip = self.prop_positions(row, llr)?;
        for i in (0..n).rev() {
            if i < 64 && skip & (1u64 << i) != 0 {
                continue;
            }
            let (x, y) = (self.sp.args(sa)[i], self.sp.args(sb)[i]);
            if x == y {
                continue;
            }
            let t0 = self.ticks;
            let d0 = self.vdepth;
            self.probe_on = true;
            self.probe_end = t0.wrapping_add(REFUTE_TICKS);
            self.set_alarm();
            let r = self.defeq(x, y);
            self.probe_on = false;
            self.set_alarm();
            match r {
                Ok(false) => return Ok(true),
                Ok(true) => {}
                Err(Stop::Budget) => self.vdepth_to(d0),
                Err(e) => return Err(e),
            }
        }
        Ok(false)
    }

    /// Milestone 48: `f` under a budget of `budget` ticks; `None` when the
    /// budget ran out (binders opened inside are closed again).
    fn budgeted_n(&mut self, budget: u32, f: impl FnOnce(&mut Self) -> R<bool>) -> R<Option<bool>> {
        let d0 = self.vdepth;
        self.probe_on = true;
        self.probe_end = self.ticks.wrapping_add(budget);
        self.set_alarm();
        let r = f(self);
        self.probe_on = false;
        self.set_alarm();
        match r {
            Ok(r) => Ok(Some(r)),
            Err(Stop::Budget) => {
                self.vdepth_to(d0);
                Ok(None)
            }
            Err(e) => Err(e),
        }
    }

    /// Milestone 48: two applications `a`, `b` of the same regular
    /// definition (arguments `sa`, `sb`) whose arguments were not refuted
    /// (args_refuted). Lean's order compares the arguments, unbudgeted, and
    /// unfolds both sides only when they differ; that can walk without end
    /// where unfolding decides at once: `(false && A) && B =?= (false && A')
    /// && B'`, `A`, `A'` open computations that differ (CFSG's
    /// Batch27581.p2). So before the arguments, both sides unfolded and
    /// compared under the budget args_refuted has (DOVETAIL ticks): an
    /// answer within it decides, true or false (it is what the reference
    /// loop comes to after unequal arguments); past it, the arguments as
    /// before. `Some(Equal | Differ)`: decided; `None`: the arguments
    /// differ (both sides unfold next).
    ///
    /// (Taking turns between the two ways under a doubling budget, tried
    /// first, blew CFSG's lyLet and AlphaMc_SuzData slices past 6 GB: under
    /// a budget no inner probe runs (CommonHeadFirst, args_refuted, the
    /// hand-ups), and the arguments' way grew far dearer than unbudgeted.)
    fn dovetail_args(&mut self, a: V, b: V, sa: u32, sb: u32, ra: u32, la: u32) -> R<Option<DStep>> {
        let t0 = self.ticks;
        self.stats.dovetail[0] += 1;
        let r = self.unfold_first(a, b);
        self.stats.dovetail[4] += self.ticks.wrapping_sub(t0) as u64;
        match r? {
            Some(d) => {
                self.stats.dovetail[3] += 1;
                Ok(Some(d))
            }
            None => {
                self.stats.dovetail[1] += 1;
                Ok(if self.spines_defeq_skip(sa, sb, ra, la, true)? { Some(DStep::Equal) } else { None })
            }
        }
    }

    fn unfold_first(&mut self, a: V, b: V) -> R<Option<DStep>> {
        self.pdead_off = true;
        self.dove_deep = false;
        let mut refused = false;
        // the unfolding itself is inside the budget: unfolding a matcher
        // or a casesOn evaluates its major premise (match_direct,
        // cases_direct), which may be a whole computation
        let r = self.budgeted_n(self.dovetail, |s| {
            // a side whose unfolding is refused (no value to unfold):
            // the arguments alone, as before
            let (Some(ua), Some(ub)) = (s.unfold(a)?, s.unfold(b)?) else {
                refused = true;
                return Ok(false);
            };
            let x = s.whnf_core_c(ua, true)?;
            let y = s.whnf_core_c(ub, true)?;
            s.defeq(x, y)
        });
        self.pdead_off = false;
        if std::mem::take(&mut self.dove_deep) || refused {
            return Ok(None);
        }
        Ok(r?.map(|r| if r { DStep::Equal } else { DStep::Differ }))
    }

    fn probe_args(&mut self, sa: u32, sb: u32, row: u32, llr: u32) -> R<bool> {
        if self.probe_on {
            return self.spines_defeq_skip(sa, sb, row, llr, true);
        }
        self.stats.probe[0] += 1;
        let t0 = self.ticks;
        let d0 = self.vdepth;
        self.probe_on = true;
        self.probe_end = t0.wrapping_add(1024);
        self.set_alarm();
        let r = self.spines_defeq_skip(sa, sb, row, llr, true);
        self.probe_on = false;
        self.set_alarm();
        self.stats.probe[3] += self.ticks.wrapping_sub(t0) as u64;
        match r {
            Ok(true) => {
                self.stats.probe[1] += 1;
                Ok(true)
            }
            Ok(false) => Ok(false),
            Err(Stop::Budget) => {
                self.stats.probe[2] += 1;
                // binders opened inside the probe are gone (in depth mode
                // their depths are free again; otherwise their variables
                // stay marked in scope: fewer reuses, never a sharing)
                self.vdepth_to(d0);
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }

    /// The last projection in a neutral value's spine: (position, elim).
    fn last_proj(&self, v: V) -> Option<(Val, SpineVec, usize)> {
        let Val::Neu { head, spine } = self.val(v) else { return None };
        if spine == EMPTY || !self.spine_has_proj(spine) {
            return None;
        }
        let elims = self.spine(spine);
        let p = elims.iter().rposition(|&e| e & PROJ_BIT != 0)?;
        Some((Val::Neu { head, spine }, elims, p))
    }

    /// The value a neutral spine stands for up to (not including) elim `p`.
    fn spine_prefix(&mut self, head: Head, spine: u32, p: usize) -> R<V> {
        match head {
            Head::Stuck(x) if p == 0 => Ok(x),
            _ => self.neu_prefix(head, spine, p),
        }
    }

    /// `c.i as =?= d.i bs` (Pestka's eqProj and eqProjApp): with arguments,
    /// the projections first (as heads), then the arguments; a bare
    /// projection compares its structures by lazy delta. `None` when the
    /// two values are not projections of the same field with as many
    /// arguments after it.
    fn proj_eq(&mut self, a: V, b: V) -> R<Option<bool>> {
        let Some((Val::Neu { head: ha, spine: spa }, ea, pa)) = self.last_proj(a) else { return Ok(None) };
        let Some((Val::Neu { head: hb, spine: spb }, eb, pb)) = self.last_proj(b) else { return Ok(None) };
        let (xa, xb) = (ea[pa] & !PROJ_BIT, eb[pb] & !PROJ_BIT);
        if self.projs[xa as usize] != self.projs[xb as usize] || ea.len() - pa != eb.len() - pb {
            return Ok(None);
        }
        if pa + 1 < ea.len() {
            // milestone 31: an application of a projection is reduced first
            // (Lean's is_def_eq_core: whnf_core before is_def_eq_app);
            // its arguments are compared only when neither side reduces.
            // Comparing them first proved unequal arguments unequal (f vs g
            // in `inst.1 f x =?= inst.1 g x`) where the reduced sides agree.
            if true {
                let wa = self.whnf_core(a)?;
                let wb = self.whnf_core(b)?;
                if wa != a || wb != b {
                    return Ok(Some(self.defeq(wa, wb)?));
                }
            }
            let fa = self.neu_prefix(ha, spa, pa + 1)?;
            let fb = self.neu_prefix(hb, spb, pb + 1)?;
            if !self.defeq(fa, fb)? {
                return Ok(Some(false));
            }
            for k in 1..ea.len() - pa {
                if !self.defeq(ea[pa + k], eb[pb + k])? {
                    return Ok(Some(false));
                }
            }
            return Ok(Some(true));
        }
        let sa = self.spine_prefix(ha, spa, pa)?;
        let sb = self.spine_prefix(hb, spb, pb)?;
        let pe = ea[pa];
        self.stats.proj_calls += 1;
        let u0 = self.stats.unfolds;
        let r = self.lazy_delta_proj(sa, sb, pe)?;
        self.stats.proj_unfolds += self.stats.unfolds - u0;
        self.stats.proj_true += r as u64;
        Ok(Some(r))
    }

    /// Pestka's lazyDeltaProj and projFallback: unfold the two structures
    /// lazily until they meet or neither unfolds; then the fields of
    /// constructor applications, a field against the projection of the
    /// other side (FieldNotStructure), or the structures themselves.
    fn lazy_delta_proj(&mut self, mut a: V, mut b: V, pe: u32) -> R<bool> {
        let idx = self.projs[(pe & !PROJ_BIT) as usize].1;
        loop {
            self.tick()?;
            if a == b {
                return Ok(true);
            }
            match self.delta_step(a, b)? {
                DStep::Equal => return Ok(true),
                DStep::Stuck | DStep::Differ => break,
                DStep::Next(x, y) => {
                    a = x;
                    b = y;
                }
            }
            match self.quick(a, b)? {
                Some(true) => return Ok(true),
                Some(false) => break,
                None => {}
            }
            if self.quick_parts(a, b) {
                return Ok(true);
            }
        }
        let fa = self.ctor_field(a, idx)?;
        let fb = self.ctor_field(b, idx)?;
        match (fa, fb) {
            (Some(x), Some(y)) => self.defeq(x, y),
            (Some(x), None) => {
                let y = self.apply_elims(b, &[pe])?;
                self.defeq(x, y)
            }
            (None, Some(y)) => {
                let x = self.apply_elims(a, &[pe])?;
                self.defeq(x, y)
            }
            (None, None) => {
                self.stats.proj_fallback_none += 1;
                self.defeq(a, b)
            }
        }
    }

    /// Pestka's quickParts past `quick`: structurally equal (sameTerm on
    /// the terms the values stand for), already found equal, or made of
    /// such parts. Only `true` decides.
    fn quick_parts(&mut self, a: V, b: V) -> bool {
        self.same_top(a, b)
    }

    /// Structural equality with the words first (Pestka's `==` fails on
    /// different hash words at once): values whose structural hashes
    /// differ are not walked. A hash that ran out of fuel is the value's
    /// own, so only identical values pass then.
    fn same_top(&mut self, a: V, b: V) -> bool {
        if a == b {
            return true;
        }
        let mut fuel = self.same_fuel;
        let f0 = fuel;
        let r = self.same_val(a, b, &mut fuel);
        if !r {
            self.walk_wasted += (f0 - fuel) as u64;
        }
        r
    }

    /// Arguments of two applications of constant `row` (at levels `llr` on
    /// one side, equivalent on the other) compared beside the pis of its
    /// type (Pestka's ProofArgsSkipped): once the arguments before it are
    /// equal, an argument in a place whose domain is surely a proposition
    /// is a proof of the same proposition on both sides, equal by proof
    /// irrelevance. With `unfold` (the two sides would be unfolded next,
    /// lazy delta), also the arguments the definition's body never reads
    /// are left out (Pestka's unusedArgs): both unfold to the same body
    /// with only those arguments put in differently.
    fn spines_defeq_skip(&mut self, sa: u32, sb: u32, row: u32, llr: u32, unfold: bool) -> R<bool> {
        if self.spine_has_proj(sa) || self.spine_has_proj(sb) {
            return self.spines_defeq(sa, sb);
        }
        // milestone 23: the elims read in place (a spine's words never
        // change or move: `Spines::d` is a reserved range), not copied
        let n = self.sp.len(sa);
        if n != self.sp.len(sb) {
            return Ok(false);
        }
        let mut skip = self.prop_positions(row, llr)?;
        if unfold {
            let (l, m) = self.unused_args(row);
            if (l as usize) <= n {
                skip |= m;
            }
        }
        for i in 0..n {
            if i < 64 && skip & (1u64 << i) != 0 {
                continue;
            }
            let (x, y) = (self.sp.args(sa)[i], self.sp.args(sb)[i]);
            if !self.defeq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// (leading lambdas, positions never read) of a definition's value.
    fn unused_args(&mut self, row: u32) -> (u8, u64) {
        let l = self.shared.unused_l[row as usize].load(Ordering::Acquire);
        if l != 0 {
            let m = self.shared.unused_m[row as usize].load(Ordering::Relaxed);
            return (if l == 255 { 255 } else { l - 1 }, m);
        }
        let r = match self.consts[row as usize].kind {
            CKind::Defn { value, .. } if value < self.mlen => {
                let mut b = value;
                let mut l = 0u32;
                while is_lam(self.tk(b)) && l < 64 {
                    b = self.tb(b);
                    l += 1;
                }
                if is_lam(self.tk(b)) {
                    (255, 0)
                } else {
                    let mut m = 0u64;
                    for i in 0..l {
                        if !self.uses_var(b, l - 1 - i) {
                            m |= 1 << i;
                        }
                    }
                    (l as u8, m)
                }
            }
            _ => (255, 0),
        };
        self.shared.unused_m[row as usize].store(r.1, Ordering::Relaxed);
        self.shared.unused_l[row as usize].store(if r.0 == 255 { 255 } else { r.0 + 1 }, Ordering::Release);
        r
    }

    /// Argument positions of constant `row` at levels `llr` whose domain is
    /// surely a proposition, read from its type as written (Pestka's
    /// isProposition): after its own pis, a variable or constant applied to
    /// as many arguments as its type has pis, that type ending in a sort
    /// that is zero at these levels.
    fn prop_positions(&mut self, row: u32, llr: u32) -> R<u64> {
        if let Some(&m) = self.prop_pos.get(&(row, llr)) {
            return Ok(m);
        }
        let ls = self.mk_ls(row, llr);
        let mut t = self.consts[row as usize].ty;
        let mut ctx: Vec<u32> = Vec::new();
        let mut m = 0u64;
        let mut i = 0;
        while i < 64 && is_pi(self.tk(t)) {
            let d = self.ta(t);
            if self.surely_prop(d, &ctx, ls) {
                m |= 1 << i;
            }
            ctx.push(d);
            t = self.tb(t);
            i += 1;
        }
        self.prop_pos.insert((row, llr), m);
        Ok(m)
    }

    fn surely_prop(&mut self, d: u32, ctx: &[u32], ls: u32) -> bool {
        let mut ctx: Vec<u32> = ctx.to_vec();
        let mut d = d;
        while is_pi(self.tk(d)) {
            ctx.push(self.ta(d));
            d = self.tb(d);
        }
        let mut f = d;
        let mut m = 0;
        while self.tk(f) == APP {
            f = self.ta(f);
            m += 1;
        }
        let peel = |w: &Self, mut x: u32| -> Option<u32> {
            for _ in 0..m {
                if !is_pi(w.tk(x)) {
                    return None;
                }
                x = w.tb(x);
            }
            if w.tk(x) == SORT { Some(w.tp(x)) } else { None }
        };
        match self.tk(f) {
            BVAR => {
                let j = self.tp(f) as usize;
                if j >= ctx.len() {
                    return false;
                }
                let dom = ctx[ctx.len() - 1 - j];
                match peel(self, dom) {
                    Some(l) => {
                        let l = self.lsub(l, ls);
                        self.lv.zeroish(l)
                    }
                    None => false,
                }
            }
            CONST => {
                let crow = self.row_of(self.ta(f));
                if crow == NONE {
                    return false;
                }
                let cty = self.consts[crow as usize].ty;
                let Some(l) = peel(self, cty) else { return false };
                if self.lv.zeroish(l) {
                    return true;
                }
                let llr2 = self.lsub_ll(f, ls);
                let llr2 = self.canon_ll(llr2);
                if self.ll_get(llr2).len() != self.consts[crow as usize].lparams.len() {
                    return false;
                }
                let ls2 = self.mk_ls(crow, llr2);
                let l = self.lsub(l, ls2);
                self.lv.zeroish(l)
            }
            _ => false,
        }
    }

    fn levels_equiv(&mut self, la: u32, lb: u32) -> bool {
        if la == lb {
            return true;
        }
        let xa = self.ll_get(la).to_vec();
        let xb = self.ll_get(lb).to_vec();
        xa.len() == xb.len() && xa.iter().zip(xb.iter()).all(|(&x, &y)| self.lv.equiv(x, y))
    }

    fn spines_defeq(&mut self, sa: u32, sb: u32) -> R<bool> {
        if !self.spines_same_shape(sa, sb) {
            return Ok(false);
        }
        for i in 0..self.sp.len(sa) {
            let (x, y) = (self.sp.args(sa)[i], self.sp.args(sb)[i]);
            if x & PROJ_BIT == 0 && !self.defeq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Milestone 48: two spines of one length with their projections at the
    /// same places, of the same fields. Read before any argument is
    /// compared: CFSG's HNSchreier.matG_sU compared `↑(dJ⁻¹)` (Subgroup's
    /// inverse: `Subtype.val _ _ Y .1`) with `(↑dJ)⁻¹` (Units': `Subtype.val
    /// _ _ dJ .0`) argument by argument, `Y =?= dJ` first: two 133x133
    /// matrices multiplied out entry by entry (past 200 GB on AWS) before
    /// the next position showed field 1 against field 0.
    fn spines_same_shape(&self, sa: u32, sb: u32) -> bool {
        let n = self.sp.len(sa);
        if n != self.sp.len(sb) {
            return false;
        }
        for i in 0..n {
            let (x, y) = (self.sp.args(sa)[i], self.sp.args(sb)[i]);
            let px = x & PROJ_BIT != 0;
            if px != (y & PROJ_BIT != 0) {
                return false;
            }
            if px && self.projs[(x & !PROJ_BIT) as usize].1 != self.projs[(y & !PROJ_BIT) as usize].1 {
                return false;
            }
        }
        true
    }

    fn defeq_app(&mut self, a: V, b: V) -> R<bool> {
        let (Val::Neu { head: ha, spine: sa }, Val::Neu { head: hb, spine: sb }) = (self.val(a), self.val(b))
        else {
            return Ok(false);
        };
        let heads = match (ha, hb) {
            (Head::FVar(x), Head::FVar(y)) => x == y,
            (Head::Const(r1, l1), Head::Const(r2, l2)) => {
                if r1 == r2 && self.levels_equiv(l1, l2) {
                    return self.spines_defeq_skip(sa, sb, r1, l1, false);
                }
                false
            }
            (Head::Stuck(x), Head::Stuck(y)) => self.spines_same_shape(sa, sb) && self.defeq(x, y)?,
            _ => false,
        };
        if !heads {
            return Ok(false);
        }
        self.spines_defeq(sa, sb)
    }

    fn try_eta(&mut self, a: V, b: V) -> R<bool> {
        if !self.is_lam_val(a) || self.is_lam_val(b) {
            return Ok(false);
        }
        let tb = self.infer_val(b)?;
        let tb = self.whnf(tb)?;
        if !self.is_pi_val(tb) {
            return Ok(false);
        }
        let da = self.bind_dom(a)?;
        let db = self.bind_dom(tb)?;
        if !self.defeq(da, db)? {
            return Ok(false);
        }
        let d0 = self.vdepth;
        let x = self.open_var(da)?;
        let r = (|| {
            let ba = self.bind_body(a, x)?;
            let bb = self.apply(b, x)?;
            self.defeq(ba, bb)
        })();
        self.close_var(x, d0);
        r
    }

    /// Structure eta: `a` against `mk params fields` (`b`). Milestone 19
    /// (Pestka's EtaProofFieldsSkipped): once the types are equal and the
    /// fields before it are, a field whose domain in the constructor's type
    /// is surely a proposition (`prop_positions`) is a proof of the same
    /// proposition as the projection of `a` in its place: equal by proof
    /// irrelevance, not compared.
    fn try_eta_struct(&mut self, a: V, b: V) -> R<bool> {
        let Some((crow, cll, spine)) = self.const_head(b) else { return Ok(false) };
        let CKind::Ctor { induct, nparams, nfields, .. } = self.consts[crow as usize].kind else { return Ok(false) };
        let Some(args) = self.app_args(spine) else { return Ok(false) };
        if args.len() != nparams as usize + nfields as usize {
            return Ok(false);
        }
        let irow = self.row_of(induct);
        if irow == NONE || !self.structure_like(irow) {
            return Ok(false);
        }
        let ta = self.infer_val(a)?;
        let tb = self.infer_val(b)?;
        if !self.defeq(ta, tb)? {
            return Ok(false);
        }
        let sname = self.consts[irow as usize].name;
        let skip = if true { self.prop_positions(crow, cll)? } else { 0 };
        for i in 0..nfields {
            let k = nparams as u32 + i as u32;
            if k < 64 && skip & (1u64 << k) != 0 {
                continue;
            }
            let p = self.proj_val(a, i, sname)?;
            if !self.defeq(p, args[nparams as usize + i as usize])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn string_expansion(&mut self, a: V, b: V) -> R<Option<bool>> {
        for (x, y) in [(a, b), (b, a)] {
            if let Val::Lit(i) = self.val(x) {
                if let LitVal::Str(s) = self.lit(i).clone() {
                    if let Some((r, _, sp)) = self.const_head(y) {
                        if sp != EMPTY && self.canon_of_row(r) == self.env.known.string_of_list {
                            let Some(e) = self.str_lit_expand(&s)? else { return Ok(None) };
                            let e = self.whnf(e)?;
                            return Ok(Some(self.defeq(e, y)?));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    fn unit_like(&mut self, a: V, b: V) -> R<bool> {
        if matches!(self.val(a), Val::Sort(_)) || self.is_pi_val(a) {
            return Ok(false);
        }
        let ta = self.infer_val(a)?;
        let ta = self.whnf(ta)?;
        let Some((irow, _, _)) = self.const_head(ta) else { return Ok(false) };
        if !self.structure_like(irow) {
            return Ok(false);
        }
        let (_, _, ctors, _) = self.ind_info(irow).unwrap();
        let crow = self.row_of(ctors[0]);
        if crow == NONE {
            return Ok(false);
        }
        let CKind::Ctor { nfields, .. } = self.consts[crow as usize].kind else { return Ok(false) };
        if nfields != 0 {
            return Ok(false);
        }
        let tb = self.infer_val(b)?;
        self.defeq(ta, tb)
    }

    // -----------------------------------------------------------------------
    // Declarations

    pub fn setup_decl(&mut self, row: u32, safety: u8) {
        self.safety = safety;
        self.cur_lparams = self.consts[row as usize].lparams.iter().map(|&n| self.env.canon(n)).collect();
        self.cur_lp_list = NONE;
        self.cur_lp = self.lp_list();
        self.lp_ok.clear();
        self.ground_fuel = self.ground_fuel0;
        self.ground_out_at = None;
        self.gm = None;
    }

    pub fn set_lparams(&mut self, lp: Vec<u32>) {
        self.cur_lparams = lp;
        self.cur_lp_list = NONE;
        self.cur_lp = self.lp_list();
        self.lp_ok.clear();
    }

    /// Checks that `ty` (a MAIN id) is a closed, well-formed type; returns its sort.
    pub fn check_type(&mut self, ty: u32) -> R<u32> {
        if self.trng(ty) != 0 {
            return reject("type has loose bound variables");
        }
        // milestone 29: open facts are looked up in the body of the type's
        // Pi telescope
        if ty < self.mlen && is_pi(self.tk(ty)) && self.open_facts_on() {
            self.kb_root = ty;
        }
        let s = self.infer(ty, EMPTY, 0, true);
        self.kb_root = NONE;
        self.kb_tele = NONE;
        self.kb_env = NONE;
        self.sort_of(s?, "declaration type")
    }

    #[inline(always)]
    fn open_facts_on(&self) -> bool {
        self.safety == 0 && !self.scratch
    }

    /// Milestone 29: check-mode inference of `t` at ls = 0 in the body of
    /// the declaration type's Pi telescope, answered by an open fact when
    /// there is one.
    #[cold]
    #[inline(never)]
    fn infer_known(&mut self, t: u32, env: u32) -> R<V> {
        if t < self.mlen && self.trng(t) != 0 {
            let x = self.shared.checked[t as usize].load(Ordering::Relaxed);
            if x != 0 && x >> 32 == 0 {
                if let Some(v) = self.open_fact(t, x as u32 - 1, env)? {
                    if STATS { self.stats.open_hits += 1; }
                    // release-da: the term checked anyway, its type equal
                    #[cfg(debug_assertions)]
                    {
                        let w = self.infer_core(t, env, 0, true)?;
                        assert!(self.defeq(v, w)?, "open fact for term {t}: a type not the inferred one");
                    }
                    return Ok(v);
                }
            }
        }
        self.infer_core(t, env, 0, true)
    }

    /// Milestone 29: safe definition `row`, of an earlier declaration under
    /// level parameters the current one has too, was checked: its value's
    /// lambda body `b` under the domains `A` (as Lean's lambda check does)
    /// and its type, so the codomain `B` under its Pi domains. When the
    /// current telescope's domains are the same terms `A` (as many, in the
    /// same order) and `t` is `b`, or the type's domains are those terms
    /// and `t` is `B`, then `t` is well typed here (the context is the
    /// same; typing survives the environment's growth): it is inferred
    /// without checking. Equation lemmas `f xs = b` state both (`@Eq B ..`).
    fn open_fact(&mut self, t: u32, row: u32, env: u32) -> R<Option<V>> {
        let c = &self.env.consts[row as usize];
        if c.decl >= self.cur_decl {
            return Ok(None);
        }
        let CKind::Defn { value, safety: 0, .. } = c.kind else {
            return Ok(None);
        };
        for &p in c.lparams.iter() {
            if !self.cur_lparams.contains(&self.env.canon(p)) {
                return Ok(None);
            }
        }
        let (mut p, mut a, mut ty) = (self.kb_tele, value, c.ty);
        let (mut lam_ok, mut pi_ok) = (true, true);
        while is_pi(self.tk(p)) {
            let d = self.ta(p);
            lam_ok = lam_ok && is_lam(self.tk(a)) && self.ta(a) == d;
            if lam_ok {
                a = self.tb(a);
            }
            pi_ok = pi_ok && is_pi(self.tk(ty)) && self.ta(ty) == d;
            if pi_ok {
                ty = self.tb(ty);
            }
            p = self.tb(p);
        }
        if (lam_ok && a == t) || (pi_ok && ty == t) {
            return Ok(Some(self.infer(t, env, 0, false)?));
        }
        Ok(None)
    }

    /// Milestone 29: safe definition `row` was checked: its value's lambda
    /// body and its type's codomain under as many Pis become open facts
    /// (`open_fact`); the latest replaces a stored one.
    fn open_record(&mut self, row: u32, value: u32, ty: u32) {
        let (mut a, mut p) = (value, ty);
        if !is_lam(self.tk(a)) {
            return;
        }
        while is_lam(self.tk(a)) {
            a = self.tb(a);
            p = if p != NONE && is_pi(self.tk(p)) { self.tb(p) } else { NONE };
        }
        for t in [a, p] {
            if t != NONE && t < self.mlen && self.trng(t) != 0 {
                self.shared.checked[t as usize].store(row as u64 + 1, Ordering::Relaxed);
            }
        }
    }

    pub fn check_value(&mut self, val: u32, ty: u32) -> R<()> {
        if self.trng(val) != 0 {
            return reject("value has loose bound variables");
        }
        let vt = self.infer(val, EMPTY, 0, true)?;
        let tv = self.eval(ty, EMPTY, 0)?;
        if !self.defeq(vt, tv)? {
            return reject("value's type does not match the declared type");
        }
        Ok(())
    }

    pub fn check_decl(&mut self, d: u32) -> R<()> {
        self.reset(d);
        let (first, _) = self.env.decl_rows[d as usize];
        // quotient, inductive groups, unsafe and partial declarations run in
        // the scratch arena (see STATUS.md, milestone 10)
        let scratch = match &self.consts[first as usize].kind {
            CKind::Axiom { unsafe_ } | CKind::Opaque { unsafe_, .. } => *unsafe_,
            CKind::Defn { safety, .. } => *safety != 0,
            CKind::Thm { .. } => false,
            _ => true,
        };
        if scratch {
            self.enter_scratch();
        }
        let r = if scratch { self.check_decl_in(d) } else { self.check_decl_deep(d) };
        self.leave_scratch();
        // a failure, or a built-in reading not available yet: the session
        // ends before the next declaration
        if r.is_err() || self.stats.known_miss != self.known_miss0 {
            self.sess_end = true;
        }
        r
    }

    /// Milestone 45: the declaration, with the inferences and comparisons
    /// handed up from too deep (`Stop::DeepInfer`, `Stop::DeepDefeq`)
    /// worked out here, deepest first, and the declaration tried again.
    fn check_decl_deep(&mut self, d: u32) -> R<()> {
        enum Up {
            Inf(u32, u32, bool),
            Eq(V, V),
        }
        let (a0, l0, d0) = (self.argstack.len(), self.let_vals.len(), self.vdepth);
        let mut pend: Vec<Up> = Vec::new();
        loop {
            let r = match pend.last() {
                None => self.check_decl_in(d),
                Some(&Up::Inf(t, ls, c)) => self.infer(t, EMPTY, ls, c).map(|_| ()),
                Some(&Up::Eq(a, b)) => self.defeq(a, b).map(|_| ()),
            };
            let up = match r {
                Ok(()) => {
                    if pend.pop().is_none() {
                        return Ok(());
                    }
                    continue;
                }
                Err(Stop::DeepInfer) => {
                    let (t, ls, c) = self.deep_inf;
                    Up::Inf(t, ls, c)
                }
                Err(Stop::DeepDefeq) => Up::Eq(self.deep_eq.0, self.deep_eq.1),
                Err(e) => return Err(e),
            };
            // the frames between were unwound: their stacks too
            self.argstack.truncate(a0);
            self.let_vals.truncate(l0);
            self.vdepth_to(d0);
            self.wdepth = 0;
            self.stats.deep_up += 1;
            if pend.len() >= DEEP_PEND_CAP {
                return decline("recursion too deep (hand-ups)");
            }
            pend.push(up);
        }
    }

    fn check_decl_in(&mut self, d: u32) -> R<()> {
        let env = self.env;
        if env.decl_dup_params[d as usize] {
            return reject("universe parameters named twice");
        }
        let (first, _n) = env.decl_rows[d as usize];
        let c = &env.consts[first as usize];
        match &c.kind {
            CKind::Axiom { unsafe_ } => {
                self.setup_decl(first, if *unsafe_ { 1 } else { 0 });
                self.p1_active = 3 > 0;
                self.check_type(c.ty)?;
            }
            CKind::Defn { value, safety, .. } => {
                self.setup_decl(first, *safety);
                self.p1_active = 3 > 0;
                self.check_type(c.ty)?;
                if *safety == 1 {
                    self.self_vis = 4;
                }
                self.check_value(*value, c.ty)?;
                if *safety == 0 && *value < self.mlen && self.open_facts_on() {
                    self.open_record(first, *value, c.ty);
                }
            }
            CKind::Opaque { value, unsafe_, .. } => {
                self.setup_decl(first, if *unsafe_ { 1 } else { 0 });
                self.p1_active = 3 > 0;
                self.check_type(c.ty)?;
                self.check_value(*value, c.ty)?;
            }
            CKind::Thm { value, .. } => {
                self.setup_decl(first, 0);
                self.p1_active = 3 > 0;
                let val = match value {
                    ThmVal::Main(v) => *v,
                    ThmVal::Block(bi) => match self.block_roots.get(bi) {
                        // decoded already in this session (a block shared
                        // with an earlier theorem)
                        Some(&Some(r)) => r,
                        _ => {
                            let r = self.decode_block(*bi)?;
                            // the theorem is not visible in its own
                            // declaration; later ones in the session may
                            // unfold it
                            self.block_roots.insert(*bi, if self.trng(r) == 0 { Some(r) } else { None });
                            r
                        }
                    },
                };
                self.check_type(c.ty)?;
                let tv = self.eval(c.ty, EMPTY, 0)?;
                if !self.is_prop_type(tv)? {
                    return reject("theorem type is not a proposition");
                }
                self.check_value(val, c.ty)?;
            }
            CKind::Quot { .. } => self.check_quot(first)?,
            CKind::Induct { .. } | CKind::Ctor { .. } | CKind::Rec { .. } => self.check_inductive(d)?,
        }
        Ok(())
    }
}

const PDM_MASK: usize = (1 << 14) - 1;
/// milestone 22: slots of the canonical-application memo `cdm` (2^14 of 20
/// bytes, 320 KiB per worker; it was 2^16 = 1.3 MiB, which at 4 workers
/// crowded the shared L2: cycles -4..-5% for +0.2..+0.3% instructions), and
/// the default session size (the room this frees pays for 8 MiB sessions)
const CDM_BITS: u32 = 14;
const SESSION_MIB: usize = 8;
/// milestone 29: wide used-entry keys (`used_env_id_wide`): at most this
/// many variables, found within this many nodes
const WIDE_K: usize = 8;
/// (release-da: from the first tick, so the gates and vectors meet them)
/// milestone 31: names (and the inference site) from the first unfolding
/// in release-da, so the gates' small files exercise every name hit
/// milestone 31: the inference site's name budget and cost model (see `infer_full`)
const INFER_NAME_FUEL: u32 = 4096;
const INFER_NAME_CALLS: u64 = 256;
const INFER_REARM: u32 = 2;
const INFER_NAME_HITS: u64 = 4;
const INFER_NAME_PAY: u64 = 8;
const P2_VALUES: u64 = 1 << 20;
const MEMO_FLUSH: usize = 1 << 20;
const P2_UNFOLDS: u64 = if cfg!(debug_assertions) { 0 } else { 10_000 };
const WIDE_TICKS: u32 = if cfg!(debug_assertions) { 0 } else { 1 << 20 };
const WIDE_NODES: u32 = 256;
/// milestone 29: same_term's table marks a value-term pair by this depth
const VT_MARK: u32 = 0x7fff_fffe;
/// milestone 22: the mask of direct-mapped table k (0 pdm, 1 udm, 2 tdm)
fn dm_bits(k: usize) -> usize {
    [PDM_MASK, UDM_MASK, TDM_MASK][k]
}
/// an entry of a frame the term never reads (not a value id: `intern`
/// stops below it)
pub const HOLE: u32 = PROJ_BIT - 1;
/// milestone 27: ticks between two stack measurements (a power of two
/// dividing 4096, the cancellation period)
const TICK_STACK: u32 = 256;
const UDM_MASK: usize = (1 << 14) - 1;
/// milestone 34: slots of `lam_dm` minus one (a map grew with every checked
/// lambda of closed body type: cedar and con-leche +1%)
const LAM_DM_MASK: usize = (1 << 12) - 1;

#[cfg(feature = "cnt")]
pub static THUNK_KINDS: [std::sync::atomic::AtomicU64; 1200] = [const { std::sync::atomic::AtomicU64::new(0) }; 1200];

/// milestone 17: slots of same_term's direct-mapped memo, minus one
const TDM_MASK: usize = (1 << 13) - 1;
#[inline(always)]
fn hmix(h: u64, x: u64) -> u64 {
    (h ^ x).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(29)
}

#[cfg(test)]
mod nat_tests {
    use super::*;
    #[test]
    fn nat_mul_matches() {
        let mut seed = 0x1234_5678_9abc_def0u64;
        let mut rnd = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..2000 {
            let nl = 32 + (rnd() % 64) as usize;
            let ns = 1 + (rnd() % 4) as usize;
            let mut a: Vec<u32> = (0..2 * nl).map(|_| if rnd() % 3 == 0 { rnd() as u32 } else { 0 }).collect();
            a.push(1);
            let b: Vec<u32> = (0..2 * ns).map(|_| if rnd() % 4 == 0 { 0 } else { rnd() as u32 }).collect();
            let (x, y) = (BigUint::new(a), BigUint::new(b));
            assert_eq!(nat_mul(&x, &y), &x * &y);
            assert_eq!(nat_mul(&y, &x), &x * &y);
        }
    }
}
