//! Milestone 39: the ground machine (docs/architecture.md, Ground
//! machine). A closed computation compared with data (`decide p =?= true`,
//! `f x =?= 1209600`, a computed array against a constructor application)
//! is worked out by a call-by-need machine of its own instead of the
//! session's hash-consed values: its thunks are updated in place and drop
//! their environments once forced, and its objects are reference counted,
//! so what a computation no longer reaches is freed at once (a session's
//! values live until a region rolls back or the session ends: a lazy
//! `Array.push` chain kept every intermediate list, O(n^2) values).
//!
//! It runs the kernel's own rules on the same terms (Susz ids, level
//! substitutions of the session): beta, zeta, delta of visible definitions
//! and theorems with as many levels as parameters, iota with the
//! recursors' rules (Nat and String literals as constructors), projections
//! of constructor applications, the Nat operations on literals. Every
//! other step is handed to the kernel (`whnf`, `iota`, `quot_reduce`,
//! `defeq` on values exported from the machine): K-like recursors,
//! structure eta, quotients, stuck projections, sorts and Pi types.
//! A comparison it cannot finish (a mismatch, a function) goes to the
//! kernel's `defeq` on the two weak head normal forms, so the machine only
//! ever answers `true` by itself; `false` and everything else come from
//! the kernel.
use super::*;
use std::cell::RefCell;
use std::rc::Rc;

pub(super) type O = Rc<Obj>;

pub(super) enum Obj {
    Nat(BigUint),
    /// a string literal (index into the literal table)
    Str(u32),
    /// a constant applied to arguments: a constructor (`ctor`), or a
    /// constant that does not reduce with them; `part`: a recursor or
    /// quotient eliminator short of its major premise
    Con { row: u32, llr: u32, args: Vec<O>, ctor: bool, part: bool },
    /// a lambda with its environment
    Clo { term: u32, env: Env, ls: u32 },
    /// a value of the kernel in weak head normal form kept as it is (sorts,
    /// Pi types, free variables, stuck projections)
    G(V),
    Th(RefCell<Th>),
    /// a constructor's parameter that was a delayed term over an
    /// environment: dropped so that the environment can go (a type such as
    /// `PProd (motive x) (List.below motive x)` in every cell of a
    /// structural recursion kept the list it recursed on); anything that
    /// needs it gives the run back to the kernel
    Erased,
}

pub(super) enum Th {
    Delay(u32, Env, u32),
    /// a value of the kernel not looked at yet
    Ext(V),
    /// field `.0` (structure name `.1`... see `g_eta`) of an object, not
    /// looked at yet: structure eta of a recursor's major premise
    Proj(O, u32, u32),
    Busy,
    Done(O),
}

#[derive(Clone)]
pub(super) enum Env {
    Nil,
    Cons(Rc<ENode>),
    /// an environment of the kernel
    G(u32),
}
pub(super) struct ENode {
    v: O,
    next: Env,
}

#[derive(Clone)]
enum El {
    App(O),
    /// field index, structure name
    Proj(u32, u32),
}

enum Fr {
    Stop(usize),
    /// a thunk forced: its update, the base below it, and (milestone 40)
    /// the clock when it began and the key it is memoised under
    Upd(O, usize, u64, u32, Option<Box<[Atom]>>, Orig),
    Rec { row: u32, llr: u32, pre: Vec<O>, major: O, base: usize },
    /// casesOn `row` read directly (its recursor `rrow`): all its arguments
    Cases { row: u32, llr: u32, rrow: u32, args: Vec<O>, base: usize },
    /// unary Nat operation (`SUCC` or `LOG2`) waiting for its operand
    Nat1 { row: u32, llr: u32, op: u8, x: O, base: usize },
    NatA { row: u32, llr: u32, op: u8, x: O, y: O, base: usize },
    NatB { row: u32, llr: u32, op: u8, a: O, x: O, y: O, base: usize },
}

/// Milestone 40: what a thunk held before it was forced, to put back when
/// the run is given back while the thunk is being forced (the environment
/// weakly: holding it during the forcing would keep what the evaluation
/// lets go of)
enum Orig {
    Delay(u32, Option<std::rc::Weak<ENode>>, u32, Option<u32>),
    Ext(V),
    Proj(O, u32, u32),
}

enum C {
    Ev(u32, Env, u32),
    Ob(O),
    Hd(u32, u32),
}

const SUCC: u8 = 100;
const LOG2: u8 = 101;

/// Milestone 40: a part of a delayed term's key (`g_memo_key`): the term
/// and level substitution, a small literal by value, a value of the kernel
/// or a kernel environment by id, any other object by address. The weak
/// reference keeps the address taken while the key lives (no other object
/// can be made there), so equal keys name the same objects.
#[derive(Clone)]
pub(super) enum Atom {
    T(u32, u32),
    N(u64),
    X(V),
    G(u32, u32),
    E,
    End,
    P(std::rc::Weak<Obj>),
}
impl PartialEq for Atom {
    fn eq(&self, o: &Atom) -> bool {
        match (self, o) {
            (Atom::T(a, b), Atom::T(c, d)) | (Atom::G(a, b), Atom::G(c, d)) => a == c && b == d,
            (Atom::N(a), Atom::N(b)) => a == b,
            (Atom::X(a), Atom::X(b)) => a == b,
            (Atom::E, Atom::E) | (Atom::End, Atom::End) => true,
            (Atom::P(a), Atom::P(b)) => std::rc::Weak::ptr_eq(a, b),
            _ => false,
        }
    }
}
impl Eq for Atom {}
impl std::hash::Hash for Atom {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        match self {
            Atom::T(a, b) => (1u8, *a, *b).hash(h),
            Atom::N(a) => (2u8, *a).hash(h),
            Atom::X(a) => (3u8, *a).hash(h),
            Atom::G(a, b) => (4u8, *a, *b).hash(h),
            Atom::E => 5u8.hash(h),
            Atom::End => 6u8.hash(h),
            Atom::P(w) => (7u8, w.as_ptr() as usize).hash(h),
        }
    }
}

/// Milestone 40: what forcing a term has cost so far (steps, forcings) and
/// how its memo lookups went.
#[derive(Default, Clone, Copy)]
pub(super) struct TStat {
    n: u32,
    steps: u64,
    look: u32,
    hit: u32,
}

/// The machine's state: a run's stacks and maps, and what the runs of one
/// declaration share (milestone 40: the heap is kept from run to run).
pub(super) struct Gm {
    el: Vec<El>,
    base: usize,
    fr: Vec<Fr>,
    /// the kernel's values imported: the object while the machine holds
    /// it, and the last run that imported it (a strong map kept every
    /// intermediate list of a lazy push chain built by the kernel alive)
    imp: FxHashMap<V, (std::rc::Weak<Obj>, u32)>,
    /// milestone 40: values imported again by a later run, kept: what the
    /// kernel hands the machine run after run (a table, a list every
    /// element of a loop reads) is worked out once
    pin: FxHashMap<V, O>,
    lits: FxHashMap<u32, O>,
    exp: FxHashMap<usize, V>,
    eexp: FxHashMap<usize, u32>,
    keep: Vec<O>,
    ekeep: Vec<Rc<ENode>>,
    erased: O,
    /// constants met with no arguments (a table, a closed value): one
    /// delayed object each, forced once, as the kernel's value of a
    /// constant keeps its whnf
    caf: FxHashMap<(u32, u32), O>,
    /// steps left; out of them the run is given back to the kernel
    fuel: u64,
    out: bool,
    /// knobs, SK_GROUND_SHARE: repeated thunks being forced (frame index,
    /// an earlier one alive, term)
    rep: Vec<(usize, bool, u32)>,
    /// runs so far, and the arena's lengths when the last one ended (the
    /// heap names no value, environment or literal past them)
    run: u32,
    hv: u32,
    he: u32,
    hw: u32,
    /// milestone 40: forced delayed terms by key (their results), and
    /// per term what forcing it costs
    memo: FxHashMap<Box<[Atom]>, O>,
    tstat: FxHashMap<u32, TStat>,
    /// milestone 40: the last export stopped at an erased parameter
    erased_hit: bool,
}

impl Gm {
    /// A result kept under its key, unless the machine already holds more
    /// objects than the kernel's arena has values: then the memo starts
    /// over (it may not keep more than the kernel would).
    fn memo_put(&mut self, k: Box<[Atom]>, w: O, vals: usize) {
        if NOBJ.with(|n| n.get()) > vals as i64 && !self.memo.is_empty() {
            self.memo = FxHashMap::default();
        }
        self.memo.insert(k, w);
    }
    fn new() -> Gm {
        Gm {
            el: Vec::new(),
            base: 0,
            fr: Vec::new(),
            imp: FxHashMap::default(),
            pin: FxHashMap::default(),
            lits: FxHashMap::default(),
            exp: FxHashMap::default(),
            eexp: FxHashMap::default(),
            keep: Vec::new(),
            ekeep: Vec::new(),
            erased: mk(Obj::Erased),
            fuel: 0,
            out: false,
            caf: FxHashMap::default(),
            rep: Vec::new(),
            run: 0,
            hv: 0,
            he: 0,
            hw: 0,
            memo: FxHashMap::default(),
            tstat: FxHashMap::default(),
            erased_hit: false,
        }
    }
    /// Milestone 40: a run given back: every thunk being forced gets what
    /// it held back, so the heap stays usable. false: one cannot (its
    /// environment is gone); the heap must go.
    fn restore(&mut self) -> bool {
        let mut ok = true;
        while let Some(f) = self.fr.pop() {
            if let Fr::Upd(th, _, _, _, _, orig) = f {
                let Obj::Th(cell) = &*th else { continue };
                if !matches!(&*cell.borrow(), Th::Busy) {
                    continue;
                }
                let back = match orig {
                    Orig::Delay(t, None, ls, g) => Some(Th::Delay(t, g.map_or(Env::Nil, Env::G), ls)),
                    Orig::Delay(t, Some(w), ls, _) => w.upgrade().map(|n| Th::Delay(t, Env::Cons(n), ls)),
                    Orig::Ext(v) => Some(Th::Ext(v)),
                    Orig::Proj(x, i, s) => Some(Th::Proj(x, i, s)),
                };
                match back {
                    Some(b) => *cell.borrow_mut() = b,
                    None => ok = false,
                }
            }
        }
        ok
    }

    /// The next run: per-run state cleared.
    fn start(&mut self) {
        self.el.clear();
        self.base = 0;
        self.fr.clear();
        self.exp.clear();
        self.eexp.clear();
        self.keep.clear();
        self.ekeep.clear();
        self.out = false;
        self.rep.clear();
        self.run += 1;
    }
}

thread_local! {
    /// milestone 40: live machine objects (all builds): the kept heap may
    /// not outgrow the kernel's own arena
    pub(super) static NOBJ: std::cell::Cell<i64> = const { std::cell::Cell::new(0) };
}

thread_local! {
    /// knobs: live objects by kind (Nat, Str, Con, Clo, G, Th, ENode)
    pub(super) static LIVE: std::cell::Cell<[i64; 7]> = const { std::cell::Cell::new([0; 7]) };
}
fn kind_ix(o: &Obj) -> usize {
    match o {
        Obj::Nat(_) => 0,
        Obj::Str(_) => 1,
        Obj::Con { .. } => 2,
        Obj::Clo { .. } => 3,
        Obj::G(_) => 4,
        Obj::Th(_) | Obj::Erased => 5,
    }
}
fn live_add(i: usize, d: i64) {
    if KNOBS {
        LIVE.with(|l| {
            let mut x = l.get();
            x[i] += d;
            l.set(x);
        });
    }
}
thread_local! {
    /// knobs, SK_GROUND_CENSUS=1: live objects by what made them
    pub(super) static CENSUS: RefCell<(bool, FxHashMap<usize, (u8, u32)>, FxHashMap<(u8, u32), i64>)> =
        RefCell::new((KNOBS && std::env::var_os("SK_GROUND_CENSUS").is_some(), FxHashMap::default(), FxHashMap::default()));
}
thread_local! {
    /// knobs: objects made per constructor row / closure term (diagnostics)
    pub(super) static MADE: RefCell<FxHashMap<(u8, u32), u64>> = RefCell::new(FxHashMap::default());
}
thread_local! {
    /// knobs, SK_GROUND_SHARE=1: a structural key per object (address ->
    /// key), forced thunks and unfolded applications by key: how much
    /// work the machine repeats that hash-consing would share
    pub(super) static SHARE: RefCell<Share> = RefCell::new(Share {
        on: KNOBS && std::env::var_os("SK_GROUND_SHARE").is_some(),
        sid: FxHashMap::default(),
        forced: FxHashMap::default(),
        unf: FxHashMap::default(),
        nforced: 0,
        nunf: 0,
        saved: 0,
        saved_live: 0,
        saved_by: FxHashMap::default(),
    });
}
pub(super) struct Share {
    on: bool,
    sid: FxHashMap<usize, u64>,
    /// key -> (term, times forced, the last one forced)
    forced: FxHashMap<u64, (u32, u32, std::rc::Weak<Obj>)>,
    /// steps under a repeated thunk (any earlier one / an earlier one still alive)
    saved: u64,
    saved_live: u64,
    /// outermost repeated thunk's term -> steps under it
    saved_by: FxHashMap<u32, (u64, u64)>,
    /// key -> (row, times unfolded)
    unf: FxHashMap<u64, (u32, u32)>,
    nforced: u64,
    nunf: u64,
}
fn hmix(a: u64, b: u64) -> u64 {
    (a.rotate_left(5) ^ b).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}
fn share_on() -> bool {
    KNOBS && SHARE.with(|s| s.borrow().on)
}
fn sid_of(sh: &Share, p: usize) -> u64 {
    sh.sid.get(&p).copied().unwrap_or(0xdead)
}
fn env_sid(sh: &Share, e: &Env) -> u64 {
    match e {
        Env::Nil => 1,
        Env::G(g) => hmix(2, *g as u64),
        Env::Cons(n) => sid_of(sh, Rc::as_ptr(n) as usize),
    }
}
fn obj_sid(sh: &Share, o: &Obj) -> u64 {
    match o {
        Obj::Nat(n) => n.iter_u64_digits().fold(3, hmix),
        Obj::Str(i) => hmix(4, *i as u64),
        Obj::Con { row, llr, args, .. } => {
            args.iter().fold(hmix(hmix(5, *row as u64), *llr as u64), |h, a| hmix(h, sid_of(sh, Rc::as_ptr(a) as usize)))
        }
        Obj::Clo { term, env, ls } => hmix(hmix(hmix(6, *term as u64), *ls as u64), env_sid(sh, env)),
        Obj::G(v) => hmix(7, *v as u64),
        Obj::Erased => 8,
        Obj::Th(c) => match &*c.borrow() {
            Th::Delay(t, env, ls) => hmix(hmix(hmix(9, *t as u64), *ls as u64), env_sid(sh, env)),
            Th::Ext(v) => hmix(7, *v as u64),
            Th::Proj(x, i, s) => hmix(hmix(hmix(10, sid_of(sh, Rc::as_ptr(x) as usize)), *i as u64), *s as u64),
            Th::Done(x) => sid_of(sh, Rc::as_ptr(x) as usize),
            Th::Busy => 11,
        },
    }
}
/// (repeated, an earlier one alive)
fn share_forced(o: &O, t: u32) -> (bool, bool) {
    SHARE.with(|s| {
        let mut s = s.borrow_mut();
        let k = sid_of(&s, Rc::as_ptr(o) as usize);
        s.nforced += 1;
        let e = s.forced.entry(k).or_insert((t, 0, std::rc::Weak::new()));
        e.1 += 1;
        let live = e.2.upgrade().is_some();
        e.2 = Rc::downgrade(o);
        (e.1 > 1, live)
    })
}
fn share_step(m: &Gm) {
    if let Some(&(_, live, t)) = m.rep.first() {
        let anylive = live || m.rep.iter().any(|r| r.1);
        SHARE.with(|s| {
            let s = &mut *s.borrow_mut();
            s.saved += 1;
            if anylive {
                s.saved_live += 1;
            }
            let e = s.saved_by.entry(t).or_insert((0, 0));
            e.0 += 1;
            if anylive {
                e.1 += 1;
            }
        })
    }
}
fn share_unf(row: u32, llr: u32, args: &[O]) {
    SHARE.with(|s| {
        let mut s = s.borrow_mut();
        let k = args.iter().fold(hmix(hmix(12, row as u64), llr as u64), |h, a| hmix(h, sid_of(&s, Rc::as_ptr(a) as usize)));
        s.nunf += 1;
        s.unf.entry(k).or_insert((row, 0)).1 += 1;
    })
}
#[inline(always)]
fn mk(o: Obj) -> O {
    NOBJ.with(|n| n.set(n.get() + 1));
    if KNOBS {
        if share_on() {
            let r = Rc::new(o);
            SHARE.with(|s| {
                let mut s = s.borrow_mut();
                let k = obj_sid(&s, &r);
                s.sid.insert(Rc::as_ptr(&r) as usize, k);
            });
            return r;
        }
        let k = match &o {
            Obj::Con { row, ctor, .. } => Some((*ctor as u8, *row)),
            Obj::Clo { term, .. } => Some((2, *term)),
            Obj::Th(c) => match &*c.borrow() { Th::Delay(t, ..) => Some((3, *t)), _ => None },
            _ => None,
        };
        if let Some(k) = k {
            MADE.with(|m| *m.borrow_mut().entry(k).or_insert(0) += 1);
        }
        live_add(kind_ix(&o), 1);
        let r = Rc::new(o);
        if CENSUS.with(|c| c.borrow().0) {
            let k = k.unwrap_or((9, kind_ix(&r) as u32));
            CENSUS.with(|c| {
                let mut c = c.borrow_mut();
                c.1.insert(Rc::as_ptr(&r) as usize, k);
                *c.2.entry(k).or_insert(0) += 1;
            });
        }
        return r;
    }
    Rc::new(o)
}
#[inline(always)]
fn mke(n: ENode) -> Rc<ENode> {
    live_add(6, 1);
    if share_on() {
        let r = Rc::new(n);
        SHARE.with(|s| {
            let mut s = s.borrow_mut();
            let k = hmix(hmix(13, sid_of(&s, Rc::as_ptr(&r.v) as usize)), env_sid(&s, &r.next));
            s.sid.insert(Rc::as_ptr(&r) as usize, k);
        });
        return r;
    }
    Rc::new(n)
}
impl Drop for ENode {
    fn drop(&mut self) {
        live_add(6, -1);
        // milestone 42: the rest of the chain freed without recursion (a
        // chain dropped from outside an object, a local or a table, freed
        // one Rust frame per node before)
        let mut next = std::mem::replace(&mut self.next, Env::Nil);
        while let Env::Cons(n) = next {
            match Rc::try_unwrap(n) {
                // its own `next` taken first: its drop does not walk on
                Ok(mut node) => next = std::mem::replace(&mut node.next, Env::Nil),
                Err(_) => break,
            }
        }
    }
}

// Objects are freed without recursion: a list of millions of cells would
// otherwise drop one Rust frame per cell.
struct Drain {
    on: bool,
    o: Vec<O>,
    e: Vec<Rc<ENode>>,
}
thread_local! {
    static DRAIN: RefCell<Drain> = const { RefCell::new(Drain { on: false, o: Vec::new(), e: Vec::new() }) };
}
fn kids(x: &mut Obj, d: &mut Drain) {
    match x {
        Obj::Con { args, .. } => d.o.append(args),
        Obj::Clo { env, .. } => {
            if let Env::Cons(n) = std::mem::replace(env, Env::Nil) {
                d.e.push(n)
            }
        }
        Obj::Th(c) => match std::mem::replace(c.get_mut(), Th::Busy) {
            Th::Delay(_, Env::Cons(n), _) => d.e.push(n),
            Th::Done(o) | Th::Proj(o, ..) => d.o.push(o),
            _ => {}
        },
        _ => {}
    }
}
impl Drop for Obj {
    fn drop(&mut self) {
        NOBJ.with(|n| n.set(n.get() - 1));
        live_add(kind_ix(self), -1);
        if KNOBS && CENSUS.with(|c| c.borrow().0) {
            let p = self as *const Obj as usize;
            CENSUS.with(|c| {
                let mut c = c.borrow_mut();
                if let Some(k) = c.1.remove(&p) {
                    *c.2.entry(k).or_insert(0) -= 1;
                }
            });
        }
        match self {
            Obj::Nat(_) | Obj::Str(_) | Obj::G(_) | Obj::Erased => return,
            Obj::Con { args, .. } if args.is_empty() => return,
            _ => {}
        }
        DRAIN.with(|cell| {
            let mut d = cell.borrow_mut();
            kids(self, &mut d);
            if d.on {
                return;
            }
            d.on = true;
            loop {
                if let Some(o) = d.o.pop() {
                    drop(d);
                    let p = Rc::as_ptr(&o) as usize;
                    if let Ok(mut x) = Rc::try_unwrap(o) {
                        if KNOBS && CENSUS.with(|c| c.borrow().0) {
                            CENSUS.with(|c| {
                                let mut c = c.borrow_mut();
                                if let Some(k) = c.1.remove(&p) {
                                    *c.2.entry(k).or_insert(0) -= 1;
                                }
                            });
                        }
                        kids(&mut x, &mut cell.borrow_mut());
                    }
                    d = cell.borrow_mut();
                    continue;
                }
                if let Some(e) = d.e.pop() {
                    drop(d);
                    if let Ok(mut n) = Rc::try_unwrap(e) {
                        let next = std::mem::replace(&mut n.next, Env::Nil);
                        let mut dd = cell.borrow_mut();
                        if let Env::Cons(m) = next {
                            dd.e.push(m);
                        }
                        drop(dd);
                        // n.v drops here (its kids go to the stack)
                        drop(n);
                    }
                    d = cell.borrow_mut();
                    continue;
                }
                break;
            }
            d.on = false;
        })
    }
}

/// Stop::Ground, with its reason under SK_GROUND_TRACE (knobs)
#[cold]
fn gstop<T>(why: &str) -> R<T> {
    if KNOBS && std::env::var_os("SK_GROUND_TRACE").is_some() {
        eprintln!("GSTOP {why}");
    }
    Err(Stop::Ground)
}

fn top_app(m: &Gm) -> bool {
    m.el.len() > m.base && matches!(m.el.last(), Some(El::App(_)))
}

/// The kernel's Nat operation `op` (index into NAT_OPS) on literals, or
/// the reason Lean's kernel refuses it (milestone 47, Lean's rule from
/// v4.34: a count past 32 bits, or a result past `NAT_MAX_BYTES`, is a
/// kernel exception; the operation is never unfolded from its definition).
pub(super) enum NatR {
    N(BigUint),
    B(bool),
}
pub(super) fn nat_fold(op: usize, x: &BigUint, y: &BigUint) -> Result<NatR, &'static str> {
    Ok(NatR::N(match NAT_OPS[op] {
        "add" => nat_sized(x + y)?,
        "sub" => {
            if x >= y {
                x - y
            } else {
                BigUint::zero()
            }
        }
        "mul" => {
            // the product has at least bits(x) + bits(y) - 1 bits: past
            // the bound it is refused before it is made
            if !x.is_zero() && !y.is_zero() && (x.bits() + y.bits() - 1).div_ceil(8) > NAT_MAX_BYTES {
                return Err(NAT_SIZE_MSG);
            }
            nat_sized(nat_mul(x, y))?
        }
        "div" => {
            if y.is_zero() {
                BigUint::zero()
            } else {
                x / y
            }
        }
        "mod" => {
            if y.is_zero() {
                x.clone()
            } else {
                x % y
            }
        }
        "gcd" => num_integer::Integer::gcd(x, y),
        "beq" => return Ok(NatR::B(x == y)),
        "ble" => return Ok(NatR::B(x <= y)),
        "land" => x & y,
        "lor" => x | y,
        "xor" => x ^ y,
        "shiftLeft" => {
            if x.is_zero() {
                // Lean reads no count for 0 <<< _
                BigUint::zero()
            } else {
                let Some(k) = y.to_u32() else {
                    return Err("the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer");
                };
                // Lean's estimate: size(x) + k/8 + 1 bytes
                if nat_bytes(x) + k as u64 / 8 + 1 > NAT_MAX_BYTES {
                    return Err(NAT_SIZE_MSG);
                }
                x << k
            }
        }
        "shiftRight" => match y.to_u64() {
            Some(s) => x >> s,
            None => BigUint::zero(),
        },
        "pow" => {
            let Some(k) = y.to_u32() else {
                return Err("the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer");
            };
            // Lean's estimate: size(x) * k bytes, compared by division
            if k != 0 && *x > BigUint::from(1u32) && nat_bytes(x) > NAT_MAX_BYTES / k as u64 {
                return Err("the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; increase the LEAN_NAT_MAX_SIZE environment variable to allow it");
            }
            x.pow(k)
        }
        _ => unreachable!("NAT_OPS"),
    }))
}

impl Worker {
    /// knobs: the most made objects of the ground machine
    pub(super) fn ground_share_report(&self) {
        SHARE.with(|s| {
            let s = s.borrow();
            if !s.on {
                return;
            }
            eprintln!("SHARE forced {} distinct {} | unfolds {} distinct {} | ev steps under repeats {} (earlier alive {})", s.nforced, s.forced.len(), s.nunf, s.unf.len(), s.saved, s.saved_live);
            let mut v: Vec<(u64, u64, u32)> = s.saved_by.iter().map(|(&t, &(a, l))| (a, l, t)).collect();
            v.sort_unstable_by(|a, b| b.cmp(a));
            for (a, l, t) in v.into_iter().take(15) {
                eprintln!("SHARE-S steps {a:>11} alive {l:>11} term {t} {}", self.g_term_str(t, 6));
            }
            let mut byt: FxHashMap<u32, (u64, u64)> = FxHashMap::default();
            for &(t, c, _) in s.forced.values() {
                let e = byt.entry(t).or_insert((0, 0));
                e.0 += c as u64;
                e.1 += 1;
            }
            let mut v: Vec<(u64, u64, u32)> = byt.into_iter().map(|(t, (c, d))| (c - d, c, t)).collect();
            v.sort_unstable_by(|a, b| b.cmp(a));
            for (rep, c, t) in v.into_iter().take(15) {
                eprintln!("SHARE-T repeat {rep:>11} of {c:>11} term {t} {}", self.g_term_str(t, 5));
            }
            let mut byr: FxHashMap<u32, (u64, u64)> = FxHashMap::default();
            for &(r, c) in s.unf.values() {
                let e = byr.entry(r).or_insert((0, 0));
                e.0 += c as u64;
                e.1 += 1;
            }
            let mut v: Vec<(u64, u64, u32)> = byr.into_iter().map(|(r, (c, d))| (c - d, c, r)).collect();
            v.sort_unstable_by(|a, b| b.cmp(a));
            for (rep, c, r) in v.into_iter().take(25) {
                eprintln!("SHARE-U repeat {rep:>11} of {c:>11} {}", self.env.name_str(self.consts[r as usize].name));
            }
        });
    }

    pub(super) fn ground_made_report(&self) {
        self.ground_share_report();
        CENSUS.with(|c| {
            let c = c.borrow();
            let mut v: Vec<(i64, (u8, u32))> = c.2.iter().map(|(&k, &n)| (n, k)).collect();
            v.sort_unstable_by(|a, b| b.cmp(a));
            for (n, (k, x)) in v.into_iter().take(20) {
                let what = match k {
                    0 | 1 => self.env.name_str(self.consts[x as usize].name).to_string(),
                    9 => format!("kind {x}"),
                    _ => format!("term {x} {}", self.g_term_str(x, 4)),
                };
                eprintln!("CENSUS {n:>12} {k} {what}");
            }
        });
        MADE.with(|m| {
            let m = m.borrow();
            let mut v: Vec<(u64, (u8, u32))> = m.iter().map(|(&k, &c)| (c, k)).collect();
            v.sort_unstable_by(|a, b| b.cmp(a));
            for (c, (k, x)) in v.into_iter().take(30) {
                let what = match k {
                    0 | 1 => self.env.name_str(self.consts[x as usize].name).to_string(),
                    5 if x >= 10 => self.env.name_str(self.consts[(x - 10) as usize].name).to_string(),
                    _ => format!("term {x} {}", self.g_term_str(x, 4)),
                };
                eprintln!("GM {c:>12} {} {what}", ["stuck", "ctor", "clo", "thunk", "reimp-thunk", "reimp-kind"][k as usize]);
            }
        });
    }

    /// knobs, SK_SHOW=NAME,...: the named constants' kinds, types and
    /// values as text (milestone 41: reading compiled bodies)
    pub fn show_consts(&self) {
        let Some(want) = std::env::var("SK_SHOW").ok() else { return };
        let d: u32 = std::env::var("SK_SHOW_DEPTH").ok().and_then(|s| s.parse().ok()).unwrap_or(40);
        let want: Vec<&str> = want.split(',').collect();
        for (r, c) in self.consts.iter().enumerate() {
            let n = self.env.name_str(c.name);
            if !want.iter().any(|w| *w == n) {
                continue;
            }
            eprintln!("SHOW {n} row {r} kind {:?}", c.kind);
            eprintln!("  type  {}", self.g_term_str(c.ty, d));
            let v = match c.kind {
                CKind::Defn { value, .. } => Some(value),
                CKind::Thm { value: ThmVal::Main(v), .. } => Some(v),
                CKind::Opaque { value, .. } => Some(value),
                _ => None,
            };
            if let Some(v) = v {
                eprintln!("  value {}", self.g_term_str(v, d));
            }
            if let CKind::Rec { rules, .. } = &c.kind {
                for &(cn, nf, rhs) in rules.iter() {
                    eprintln!("  rule {} {nf}: {}", self.env.name_str(cn), self.g_term_str(rhs, d));
                }
            }
        }
    }

    /// knobs: a term as text (depth-limited)
    fn g_term_str(&self, t: u32, d: u32) -> String {
        if d == 0 {
            return "…".into();
        }
        let n = self.node(t);
        match n.kind {
            BVAR => format!("#{}", n.p),
            CONST => self.env.name_str(n.a).to_string(),
            APP => {
                let mut f = t;
                let mut xs = Vec::new();
                while self.node(f).kind == APP {
                    xs.push(self.node(f).b);
                    f = self.node(f).a;
                }
                let mut s = format!("({}", self.g_term_str(f, d - 1));
                for &x in xs.iter().rev() {
                    s.push(' ');
                    s.push_str(&self.g_term_str(x, d - 1));
                }
                s.push(')');
                s
            }
            NAT => format!("{}", match self.lit(n.p) { LitVal::Nat(x) => x.to_string(), _ => "?".into() }),
            k if is_lam(k) => format!("(λ {})", self.g_term_str(n.b, d - 1)),
            k if is_pi(k) => format!("(Π {})", self.g_term_str(n.b, d - 1)),
            LET => format!("(let {})", self.g_term_str(self.let_body(t), d - 1)),
            PROJ => format!("{}.{}", self.g_term_str(n.a, d - 1), n.b),
            _ => format!("k{}", n.kind),
        }
    }

    /// Is `v` data: a literal or a constructor application?
    fn g_data(&self, v: V) -> bool {
        matches!(self.val(v), Val::Lit(_)) || self.is_ctor_app_only(v)
    }
    /// Milestone 39: the comparison of `a` and `b` (both after whnf_core)
    /// by the ground machine, when one side is data (a literal or a
    /// constructor application) and the other a closed computation headed
    /// by a constant, once the session wants regions (a heavy declaration:
    /// the kernel's own way has made 2^22 values). Lazy delta would unfold
    /// the computing side until its head is a constructor too: the same
    /// weak head normal form the machine computes.
    pub(super) fn ground_try(&mut self, a: V, b: V) -> R<Option<bool>> {
        if !self.ground || self.ground_busy || !self.ground_wanted() {
            return Ok(None);
        }
        let (da, db) = (self.g_data(a), self.g_data(b));
        let (x, y) = if da { (b, a) } else { (a, b) };
        if self.ground_all {
            if da && db || !matches!(self.val(x), Val::Neu { head: Head::Const(..), .. }) {
                return Ok(None);
            }
        } else {
            if da == db {
                return Ok(None);
            }
            if !matches!(self.val(x), Val::Neu { head: Head::Const(..), .. }) {
                return Ok(None);
            }
        }
        if self.has_fvar(x) || self.has_fvar(y) || !self.ground_may_run() {
            return Ok(None);
        }
        self.ground_defeq(x, y)
    }

    /// Milestone 39: the weak head normal form of a closed value by the
    /// ground machine, once the session wants regions (a heavy
    /// declaration). None: not taken.
    pub(super) fn ground_whnf(&mut self, v: V) -> R<Option<V>> {
        if !self.ground || self.ground_busy || !self.ground_wanted() || self.has_fvar(v) || !self.ground_may_run() {
            return Ok(None);
        }
        self.ground_busy = true;
        self.stats.gr[0] += 1;
        let mut m = self.gm_take();
        m.fuel = self.ground_fuel_now();
        let f0 = m.fuel;
        let trace = KNOBS && std::env::var_os("SK_GROUND_TRACE").is_some();
        if trace {
            eprintln!("GW-start v{v} {}", self.vshow(v, 4));
        }
        if dstack_on() {
            dstack_push(b'g', v, NONE, self.ticks);
        }
        let r = (|| -> R<V> {
            let o = self.g_import(&mut m, v);
            let w = self.g_whnf(&mut m, o)?;
            self.g_export_root(&mut m, &w, v)
        })();
        if dstack_on() {
            dstack_pop();
        }
        self.ground_busy = false;
        let m_out = m.out;
        let ok = r.is_ok();
        if trace {
            let h = match self.val(v) {
                Val::Neu { head: Head::Const(r, _), .. } => self.env.name_str(self.consts[r as usize].name).to_string(),
                Val::Thunk { term, .. } => format!("thunk {}", self.g_term_str(term, 3)),
                _ => "other".into(),
            };
            eprintln!("GW v{v} steps {} {h} -> {:?}", f0 - m.fuel, r.as_ref().map(|&x| self.vshow(x, 2)));
        }
        self.gm_put(m, ok);
        let r = match r {
            Err(Stop::Ground) => {
                self.stats.gr[2] += 1;
                if m_out {
                    self.ground_ran_out();
                }
                return Ok(None);
            }
            r => r?,
        };
        if r != v {
            self.memo_w(r).whnf = r;
        }
        Ok(Some(r))
    }

    /// Milestone 40: the machine of this declaration, kept from its last
    /// run unless a rollback since then cut the arena below what its heap
    /// may name (values, environments, literals made before the last run
    /// ended).
    fn gm_take(&mut self) -> Box<Gm> {
        let c = std::mem::replace(&mut self.ground_cut, (u32::MAX, u32::MAX, u32::MAX));
        let mut m = match self.gm.take() {
            Some(m) if c.0 >= m.hv && c.1 >= m.he && c.2 >= m.hw => m,
            Some(m) => {
                self.stats.gr[8] += 1;
                drop(m);
                Box::new(Gm::new())
            }
            None => Box::new(Gm::new()),
        };
        m.start();
        m
    }
    /// After a run: the machine kept for the next one, unless the run
    /// failed (a thunk may be left busy) or the kept heap holds more objects
    /// than the kernel's arena has values (it may not outgrow the kernel).
    fn gm_put(&mut self, mut m: Box<Gm>, ok: bool) {
        let ok = ok || m.restore();
        m.exp.clear();
        m.eexp.clear();
        m.keep.clear();
        m.ekeep.clear();
        m.el.clear();
        m.fr.clear();
        // rollbacks inside the run cut only what the run made after its
        // own ids (the kernel's calls from the machine)
        self.ground_cut = (u32::MAX, u32::MAX, u32::MAX);
        if !ok || NOBJ.with(|n| n.get()) > self.vals.len() as i64 {
            if ok {
                self.stats.gr[9] += 1;
            }
            drop(m);
            return;
        }
        m.hv = self.vals.len() as u32;
        m.he = self.eloc.len() as u32;
        m.hw = self.wlits.len() as u32;
        self.gm = Some(m);
    }

    /// Milestone 39: the machine takes closed computations once the
    /// session holds `ground_at` values (`GROUND_AT`, 16 times the values
    /// that open regions: regions did not keep the declaration small;
    /// below it the kernel's hash-consing shares repeated work the machine
    /// would redo: CFSG's SuzData holds about 2^25.4), or in the gate mode.
    pub(super) fn ground_wanted(&self) -> bool {
        self.ground_heavy() || self.ground_all
    }
    fn ground_heavy(&self) -> bool {
        self.vals.len() >= self.ground_at && !self.scratch
    }

    /// The budget of a run: none in a heavy declaration (the session wants
    /// regions: the declaration is a computation, and the kernel's way is
    /// the one that ran out of memory), else `ground_fuel`.
    fn ground_fuel_now(&mut self) -> u64 {
        if self.ground_heavy() { u64::MAX } else { self.ground_fuel }
    }
    /// May a run start? Not until the kernel has worked as many ticks as
    /// the budget since a run last ran out.
    fn ground_may_run(&mut self) -> bool {
        match self.ground_out_at {
            Some(t) if !self.ground_heavy() => self.ticks.wrapping_sub(t as u32) as u64 >= self.ground_fuel.min(u32::MAX as u64 / 2),
            _ => true,
        }
    }
    fn ground_ran_out(&mut self) {
        self.ground_fuel = self.ground_fuel.saturating_mul(2);
        self.ground_out_at = Some(self.ticks as u64);
    }

    fn ground_defeq(&mut self, a: V, b: V) -> R<Option<bool>> {
        self.ground_busy = true;
        self.stats.gr[0] += 1;
        let mut m = self.gm_take();
        m.fuel = self.ground_fuel_now();
        let f0 = m.fuel;
        if KNOBS && std::env::var_os("SK_GROUND_TRACE").is_some() {
            eprintln!("GD-start {} =?= {}", self.vshow(a, 6), self.vshow(b, 3));
        }
        if dstack_on() {
            dstack_push(b'G', a, b, self.ticks);
        }
        let r = self.g_top(&mut m, a, b);
        if dstack_on() {
            dstack_pop();
        }
        self.ground_busy = false;
        let m_out = m.out;
        let ok = r.is_ok();
        if KNOBS && std::env::var_os("SK_GROUND_TRACE").is_some() {
            eprintln!("GD steps {} {} =?= {} -> {:?}", f0 - m.fuel, self.vshow(a, 3), self.vshow(b, 2), r);
        }
        self.gm_put(m, ok);
        match r {
            Err(Stop::Ground) => {
                self.stats.gr[2] += 1;
                if m_out {
                    self.ground_ran_out();
                }
                Ok(None)
            }
            r => r.map(Some),
        }
    }

    fn g_top(&mut self, m: &mut Gm, a: V, b: V) -> R<bool> {
        let oa = self.g_import(m, a);
        let ob = self.g_import(m, b);
        if self.g_eq(m, oa.clone(), ob.clone())? {
            self.stats.gr[1] += 1;
            return Ok(true);
        }
        // the kernel compares the two weak head normal forms
        self.stats.gr[2] += 1;
        let wa = self.g_whnf(m, oa)?;
        let wb = self.g_whnf(m, ob)?;
        let va = self.g_export_root(m, &wa, a)?;
        let vb = self.g_export_root(m, &wb, b)?;
        self.defeq(va, vb)
    }

    /// Both sides brought to weak head normal form and compared part by
    /// part: constructor applications with the same constructor at
    /// equivalent levels by their arguments (positions whose declared type
    /// is a proposition skipped: proofs of the same proposition once the
    /// arguments before them are equal), literals by value; what the
    /// machine does not take apart, by the kernel. true: equal; false: not
    /// shown equal here.
    fn g_eq(&mut self, m: &mut Gm, a: O, b: O) -> R<bool> {
        let mut st: Vec<(O, O)> = vec![(a, b)];
        while let Some((x, y)) = st.pop() {
            if Rc::ptr_eq(&x, &y) {
                continue;
            }
            let x = self.g_whnf(m, x)?;
            let y = self.g_whnf(m, y)?;
            if Rc::ptr_eq(&x, &y) {
                continue;
            }
            if matches!(&*x, Obj::Erased) || matches!(&*y, Obj::Erased) {
                return gstop("erased-eq");
            }
            let ok = match (&*x, &*y) {
                (Obj::Nat(p), Obj::Nat(q)) => p == q,
                (Obj::Str(i), Obj::Str(j)) => self.lit(*i) == self.lit(*j),
                (Obj::Nat(n), Obj::Con { row, args, ctor: true, .. }) | (Obj::Con { row, args, ctor: true, .. }, Obj::Nat(n)) => {
                    let c = self.canon_of_row(*row);
                    let k = self.env.known;
                    if n.is_zero() {
                        c == k.nat_zero && args.is_empty()
                    } else if c == k.nat_succ && args.len() == 1 {
                        let p = mk(Obj::Nat(n - 1u32));
                        st.push((p, args[0].clone()));
                        true
                    } else {
                        false
                    }
                }
                (
                    Obj::Con { row: r1, llr: l1, args: a1, ctor: c1, .. },
                    Obj::Con { row: r2, llr: l2, args: a2, ctor: c2, .. },
                ) => {
                    if c1 == c2 && a1.len() == a2.len() && self.canon_of_row(*r1) == self.canon_of_row(*r2) && self.levels_equiv(*l1, *l2) {
                        let skip = self.prop_positions(*r1, *l1)?;
                        for i in 0..a1.len() {
                            if i < 64 && skip & (1u64 << i) != 0 {
                                continue;
                            }
                            st.push((a1[i].clone(), a2[i].clone()));
                        }
                        true
                    } else {
                        false
                    }
                }
                (Obj::G(u), Obj::G(v)) => {
                    let (u, v) = (*u, *v);
                    self.defeq(u, v)?
                }
                _ => {
                    self.stats.gr[5] += 1;
                    let u = self.g_export(m, &x)?;
                    let v = self.g_export(m, &y)?;
                    self.defeq(u, v)?
                }
            };
            if !ok {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn g_import(&mut self, m: &mut Gm, v: V) -> O {
        if let Some(o) = m.pin.get(&v) {
            return o.clone();
        }
        let run = m.run;
        if let Some((w, r)) = m.imp.get_mut(&v) {
            let earlier = *r != run;
            *r = run;
            if let Some(o) = w.upgrade() {
                if earlier {
                    m.pin.insert(v, o.clone());
                }
                return o;
            }
            if earlier {
                // imported by an earlier run and let go: kept from now on
                let o = mk(Obj::Th(RefCell::new(Th::Ext(v))));
                *w = Rc::downgrade(&o);
                m.pin.insert(v, o.clone());
                return o;
            }
        }
        self.stats.gr[6] += 1;
        if KNOBS && m.imp.contains_key(&v) {
            // imported again after the machine let it go (diagnostics)
            if let Val::Thunk { term, .. } = self.val(v) {
                MADE.with(|mm| *mm.borrow_mut().entry((4, term)).or_insert(0) += 1);
            } else {
                let k = match self.val(v) { Val::Lit(_) => 1, Val::Neu { head: Head::Const(r, _), .. } => 10 + r, Val::Neu { .. } => 2, Val::Clo { .. } => 3, _ => 4 };
                MADE.with(|mm| *mm.borrow_mut().entry((5, k)).or_insert(0) += 1);
            }
        }
        let o = mk(Obj::Th(RefCell::new(Th::Ext(v))));
        m.imp.insert(v, (Rc::downgrade(&o), run));
        o
    }

    fn g_lit(&mut self, m: &mut Gm, i: u32) -> O {
        if let Some(o) = m.lits.get(&i) {
            return o.clone();
        }
        let o = match self.lit(i) {
            LitVal::Nat(n) => mk(Obj::Nat(n.clone())),
            LitVal::Str(_) => mk(Obj::Str(i)),
        };
        m.lits.insert(i, o.clone());
        o
    }

    fn g_var(&mut self, m: &mut Gm, env: &Env, i: u32) -> R<O> {
        let mut e = env;
        let mut i = i;
        loop {
            match e {
                Env::Nil => return reject("loose bound variable"),
                Env::Cons(n) => {
                    if i == 0 {
                        return Ok(n.v.clone());
                    }
                    i -= 1;
                    e = &n.next;
                }
                Env::G(g) => {
                    let v = self.env_get(*g, i)?;
                    if v == HOLE {
                        return gstop("hole");
                    }
                    return Ok(self.g_import(m, v));
                }
            }
        }
    }

    /// An argument: variables, literals and lambdas as they are, the rest
    /// delayed.
    fn g_arg(&mut self, m: &mut Gm, t: u32, env: &Env, ls: u32) -> R<O> {
        let n = self.node(t);
        Ok(match n.kind {
            BVAR => return self.g_var(m, env, n.p),
            NAT | STR => self.g_lit(m, n.p),
            k if is_lam(k) => mk(Obj::Clo { term: t, env: self.g_trim(m, t, env), ls }),
            _ => mk(Obj::Th(RefCell::new(Th::Delay(t, self.g_trim(m, t, env), ls)))),
        })
    }

    /// Milestone 40: the key of delayed term `t` over `env` at `ls`, when a
    /// lookup is worth it: the term's forcings so far cost more steps on
    /// average, times the share of lookups that hit (with one hit and one
    /// miss assumed), than a lookup costs (`MEMO_COST` steps plus one per
    /// part of the key). The key is the term, the level substitution and
    /// each entry the term reads: a forced thunk by its value, a small
    /// literal by value, a value of the kernel by id, an unforced delayed
    /// term by its own key (as long as the parts stay below the term's
    /// average cost), anything else by address. Equal keys: the same term
    /// over the same values (forced thunks are their values), so the same
    /// weak head normal form.
    fn g_memo_key(&mut self, m: &mut Gm, t: u32, env: &Env, ls: u32) -> Option<Box<[Atom]>> {
        let st = m.tstat.get(&t).copied().unwrap_or_default();
        if st.n == 0 {
            return None;
        }
        let avg = st.steps / st.n as u64;
        // expected saving per lookup against its cost
        let budget = (avg * (st.hit as u64 + 1) / (st.look as u64 + 2)).saturating_sub(self.memo_cost);
        if budget == 0 {
            return None;
        }
        let mut out: Vec<Atom> = Vec::with_capacity(8);
        let mut left = budget as usize;
        self.g_key_term(t, env, ls, &mut out, &mut left);
        m.tstat.entry(t).or_default().look += 1;
        Some(out.into_boxed_slice())
    }
    /// A term over an environment: the term, the levels, and the entries it
    /// reads; past the budget an entry is keyed by address.
    fn g_key_term(&self, t: u32, env: &Env, ls: u32, out: &mut Vec<Atom>, left: &mut usize) {
        out.push(Atom::T(t, ls));
        self.g_key_env(t, env, out, left);
    }
    fn g_key_env(&self, t: u32, env: &Env, out: &mut Vec<Atom>, left: &mut usize) {
        let r = self.trng(t) as usize;
        let mut e = env;
        let mut i = 0;
        while i < r {
            match e {
                Env::Cons(n) => {
                    self.g_key_obj(&n.v, out, left);
                    e = &n.next;
                }
                Env::G(g) => {
                    out.push(Atom::G(*g, (r - i) as u32));
                    break;
                }
                Env::Nil => break,
            }
            i += 1;
        }
        out.push(Atom::End);
    }
    /// An object: a forced thunk by its value, a small literal by value, a
    /// value of the kernel by id; while the budget lasts a delayed term by
    /// its parts; else by address.
    fn g_key_obj(&self, o: &O, out: &mut Vec<Atom>, left: &mut usize) {
        let mut x = o.clone();
        loop {
            let next = match &*x {
                Obj::Th(c) => match &*c.borrow() {
                    Th::Done(v) => v.clone(),
                    Th::Ext(v) => {
                        out.push(Atom::X(*v));
                        return;
                    }
                    Th::Delay(t, env, ls) if *left > 0 => {
                        *left -= 1;
                        let (t, ls) = (*t, *ls);
                        let env = env.clone();
                        self.g_key_term(t, &env, ls, out, left);
                        return;
                    }
                    _ => break,
                },
                Obj::Nat(n) => {
                    if let Some(k) = n.to_u64() {
                        out.push(Atom::N(k));
                        return;
                    }
                    break;
                }
                Obj::G(v) => {
                    out.push(Atom::X(*v));
                    return;
                }
                Obj::Erased => {
                    out.push(Atom::E);
                    return;
                }
                _ => break,
            };
            x = next;
        }
        out.push(Atom::P(Rc::downgrade(&x)));
    }

    /// The environment a delayed term or closure `t` keeps: its entries cut
    /// to `t`'s range and the ones it never reads left out (the erased
    /// object in their place). A whole environment kept by every delayed
    /// term is the classic space leak of lazy evaluation: an element
    /// `f i` of `Array.ofFn`'s loop kept the accumulator `acc`, so every
    /// intermediate list of the push chain stayed alive (O(n^2) cells).
    fn g_trim(&self, m: &Gm, t: u32, env: &Env) -> Env {
        let r = self.trng(t) as usize;
        if r == 0 {
            return Env::Nil;
        }
        let mask = self.used_mask(t);
        // a read at 63 or past it: kept whole
        if r > 63 {
            return env.clone();
        }
        let mut xs: smallvec::SmallVec<[Option<O>; 16]> = smallvec::SmallVec::new();
        let mut e = env;
        let mut same = true;
        let mut tail = Env::Nil;
        while xs.len() < r {
            match e {
                Env::Cons(n) => {
                    let i = xs.len();
                    if mask & (1u64 << i) != 0 {
                        xs.push(Some(n.v.clone()));
                    } else {
                        same = false;
                        xs.push(None);
                    }
                    e = &n.next;
                }
                Env::G(_) => {
                    tail = e.clone();
                    break;
                }
                Env::Nil => break,
            }
        }
        if xs.len() == r && !matches!(e, Env::Nil | Env::G(_)) {
            same = false;
        } else if xs.len() == r {
            tail = e.clone();
        }
        if same {
            return env.clone();
        }
        let mut out = tail;
        for x in xs.into_iter().rev() {
            let v = x.unwrap_or_else(|| m.erased.clone());
            out = Env::Cons(mke(ENode { v, next: out }));
        }
        out
    }

    fn g_push_env(env: Env, body_rng: u16, v: O) -> Env {
        if body_rng == 0 { Env::Nil } else { Env::Cons(mke(ENode { v, next: env })) }
    }

    /// Weak head normal form of `o`.
    fn g_whnf(&mut self, m: &mut Gm, o: O) -> R<O> {
        match &*o {
            Obj::Th(c) => {
                if let Th::Done(v) = &*c.borrow() {
                    return Ok(v.clone());
                }
            }
            Obj::Con { part: false, .. } | Obj::Nat(_) | Obj::Str(_) | Obj::Clo { .. } | Obj::G(_) => return Ok(o),
            _ => {}
        }
        let b0 = m.base;
        m.fr.push(Fr::Stop(b0));
        m.base = m.el.len();
        let mut c = C::Ob(o);
        loop {
            c = match c {
                C::Ev(t, env, ls) => self.g_ev(m, t, env, ls)?,
                C::Hd(row, llr) => self.g_hd(m, row, llr)?,
                C::Ob(o) => match self.g_ob(m, o)? {
                    Ok(next) => next,
                    Err(w) => match self.g_ret(m, w)? {
                        Ok(next) => next,
                        Err(w) => return Ok(w),
                    },
                },
            };
        }
    }

    fn g_ev(&mut self, m: &mut Gm, t: u32, env: Env, ls: u32) -> R<C> {
        self.tick()?;
        if m.fuel == 0 {
            m.out = true;
            return gstop("fuel");
        }
        m.fuel -= 1;
        self.stats.gr[4] += 1;
        if KNOBS && !m.rep.is_empty() {
            share_step(m);
        }
        let n = self.node(t);
        Ok(match n.kind {
            BVAR => C::Ob(self.g_var(m, &env, n.p)?),
            APP => {
                let mut f = t;
                loop {
                    let nd = self.node(f);
                    if nd.kind != APP {
                        break;
                    }
                    let a = self.g_arg(m, nd.b, &env, ls)?;
                    m.el.push(El::App(a));
                    f = nd.a;
                }
                C::Ev(f, env, ls)
            }
            k if is_lam(k) => {
                if top_app(m) {
                    let Some(El::App(a)) = m.el.pop() else { unreachable!() };
                    let body = n.b;
                    let r = self.node(body).rng;
                    C::Ev(body, Self::g_push_env(env, r, a), ls)
                } else {
                    C::Ob(mk(Obj::Clo { term: t, env: self.g_trim(m, t, &env), ls }))
                }
            }
            LET => {
                let body = self.let_body(t);
                let a = self.g_arg(m, n.b, &env, ls)?;
                let r = self.node(body).rng;
                C::Ev(body, Self::g_push_env(env, r, a), ls)
            }
            CONST => {
                let row = self.row_of(n.a);
                if row == NONE || !self.visible(row) {
                    return decline(format!(
                        "reduction reached constant {} that is not declared before this declaration",
                        self.env.name_str(n.a)
                    ));
                }
                let llr = self.const_ll(t, ls);
                C::Hd(row, llr)
            }
            NAT | STR => C::Ob(self.g_lit(m, n.p)),
            PROJ => {
                m.el.push(El::Proj(n.b, n.p));
                C::Ev(n.a, env, ls)
            }
            _ => {
                // sorts and Pi types: the kernel's own values
                let e = self.g_export_env(m, &env)?;
                let v = self.eval(t, e, ls)?;
                C::Ob(mk(Obj::G(v)))
            }
        })
    }

    /// The pending arguments on top, first first, as long as they are
    /// applications (at most `n`).
    fn g_take_apps(m: &mut Gm, n: usize) -> Vec<O> {
        let mut xs = Vec::new();
        while xs.len() < n && top_app(m) {
            let Some(El::App(a)) = m.el.pop() else { unreachable!() };
            xs.push(a);
        }
        xs
    }
    fn g_napps(m: &Gm) -> usize {
        m.el[m.base..].iter().rev().take_while(|e| matches!(e, El::App(_))).count()
    }
    fn g_push_args(m: &mut Gm, xs: &[O]) {
        for x in xs.iter().rev() {
            m.el.push(El::App(x.clone()));
        }
    }

    fn g_stuck(&mut self, m: &mut Gm, row: u32, llr: u32, part: bool) -> C {
        let args = Self::g_take_apps(m, usize::MAX);
        C::Ob(mk(Obj::Con { row, llr, args, ctor: false, part }))
    }

    /// Constant `row` at levels `llr` applied to the pending arguments.
    fn g_hd(&mut self, m: &mut Gm, row: u32, llr: u32) -> R<C> {
        self.tick()?;
        if KNOBS {
            UHIST.with(|h| {
                if let Some(h) = h.borrow_mut().as_mut() {
                    *h.entry(row).or_insert(0) += 1;
                }
            });
        }
        let env = self.env;
        let napp = Self::g_napps(m);
        match &env.consts[row as usize].kind {
            CKind::Ctor { .. } => {
                // Nat.zero is the literal 0 (the kernel's Nat operations read
                // it as one: `nat_ref`)
                if napp == 0 && self.canon_of_row(row) == env.known.nat_zero {
                    return Ok(C::Ob(mk(Obj::Nat(BigUint::zero()))));
                }
                if napp == 0 && self.canon_of_row(row) == env.known.nat_succ {
                    return Ok(self.g_stuck(m, row, llr, true));
                }
                if napp >= 1 && self.canon_of_row(row) == env.known.nat_succ {
                    let x = Self::g_take_apps(m, 1).pop().unwrap();
                    m.fr.push(Fr::Nat1 { row, llr, op: SUCC, x: x.clone(), base: m.base });
                    m.base = m.el.len();
                    return Ok(C::Ob(x));
                }
                let mut args = Self::g_take_apps(m, usize::MAX);
                if let CKind::Ctor { nparams, .. } = env.consts[row as usize].kind {
                    for a in args.iter_mut().take(nparams as usize) {
                        let erase = match &**a {
                            Obj::Th(c) => matches!(&*c.borrow(), Th::Delay(_, Env::Cons(_), _)),
                            _ => false,
                        };
                        if erase {
                            *a = m.erased.clone();
                        }
                    }
                }
                Ok(C::Ob(mk(Obj::Con { row, llr, args, ctor: true, part: false })))
            }
            CKind::Rec { nparams, nindices, nmotives, nminors, k, .. } => {
                let maj = (*nparams + *nmotives + *nminors + *nindices) as usize;
                if napp <= maj {
                    return Ok(self.g_stuck(m, row, llr, true));
                }
                if self.ll_get(llr).len() != env.consts[row as usize].lparams.len() {
                    return Ok(self.g_stuck(m, row, llr, false));
                }
                let mut pre = Self::g_take_apps(m, maj + 1);
                let major = pre.pop().unwrap();
                if *k {
                    // K: the kernel's iota (the major's type decides)
                    return self.g_iota_kernel(m, row, llr, pre, major);
                }
                if let Some(c) = self.g_eta(m, row, llr, &pre, &major)? {
                    return Ok(c);
                }
                m.fr.push(Fr::Rec { row, llr, pre, major: major.clone(), base: m.base });
                m.base = m.el.len();
                Ok(C::Ob(major))
            }
            CKind::Quot { kind: qk @ (2 | 3) } => {
                let mk_pos = if *qk == 2 { 5usize } else { 4 };
                if napp <= mk_pos {
                    return Ok(self.g_stuck(m, row, llr, true));
                }
                let qk = *qk;
                let args = Self::g_take_apps(m, mk_pos + 1);
                let mut xs = ArgVec::new();
                for a in &args {
                    xs.push(self.g_export(m, a)?);
                }
                self.stats.gr[3] += 1;
                match self.quot_reduce(qk, &xs)? {
                    Some(r) => Ok(C::Ob(self.g_import(m, r))),
                    None => {
                        Self::g_push_args(m, &args);
                        Ok(self.g_stuck(m, row, llr, false))
                    }
                }
            }
            CKind::Defn { .. } | CKind::Thm { .. } => {
                if !self.visible(row) || self.ll_get(llr).len() != env.consts[row as usize].lparams.len() {
                    return Ok(self.g_stuck(m, row, llr, false));
                }
                let op = env.nat_op[row as usize];
                if op == LOG2 && napp == 1 {
                    let x = Self::g_take_apps(m, 1).pop().unwrap();
                    m.fr.push(Fr::Nat1 { row, llr, op, x: x.clone(), base: m.base });
                    m.base = m.el.len();
                    return Ok(C::Ob(x));
                }
                if (1..=14).contains(&op) && napp == 2 {
                    let mut xs = Self::g_take_apps(m, 2);
                    let y = xs.pop().unwrap();
                    let x = xs.pop().unwrap();
                    m.fr.push(Fr::NatA { row, llr, op: op - 1, x: x.clone(), y, base: m.base });
                    m.base = m.el.len();
                    return Ok(C::Ob(x));
                }
                if let Some(c) = self.g_cases(m, row, llr, napp)? {
                    return Ok(c);
                }
                if napp == 0 && !(1..=14).contains(&op) && op != LOG2 {
                    if let Some(o) = m.caf.get(&(row, llr)) {
                        return Ok(C::Ob(o.clone()));
                    }
                    let Some(body) = self.decl_value(row)? else { return Ok(self.g_stuck(m, row, llr, false)) };
                    if self.trng(body) != 0 {
                        return Ok(self.g_stuck(m, row, llr, false));
                    }
                    self.stats.unfolds += 1;
                    let ls = self.mk_ls(row, llr);
                    let o = mk(Obj::Th(RefCell::new(Th::Delay(body, Env::Nil, ls))));
                    m.caf.insert((row, llr), o.clone());
                    return Ok(C::Ob(o));
                }
                // a Nat operation short of its operands (`instPowNat := ⟨Nat.pow⟩`,
                // applied later, after a thunk's whnf): kept whole, so that it
                // is computed on literals once it has them, as the kernel's
                // whnf of the whole application does
                if (op == LOG2 && napp < 1) || ((1..=14).contains(&op) && napp < 2) {
                    return Ok(self.g_stuck(m, row, llr, true));
                }
                self.g_unfold(m, row, llr)
            }
            _ => Ok(self.g_stuck(m, row, llr, false)),
        }
    }

    /// Structure eta before the major premise is reduced, as the kernel's
    /// `rec_rule` (lean4#15351/#15371): a major that is not a constructor
    /// application or a literal yet, of a recursor whose major inductive
    /// is a structure and which eliminates into every sort, is taken as
    /// `mk params major.0 ... major.(n-1)`: the rule's right-hand side gets
    /// the projections as fields (unevaluated), so a major with no weak
    /// head normal form never stops the recursor. The kernel also checks
    /// that the major's type is that structure; a recursor application in
    /// a checked term has a major of that type (its type is the major
    /// premise's binder type), and the projections name the structure.
    fn g_eta(&mut self, m: &mut Gm, row: u32, llr: u32, pre: &[O], major: &O) -> R<Option<C>> {
        let env = self.env;
        let Some(&ind) = env.rec_major.get(&row) else { return Ok(None) };
        // as the kernel's `force`: a forced thunk is its value
        let mut x = major.clone();
        loop {
            let next = match &*x {
                Obj::Th(c) => match &*c.borrow() {
                    Th::Done(v) => v.clone(),
                    _ => break,
                },
                _ => break,
            };
            x = next;
        }
        if matches!(&*x, Obj::Nat(_) | Obj::Str(_) | Obj::Con { ctor: true, .. }) {
            return Ok(None);
        }
        let irow = env.known_row(ind);
        if irow == NONE || !self.visible(irow) || !self.structure_like(irow) || !self.rec_elim_any_sort(row) {
            return Ok(None);
        }
        // K06: Lean 4.36.0 never eta-expands a proof major (lean4#15371 is
        // v4.37 only). The machine has no types: eta only for a structure
        // whose sort is never zero; otherwise the major is reduced and a
        // stuck one goes to the kernel's iota, which tests the major's type.
        if !self.struct_sort_never_zero(irow) {
            return Ok(None);
        }
        let (_, _, ctors, _) = self.ind_info(irow).unwrap();
        let crow = self.row_of(ctors[0]);
        if crow == NONE {
            return Ok(None);
        }
        let CKind::Ctor { nfields, .. } = self.consts[crow as usize].kind else { return Ok(None) };
        let CKind::Rec { rules, .. } = &env.consts[row as usize].kind else { unreachable!() };
        let cc = self.canon_of_row(crow);
        let Some(ri) = rules.iter().position(|r| env.canon(r.0) == cc) else { return Ok(None) };
        let (_, rn, rhs) = rules[ri];
        if rn != nfields || (rhs as usize) >= env.main.len() || env.main.n()[rhs as usize].rng != 0 {
            return Ok(None);
        }
        let sname = self.consts[irow as usize].name;
        let fields: Vec<O> = (0..nfields).map(|i| mk(Obj::Th(RefCell::new(Th::Proj(x.clone(), i, sname))))).collect();
        if STATS {
            self.stats.iota += 1;
        }
        Self::g_push_args(m, &fields);
        // milestone 40: the rule takes parameters, motives and minor
        // premises, not the indices (as the kernel's `iota`)
        Self::g_push_args(m, &pre[..self.rec_rule_pre(row)]);
        let ls = self.mk_ls(row, llr);
        Ok(Some(C::Ev(rhs, Env::Nil, ls)))
    }

    /// A casesOn applied to at least its arguments (the kernel's
    /// `cases_direct`): its major premise brought to a constructor, that
    /// constructor's minor premise applied to the fields and the arguments
    /// after (what unfolding, the recursor's rule and beta give). Not for
    /// K-like recursors or structures (structure eta comes before the major
    /// is reduced: the unfolding takes those).
    fn g_cases(&mut self, m: &mut Gm, row: u32, llr: u32, napp: usize) -> R<Option<C>> {
        let Some((rrow, l)) = self.cases_shape(row) else { return Ok(None) };
        if napp < l as usize || self.ll_get(llr).len() != self.consts[rrow as usize].lparams.len() {
            return Ok(None);
        }
        let env = self.env;
        let CKind::Rec { nparams, nindices, k, .. } = env.consts[rrow as usize].kind else { return Ok(None) };
        if k || env.rec_major.get(&rrow).is_some_and(|&ind| {
            let irow = env.known_row(ind);
            irow != NONE && self.structure_like(irow)
        }) {
            return Ok(None);
        }
        let args = Self::g_take_apps(m, l as usize);
        let major = args[(nparams + 1 + nindices) as usize].clone();
        m.fr.push(Fr::Cases { row, llr, rrow, args, base: m.base });
        m.base = m.el.len();
        Ok(Some(C::Ob(major)))
    }

    fn g_unfold(&mut self, m: &mut Gm, row: u32, llr: u32) -> R<C> {
        if KNOBS && share_on() {
            let xs: Vec<O> = m.el[m.base..].iter().rev().take_while(|e| matches!(e, El::App(_))).map(|e| match e {
                El::App(a) => a.clone(),
                _ => unreachable!(),
            }).collect();
            share_unf(row, llr, &xs);
        }
        let Some(body) = self.decl_value(row)? else { return Ok(self.g_stuck(m, row, llr, false)) };
        if self.trng(body) != 0 {
            return Ok(self.g_stuck(m, row, llr, false));
        }
        self.stats.unfolds += 1;
        let ls = self.mk_ls(row, llr);
        Ok(C::Ev(body, Env::Nil, ls))
    }

    /// The arguments a recursor's rule takes before the fields: parameters,
    /// motives, minor premises.
    fn rec_rule_pre(&self, row: u32) -> usize {
        let CKind::Rec { nparams, nmotives, nminors, .. } = self.env.consts[row as usize].kind else { unreachable!() };
        (nparams + nmotives + nminors) as usize
    }

    /// One iota step by the kernel (K-like recursors, structure eta).
    fn g_iota_kernel(&mut self, m: &mut Gm, row: u32, llr: u32, pre: Vec<O>, major: O) -> R<C> {
        self.stats.gr[3] += 1;
        let mut xs = ArgVec::new();
        for a in &pre {
            xs.push(self.g_export(m, a)?);
        }
        xs.push(self.g_export(m, &major)?);
        match self.iota(row, llr, &xs)? {
            Some(r) => Ok(C::Ob(self.g_import(m, r))),
            None => {
                Self::g_push_args(m, &[major]);
                Self::g_push_args(m, &pre);
                Ok(self.g_stuck(m, row, llr, false))
            }
        }
    }

    /// `o` with the pending eliminations: the next state, or Err(o) when
    /// `o` is in weak head normal form and nothing is pending.
    fn g_ob(&mut self, m: &mut Gm, o: O) -> R<Result<C, O>> {
        if let Obj::Th(cell) = &*o {
            let st = std::mem::replace(&mut *cell.borrow_mut(), Th::Busy);
            return Ok(Ok(match st {
                Th::Done(v) => {
                    *cell.borrow_mut() = Th::Done(v.clone());
                    C::Ob(v)
                }
                Th::Delay(t, env, ls) => {
                    if KNOBS && share_on() {
                        let (rep, live) = share_forced(&o, t);
                        if rep {
                            m.rep.push((m.fr.len(), live, t));
                        }
                    }
                    // milestone 40: a delayed term met again (the same term
                    // over the same values) takes the result of its first
                    // forcing
                    let key = if self.ground_memo { self.g_memo_key(m, t, &env, ls) } else { None };
                    if let Some(k) = &key {
                        if let Some(w) = m.memo.get(k) {
                            let w = w.clone();
                            m.tstat.entry(t).or_default().hit += 1;
                            self.stats.gr[1] += 1;
                            *cell.borrow_mut() = Th::Done(w.clone());
                            return Ok(Ok(C::Ob(w)));
                        }
                    }
                    let clock = self.stats.gr[4];
                    let orig = Orig::Delay(
                        t,
                        match &env {
                            Env::Cons(n) => Some(Rc::downgrade(n)),
                            _ => None,
                        },
                        ls,
                        match &env {
                            Env::G(g) => Some(*g),
                            _ => None,
                        },
                    );
                    m.fr.push(Fr::Upd(o.clone(), m.base, clock, if self.ground_memo { t } else { NONE }, key, orig));
                    m.base = m.el.len();
                    C::Ev(t, env, ls)
                }
                Th::Ext(v) => {
                    m.fr.push(Fr::Upd(o.clone(), m.base, 0, NONE, None, Orig::Ext(v)));
                    m.base = m.el.len();
                    self.g_import_code(m, v)?
                }
                Th::Proj(x, idx, sname) => {
                    m.fr.push(Fr::Upd(o.clone(), m.base, 0, NONE, None, Orig::Proj(x.clone(), idx, sname)));
                    m.base = m.el.len();
                    m.el.push(El::Proj(idx, sname));
                    C::Ob(x)
                }
                Th::Busy => return gstop("busy"),
            }));
        }
        if m.el.len() == m.base {
            return Ok(Err(o));
        }
        let app = top_app(m);
        Ok(Ok(match &*o {
            Obj::Clo { term, env, ls } if app => {
                let Some(El::App(a)) = m.el.pop() else { unreachable!() };
                let body = self.tb(*term);
                let r = self.node(body).rng;
                C::Ev(body, Self::g_push_env(env.clone(), r, a), *ls)
            }
            Obj::Con { row, llr, args, ctor: true, .. } if app => {
                if self.canon_of_row(*row) == self.env.known.nat_succ {
                    return self.g_delegate(m, &o).map(Ok);
                }
                let mut xs = args.clone();
                xs.extend(Self::g_take_apps(m, usize::MAX));
                C::Ob(mk(Obj::Con { row: *row, llr: *llr, args: xs, ctor: true, part: false }))
            }
            Obj::Con { row, args, ctor: true, .. } => {
                let Some(El::Proj(idx, _)) = m.el.last().cloned() else { unreachable!() };
                let CKind::Ctor { nparams, .. } = self.consts[*row as usize].kind else { unreachable!() };
                match args.get((nparams + idx) as usize) {
                    Some(f) => {
                        m.el.pop();
                        C::Ob(f.clone())
                    }
                    None => return self.g_delegate(m, &o).map(Ok),
                }
            }
            Obj::Con { row, llr, args, ctor: false, part: true } if app => {
                let (row, llr) = (*row, *llr);
                Self::g_push_args(m, args);
                C::Hd(row, llr)
            }
            Obj::Con { row, llr, args, ctor: false, part: false } if app => {
                let mut xs = args.clone();
                xs.extend(Self::g_take_apps(m, usize::MAX));
                C::Ob(mk(Obj::Con { row: *row, llr: *llr, args: xs, ctor: false, part: false }))
            }
            Obj::Str(i) if !app => {
                let s = match self.lit(*i) {
                    LitVal::Str(s) => s.clone(),
                    _ => unreachable!(),
                };
                match self.str_lit_expand(&s)? {
                    Some(x) => C::Ob(self.g_import(m, x)),
                    None => return self.g_delegate(m, &o).map(Ok),
                }
            }
            _ => return self.g_delegate(m, &o).map(Ok),
        }))
    }

    /// `o` with all pending eliminations, by the kernel.
    fn g_delegate(&mut self, m: &mut Gm, o: &O) -> R<C> {
        self.stats.gr[3] += 1;
        let mut v = self.g_export(m, o)?;
        while m.el.len() > m.base {
            match m.el.pop().unwrap() {
                El::App(a) => {
                    let x = self.g_export(m, &a)?;
                    v = self.apply(v, x)?;
                }
                El::Proj(idx, sname) => v = self.proj_val(v, idx, sname)?,
            }
        }
        let w = self.whnf(v)?;
        // a value of the kernel in weak head normal form: taken apart when
        // it is a constant applied to arguments (the machine then finds it
        // stuck or a constructor), else kept
        // (a stuck projection or a stuck head is kept as it is: taken apart
        // it would ask the kernel the same again)
        Ok(match self.val(w) {
            Val::Lit(i) => C::Ob(self.g_lit(m, i)),
            Val::Neu { head: Head::Const(..), spine } if spine == EMPTY || !self.spine_has_proj(spine) => self.g_import_code(m, w)?,
            Val::Clo { .. } => self.g_import_code(m, w)?,
            _ => C::Ob(mk(Obj::G(w))),
        })
    }

    /// What forcing the kernel's value `v` starts.
    fn g_import_code(&mut self, m: &mut Gm, v: V) -> R<C> {
        Ok(match self.val(v) {
            Val::Thunk { term, env, ls } => {
                let f = self.memo_at(v).whnf;
                if f != NONE {
                    C::Ob(self.g_import(m, f))
                } else {
                    C::Ev(term, if env == EMPTY { Env::Nil } else { Env::G(env) }, ls)
                }
            }
            Val::Clo { term, env, ls } if is_lam(self.tk(term)) => {
                C::Ob(mk(Obj::Clo { term, env: if env == EMPTY { Env::Nil } else { Env::G(env) }, ls }))
            }
            Val::Lit(i) => C::Ob(self.g_lit(m, i)),
            Val::Neu { head, spine } if !matches!(head, Head::FVar(_)) => {
                if spine != EMPTY {
                    let elims = self.spine_in(spine);
                    for &e in elims.iter().rev() {
                        if e & PROJ_BIT != 0 {
                            let (sname, idx) = self.projs[(e & !PROJ_BIT) as usize];
                            m.el.push(El::Proj(idx, sname));
                        } else {
                            let a = self.g_import(m, e);
                            m.el.push(El::App(a));
                        }
                    }
                }
                match head {
                    Head::Const(row, llr) => C::Hd(row, llr),
                    Head::Stuck(x) => C::Ob(self.g_import(m, x)),
                    Head::FVar(_) => unreachable!(),
                }
            }
            _ => C::Ob(mk(Obj::G(v))),
        })
    }

    /// A weak head normal form `w` reached: the frame waiting for it.
    fn g_ret(&mut self, m: &mut Gm, w: O) -> R<Result<C, O>> {
        Ok(Ok(match m.fr.pop().unwrap() {
            Fr::Stop(b) => {
                m.base = b;
                return Ok(Err(w));
            }
            Fr::Upd(th, b, clock, t, key, _) => {
                if KNOBS && m.rep.last().is_some_and(|r| r.0 == m.fr.len()) {
                    m.rep.pop();
                }
                if t != NONE {
                    let st = m.tstat.entry(t).or_default();
                    st.n += 1;
                    st.steps += self.stats.gr[4] - clock;
                    if let Some(k) = key {
                        m.memo_put(k, w.clone(), self.vals.len());
                    }
                }
                if let Obj::Th(cell) = &*th {
                    *cell.borrow_mut() = Th::Done(w.clone());
                }
                m.base = b;
                C::Ob(w)
            }
            Fr::Rec { row, llr, pre, major, base } => {
                m.base = base;
                return self.g_iota(m, row, llr, pre, major, w).map(Ok);
            }
            Fr::Cases { row, llr, rrow, args, base } => {
                m.base = base;
                let env = self.env;
                let CKind::Rec { nparams, nindices, rules, .. } = &env.consts[rrow as usize].kind else { unreachable!() };
                let mi = (nparams + 1 + nindices) as usize;
                let k = env.known;
                let hit = match &*w {
                    Obj::Nat(n) => {
                        let (c, f) = if n.is_zero() { (k.nat_zero, None) } else { (k.nat_succ, Some(mk(Obj::Nat(n - 1u32)))) };
                        rules.iter().position(|r| env.canon(r.0) == c).map(|ri| (ri, f.into_iter().collect::<Vec<O>>()))
                    }
                    Obj::Con { row: cr, args: ca, ctor: true, .. } => {
                        let cc = self.canon_of_row(*cr);
                        rules.iter().position(|r| env.canon(r.0) == cc).and_then(|ri| {
                            let nf = rules[ri].1 as usize;
                            if nf <= ca.len() { Some((ri, ca[ca.len() - nf..].to_vec())) } else { None }
                        })
                    }
                    _ => None,
                };
                match hit {
                    Some((ri, fields)) if mi + 1 + ri < args.len() => {
                        if STATS {
                            self.stats.cases_direct += 1;
                        }
                        let minor = args[mi + 1 + ri].clone();
                        Self::g_push_args(m, &fields);
                        C::Ob(minor)
                    }
                    _ => {
                        // the casesOn unfolded as any definition
                        Self::g_push_args(m, &args);
                        self.g_unfold(m, row, llr)?
                    }
                }
            }
            Fr::Nat1 { row, llr, op, x, base } => {
                m.base = base;
                match (&*w, op) {
                    (Obj::Nat(n), SUCC) => match nat_sized(n + 1u32) {
                        Ok(r) => C::Ob(mk(Obj::Nat(r))),
                        Err(why) => return gstop(why),
                    },
                    (Obj::Nat(n), _) => C::Ob(mk(Obj::Nat(if n.is_zero() { BigUint::zero() } else { BigUint::from(n.bits() - 1) }))),
                    (_, SUCC) => C::Ob(mk(Obj::Con { row, llr, args: vec![x], ctor: true, part: false })),
                    _ => {
                        Self::g_push_args(m, &[x]);
                        self.g_unfold(m, row, llr)?
                    }
                }
            }
            Fr::NatA { row, llr, op, x, y, base } => {
                if matches!(&*w, Obj::Nat(_)) {
                    m.fr.push(Fr::NatB { row, llr, op, a: w, x, y: y.clone(), base });
                    m.base = m.el.len();
                    C::Ob(y)
                } else {
                    m.base = base;
                    Self::g_push_args(m, &[x, y]);
                    self.g_unfold(m, row, llr)?
                }
            }
            Fr::NatB { row, llr, op, a, x, y, base } => {
                m.base = base;
                let r = match (&*a, &*w) {
                    (Obj::Nat(p), Obj::Nat(q)) => match nat_fold(op as usize, p, q) {
                        Ok(r) => Some(r),
                        // refused by Lean's rule: the kernel decides
                        Err(why) => return gstop(why),
                    },
                    _ => None,
                };
                match r {
                    Some(NatR::N(n)) => C::Ob(mk(Obj::Nat(n))),
                    Some(NatR::B(b)) => match self.mk_bool(b)? {
                        Some(v) => C::Ob(self.g_import(m, v)),
                        None => {
                            Self::g_push_args(m, &[x, y]);
                            self.g_unfold(m, row, llr)?
                        }
                    },
                    None => {
                        Self::g_push_args(m, &[x, y]);
                        self.g_unfold(m, row, llr)?
                    }
                }
            }
        }))
    }

    /// Recursor `row` with the arguments before its major premise `pre`,
    /// its major premise `major` in weak head normal form `w`.
    fn g_iota(&mut self, m: &mut Gm, row: u32, llr: u32, pre: Vec<O>, major: O, w: O) -> R<C> {
        let env = self.env;
        let k = env.known;
        let (crow, fields): (u32, Vec<O>) = match &*w {
            Obj::Nat(n) => {
                if n.is_zero() {
                    (self.known_visible(k.nat_zero), Vec::new())
                } else {
                    (self.known_visible(k.nat_succ), vec![mk(Obj::Nat(n - 1u32))])
                }
            }
            Obj::Str(i) => {
                let s = match self.lit(*i) {
                    LitVal::Str(s) => s.clone(),
                    _ => unreachable!(),
                };
                let Some(x) = self.str_lit_expand(&s)? else {
                    return self.g_iota_kernel(m, row, llr, pre, w);
                };
                let x = self.g_import(m, x);
                m.fr.push(Fr::Rec { row, llr, pre, major, base: m.base });
                m.base = m.el.len();
                return Ok(C::Ob(x));
            }
            Obj::Con { row: cr, args, ctor: true, .. } => (*cr, args.clone()),
            _ => return self.g_iota_kernel(m, row, llr, pre, w),
        };
        let CKind::Rec { rules, .. } = &env.consts[row as usize].kind else { unreachable!() };
        let ri = if crow == NONE {
            None
        } else {
            let cc = self.canon_of_row(crow);
            rules.iter().position(|r| env.canon(r.0) == cc)
        };
        let Some(ri) = ri else { return self.g_iota_kernel(m, row, llr, pre, w) };
        let (_, nfields, rhs) = rules[ri];
        if nfields as usize > fields.len() || (rhs as usize) >= env.main.len() || env.main.n()[rhs as usize].rng != 0 {
            return self.g_iota_kernel(m, row, llr, pre, w);
        }
        if STATS {
            self.stats.iota += 1;
        }
        Self::g_push_args(m, &fields[fields.len() - nfields as usize..]);
        // milestone 40: without the indices (M39 passed them on: an indexed
        // family's rule was applied to its indices too)
        Self::g_push_args(m, &pre[..self.rec_rule_pre(row)]);
        let ls = self.mk_ls(row, llr);
        Ok(C::Ev(rhs, Env::Nil, ls))
    }

    fn g_export_env(&mut self, m: &mut Gm, env: &Env) -> R<u32> {
        match env {
            Env::Nil => Ok(EMPTY),
            Env::G(g) => Ok(*g),
            Env::Cons(n) => {
                let key = Rc::as_ptr(n) as usize;
                if let Some(&e) = m.eexp.get(&key) {
                    return Ok(e);
                }
                let n = n.clone();
                self.g_export_run(m, None, Some(n.clone()))?;
                Ok(m.eexp[&key])
            }
        }
    }

    /// Milestone 40: the weak head normal form `o` of the kernel's closed
    /// value `v` exported. A constructor application whose parameters were
    /// erased (`g_hd`) takes them from `v`'s type: a well-typed
    /// constructor application `C ps fs : I qs is` has ps = qs (the type's
    /// parameters fix them), and its fields' types follow from the
    /// constructor's type at qs and the fields before them, so nested ones
    /// are rebuilt the same way.
    fn g_export_root(&mut self, m: &mut Gm, o: &O, v: V) -> R<V> {
        m.erased_hit = false;
        match self.g_export(m, o) {
            Err(Stop::Ground) if m.erased_hit => {
                self.stats.gr[3] += 1;
                let ty = self.infer_val(v)?;
                self.g_export_typed(m, o, ty)
            }
            r => r,
        }
    }
    fn g_export_typed(&mut self, m: &mut Gm, o: &O, ty: V) -> R<V> {
        let mut o = o.clone();
        loop {
            let next = match &*o {
                Obj::Th(c) => match &*c.borrow() {
                    Th::Done(x) => x.clone(),
                    _ => break,
                },
                _ => break,
            };
            o = next;
        }
        let (row, llr, args) = match &*o {
            Obj::Con { row, llr, args, ctor: true, .. } => (*row, *llr, args.clone()),
            _ => return self.g_export(m, &o),
        };
        m.erased_hit = false;
        match self.g_export(m, &o) {
            Err(Stop::Ground) if m.erased_hit => {}
            r => return r,
        }
        // a deep nesting goes back to the kernel rather than past the stack
        let x = 0u8;
        let sp = std::hint::black_box(&x) as *const u8 as usize;
        if self.stack_base.saturating_sub(sp) > self.stack_limit / 2 {
            return gstop("typed export too deep");
        }
        let env = self.env;
        let CKind::Ctor { induct, nparams, .. } = env.consts[row as usize].kind else { return gstop("typed export") };
        let np = nparams as usize;
        let tw = self.whnf(ty)?;
        let Some((irow, _, ispine)) = self.const_head(tw) else { return gstop("typed export: type") };
        if self.canon_of_row(irow) != env.canon(induct) {
            return gstop("typed export: inductive");
        }
        let targs: Vec<V> = match self.app_args(ispine) {
            Some(a) if a.len() >= np => a[..np].to_vec(),
            _ => return gstop("typed export: parameters"),
        };
        if self.ll_get(llr).len() != self.consts[row as usize].lparams.len() {
            return gstop("typed export: levels");
        }
        let ls = self.mk_ls(row, llr);
        let cty = self.consts[row as usize].ty;
        let mut r = self.eval(cty, EMPTY, ls)?;
        let mut xs = ArgVec::new();
        for (i, a) in args.iter().enumerate() {
            let w = self.whnf(r)?;
            if !self.is_pi_val(w) {
                return gstop("typed export: constructor type");
            }
            let x = if i < np {
                if matches!(&**a, Obj::Erased) { targs[i] } else { self.g_export(m, a)? }
            } else {
                let d = self.bind_dom(w)?;
                self.g_export_typed(m, a, d)?
            };
            r = self.bind_body(w, x)?;
            xs.push(x);
        }
        self.neu(Head::Const(row, llr), EMPTY, &xs)
    }

    fn g_export(&mut self, m: &mut Gm, o: &O) -> R<V> {
        let key = Rc::as_ptr(o) as usize;
        if let Some(&v) = m.exp.get(&key) {
            return Ok(v);
        }
        self.g_export_run(m, Some(o.clone()), None)?;
        Ok(m.exp[&key])
    }

    /// The kernel's values for machine objects (and environments), children
    /// first, without recursion.
    fn g_export_run(&mut self, m: &mut Gm, o: Option<O>, e: Option<Rc<ENode>>) -> R<()> {
        enum J {
            O(O),
            E(Rc<ENode>),
        }
        let mut st: Vec<J> = Vec::new();
        if let Some(o) = o {
            st.push(J::O(o));
        }
        if let Some(e) = e {
            st.push(J::E(e));
        }
        let env_ready = |m: &Gm, env: &Env| -> Option<Rc<ENode>> {
            match env {
                Env::Cons(n) if !m.eexp.contains_key(&(Rc::as_ptr(n) as usize)) => Some(n.clone()),
                _ => None,
            }
        };
        let env_id = |m: &Gm, env: &Env| -> u32 {
            match env {
                Env::Nil => EMPTY,
                Env::G(g) => *g,
                Env::Cons(n) => m.eexp[&(Rc::as_ptr(n) as usize)],
            }
        };
        while let Some(j) = st.last() {
            match j {
                J::O(o) => {
                    let o = o.clone();
                    let key = Rc::as_ptr(&o) as usize;
                    if m.exp.contains_key(&key) {
                        st.pop();
                        continue;
                    }
                    let mut need = false;
                    match &*o {
                        Obj::Con { args, .. } => {
                            for a in args {
                                if !m.exp.contains_key(&(Rc::as_ptr(a) as usize)) {
                                    st.push(J::O(a.clone()));
                                    need = true;
                                }
                            }
                        }
                        Obj::Clo { env, .. } => {
                            if let Some(n) = env_ready(m, env) {
                                st.push(J::E(n));
                                need = true;
                            }
                        }
                        Obj::Th(c) => match &*c.borrow() {
                            Th::Done(v) => {
                                if !m.exp.contains_key(&(Rc::as_ptr(v) as usize)) {
                                    st.push(J::O(v.clone()));
                                    need = true;
                                }
                            }
                            Th::Delay(_, env, _) => {
                                if let Some(n) = env_ready(m, env) {
                                    st.push(J::E(n));
                                    need = true;
                                }
                            }
                            Th::Proj(x, ..) => {
                                if !m.exp.contains_key(&(Rc::as_ptr(x) as usize)) {
                                    st.push(J::O(x.clone()));
                                    need = true;
                                }
                            }
                            _ => {}
                        },
                        _ => {}
                    }
                    if need {
                        continue;
                    }
                    self.stats.gr[7] += 1;
                    let v = match &*o {
                        Obj::Nat(n) => self.mk_nat(n.clone())?,
                        Obj::Str(i) => self.intern(Val::Lit(*i))?,
                        Obj::Con { row, llr, args, .. } => {
                            let xs: ArgVec = args.iter().map(|a| m.exp[&(Rc::as_ptr(a) as usize)]).collect();
                            self.neu(Head::Const(*row, *llr), EMPTY, &xs)?
                        }
                        Obj::Clo { term, env, ls } => {
                            let e = env_id(m, env);
                            let e = self.prune(*term, e);
                            self.intern(Val::Clo { term: *term, env: e, ls: *ls })?
                        }
                        Obj::G(v) => *v,
                        Obj::Erased => {
                            m.erased_hit = true;
                            return gstop("erased-export");
                        }
                        Obj::Th(c) => match &*c.borrow() {
                            Th::Done(v) => m.exp[&(Rc::as_ptr(v) as usize)],
                            Th::Ext(v) => *v,
                            Th::Proj(x, idx, sname) => {
                                let xv = m.exp[&(Rc::as_ptr(x) as usize)];
                                self.proj_val(xv, *idx, *sname)?
                            }
                            Th::Delay(t, env, ls) => {
                                let e = env_id(m, env);
                                match self.tk(*t) {
                                    APP | LET | PROJ => {
                                        let e = self.prune(*t, e);
                                        self.intern(Val::Thunk { term: *t, env: e, ls: *ls })?
                                    }
                                    _ => self.eval(*t, e, *ls)?,
                                }
                            }
                            Th::Busy => return gstop("busy"),
                        },
                    };
                    m.exp.insert(key, v);
                    m.keep.push(o);
                    st.pop();
                }
                J::E(n) => {
                    let n = n.clone();
                    let key = Rc::as_ptr(&n) as usize;
                    if m.eexp.contains_key(&key) {
                        st.pop();
                        continue;
                    }
                    let mut need = false;
                    // milestone 40: an entry the term never reads (cut by
                    // `g_trim`) is the kernel's HOLE
                    let hole = matches!(&*n.v, Obj::Erased);
                    if !hole && !m.exp.contains_key(&(Rc::as_ptr(&n.v) as usize)) {
                        st.push(J::O(n.v.clone()));
                        need = true;
                    }
                    if let Some(x) = env_ready(m, &n.next) {
                        st.push(J::E(x));
                        need = true;
                    }
                    if need {
                        continue;
                    }
                    let v = if hole { HOLE } else { m.exp[&(Rc::as_ptr(&n.v) as usize)] };
                    let next = env_id(m, &n.next);
                    let id = self.push_env(v, next);
                    m.eexp.insert(key, id);
                    m.ekeep.push(n);
                    st.pop();
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // milestone 42: an environment chain dropped from outside an object
    // (a local, a table) is freed without one frame per node
    #[test]
    fn long_env_chain_drops_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 << 10)
            .spawn(|| {
                let mut e = Env::Nil;
                for _ in 0..1_000_000 {
                    e = Env::Cons(mke(ENode { v: mk(Obj::Erased), next: e }));
                }
                // a second owner of a node in the middle: the walk stops there
                let mut mid = &e;
                for _ in 0..500_000 {
                    let Env::Cons(n) = mid else { unreachable!() };
                    mid = &n.next;
                }
                let keep = mid.clone();
                drop(e);
                drop(keep);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
