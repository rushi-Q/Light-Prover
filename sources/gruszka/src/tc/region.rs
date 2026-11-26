//! Milestone 36: regions (docs/architecture.md, Regions). A heavy
//! declaration's values were kept until its
//! session ended, so memory grew with the amount of kernel computation (a
//! CFSG certificate: 286 GB, then "a worker table is full"). Once the
//! session's arena is past `reg_at` values, every `whnf` that misses its
//! memo opens a *region*: the lengths of the arena's tables are noted, and
//! every write that could keep an id made inside the region where it
//! outlives the call is logged (`Undo`): a memo of an older value, an entry
//! of a session map. When the call returns, the region has made at least
//! `reg_min` values and its result reaches few of them, the region is
//! rolled back:
//!
//! - the values, environments, spines and literals its result reaches are
//!   copied out (`Rcp`, rebuilt after the cut through the hash-consing
//!   tables, so they are values like any other);
//! - every logged entry that names a dead id (one at or past a mark) is
//!   removed, every logged memo field that names one goes back to what it
//!   held before (or to the copy of that value);
//! - the hash-consing tables forget the dead values (`vmap` by each dead
//!   value's key, spines and frames by undoing their slots in reverse
//!   order, or by a rebuild after a growth);
//! - the tables are cut back to their marks; the direct-mapped tables
//!   stamped with the generation are dropped (`cgen_bump`).
//!
//! Why nothing else can name a dead id: values, environments and spines
//! only point to older ids (a value is made after its parts), so the only
//! pointers from before the region into it are the logged writes, and the
//! call's own result. The callers of `whnf` hold ids made before the call
//! (the region opens at its entry). Worker fields that hold value or
//! environment ids across a call are stacks balanced inside it (open
//! binders, `let_vals`) or `kb_env`, checked before a rollback. Free
//! variables are never cut (their indices stay unique, so a name or a
//! cache key that mentions one cannot meet another variable under the
//! same index). Names (`names.rs`) are keyed by value only through
//! `of_val`, `of_term` and opaque leaves; the first two are logged, the
//! leaves carry the rollback epoch. Scratch declarations (inductive
//! groups, the quotient, unsafe ones) never open regions.
//!
//! Release-da with SK_REGION_POISON=1 (knobs) keeps the dead ids instead of
//! reusing them, overwritten with a marker every read asserts against: a
//! missed log would show as a read of a dead id.
use super::*;

/// A write made while a region is open that may name an id of the region.
pub(super) enum Undo {
    /// the memo of an older value, as it was before the write
    Memo(V, Memo),
    EnvMap(u64),
    /// a slot of the spine table / frame table taken (undone in reverse)
    Sp(u32),
    Ft(u32),
    Nat(u64),
    BigNat(u64),
    Eq(u64),
    Fail(V, V),
    Infer((u64, u64)),
    InferU((u64, u64)),
    Uenv(Box<[u32]>),
    LamVar((u32, u32, u32)),
    VarSlot(u64),
    Shash(V),
    Canon((u32, u32, u32)),
    NmOfVal(V),
    NmOfTerm((u64, u64)),
    NmInfer(u64),
}

/// The marks of an open region.
#[derive(Clone, Copy)]
pub(super) struct Reg {
    vm: u32,
    em: u32,
    esm: u32,
    spm: u32,
    wm: u32,
    fvm: u32,
    ul: usize,
    um: u32,
    /// `wlit_bytes` when the region opened
    lb: usize,
    /// milestone 37: ticks when it opened; its root was found redone
    t0: u32,
    pin: bool,
    /// the enclosing region's `reg_kmax` when this one opened
    pk: usize,
    /// lengths of `pin_ids` and `reg_done` when it opened: the entries
    /// past them are this region's (their roots were made in it)
    pm: usize,
    dm: usize,
    spg: u32,
    ftg: u32,
    prev: u32,
    /// milestone 38: after a checkpoint that reopened at the marks, the
    /// lengths after its copies, and how many values the copies took: the
    /// next checkpoint waits for as many new values (copying values costs
    /// about what making them did; big literals are copied by memcpy and
    /// keep the plain bound, or a loop over big live state would hold
    /// twice of it)
    dvm: u32,
    dlb: usize,
    lv: usize,
}

/// A value of the region its result reaches, with the ids it held.
enum Rcp {
    Val(V, Val),
    Neu(V, Head, SpineVec),
    Lit(V, LitVal),
    /// milestone 40: a literal of the region by its id, moved out of its
    /// dead slot at the cut (a copy of a big literal cost a memcpy of all
    /// its bytes at every rollback: McertP_Ly's register file of
    /// 150 000-bit numbers, 57% of the time in `reach_root`)
    LitAt(V, u32),
    Env(u32, SpineVec, u64),
}

/// Milestone 37: a closed region whose root dies in a rollback is
/// remembered (`ghost`) when it cost at least this many ticks: about what a
/// rollback's bookkeeping costs (`REGION_MIN`), so cheaper work is simply
/// done again.
pub(super) const GHOST_TICKS: u32 = 256;
/// most keys in the ghost table (16 MiB); past it the table starts over
const GHOST_CAP: usize = 1 << 20;
/// values and environments `mkey` visits before it keys by id
pub(super) const KEY_FUEL: u32 = 4096;
/// A region with fewer than `reg_min` values rolls back when it made this
/// many bytes of big literals.
const REGION_MIN_LIT_BYTES: usize = 1 << 20;
const MEMO_LIT_BYTES: u64 = 1 << 14;
/// milestone 43: most keys in `lit_dropped` / `lit_redo` (8 MiB each);
/// past it the set starts over
/// milestone 46: first redos of the sampled keys before their second
/// redos decide when the others are pinned
const REDO_SAMPLE: u64 = 64;
pub(super) const LIT_KEYS_CAP: usize = 1 << 20;
/// marker of a dead value (SK_REGION_POISON): a level id no table hands out
pub const DEAD_LVL: u32 = 0xDEAD_0001;
/// marker of a dead environment's run start
pub const DEAD_RUN: u32 = 0xDEAD_0002;

impl Worker {
    /// Is a region opened here?
    #[inline(always)]
    pub(super) fn reg_wanted(&self) -> bool {
        (self.vals.len() >= self.reg_at || self.wlit_bytes >= self.reg_lit_at) && !self.scratch
    }
    #[inline(never)]
    pub(super) fn reg_open(&mut self, v: V) -> Reg {
        // milestone 37: the work of a rolled-back region asked for again
        let mut pin = false;
        if self.reg_pin && !self.ghost.is_empty() && self.ghost_shape.contains(&self.shape_key(v)) {
            let mut fuel = self.key_fuel;
            let k = self.mkey(v, &mut fuel);
            if self.pinned.contains(&k) {
                pin = true;
                self.stats.reg_redo += 1;
            } else if self.ghost.remove(&k) {
                // milestone 46: a pin keeps the work and its result through
                // every enclosing rollback for the rest of the session.
                // Pinned at its first redo it pays when redone work is
                // asked for again; when it mostly is not, the pins only
                // hold memory (MatCert_J4Fix's row5: 2.9 M first redos,
                // 0.6 M second ones, 4.7 GB; LyOm 1.1 M / 0.04 M, 6.9 GB).
                // So: an eighth of the keys (a sample by key bits) is
                // always pinned at its second redo, and counts how often a
                // redone piece of work is redone again; the other keys are
                // pinned at their first redo while at least half of the
                // sample's were (AlphaMc_Fi23Data 0.62, p6 0.60: as
                // before), else at their second (row5 0.21, LyOm 0.04).
                if self.redo_seen.len() >= GHOST_CAP {
                    self.redo_seen.clear();
                }
                let seen = self.redo_seen.contains(&k);
                let sample = k >> 61 == 0;
                if sample {
                    self.redo_n[seen as usize] += 1;
                }
                let first = !sample && self.redo_n[0] >= REDO_SAMPLE && self.redo_cut * self.redo_n[1] >= self.redo_n[0];
                if self.reg_pin_first || first || seen {
                    pin = true;
                    self.pinned.insert(k);
                    self.stats.reg_redo += 1;
                } else {
                    self.redo_seen.insert(k);
                }
            }
        }
        let mut r = self.reg_open_marks();
        r.pin = pin;
        r
    }
    fn reg_open_marks(&mut self) -> Reg {
        let r = Reg {
            t0: self.ticks,
            pin: false,
            pk: std::mem::take(&mut self.reg_kmax),
            pm: self.pin_ids.len(),
            dm: self.reg_done.len(),
            vm: self.vals.len() as u32,
            em: self.eloc.len() as u32,
            esm: self.eslots.len() as u32,
            spm: self.sp.words() as u32,
            wm: self.wlits.len() as u32,
            fvm: self.fv_ty.len() as u32,
            ul: self.undo.len(),
            um: self.uenv_next,
            lb: self.wlit_bytes,
            spg: self.sp.grows,
            ftg: self.ftab.grows,
            prev: self.reg_vm,
            dvm: self.vals.len() as u32,
            dlb: self.wlit_bytes,
            lv: 0,
        };
        self.reg_vm = r.vm;
        self.stats.reg[0] += 1;
        if KNOBS && (self.stats.reg[0] & (self.stats.reg[0] - 1)) == 0 && std::env::var("SK_REGION_REPORT").is_ok() {
            eprintln!("REG ticks {} {}", self.ticks, self.table_report());
        }
        r
    }
    /// Milestone 37: a checkpoint of whnf's loop is due: since the region
    /// (re)opened the loop made half of what opens regions (values or
    /// big-literal bytes). A rollback has a fixed cost (the direct-mapped
    /// tables start over), so checkpoints come at that scale only.
    #[inline(always)]
    pub(super) fn reg_due(&self, r: &Reg) -> bool {
        let d = self.reg_ckdiv;
        self.vals.len() - r.dvm as usize >= (self.reg_at / d).max(self.reg_min).max(r.lv)
            || self.wlit_bytes.saturating_sub(r.dlb) >= (self.reg_lit_at / d).max(REGION_MIN_LIT_BYTES)
    }
    /// Milestone 37: the region of the same whnf call, opened again after a
    /// checkpoint (same root, cost clock and pin).
    /// Milestone 38: a checkpoint: the region closes with the loop's
    /// current term `t` as its result; the next region opens at its marks
    /// when it rolled back (so the copies are in it), else after it.
    pub(super) fn reg_checkpoint(&mut self, g: &Reg, v: V, t: V) -> R<(V, Reg)> {
        self.stats.ckpts += 1;
        self.reg_ckpt_req = self.reg_ckpt_same;
        self.reg_ckpt_new = None;
        let t = self.reg_close(g, v, t);
        self.reg_ckpt_req = false;
        let t = t?;
        let g2 = match self.reg_ckpt_new.take() {
            Some(g2) => g2,
            None => self.reg_reopen(g),
        };
        Ok((t, g2))
    }
    /// Milestone 38: is `x` older than region `g` (made before it opened)?
    #[inline(always)]
    pub(super) fn reg_old(&self, g: &Reg, x: V) -> bool {
        x < g.vm
    }
    pub(super) fn reg_reopen(&mut self, old: &Reg) -> Reg {
        let mut r = self.reg_open_marks();
        r.t0 = old.t0;
        r.pin = old.pin;
        r
    }
    /// The region ends without a rollback (an error, or nothing to gain).
    pub(super) fn reg_keep(&mut self, r: &Reg) {
        self.reg_vm = r.prev;
        // what the enclosing region learns: the largest region inside it
        // that stays after an attempt (or below one that did)
        self.reg_kmax = r.pk.max(self.reg_kmax);
        if r.prev == 0 {
            // no region is open: nothing can be rolled back any more
            self.undo.clear();
            self.reg_done.clear();
            self.pin_ids.clear();
        }
    }
    /// Milestone 37: the region `r` with root `v` closed (kept or rolled
    /// back): remembered as costly work an enclosing rollback may drop, or
    /// as pinned work it must keep.
    fn reg_note(&mut self, r: &Reg, v: V) {
        if !self.reg_pin || r.prev == 0 {
            return;
        }
        if r.pin {
            if v >= r.prev {
                self.pin_ids.push(v);
            }
        } else {
            let cost = self.ticks.wrapping_sub(r.t0);
            if cost >= self.ghost_ticks && v >= r.prev {
                self.reg_done.push((v, cost));
            }
        }
    }
    /// Milestone 37: a key of `v`'s outermost shape (its term, or its
    /// head and spine length), in O(1): only a value whose shape is in
    /// `ghost_shape` has its full key (`mkey`) computed when a region opens.
    #[inline(always)]
    fn shape_key(&self, v: V) -> u64 {
        match self.vals[v as usize].v {
            Val::Thunk { term, ls, .. } | Val::Clo { term, ls, .. } | Val::CloI { term, ls, .. } => {
                hmix(hmix(1, term as u64), ls as u64)
            }
            Val::Neu { head: Head::Const(r, l), spine } => hmix(hmix(hmix(2, r as u64), l as u64), self.sp.len(spine) as u64),
            Val::Neu { head: Head::FVar(i), spine } => hmix(hmix(3, i as u64), self.sp.len(spine) as u64),
            Val::Neu { head: Head::Stuck(_), spine } => hmix(4, self.sp.len(spine) as u64),
            _ => 5,
        }
    }
    /// Milestone 37: forgets the redone-work tables (a new session: the
    /// keys name its values).
    pub(super) fn reg_forget(&mut self) {
        self.mkv.clear();
        self.mke.clear();
        self.redo_seen.clear();
        self.ghost.clear();
        self.ghost_shape.clear();
        self.pinned.clear();
        self.reg_done.clear();
        self.pin_ids.clear();
    }

    /// Milestone 37: a key of `v` by content: values older than any
    /// rollback keep their ids, so two values made the same way from the
    /// same older values get the same key. Approximate (collisions, fuel):
    /// it only decides what a rollback keeps, never an answer.
    pub(super) fn mkey(&mut self, v: V, fuel: &mut u32) -> u64 {
        if let Some(&k) = self.mkv.get(v as usize) {
            if k != 0 {
                return k;
            }
        }
        let k = if *fuel == 0 {
            hmix(0x51, v as u64)
        } else {
            *fuel -= 1;
            match self.vals[v as usize].v {
                Val::Sort(l) => hmix(1, l as u64),
                Val::Lit(i) => match self.lit(i) {
                    LitVal::Nat(n) => {
                        let mut d = n.iter_u64_digits();
                        let lo = d.next().unwrap_or(0);
                        let hi = d.next_back().unwrap_or(0);
                        hmix(hmix(hmix(2, n.bits()), lo), hi)
                    }
                    LitVal::Str(st) => hmix(3, st.len() as u64 ^ (i as u64) << 32),
                },
                Val::Clo { term, env, ls } => hmix(hmix(hmix(4, term as u64), ls as u64), self.ekey(env, fuel)),
                Val::CloI { term, env, ls } => hmix(hmix(hmix(5, term as u64), ls as u64), self.ekey(env, fuel)),
                Val::Thunk { term, env, ls } => hmix(hmix(hmix(6, term as u64), ls as u64), self.ekey(env, fuel)),
                Val::Neu { head, spine } => {
                    let mut h = match head {
                        Head::FVar(i) => hmix(7, i as u64),
                        Head::Const(r, l) => hmix(hmix(8, r as u64), l as u64),
                        Head::Stuck(x) => hmix(9, self.mkey(x, fuel)),
                    };
                    let xs = self.spine(spine);
                    for a in xs {
                        h = if a & PROJ_BIT != 0 { hmix(h, a as u64) } else { hmix(h ^ 10, self.mkey(a, fuel)) };
                    }
                    h
                }
            }
        } | 1;
        if self.mkv.len() <= v as usize {
            self.mkv.resize(v as usize + 1, 0);
        }
        self.mkv[v as usize] = k;
        k
    }
    fn ekey(&mut self, e: u32, fuel: &mut u32) -> u64 {
        if e == EMPTY {
            return 0x77;
        }
        if let Some(&k) = self.mke.get(e as usize) {
            if k != 0 {
                return k;
            }
        }
        let (st, l) = self.eloc_of(e);
        let mut h = hmix(11, self.eloc[e as usize].2);
        for i in st..st + l {
            let x = self.eslot(i);
            h = if x == HOLE { hmix(h, 12) } else { hmix(h ^ 13, self.mkey(x, fuel)) };
        }
        let k = h | 1;
        if self.mke.len() <= e as usize {
            self.mke.resize(e as usize + 1, 0);
        }
        self.mke[e as usize] = k;
        k
    }
    /// `reg_close` decided to keep the region.
    fn reg_close_keep(&mut self, r: &Reg, v: V, res: V) -> V {
        self.reg_keep(r);
        self.reg_note(r, v);
        res
    }
    /// The region of a call that returned `res`: rolled back when it is
    /// worth it. Returns the result's id after the rollback.
    #[inline(never)]
    pub(super) fn reg_close(&mut self, r: &Reg, v: V, res: V) -> R<V> {
        let made = self.vals.len() - r.vm as usize;
        // a few values may hold big literals (bit-sliced matrices, CFSG's
        // gf3): their bytes count too
        let lit_made = self.wlit_bytes.saturating_sub(r.lb);
        if (made < self.reg_min && lit_made < REGION_MIN_LIT_BYTES) || (self.kb_env != NONE && self.kb_env >= r.em) {
            return Ok(self.reg_close_keep(r, v, res));
        }
        let limit = (made * self.reg_reach8 / 8).max(64);
        // milestone 37: the log of this region (its own writes and those
        // of the regions kept inside it) is read whole by the attempt; past
        // `reg_logk` entries per value made, the attempt costs more than
        // the values it could give back (CFSG's hD: deep recursion, each
        // level read the log of all the levels below it)
        // milestone 37: an attempt reads the region's log and walks what
        // its result reaches, both about as long as what it made, and a
        // region kept after an attempt is read again by every enclosing
        // attempt: quadratic in deep recursions (CFSG's hD: 1187 s, 3 s
        // without regions). An enclosing region tries again only once it
        // made `reg_grow` times what the largest kept region inside it
        // made, so a value is read by a logarithmic number of attempts.
        if self.reg_grow != 0 && made < self.reg_grow * self.reg_kmax {
            self.stats.reg_skip += 1;
            return Ok(self.reg_close_keep(r, v, res));
        }
        if self.reg_logk != 0 && self.undo.len() - r.ul > self.reg_logk * made {
            self.stats.reg[2] += 1;
            return Ok(self.reg_close_keep(r, v, res));
        }
        let Some(rcp) = self.reg_reach(r, res, limit) else {
            self.stats.reg[2] += 1;
            self.reg_kmax = self.reg_kmax.max(made);
            return Ok(self.reg_close_keep(r, v, res));
        };
        // milestone 46: what the rollback would give back, not what the
        // region made: values and big-literal bytes not reached by the
        // copies. Below the bounds that open a rollback at all
        // (`reg_min` values, `REGION_MIN_LIT_BYTES`) the region is kept, as
        // when its result reaches too much. McertP_Ly's ly31_K proof
        // rolled back 98 K regions that copied out 1109 M of the 1111 M
        // values they made (10.3 TB of literal bytes made, 10.29 TB
        // copied): a chain of Nat operations, each whnf a region whose
        // result is the next big literal, every level copying it again
        // (2929 G; Pestka 69 G).
        if self.reg_benefit {
            let (mut cv, mut cb) = (0usize, 0usize);
            for c in &rcp {
                match c {
                    Rcp::Val(..) | Rcp::Neu(..) => cv += 1,
                    Rcp::Lit(_, l) => {
                        cv += 1;
                        if let LitVal::Nat(n) = l {
                            cb += (n.bits() / 8) as usize;
                        }
                    }
                    Rcp::LitAt(_, i) => {
                        cv += 1;
                        if let LitVal::Nat(n) = self.lit(*i) {
                            cb += (n.bits() / 8) as usize;
                        }
                    }
                    Rcp::Env(..) => {}
                }
            }
            if made.saturating_sub(cv) < self.reg_min && lit_made.saturating_sub(cb) < REGION_MIN_LIT_BYTES {
                self.stats.reg[2] += 1;
                self.reg_kmax = self.reg_kmax.max(made);
                return Ok(self.reg_close_keep(r, v, res));
            }
        }
        self.stats.reg[1] += 1;

        self.stats.reg[3] += made as u64;
        self.stats.reg[4] += rcp.len() as u64;
        let out = self.reg_cut(r, rcp, res);
        self.reg_note(r, v);
        out
    }

    #[inline(always)]
    fn dv(&self, r: &Reg, x: u32) -> bool {
        x < (1 << 28) && x >= r.vm
    }
    #[inline(always)]
    fn de(&self, r: &Reg, e: u32) -> bool {
        e != EMPTY && e >= r.em
    }

    /// The region's objects `res` reaches, parts first; None past `limit`
    /// or when it reaches a variable made in the region. Then also what
    /// the logged memos of older values name in the region, when it is
    /// small (`MEMO_REACH` objects each): a result found for an older value
    /// stays found (sharing between sibling calls depends on it).
    #[inline(never)]
    fn reg_reach(&mut self, r: &Reg, res: V, limit: usize) -> Option<Vec<Rcp>> {
        const MEMO_REACH: usize = 64;
        const CLOSED_REACH: usize = 256;
        let mut out = Vec::new();
        let mut seen_v: FxHashSet<u32> = FxHashSet::default();
        let mut seen_e: FxHashSet<u32> = FxHashSet::default();
        if res >= r.vm && !self.reach_root(r, res, limit, &mut seen_v, &mut seen_e, &mut out) {
            return None;
        }
        let mut roots: Vec<u32> = Vec::new();
        self.stats.reg_seg += (self.undo.len() - r.ul) as u64;
        for u in &self.undo[r.ul..] {
            if let Undo::Memo(v, _) = u {
                if *v < r.vm {
                    let m = *self.memo_at(*v);
                    for x in [m.whnf, m.infer, if m.core == NONE { NONE } else { m.core & !CORE_FULL }, m.unfold()] {
                        if x != NONE && x < (1 << 28) && x >= r.vm {
                            roots.push(x);
                        }
                    }
                }
            }
        }
        let mut budget = limit;
        for x in roots {
            if seen_v.contains(&x) || (self.wlit_bytes > self.reg_lit_keep && self.big_lit(x)) {
                continue;
            }
            let n0 = out.len();
            let lim = if self.reg_memo_all { budget } else { MEMO_REACH.min(budget) };
            if self.reach_root(r, x, lim, &mut seen_v, &mut seen_e, &mut out) {
                budget = budget.saturating_sub(out.len() - n0);
            } else if self.reg_memo_all {
                // a memo of an older value would be lost: work found once
                // would be done again (shared lazy structures: Arena's
                // reachability tests thrashed); the region stays
                return None;
            }
        }
        self.reg_pairs.clear();
        // milestone 37: pinned work (found done again after a rollback)
        // stays, with its result, or the region does
        for i in r.pm..self.pin_ids.len() {
            let x = self.pin_ids[i];
            if x < r.vm || seen_v.contains(&x) {
                continue;
            }
            let n0 = out.len();
            if !self.reach_root(r, x, budget, &mut seen_v, &mut seen_e, &mut out) {
                self.stats.reg_pin_kept += 1;
                return None;
            }
            budget = budget.saturating_sub(out.len() - n0);
            let w = self.memo_at(x).whnf;
            if w != NONE && w < (1 << 28) && w >= r.vm && !seen_v.contains(&w) {
                let n0 = out.len();
                if !self.reach_root(r, w, budget, &mut seen_v, &mut seen_e, &mut out) {
                    self.stats.reg_pin_kept += 1;
                    return None;
                }
                budget = budget.saturating_sub(out.len() - n0);
            }
        }
        // milestone 37: a copy keeps the whnf memo (a thunk's forced value)
        // of the value it copies: the copy is the same computation (same
        // hash-consing key), and without it every later force of a lazy
        // structure the result reaches did its work again, at every
        // enclosing region (CFSG's p6: 1660 s, 3.07 s with regions off).
        // A memo that names an older value costs nothing; one that names a
        // value of the region makes its target reached too.
        if self.reg_fwd != 0 {
            let mut i = 0;
            while i < out.len() {
                let id = match &out[i] {
                    Rcp::Val(id, _) | Rcp::Neu(id, _, _) | Rcp::Lit(id, _) | Rcp::LitAt(id, _) => *id,
                    Rcp::Env(..) => {
                        i += 1;
                        continue;
                    }
                };
                i += 1;
                let w = self.memo_at(id).whnf;
                if w == NONE || w >= (1 << 28) || w == id {
                    continue;
                }
                if w >= r.vm && !seen_v.contains(&w) {
                    if self.wlit_bytes > self.reg_lit_keep && self.big_lit(w) {
                        continue;
                    }
                    let n0 = out.len();
                    if self.reach_root(r, w, budget, &mut seen_v, &mut seen_e, &mut out) {
                        budget = budget.saturating_sub(out.len() - n0);
                    } else if self.reg_fwd == 1 {
                        return None;
                    } else {
                        continue;
                    }
                }
                self.reg_pairs.push((id, w));
            }
        }
        // closed thunks forced in the region keep their forced values: a
        // later call meets them again through hash-consing ((term, EMPTY,
        // ls) is their whole identity) and would compute them again
        if self.reg_front != 0 {
            // milestone 37: every value of the region made only of older
            // parts (a thunk or closure over an older or EMPTY environment,
            // or over a new frame of older values; an application of an
            // older head to older arguments) can be made again by a later
            // call through hash-consing, with the same key: its whnf memo is
            // a result that call would compute again. Such values keep their
            // memos; one that does not fit keeps the region
            // (SK_REGION_FRONT=2: is dropped). CFSG's p6 checks a BFS
            // closure for each element of a list; each check's region
            // made the BFS thunk (older parts) and returned a Bool, so the
            // BFS was done again for every element.
            for d in r.vm..self.vals.len() as u32 {
                let w = self.memo_at(d).whnf;
                if w == NONE || w == d || w >= (1 << 28) {
                    continue;
                }
                // read directly: dead markers of inner rollbacks (SK_REGION_POISON)
                let front = match self.vals[d as usize].v {
                    Val::Thunk { env, .. } => self.env_old(r, env),
                    Val::Neu { head, spine } => {
                        (match head {
                            Head::Stuck(x) => x < r.vm,
                            Head::FVar(i) => i < r.fvm,
                            _ => true,
                        }) && self.sp.args(spine).iter().all(|&a| a & PROJ_BIT != 0 || a < r.vm)
                    }
                    _ => false,
                };
                if !front {
                    continue;
                }
                if self.wlit_bytes > self.reg_lit_keep && self.big_lit(w) {
                    continue;
                }
                let n0 = out.len();
                if (seen_v.contains(&d) || self.reach_root(r, d, budget, &mut seen_v, &mut seen_e, &mut out))
                    && (w < r.vm || seen_v.contains(&w) || self.reach_root(r, w, budget, &mut seen_v, &mut seen_e, &mut out))
                {
                    budget = budget.saturating_sub(out.len() - n0);
                    self.reg_pairs.push((d, w));
                } else if self.reg_front == 1 {
                    return None;
                }
            }
        } else if self.reg_closed {
            for d in r.vm..self.vals.len() as u32 {
                if budget == 0 {
                    break;
                }
                // read directly: dead markers of inner rollbacks (SK_REGION_POISON)
                let Val::Thunk { env, .. } = self.vals[d as usize].v else { continue };
                if env != EMPTY && (env >= r.em || !self.reg_oldenv) {
                    continue;
                }
                let w = self.memo_at(d).whnf;
                if w == NONE {
                    continue;
                }
                let n0 = out.len();
                let lim = CLOSED_REACH.min(budget);
                if !seen_v.contains(&d) && !self.reach_root(r, d, lim, &mut seen_v, &mut seen_e, &mut out) {
                    continue;
                }
                if w >= r.vm && !seen_v.contains(&w) && !self.reach_root(r, w, lim, &mut seen_v, &mut seen_e, &mut out) {
                    continue;
                }
                budget = budget.saturating_sub(out.len() - n0);
                self.reg_pairs.push((d, w));
            }
        }
        // milestone 37: costly closed regions whose roots die here: their
        // keys go to the ghost table (a region opened later on a value of
        // the same key is the same work done again)
        if self.reg_pin {
            for i in r.dm..self.reg_done.len() {
                let (x, cost) = self.reg_done[i];
                if x < r.vm {
                    continue;
                }
                if !seen_v.contains(&x) {
                    // the key costs at most a quarter of the work it stands for
                    let mut fuel = self.key_fuel.min(cost / 4);
                    let k = self.mkey(x, &mut fuel);
                    if self.ghost.len() >= GHOST_CAP {
                        self.ghost.clear();
                        self.ghost_shape.clear();
                    }
                    self.ghost.insert(k);
                    let sk = self.shape_key(x);
                    self.ghost_shape.insert(sk);
                }
            }
            self.reg_done.truncate(r.dm);
        }
        Some(out)
    }

    /// Milestone 37: an environment a later call can make again with the
    /// same id or key: EMPTY, older than the region, or a frame of the
    /// region whose entries are all older.
    fn env_old(&self, r: &Reg, env: u32) -> bool {
        if env == EMPTY || env < r.em {
            return true;
        }
        let (s, l) = self.eloc_of(env);
        (s..s + l).all(|k| {
            let x = self.eslot(k);
            x == HOLE || x < r.vm
        })
    }

    /// A Nat literal past `MEMO_LIT_BYTES`: once the session's big literals
    /// pass `reg_lit_keep` bytes, a memo that names one is not kept by a
    /// rollback (made again if asked again; CFSG's gf3 holds
    /// 609961-bit intermediates of matrix products that are read once).
    /// Milestone 43: unless a literal of the same content was made again
    /// after such a drop (`lit_redo`): then the drop cost the work again
    /// and the memo stays. CFSG's LyOm.neg_a3 forces the same table
    /// entries (2290-limb products) about 100 times each: every force
    /// after a rollback multiplied again (> 80 min; 37 s with the memos
    /// kept, as with SK_REGION_LIT_KEEP past its literals). Read-once
    /// intermediates are never made again, so they are still dropped.
    fn big_lit(&mut self, x: V) -> bool {
        let k = match self.val(x) {
            Val::Lit(i) => match self.lit(i) {
                LitVal::Nat(n) if n.bits() > 8 * MEMO_LIT_BYTES => lit_key(n),
                _ => return false,
            },
            _ => return false,
        };
        if !self.lit_redo_on {
            return true;
        }
        if self.lit_redo.contains(&k) {
            return false;
        }
        if self.lit_dropped.len() >= LIT_KEYS_CAP {
            self.lit_dropped.clear();
        }
        self.lit_dropped.insert(k);
        true
    }

    /// `reg_reach` from one root: false (and nothing added) past `limit`
    /// objects or at a variable made in the region.
    #[inline(never)]
    fn reach_root(&mut self, r: &Reg, root: V, limit: usize, seen_v: &mut FxHashSet<u32>, seen_e: &mut FxHashSet<u32>, out: &mut Vec<Rcp>) -> bool {
        let g = self.env.lits.len() as u32;
        let n0 = out.len();
        let mut touched: Vec<(bool, u32)> = Vec::new();
        // (is environment, id, children pushed)
        let mut st: Vec<(bool, u32, bool)> = vec![(false, root, false)];
        let mut ok = true;
        while let Some((is_env, id, done)) = st.pop() {
            if out.len() - n0 > limit || touched.len() > 4 * limit + 16 {
                ok = false;
                break;
            }
            if !is_env {
                if done {
                    let v = self.val(id);
                    let rc = match v {
                        Val::Lit(i) if i >= g + r.wm => Rcp::LitAt(id, i),
                        Val::Neu { head, spine } if spine != EMPTY => Rcp::Neu(id, head, SpineVec::from_slice(self.sp.args(spine))),
                        _ => Rcp::Val(id, v),
                    };
                    out.push(rc);
                    continue;
                }
                if !seen_v.insert(id) {
                    continue;
                }
                touched.push((false, id));
                st.push((false, id, true));
                match self.val(id) {
                    Val::Sort(_) | Val::Lit(_) => {}
                    Val::Clo { env, .. } | Val::CloI { env, .. } | Val::Thunk { env, .. } => {
                        if self.de(r, env) && !seen_e.contains(&env) {
                            st.push((true, env, false));
                        }
                    }
                    Val::Neu { head, spine } => {
                        match head {
                            Head::FVar(i) if i >= r.fvm => {
                                ok = false;
                                break;
                            }
                            Head::Stuck(x) if x >= r.vm && !seen_v.contains(&x) => st.push((false, x, false)),
                            _ => {}
                        }
                        for &a in self.sp.args(spine) {
                            if a & PROJ_BIT == 0 && a >= r.vm && !seen_v.contains(&a) {
                                st.push((false, a, false));
                            }
                        }
                    }
                }
            } else {
                if done {
                    let (s, l) = self.eloc_of(id);
                    let m = self.eloc[id as usize].2;
                    let c = SpineVec::from_slice(&self.eslots[s as usize..(s + l) as usize]);
                    out.push(Rcp::Env(id, c, m));
                    continue;
                }
                if !seen_e.insert(id) {
                    continue;
                }
                touched.push((true, id));
                st.push((true, id, true));
                let (s, l) = self.eloc_of(id);
                for k in s..s + l {
                    let x = self.eslot(k);
                    if x != HOLE && x >= r.vm && !seen_v.contains(&x) {
                        st.push((false, x, false));
                    }
                }
            }
        }
        if !ok {
            out.truncate(n0);
            for (e, id) in touched {
                if e {
                    seen_e.remove(&id);
                } else {
                    seen_v.remove(&id);
                }
            }
        }
        ok
    }

    /// The rollback itself (see the module comment).
    #[inline(never)]
    fn reg_cut(&mut self, r: &Reg, rcp: Vec<Rcp>, res: V) -> R<V> {
        self.reg_epoch = self.reg_epoch.wrapping_add(1);
        // milestone 40: the ground machine's kept heap may name older ids
        let c = &mut self.ground_cut;
        *c = (c.0.min(r.vm), c.1.min(r.em), c.2.min(r.wm));
        let log: Vec<Undo> = self.undo.drain(r.ul..).collect();
        // SK_REGION_DELALL=1 (knobs, region gate): deletion by key at
        // every rollback, so the gate exercises it
        let sp_ok = self.sp.grows == r.spg && !self.reg_delall;
        let ft_ok = self.ftab.grows == r.ftg && !self.reg_delall;
        let mut memos: Vec<(V, Memo)> = Vec::new();
        // entries that name no dead id stay facts; an open parent region
        // must still see them (they may name ids dead for it)
        let mut keep: Vec<Undo> = Vec::new();
        for u in log.into_iter().rev() {
            let kill = match &u {
                Undo::Memo(v, m) => {
                    if *v < r.vm {
                        memos.push((*v, *m));
                    }
                    continue;
                }
                Undo::EnvMap(k) => {
                    // every environment made in the region is dead
                    self.env_map.remove(k);
                    continue;
                }
                Undo::Sp(s) => {
                    if sp_ok {
                        self.sp.unadd(*s as usize);
                    }
                    continue;
                }
                Undo::Ft(s) => {
                    if ft_ok {
                        self.ftab.unadd(*s as usize);
                    }
                    continue;
                }
                Undo::Uenv(k) => {
                    // its id was counted in the region: never handed out again
                    self.uenv_map.remove(&k[..]);
                    continue;
                }
                // milestone 37: an entry no longer in its map (taken out
                // by an inner rollback) is forgotten, not passed up: such
                // entries piled up in the enclosing regions' logs (hD:
                // 18x the log reads with big literals shared)
                Undo::Nat(k) if !self.nat_map.contains_key(k) => continue,
                Undo::BigNat(k) if !self.big_map.contains_key(k) => continue,
                Undo::Eq(pk) if !self.eq_cache.contains_key(pk) => continue,
                Undo::Fail(a, b) if !self.fail_cache.contains(&(*a, *b)) => continue,
                Undo::Infer(k) if !self.infer_cache.contains_key(k) => continue,
                Undo::InferU(k) if !self.infer_u.contains_key(k) => continue,
                Undo::LamVar(k) if !self.lam_var.contains_key(k) => continue,
                Undo::VarSlot(k) if !self.var_slots.contains_key(k) => continue,
                Undo::Shash(v) if !self.shash_memo.contains_key(v) => continue,
                Undo::Canon(k) if !self.canon_memo.contains_key(k) => continue,
                Undo::NmOfVal(v) if !self.nm.of_val.contains_key(v) => continue,
                Undo::NmOfTerm(k) if !self.nm.of_term.contains_key(k) => continue,
                Undo::NmInfer(k) if !self.nm.infer.contains_key(k) => continue,
                Undo::Nat(k) => self.nat_map.get(k).is_some_and(|&x| self.dv(r, x)),
                Undo::BigNat(k) => self.big_map.get(k).is_some_and(|&x| self.dv(r, x)),
                Undo::Eq(pk) => self.dv(r, (pk >> 32) as u32) || self.dv(r, *pk as u32),
                Undo::Fail(a, b) => self.dv(r, *a) || self.dv(r, *b),
                Undo::Infer(k) => self.de(r, k.0 as u32) || self.infer_cache.get(k).is_some_and(|x| self.dv(r, x.0)),
                Undo::InferU(k) => k.0 as u32 >= r.um || self.infer_u.get(k).is_some_and(|x| self.dv(r, x.0)),
                Undo::LamVar(k) => self.de(r, k.1) || self.lam_var.get(k).is_some_and(|&x| self.dv(r, x)),
                Undo::VarSlot(k) => self.var_slots.get(k).is_some_and(|&x| self.dv(r, x)),
                Undo::Shash(v) => self.dv(r, *v),
                Undo::Canon(k) => self.de(r, k.1) || self.canon_memo.get(k).is_some_and(|&x| self.dv(r, x)),
                Undo::NmOfVal(v) => self.dv(r, *v),
                Undo::NmOfTerm(k) => self.de(r, k.0 as u32),
                Undo::NmInfer(k) => self.nm.infer.get(k).is_some_and(|x| self.dv(r, x.0)),
            };
            if !kill {
                keep.push(u);
                continue;
            }
            match u {
                Undo::Nat(k) => {
                    self.nat_map.remove(&k);
                }
                Undo::BigNat(k) => {
                    self.big_map.remove(&k);
                }
                Undo::Eq(pk) => {
                    self.eq_cache.remove(&pk);
                }
                Undo::Fail(a, b) => {
                    self.fail_cache.remove(&(a, b));
                }
                Undo::Infer(k) => {
                    self.infer_cache.remove(&k);
                }
                Undo::InferU(k) => {
                    self.infer_u.remove(&k);
                }
                Undo::LamVar(k) => {
                    self.lam_var.remove(&k);
                }
                Undo::VarSlot(k) => {
                    self.var_slots.remove(&k);
                }
                Undo::Shash(v) => {
                    self.shash_memo.remove(&v);
                }
                Undo::Canon(k) => {
                    self.canon_memo.remove(&k);
                }
                Undo::NmOfVal(v) => {
                    self.nm.of_val.remove(&v);
                }
                Undo::NmOfTerm(k) => {
                    self.nm.of_term.remove(&k);
                }
                Undo::NmInfer(k) => {
                    self.nm.infer.remove(&k);
                }
                _ => unreachable!(),
            }
        }
        // milestone 37: after a growth inside the region the logged slots
        // are stale: the dead entries leave the tables one by one (deletion
        // by key; it was a rebuild of the whole table, once per open region
        // after one growth: CFSG's hD rebuilt a 130 MB spine table at each
        // rollback)
        if !sp_ok {
            if self.reg_rebuild {
                self.sp.rebuild_below(&self.vals, r.vm);
            } else {
                for d in (r.vm..self.vals.len() as u32).rev() {
                    if let Val::Neu { spine, .. } = self.vals[d as usize].v {
                        if spine != EMPTY {
                            self.sp.remove_value(&self.vals, d);
                        }
                    }
                }
            }
        }
        if !ft_ok {
            let (eloc, eslots) = (&self.eloc, &self.eslots);
            let hash_of = |x: u32| {
                let (s, l, _) = eloc[x as usize];
                frames::fhash(&eslots[s as usize..(s + l) as usize])
            };
            if self.reg_rebuild {
                self.ftab.rebuild_below(r.em, hash_of);
            } else {
                for e in (r.em..eloc.len() as u32).rev() {
                    if eloc[e as usize].0 != DEAD_RUN {
                        self.ftab.remove(hash_of(e), e, hash_of);
                    }
                }
            }
        }
        // the interned values among the dead ones leave `vmap`
        let mut lit_bytes = 0usize;
        for d in r.vm..self.vals.len() as u32 {
            // read directly: under SK_REGION_POISON an inner rollback left
            // dead markers here
            let v = self.vals[d as usize].v;
            match v {
                Val::Neu { spine, .. } if spine != EMPTY => {}
                _ => {
                    let k = vkey(&v);
                    if self.vmap.get(&k) == Some(&d) {
                        self.vmap.remove(&k);
                    }
                }
            }
        }
        for i in r.wm as usize..self.wlits.len() {
            if let LitVal::Nat(n) = &self.wlits[i] {
                if n.to_u64().is_none() {
                    lit_bytes += (n.bits() / 8) as usize;
                }
            }
        }
        self.wlit_bytes -= lit_bytes.min(self.wlit_bytes);
        // milestone 40: the literals the result reaches leave their dead
        // slots (moved, not copied)
        let mut rcp = rcp;
        {
            let g = self.env.lits.len() as u32;
            let mut moved: FxHashMap<u32, usize> = FxHashMap::default();
            for k in 0..rcp.len() {
                if let Rcp::LitAt(id, i) = rcp[k] {
                    let l = match moved.get(&i) {
                        Some(&j) => match &rcp[j] {
                            Rcp::Lit(_, l) => l.clone(),
                            _ => unreachable!(),
                        },
                        None => {
                            moved.insert(i, k);
                            std::mem::replace(&mut self.wlits[(i - g) as usize], LitVal::Nat(BigUint::zero()))
                        }
                    };
                    rcp[k] = Rcp::Lit(id, l);
                }
            }
        }
        if self.reg_poison {
            for d in r.vm as usize..self.vals.len() {
                self.vals[d] = Rec { v: Val::Sort(DEAD_LVL), m: Memo::NEW };
            }
            for e in r.em as usize..self.eloc.len() {
                self.eloc[e] = (DEAD_RUN, 0, 0);
            }
            for i in r.wm as usize..self.wlits.len() {
                self.wlits[i] = LitVal::Str("\u{0}dead".into());
            }
        } else {
            self.vals.truncate(r.vm as usize);
            self.eloc.truncate(r.em as usize);
            self.eslots.truncate(r.esm as usize);
            self.sp.truncate(r.spm as usize);
            self.wlits.truncate(r.wm as usize);
        }
        self.reg_keep(r);
        if self.reg_vm != 0 {
            self.undo.extend(keep);
        }
        // milestone 38: a checkpoint opens the next region at this one's
        // marks, before the copies: the loop's state copied out lives in the
        // region and dies at the next checkpoint unless reached again (it
        // piled up in the enclosing context, one loop state per checkpoint,
        // forever when no region encloses the loop)
        if self.reg_ckpt_req {
            self.reg_ckpt_req = false;
            let mut g = self.reg_open_marks();
            g.t0 = r.t0;
            g.pin = r.pin;
            g.pm = r.pm;
            g.dm = r.dm;
            self.reg_ckpt_new = Some(g);
        }
        self.cgen_bump();
        // the copies, parts first
        let mut mv: FxHashMap<u32, u32> = FxHashMap::default();
        let mut me: FxHashMap<u32, u32> = FxHashMap::default();
        let fv = |mv: &FxHashMap<u32, u32>, x: u32| -> u32 { mv.get(&x).copied().unwrap_or(x) };
        let mut ok = true;
        for c in rcp {
            let made = match c {
                Rcp::LitAt(..) => unreachable!(),
                Rcp::Lit(old, l) => {
                    let n = match l {
                        LitVal::Nat(n) => self.mk_nat(n),
                        LitVal::Str(s) => {
                            let i = self.env.lits.len() as u32 + self.wlits.len() as u32;
                            self.wlits.push(LitVal::Str(s));
                            self.intern(Val::Lit(i))
                        }
                    };
                    n.map(|n| (false, old, n))
                }
                Rcp::Val(old, v) => {
                    let v = match v {
                        Val::Clo { term, env, ls } => Val::Clo { term, env: fv(&me, env), ls },
                        Val::CloI { term, env, ls } => Val::CloI { term, env: fv(&me, env), ls },
                        Val::Thunk { term, env, ls } => Val::Thunk { term, env: fv(&me, env), ls },
                        Val::Neu { head: Head::Stuck(x), spine } => Val::Neu { head: Head::Stuck(fv(&mv, x)), spine },
                        v => v,
                    };
                    self.intern(v).map(|n| (false, old, n))
                }
                Rcp::Neu(old, head, args) => {
                    let head = match head {
                        Head::Stuck(x) => Head::Stuck(fv(&mv, x)),
                        h => h,
                    };
                    let xs: SpineVec = args.iter().map(|&a| if a & PROJ_BIT != 0 { a } else { fv(&mv, a) }).collect();
                    self.neu(head, EMPTY, &xs).map(|n| (false, old, n))
                }
                Rcp::Env(old, c, m) => {
                    let xs: SpineVec = c.iter().map(|&a| if a == HOLE { a } else { fv(&mv, a) }).collect();
                    Ok((true, old, self.reg_env(&xs, m)))
                }
            };
            match made {
                Ok((false, old, n)) => {
                    mv.insert(old, n);
                }
                Ok((true, old, n)) => {
                    me.insert(old, n);
                }
                Err(_) => {
                    ok = false;
                    break;
                }
            }
        }
        // memo fields that named a dead id: its copy, else what they held
        // before the write that put it there (the log, latest first; ids
        // are compared before the copies were made, so a copy is never
        // taken for a dead id). An open parent region learns each value's
        // memo as it was before this region (its first logged state): the
        // states logged inside this region may name ids dead for it too.
        let mut by_v: FxHashMap<V, Vec<Memo>> = FxHashMap::default();
        let mut order: Vec<V> = Vec::new();
        for (v, old) in memos {
            by_v.entry(v).or_insert_with(|| {
                order.push(v);
                Vec::new()
            }).push(old);
        }
        let vm = r.vm;
        // the id a memo word names (None: no id)
        fn wid(f: usize, w: u32) -> Option<u32> {
            let x = match f {
                1 => if w == NONE { NONE } else { w & !CORE_FULL },
                3 => w & UF_MASK,
                _ => w,
            };
            if x != NONE && x < (1 << 28) { Some(x) } else { None }
        }
        fn wset(f: usize, w: u32, x: u32) -> u32 {
            match f {
                1 => x | (w & CORE_FULL),
                3 => (w & !UF_MASK) | x,
                _ => x,
            }
        }
        fn words(m: &Memo) -> [u32; 4] {
            [m.whnf, m.core, m.infer, m.uf]
        }
        for v in order {
            let olds = &by_v[&v];
            let cur = *self.memo_at(v);
            let cw = words(&cur);
            let mut nw = cw;
            for f in 0..4 {
                let mut w = cw[f];
                let mut k = 0;
                loop {
                    match wid(f, w) {
                        Some(x) if x >= vm => {
                            if let (true, Some(&y)) = (ok, mv.get(&x)) {
                                w = wset(f, w, y);
                                break;
                            }
                            if k == olds.len() {
                                // not reached: the first logged state is
                                // from before the region
                                w = match f {
                                    1 | 2 | 0 => NONE,
                                    _ => (w & !UF_MASK) | UF_NONE,
                                };
                                break;
                            }
                            let ow = words(&olds[k])[f];
                            // the fvar bits stay the current ones
                            w = if f == 3 { (w & !UF_MASK) | (ow & UF_MASK) } else { ow };
                            k += 1;
                        }
                        _ => break,
                    }
                }
                nw[f] = w;
            }
            let m = Memo { whnf: nw[0], core: nw[1], infer: nw[2], uf: nw[3] };
            if v < self.reg_vm {
                self.undo.push(Undo::Memo(v, *olds.last().unwrap()));
            }
            *self.memo_mut(v) = m;
        }
        // milestone 37: pinned roots of the region now live as their copies
        // (or are gone); the keys of dead ids go
        self.mkv.truncate(r.vm as usize);
        self.mke.truncate(r.em as usize);
        if ok {
            let mut j = r.pm;
            for i in r.pm..self.pin_ids.len() {
                let x = self.pin_ids[i];
                let y = if x >= r.vm { mv.get(&x).copied() } else { Some(x) };
                if let Some(y) = y {
                    self.pin_ids[j] = y;
                    j += 1;
                }
            }
            self.pin_ids.truncate(j);
        }
        if ok {
            for (d, w) in std::mem::take(&mut self.reg_pairs) {
                let d2 = mv[&d];
                let w2 = if w >= r.vm { mv[&w] } else { w };
                if self.memo_at(d2).whnf == NONE {
                    self.memo_w(d2).whnf = w2;
                }
            }
        }
        if !ok {
            // a copy failed (an arena limit)
            return decline(VALS_FULL);
        }
        // milestone 38: the next checkpoint waits for new work at least as
        // large as what this one copied, so copying the loop's state again
        // at every checkpoint costs at most the work done in between
        if let Some(g) = &mut self.reg_ckpt_new {
            g.dvm = self.vals.len() as u32;
            g.dlb = self.wlit_bytes;
            g.lv = (g.dvm - g.vm) as usize;
        }
        if self.reg_check {
            self.reg_check_tables();
        }
        Ok(if res < r.vm { res } else { mv[&res] })
    }

    /// An environment with content `c` (oldest first), as a frame of mask
    /// `m` (m != 0) or as pushes.
    #[inline(never)]
    fn reg_env(&mut self, c: &[u32], m: u64) -> u32 {
        if m == 0 {
            let mut e = EMPTY;
            for &x in c {
                e = self.push_env(x, e);
            }
            return e;
        }
        let h = frames::fhash(c);
        let (eloc, eslots) = (&self.eloc, &self.eslots);
        let run = |e: u32| {
            let (s, l, _) = eloc[e as usize];
            &eslots[s as usize..(s + l) as usize]
        };
        match self.ftab.find(h, c, run) {
            Ok(e) => e,
            Err(slot) => {
                let e = self.eloc.len() as u32;
                self.eloc.push((self.eslots.len() as u32, c.len() as u32, m));
                self.eslots.extend_from_slice(c);
                self.ft_insert(h, slot, e);
                e
            }
        }
    }

    /// `ftab.insert`, logged in a region.
    pub(super) fn ft_insert(&mut self, h: u64, slot: usize, e: u32) {
        let (eloc, eslots) = (&self.eloc, &self.eslots);
        let s = self.ftab.insert(h, slot, e, |x| {
            let (s, l, _) = eloc[x as usize];
            frames::fhash(&eslots[s as usize..(s + l) as usize])
        });
        if self.reg_vm != 0 {
            if let Some(s) = s {
                self.undo.push(Undo::Ft(s as u32));
            }
        }
    }

    /// Logs a write to the memo of `v` (before it is made).
    #[inline(always)]
    pub(super) fn memo_w(&mut self, v: V) -> &mut Memo {
        if v < self.reg_vm {
            let m = *self.memo_at(v);
            self.undo.push(Undo::Memo(v, m));
        }
        self.memo_mut(v)
    }
    #[inline(always)]
    pub(super) fn ulog(&mut self, u: Undo) {
        #[cfg(debug_assertions)]
        if self.reg_poison {
            if let Undo::Eq(pk) = &u {
                for x in [(*pk >> 32) as u32, *pk as u32] {
                    assert!(!matches!(self.vals[x as usize].v, Val::Sort(DEAD_LVL)), "eq_cache keyed by dead value {x}");
                }
            }
        }
        if self.reg_vm != 0 {
            self.undo.push(u);
        }
    }

    /// SK_REGION_POISON=2 (release-da gates): no table names a dead id
    /// (a marker left by SK_REGION_POISON). A stale key would be found
    /// again once ids are reused; a stale value would be read.
    #[cold]
    #[inline(never)]
    fn reg_check_tables(&self) {
        let n = self.vals.len() as u32;
        let dv = |x: u32| x < (1 << 28) && x < n && matches!(self.vals[x as usize].v, Val::Sort(DEAD_LVL));
        let de = |e: u32| e != EMPTY && (e as usize) < self.eloc.len() && self.eloc[e as usize].0 == DEAD_RUN;
        let bad = |what: &str| panic!("region check: {what} names a dead id");
        for v in 0..n {
            let m = self.vals[v as usize].m;
            if matches!(self.vals[v as usize].v, Val::Sort(DEAD_LVL)) {
                continue;
            }
            let c = if m.core == NONE { NONE } else { m.core & !CORE_FULL };
            if dv(m.whnf) || dv(m.infer) || dv(c) || dv(m.unfold()) {
                bad("a memo");
            }
            match self.vals[v as usize].v {
                Val::Clo { env, .. } | Val::CloI { env, .. } | Val::Thunk { env, .. } => {
                    if de(env) {
                        bad("a closure");
                    }
                }
                Val::Neu { head, spine } => {
                    if let Head::Stuck(x) = head {
                        if dv(x) {
                            bad("a stuck head");
                        }
                    }
                    for &a in self.sp.args(spine) {
                        if a & PROJ_BIT == 0 && dv(a) {
                            bad("a spine");
                        }
                    }
                }
                _ => {}
            }
        }
        for (e, &(s, l, _)) in self.eloc.iter().enumerate() {
            if s == DEAD_RUN {
                continue;
            }
            for k in s..s + l {
                let x = self.eslots[k as usize];
                if x != HOLE && dv(x) {
                    bad(&format!("environment {e}"));
                }
            }
        }
        for (k, &x) in self.vmap.iter() {
            // vkey: (kind << 32 | a, b << 32 | c)
            let kind = (k.0 >> 32) as u8;
            let (a, b) = (k.0 as u32, (k.1 >> 32) as u32);
            let stale = match kind {
                2 | 3 | 7 => de(b),
                6 => dv(a),
                _ => false,
            };
            if dv(x) || stale {
                bad("vmap");
            }
        }
        for (&k, &e) in self.env_map.iter() {
            if de(e) || dv((k >> 32) as u32) || de(k as u32) {
                bad("env_map");
            }
        }
        for x in self.sp.entries() {
            if dv(x) {
                bad("the spine table");
            }
        }
        for e in self.ftab.entries() {
            if de(e) {
                bad("the frame table");
            }
        }
        for (_, &x) in self.nat_map.iter().chain(self.big_map.iter()) {
            if dv(x) {
                bad("nat_map");
            }
        }
        for &pk in self.eq_cache.keys() {
            if dv((pk >> 32) as u32) || dv(pk as u32) {
                bad("eq_cache");
            }
        }
        for &(a, b) in self.fail_cache.iter() {
            if dv(a) || dv(b) {
                bad("fail_cache");
            }
        }
        for (k, x) in self.infer_cache.iter() {
            if de(k.0 as u32) || dv(x.0) {
                bad("infer_cache");
            }
        }
        for (_, x) in self.infer_u.iter() {
            if dv(x.0) {
                bad("infer_u");
            }
        }
        for k in self.uenv_map.keys() {
            if k[2..].iter().any(|&x| dv(x)) && k[0] | k[1] != 0 {
                bad("uenv_map");
            }
        }
        for (k, &x) in self.lam_var.iter() {
            if de(k.1) || dv(x) {
                bad("lam_var");
            }
        }
        for (_, &x) in self.var_slots.iter() {
            if dv(x) {
                bad("var_slots");
            }
        }
        for &v in self.shash_memo.keys() {
            if dv(v) {
                bad("shash_memo");
            }
        }
        for (k, &x) in self.canon_memo.iter() {
            if de(k.1) || dv(x) {
                bad("canon_memo");
            }
        }
        for &v in self.nm.of_val.keys() {
            if dv(v) {
                bad("names of values");
            }
        }
        for k in self.nm.of_term.keys() {
            if de(k.0 as u32) {
                bad("names of terms");
            }
        }
        for x in self.nm.infer.values() {
            if dv(x.0) {
                bad("inference by name");
            }
        }
    }
}

