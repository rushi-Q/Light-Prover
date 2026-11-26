//! Proposal 2 (milestone 5): term names on demand in heavy declarations.
//!
//! The name of a value is the substituted term it stands for, unreduced,
//! as an id in a per-declaration hash-consed table of name nodes (exact:
//! equal ids are equal terms, never a hash taken as identity). Bound
//! variables of the term's own binders are de Bruijn indices; a variable
//! bound by the environment is its entry's name; free variables are their
//! ids; constants carry their instantiated level lists, sorts their
//! instantiated levels. Closed MAIN terms are leaves (term, level
//! substitution); `infer` closures are opaque leaves (the value id).
//! Two values with one name stand for one term, so a result found for one
//! (whnf, whnf_core, an unfolding, a type, an equality) holds for the
//! other. Names are only computed after a per-value memo miss, and only
//! once the declaration is past a work threshold; a name that would take
//! more than a node budget is not made (the plain path runs).
use super::*;

/// names kept across declarations up to this many nodes
const PNAMES_CAP: usize = 1 << 21;
const T_BV: u8 = 0;
const T_CONST: u8 = 1;
const T_SORT: u8 = 2;
const T_APP: u8 = 3;
const T_LAM: u8 = 4;
const T_PI: u8 = 5;
const T_LET: u8 = 6;
const T_LETTV: u8 = 7;
const T_PROJ: u8 = 8;
const T_PJ: u8 = 9;
const T_LIT: u8 = 10;
const T_NAT: u8 = 11;
const T_MAIN: u8 = 12;
const T_FV: u8 = 13;
const T_VAL: u8 = 14;

#[derive(Default)]
pub struct Names {
    nodes: FxHashMap<(u8, u32, u32), u32>,
    /// value -> name (NONE: over budget or past half the stack once; not
    /// retried, milestone 45)
    pub(super) of_val: FxHashMap<V, u32>,
    /// (term, env, ls, depth) -> name
    pub(super) of_term: FxHashMap<(u64, u64), u32>,
    pub whnf: FxHashMap<u32, V>,
    pub core: FxHashMap<u64, V>,
    pub unfold: FxHashMap<u32, V>,
    /// name key -> (type, ticks the inference took)
    pub infer: FxHashMap<u64, (V, u32)>,
    /// milestone 31: the inference site's cost model in this declaration:
    /// calls, name nodes walked, ticks the hits saved
    pub icalls: u64,
    /// milestone 32: ticks into the declaration when the site went off
    /// (0: on); it is tried again on a fresh sample at twice that
    pub ioff: u32,
    pub ispent: u64,
    pub isaved: u64,
    pub eq: FxHashMap<u64, bool>,
    pub fuel: u32,
    pub hits: [u64; 6],
    pub nones: u64,
    pub calls: u64,
    pub made: u64,
    pub term_flushes: u64,
    /// milestone 8: per node, 1 when it holds a free variable or an opaque
    /// value leaf (meaningful in its declaration only)
    flags: Vec<u8>,
    /// closed name pair -> (declaration << 1 | outcome), kept across
    /// declarations with the node table
    pub peq: FxHashMap<u64, u64>,
    /// head pairs of the kept pairs (see `Worker::head_pair`)
    pub peq_heads: FxHashSet<u64>,
    /// literals that are not small Nats, by content
    plits_n: FxHashMap<BigUint, u32>,
    plits_s: FxHashMap<Box<str>, u32>,
    pub phits: u64,
    pub pstored: u64,
    pub pflushes: u64,
    /// names were made in this declaration (its tables need a reset)
    pub dirty: bool,
}

impl Names {
    /// Milestone 37: bytes held by the tables (room included)
    pub fn held_bytes(&self) -> usize {
        fn h<K, W>(m: &FxHashMap<K, W>) -> usize {
            m.capacity() * (std::mem::size_of::<(K, W)>() + 1)
        }
        h(&self.nodes) + h(&self.of_val) + h(&self.of_term) + h(&self.whnf) + h(&self.core) + h(&self.unfold)
            + h(&self.infer) + h(&self.eq) + self.flags.capacity() + h(&self.peq)
            + self.peq_heads.capacity() * 9 + h(&self.plits_n) + h(&self.plits_s)
            + self.plits_n.keys().map(|n| (n.bits() / 8) as usize).sum::<usize>()
    }
    /// Empties the tables for the next declaration. Their room is kept (a
    /// heavy declaration tends to follow another) up to `KEEP` entries each.
    pub fn reset(&mut self) {
        const KEEP: usize = 1 << 18;
        fn clr<K, W>(m: &mut FxHashMap<K, W>) {
            // a few names made in a light declaration must not cost a sweep
            // of the room a heavy one left
            if m.capacity() > 2 * KEEP || (m.capacity() > 1024 && m.len() < m.capacity() / 16) {
                *m = FxHashMap::default();
            } else {
                m.clear();
            }
        }
        if self.nodes.len() > super::capped(PNAMES_CAP) {
            self.flush_persistent();
        }
        clr(&mut self.of_val);
        clr(&mut self.of_term);
        clr(&mut self.whnf);
        clr(&mut self.core);
        clr(&mut self.unfold);
        clr(&mut self.infer);
        clr(&mut self.eq);
        self.dirty = false;
        self.icalls = 0;
        self.ioff = 0;
        self.ispent = 0;
        self.isaved = 0;
        self.fuel = 0;
        self.hits = [0; 6];
        self.nones = 0;
        self.calls = 0;
        self.made = 0;
        self.term_flushes = 0;
    }
    /// Empties the node table and every fact keyed by its nodes.
    pub fn flush_persistent(&mut self) {
        if self.nodes.is_empty() && self.peq.is_empty() && self.peq_heads.is_empty() {
            return;
        }
        self.nodes = FxHashMap::default();
        self.flags = Vec::new();
        self.peq = FxHashMap::default();
        self.peq_heads = FxHashSet::default();
        self.plits_n = FxHashMap::default();
        self.plits_s = FxHashMap::default();
        self.pflushes += 1;
    }
    /// Does the name mean the same term in every declaration (no free
    /// variable, no opaque value leaf)?
    pub fn closed(&self, n: u32) -> bool {
        self.flags[n as usize] == 0
    }
}

impl Worker {
    /// Is proposal 2 on for this point of the declaration?
    #[inline(always)]
    pub(super) fn p2(&mut self) -> bool {
        if self.p2_on {
            return true;
        }
        if (self.vals.len() as u64).saturating_sub(self.p2_vals0) >= P2_VALUES || self.stats.unfolds - self.p2_unfolds0 >= P2_UNFOLDS {
            self.p2_on = true;
        }
        self.p2_on
    }

    fn nm_node(&mut self, tag: u8, a: u32, b: u32) -> u32 {
        let n = self.nm.nodes.len() as u32;
        let r = *self.nm.nodes.entry((tag, a, b)).or_insert(n);
        if r == n {
            let f = match tag {
                T_FV | T_VAL => 1,
                T_APP | T_PROJ | T_LET | T_LETTV | T_LAM | T_PI => self.nm.flags[a as usize] | self.nm.flags[b as usize],
                _ => 0,
            };
            self.nm.flags.push(f);
        }
        r
    }

    /// The name of value `v`, or None over the node budget.
    pub(super) fn name_v(&mut self, v: V) -> Option<u32> {
        self.nm.dirty = true;
        self.nm.fuel = 1 << 16;
        self.nm.calls += 1;
        let r = self.nv(v);
        if r != NONE {
            Some(r)
        } else {
            self.nm.nones += 1;
            None
        }
    }
    /// `name_t` within `fuel` name nodes.
    pub(super) fn name_t_f(&mut self, t: u32, env: u32, ls: u32, fuel: u32) -> Option<u32> {
        self.nm.dirty = true;
        self.nm.fuel = fuel;
        self.nm.calls += 1;
        let r = self.nt(t, env, ls, 0);
        if r != NONE {
            Some(r)
        } else {
            self.nm.nones += 1;
            None
        }
    }

    fn nv(&mut self, v: V) -> u32 {
        if let Some(&n) = self.nm.of_val.get(&v) {
            return n;
        }
        // milestone 42: one frame per level; past half the stack no name
        // (the plain path runs), as over the node budget
        if self.nm.fuel == 0 || self.stack_half() {
            return NONE;
        }
        self.nm.fuel -= 1;
        let n = match self.val(v) {
            Val::Thunk { term, env, ls } => self.nt(term, env, ls, 0),
            Val::Clo { term, env, ls } => self.nt(term, env, ls, 0),
            // milestone 36: with the rollback epoch (a value id is reused
            // after a region's rollback)
            Val::CloI { .. } => self.nm_node(T_VAL, v, self.reg_epoch),
            Val::Sort(l) => self.nm_node(T_SORT, l, 0),
            Val::Lit(i) => self.nm_lit(i),
            Val::Neu { head, spine } => {
                let mut h = match head {
                    Head::Const(r, l) => {
                        let c = self.canon_of_row(r);
                        self.nm_node(T_CONST, c, l)
                    }
                    Head::FVar(i) => self.nm_node(T_FV, i, 0),
                    Head::Stuck(x) => self.nv(x),
                };
                if h != NONE {
                    let elims: SmallVec16 = SmallVec16::from_slice(self.sp.args(spine));
                    for &e in elims.iter() {
                        if e & PROJ_BIT != 0 {
                            let (sname, idx) = self.projs[(e & !PROJ_BIT) as usize];
                            let pj = self.nm_node(T_PJ, sname, idx);
                            h = self.nm_node(T_PROJ, pj, h);
                        } else {
                            let a = self.nv(e);
                            if a == NONE {
                                h = NONE;
                                break;
                            }
                            h = self.nm_node(T_APP, h, a);
                        }
                    }
                }
                h
            }
        };
        if n != NONE {
            self.nm.of_val.insert(v, n);
            self.ulog(Undo::NmOfVal(v));
            self.nm.made += 1;
        } else {
            // milestone 45: over the budget or past half the stack (the
            // only ways to no name): not walked again. A list literal of
            // 913 K elements (CFSG's RG.chars) was walked to the budget or
            // the stack once per element compared. A value walked again
            // from a shallower stack might have had a name: only sharing
            // is lost, as over the budget
            self.nm.of_val.insert(v, NONE);
            self.ulog(Undo::NmOfVal(v));
        }
        n
    }

    fn nm_lit(&mut self, i: u32) -> u32 {
        match self.lit(i) {
            LitVal::Nat(n) => match n.to_u64() {
                Some(k) => self.nm_node(T_NAT, k as u32, (k >> 32) as u32),
                None => {
                    // by content: a literal index means something else in
                    // another declaration's block
                    let n = n.clone();
                    let c = self.nm.plits_n.len() + self.nm.plits_s.len();
                    let id = *self.nm.plits_n.entry(n).or_insert(c as u32);
                    self.nm_node(T_LIT, id, 0)
                }
            },
            LitVal::Str(s) => {
                let s = s.clone();
                let c = self.nm.plits_n.len() + self.nm.plits_s.len();
                let id = *self.nm.plits_s.entry(s).or_insert(c as u32);
                self.nm_node(T_LIT, id, 0)
            }
        }
    }

    fn nt(&mut self, t: u32, env: u32, ls: u32, depth: u32) -> u32 {
        let r = self.trng(t);
        if r == 0 && t < self.m {
            return self.nm_node(T_MAIN, t, ls);
        }
        // a term with no variable bound by the environment: its name does
        // not depend on the environment or on the depth (all its variables
        // are its own binders' de Bruijn indices)
        let (env, depth) = if r <= depth { (EMPTY, 1 << 30) } else { (env, depth) };
        let key = (((t as u64) << 32) | env as u64, ((ls as u64) << 32) | depth as u64);
        if let Some(&n) = self.nm.of_term.get(&key) {
            return n;
        }
        if self.nm.fuel == 0 || self.stack_half() {
            return NONE;
        }
        self.nm.fuel -= 1;
        let n = match self.tk(t) {
            BVAR => {
                let i = self.tp(t);
                if i < depth {
                    self.nm_node(T_BV, i, 0)
                } else {
                    match self.env_get(env, i - depth) {
                        Ok(x) => self.nv(x),
                        Err(_) => NONE,
                    }
                }
            }
            CONST => {
                let c = self.env.canon(self.ta(t));
                let l = self.const_ll(t, ls);
                self.nm_node(T_CONST, c, l)
            }
            SORT => {
                let l = self.lsub(self.tp(t), ls);
                self.nm_node(T_SORT, l, 0)
            }
            NAT | STR => self.nm_lit(self.tp(t)),
            APP => {
                let f = self.nt(self.ta(t), env, ls, depth);
                let a = if f == NONE { NONE } else { self.nt(self.tb(t), env, ls, depth) };
                if a == NONE { NONE } else { self.nm_node(T_APP, f, a) }
            }
            PROJ => {
                let s = self.nt(self.ta(t), env, ls, depth);
                if s == NONE {
                    NONE
                } else {
                    let pj = self.nm_node(T_PJ, self.tp(t), self.tb(t));
                    self.nm_node(T_PROJ, pj, s)
                }
            }
            LET => {
                let a = self.nt(self.ta(t), env, ls, depth);
                let b = if a == NONE { NONE } else { self.nt(self.tb(t), env, ls, depth) };
                let c = if b == NONE { NONE } else { self.nt(self.let_body(t), env, ls, depth + 1) };
                if c == NONE {
                    NONE
                } else {
                    let tv = self.nm_node(T_LETTV, a, b);
                    self.nm_node(T_LET, tv, c)
                }
            }
            k => {
                let a = self.nt(self.ta(t), env, ls, depth);
                let b = if a == NONE { NONE } else { self.nt(self.tb(t), env, ls, depth + 1) };
                if b == NONE { NONE } else { self.nm_node(if is_lam(k) { T_LAM } else { T_PI }, a, b) }
            }
        };
        if n != NONE {
            // the memo is a cache over names that stay: emptied when full
            if self.nm.of_term.len() >= (1 << 19) {
                self.nm.of_term.clear();
                self.nm.term_flushes += 1;
            }
            self.nm.of_term.insert(key, n);
            self.ulog(Undo::NmOfTerm(key));
        }
        n
    }
}
