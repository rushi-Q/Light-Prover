//! Inductive declarations, checked as Lean's `inductive.cpp` does:
//! parameters and universes of the types, nested occurrences eliminated
//! into auxiliary types, constructor types (parameters, universe of each
//! field, strict positivity, return type), then the computed facts (isRec,
//! isReflexive, numNested, K, large elimination) against what the file
//! says, and the recursors: each recursor type and each rule is compared
//! with the one Lean would generate.
//!
//! Nothing in the declaration record is trusted. The recursor type in the
//! file is walked as a value against the expected telescope, leaves compared
//! by definitional equality. A rule is compared by applying the file's
//! right-hand side to fresh variables (parameters, motives, minor premises,
//! fields) and checking the result against the expected minor premise
//! application; induction hypotheses are compared extensionally. Iota only
//! ever uses a rule fully applied, so this is the meaning that matters.
//!
//! Nested inductives: Lean replaces each occurrence `J Ds` (J an earlier
//! inductive type whose parameters Ds mention the block) by an auxiliary
//! type with copies of the constructors of J's mutual group, checks the
//! enlarged block, then turns the auxiliary types back into `J Ds` (their
//! recursors become `I.rec_1`, `I.rec_2`, ...). Here the auxiliary types are
//! never built: an auxiliary type *is* the triple (J, levels, Ds), its
//! constructors are J's at those parameters, and every check runs on the
//! enlarged block directly in that restored form.

use crate::env::*;
use crate::tc::*;

/// A type of the (enlarged) block.
#[derive(Clone)]
pub struct TInfo {
    /// The constant: the block's own type, or the nested J.
    row: u32,
    /// Its universe levels.
    llr: u32,
    /// Its parameter arguments: the block's parameters, or Ds.
    pargs: Vec<V>,
    nidx: u32,
    ctors: Vec<u32>,
    aux: bool,
}

pub struct Ind {
    types: Vec<TInfo>,
    /// Canonical names of the block's own types.
    canon: Vec<u32>,
    np: u32,
    params: Vec<V>,
    llr: u32,
    lvls: Vec<u32>,
    result: u32,
    unsafe_: bool,
    /// milestone 24s: canonical names of outParam, semiOutParam, optParam
    /// and autoParam (NONE when absent), for consume_type_annotations
    ann: [u32; 4],
}

/// Milestone 24s: a syntactic closure, compared structurally (binder names
/// and binder infos aside, as Lean's `Expr.eqv`): a term under an
/// environment of values and a level substitution, or a value read back as
/// the term it stands for (a variable as itself, a thunk as its term, a
/// neutral value as its head applied to its spine). Nothing is reduced.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Sx {
    T(u32, u32, u32),
    V(V),
}

/// Milestone 28: what the walks of one inductive block found, so that a
/// term shared many times in the block's types (MAIN is a DAG) is walked
/// once per environment: occurrence tests by (term, environment, depth) and
/// by value, the nested scan by (term, environment, levels, depth), and
/// the pairs found structurally equal. Ids are the block's (it runs in the
/// scratch arena); emptied at the start and end of every block.
pub struct IndMemo {
    occ: rustc_hash::FxHashMap<(u32, u32, u32), bool>,
    occv: rustc_hash::FxHashMap<u32, bool>,
    scan: rustc_hash::FxHashSet<(u32, u32, u32, u32)>,
    eq: rustc_hash::FxHashSet<(Sx, Sx)>,
    /// memoizing (after `LIMIT` walk steps in the block: small blocks
    /// walk less than the tables cost)
    on: bool,
    /// steps walked unmemoized; u32::MAX: memo disabled
    n: u32,
}
impl IndMemo {
    /// Milestone 37: bytes held (room included)
    pub fn held_bytes(&self) -> usize {
        self.occ.capacity() * 14 + self.occv.capacity() * 6 + self.scan.capacity() * 17
            + self.eq.capacity() * (std::mem::size_of::<(Sx, Sx)>() + 1)
    }
}
/// release-da memoizes from the first step, so the gates (small blocks)
/// run the memoized walks too
const IND_MEMO_AFTER: u32 = if cfg!(debug_assertions) { 0 } else { 4096 };
impl Default for IndMemo {
    fn default() -> Self {
        IndMemo { occ: Default::default(), occv: Default::default(), scan: Default::default(), eq: Default::default(), on: false, n: u32::MAX }
    }
}
impl IndMemo {
    #[inline(always)]
    fn use_memo(&mut self) -> bool {
        if !self.on && self.n < IND_MEMO_AFTER {
            self.n += 1;
            return false;
        }
        self.on = self.n != u32::MAX;
        self.on
    }
    fn clear(&mut self) {
        self.occ = Default::default();
        self.occv = Default::default();
        self.scan = Default::default();
        self.eq = Default::default();
    }
}


/// The head of a closure that is not an application.
enum Atom {
    Const(u32, smallvec::SmallVec<[u32; 8]>),
    FVar(u32),
    Sort(u32),
    Lit(u32),
    /// a lambda or Pi term, its environment and level substitution
    Bind(u32, u32, u32),
    Proj(u32, u32, Sx),
    Let(u32, u32, u32),
    None,
}

const MAX_AUX: usize = 4096;

/// What a rule is compared under: the recursor type's parameter, motive and
/// minor binders (domain and environment) and variables, the recursors.
struct RuleCtx<'a> {
    doms: &'a [(u32, u32)],
    motives: &'a [V],
    minors: &'a [V],
    rec_rows: &'a [u32],
    rec_llr: u32,
}

impl Worker {
    fn same_name(&self, a: u32, b: u32) -> bool {
        self.env.canon(a) == self.env.canon(b)
    }

    /// Does term `t` (under `env`, `depth` binders deep) mention one of the
    /// inductive types? Bound variables pointing into `env` look at the
    /// values there (the term as Lean would see it, instantiated).
    fn occ_term(&mut self, t: u32, env: u32, depth: u32, set: &[u32]) -> R<bool> {
        self.tick()?;
        let k = self.tk(t);
        if matches!(k, BVAR | CONST) || !self.ind_memo.use_memo() {
            return self.occ_term_go(t, env, depth, set, k);
        }
        // a term that reads nothing of `env` is the same test at any depth
        let key = if self.trng(t) <= depth { (t, u32::MAX, 0) } else { (t, env, depth) };
        if let Some(&b) = self.ind_memo.occ.get(&key) {
            // release-da: a hit is the walk's own answer
            #[cfg(debug_assertions)]
            assert_eq!(self.occ_term_go(t, env, depth, set, k)?, b, "occurrence memo: another answer for term {t}");
            return Ok(b);
        }
        let b = self.occ_term_go(t, env, depth, set, k)?;
        self.ind_memo.occ.insert(key, b);
        Ok(b)
    }

    fn occ_term_go(&mut self, t: u32, env: u32, depth: u32, set: &[u32], k: u8) -> R<bool> {
        Ok(match k {
            BVAR => {
                let i = self.tp(t);
                if i >= depth {
                    let v = self.env_get(env, i - depth)?;
                    self.occ_val(v, set)?
                } else {
                    false
                }
            }
            CONST => set.contains(&self.env.canon(self.ta(t))),
            APP => self.occ_term(self.ta(t), env, depth, set)? || self.occ_term(self.tb(t), env, depth, set)?,
            LET => {
                let b = self.let_body(t);
                self.occ_term(self.ta(t), env, depth, set)?
                    || self.occ_term(self.tb(t), env, depth, set)?
                    || self.occ_term(b, env, depth + 1, set)?
            }
            PROJ => self.occ_term(self.ta(t), env, depth, set)?,
            k if is_lam(k) || is_pi(k) => {
                self.occ_term(self.ta(t), env, depth, set)? || self.occ_term(self.tb(t), env, depth + 1, set)?
            }
            _ => false,
        })
    }

    fn occ_val(&mut self, v: V, set: &[u32]) -> R<bool> {
        if !self.ind_memo.use_memo() {
            return self.occ_val_go(v, set);
        }
        if let Some(&b) = self.ind_memo.occv.get(&v) {
            #[cfg(debug_assertions)]
            assert_eq!(self.occ_val_go(v, set)?, b, "occurrence memo: another answer for value {v}");
            return Ok(b);
        }
        let b = self.occ_val_go(v, set)?;
        self.ind_memo.occv.insert(v, b);
        Ok(b)
    }

    fn occ_val_go(&mut self, v: V, set: &[u32]) -> R<bool> {
        // milestone 42: stuck heads and spines recurse here without a term
        // step: the tick measures the stack
        self.tick()?;
        match self.val(v) {
            Val::Thunk { term, env, .. } | Val::Clo { term, env, .. } | Val::CloI { term, env, .. } => self.occ_term(term, env, 0, set),
            Val::Sort(_) | Val::Lit(_) => Ok(false),
            Val::Neu { head, spine } => {
                match head {
                    Head::Const(r, _) => {
                        if set.contains(&self.canon_of_row(r)) {
                            return Ok(true);
                        }
                    }
                    Head::Stuck(x) => {
                        if self.occ_val(x, set)? {
                            return Ok(true);
                        }
                    }
                    Head::FVar(_) => {}
                }
                for e in self.spine(spine) {
                    if e & 0x8000_0000 == 0 && self.occ_val(e, set)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    /// The free variable a value is, syntactically (following bound
    /// variables through environments, never evaluating).
    fn as_fvar(&self, mut v: V) -> Option<u32> {
        loop {
            match self.val(v) {
                Val::Neu { head: Head::FVar(i), spine: EMPTY } => return Some(i),
                Val::Thunk { term, env, .. } if self.tk(term) == BVAR => {
                    v = self.env_get(env, self.tp(term)).ok()?;
                }
                _ => return None,
            }
        }
    }

    /// `T pargs indices` with `T` a type of the enlarged block and no type
    /// of the block in the indices. Returns the type's index.
    fn valid_ind_app_val(&mut self, ind: &Ind, v: V) -> R<Option<usize>> {
        let Some((row, llr, spine)) = self.const_head(v) else { return Ok(None) };
        let Some(args) = self.app_args(spine) else { return Ok(None) };
        'types: for j in 0..ind.types.len() {
            let ti = &ind.types[j];
            if ti.row != row || args.len() != ti.pargs.len() + ti.nidx as usize {
                continue;
            }
            if self.ll_get(llr) != self.ll_get(ti.llr) {
                continue;
            }
            let ti = ti.clone();
            for i in 0..ti.pargs.len() {
                if ti.aux {
                    // milestone 24s: an auxiliary type is its parameters as
                    // terms (Lean compares the occurrences with `==`)
                    if !self.sx_eq(Sx::V(args[i]), Sx::V(ti.pargs[i]))? {
                        continue 'types;
                    }
                } else {
                    let p = self.as_fvar(ti.pargs[i]);
                    if p.is_none() || self.as_fvar(args[i]) != p {
                        continue 'types;
                    }
                }
            }
            for &a in &args[ti.pargs.len()..] {
                if self.occ_val(a, &ind.canon)? {
                    return Ok(None);
                }
            }
            return Ok(Some(j));
        }
        Ok(None)
    }

    /// Lean's `is_valid_ind_app` on a constructor's return type (a term):
    /// `t` under `depth` binders, params are binders 0..np.
    fn valid_ind_app_term(&mut self, ind: &Ind, t: u32, depth: u32, idx: usize, env: u32) -> R<bool> {
        let mut args = Vec::new();
        let mut f = t;
        while self.tk(f) == APP {
            args.push(self.tb(f));
            f = self.ta(f);
        }
        args.reverse();
        if self.tk(f) != CONST || self.env.canon(self.ta(f)) != ind.canon[idx] {
            return Ok(false);
        }
        if self.ll_get(f) != &ind.lvls[..] {
            return Ok(false);
        }
        if args.len() != ind.np as usize + ind.types[idx].nidx as usize {
            return Ok(false);
        }
        for i in 0..ind.np as usize {
            let a = args[i];
            if self.tk(a) != BVAR || self.tp(a) != depth - 1 - i as u32 {
                return Ok(false);
            }
        }
        for &a in &args[ind.np as usize..] {
            if self.occ_term(a, env, 0, &ind.canon)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn positivity(&mut self, ind: &Ind, t: V) -> R<()> {
        let t = self.whnf(t)?;
        if !self.occ_val(t, &ind.canon)? {
            return Ok(());
        }
        if self.is_pi_val(t) {
            let d = self.bind_dom(t)?;
            if self.occ_val(d, &ind.canon)? {
                return reject("non-positive occurrence of the inductive type in a constructor argument");
            }
            let x = self.fresh(d)?;
            let b = self.bind_body(t, x)?;
            return self.positivity(ind, b);
        }
        if self.valid_ind_app_val(ind, t)?.is_some() {
            return Ok(());
        }
        reject("invalid occurrence of the inductive type in a constructor argument")
    }

    /// Lean's `is_rec_argument`: the type's telescope ends in a valid
    /// inductive application. Returns its index, the fresh variables and the
    /// final application.
    fn rec_argument(&mut self, ind: &Ind, ty: V) -> R<Option<(usize, Vec<V>, V)>> {
        let mut t = self.whnf(ty)?;
        let mut xs = Vec::new();
        while self.is_pi_val(t) {
            let d = self.bind_dom(t)?;
            let x = self.fresh(d)?;
            xs.push(x);
            let b = self.bind_body(t, x)?;
            t = self.whnf(b)?;
        }
        Ok(self.valid_ind_app_val(ind, t)?.map(|j| (j, xs, t)))
    }

    /// Level substitution for a row of block type `j` (its own type or a
    /// constructor): identity for the block's own, J's levels for auxiliary.
    fn ls_for(&mut self, ind: &Ind, j: usize, row: u32) -> u32 {
        if ind.types[j].aux { self.mk_ls(row, ind.types[j].llr) } else { 0 }
    }

    /// The type of block type `row` (type `j`) with its parameter binders
    /// opened at type `j`'s parameter arguments, binders found after whnf
    /// (as the type was checked).
    fn open_params_val(&mut self, ind: &Ind, j: usize, row: u32) -> R<V> {
        let ls = self.ls_for(ind, j, row);
        let mut v = self.eval(self.env.consts[row as usize].ty, EMPTY, ls)?;
        for &p in &ind.types[j].pargs.clone() {
            let w = self.whnf(v)?;
            if !self.is_pi_val(w) {
                return reject("inductive: too few parameter binders");
            }
            v = self.bind_body(w, p)?;
        }
        Ok(v)
    }

    /// Opens the parameter binders of `row`'s type with type `j`'s
    /// parameter arguments. Returns (rest of the term, env, ls).
    fn open_params(&mut self, ind: &Ind, j: usize, row: u32) -> R<(u32, u32, u32)> {
        let ls = self.ls_for(ind, j, row);
        let mut t = self.env.consts[row as usize].ty;
        let mut e = EMPTY;
        for &p in &ind.types[j].pargs.clone() {
            if !is_pi(self.tk(t)) {
                return reject("inductive: too few parameter binders");
            }
            e = self.push_env(p, e);
            t = self.tb(t);
        }
        Ok((t, e, ls))
    }

    /// Finds nested occurrences in `t` (top-down, as Lean's `replace`),
    /// adding auxiliary types to the block.
    fn scan_nested(&mut self, ind: &mut Ind, t: u32, env: u32, ls: u32, depth: u32, dummy: V) -> R<()> {
        self.tick()?;
        // the same closure scanned again finds the same occurrences, whose
        // auxiliary types are there already (nested_found returns at an
        // equal one)
        if self.tk(t) != BVAR && self.ind_memo.use_memo() {
            let key = if self.trng(t) <= depth { (t, u32::MAX, ls, 0) } else { (t, env, ls, depth) };
            if !self.ind_memo.scan.insert(key) {
                // release-da: scanned again, it finds nothing new
                #[cfg(debug_assertions)]
                {
                    let n0 = ind.types.len();
                    self.scan_nested_go(ind, t, env, ls, depth, dummy)?;
                    assert_eq!(ind.types.len(), n0, "nested scan memo: a revisit finds a new occurrence");
                }
                return Ok(());
            }
        }
        self.scan_nested_go(ind, t, env, ls, depth, dummy)
    }

    fn scan_nested_go(&mut self, ind: &mut Ind, t: u32, env: u32, ls: u32, depth: u32, dummy: V) -> R<()> {
        let mut args = Vec::new();
        let mut f = t;
        while self.tk(f) == APP {
            args.push(self.tb(f));
            f = self.ta(f);
        }
        args.reverse();
        // X07 055 fix: a parameter of an auxiliary type applied to arguments (`t α` with t := Box in BaseFoo's
        // constructor): Lean instantiates the parameters first and sees the constant-headed `Box Foo3`
        if !args.is_empty() && self.tk(f) == BVAR && self.tp(f) >= depth {
            let mut v = self.env_get(env, self.tp(f) - depth)?;
            // (row, level list, head argument values) of the parameter's argument, if it is a constant application
            let mut head: Option<(u32, u32, Vec<V>)> = None;
            // Z04-9 fix: argument values of the spines peeled so far, outermost last. Lean substitutes the
            // parameters syntactically (instantiate_rev, no beta), so a parameter whose argument is itself a
            // parameter application (`g α` with g := `f β`, f := `Box2`) is the constant application
            // `Box2 β α`: a variable head is followed into its value, and the arguments peeled on the way
            // are appended after the head's own ones
            let mut acc: Vec<V> = Vec::new();
            loop {
                self.tick()?;
                match self.val(v) {
                    Val::Thunk { term, env: he, ls: hl } => {
                        let mut hargs = Vec::new();
                        let mut hf = term;
                        while self.tk(hf) == APP {
                            hargs.push(self.tb(hf));
                            hf = self.ta(hf);
                        }
                        hargs.reverse();
                        if self.tk(hf) == BVAR {
                            let mut hv = Vec::with_capacity(hargs.len() + acc.len());
                            for &a in &hargs {
                                hv.push(self.thunk(a, he, hl)?);
                            }
                            hv.extend_from_slice(&acc);
                            acc = hv;
                            v = self.env_get(he, self.tp(hf))?;
                            continue;
                        }
                        if self.tk(hf) == CONST {
                            let r = self.env.row(self.ta(hf));
                            if r != NONE {
                                let mut hv = Vec::with_capacity(hargs.len() + acc.len());
                                for &a in &hargs {
                                    hv.push(self.thunk(a, he, hl)?);
                                }
                                hv.extend_from_slice(&acc);
                                let l = self.lsub_ll(hf, hl);
                                head = Some((r, l, hv));
                            }
                        }
                    }
                    Val::Neu { head: Head::Const(r, l), spine } => {
                        if let Some(xs) = self.app_args(spine) {
                            let mut hv = xs.to_vec();
                            hv.extend_from_slice(&acc);
                            head = Some((r, l, hv));
                        }
                    }
                    _ => {}
                }
                break;
            }
            if let Some((jrow, jllr, hv)) = head {
                if self.visible(jrow) && !ind.canon.contains(&self.canon_of_row(jrow)) {
                    if let CKind::Induct { nparams: jnp, all: jall, .. } = &self.env.consts[jrow as usize].kind {
                        let jnp = *jnp as usize;
                        let jall = jall.clone();
                        let nh = hv.len().min(jnp);
                        let na = jnp - nh;
                        if args.len() >= na {
                            let mut nested = false;
                            for &x in &hv[..nh] {
                                if self.occ_val(x, &ind.canon)? {
                                    nested = true;
                                }
                            }
                            for &a in &args[..na] {
                                if self.occ_term(a, env, depth, &ind.canon)? {
                                    nested = true;
                                }
                            }
                            if nested {
                                for &a in &args[..na] {
                                    for d in 0..depth {
                                        if self.uses_var(a, d) {
                                            return reject(format!(
                                                "invalid nested inductive datatype '{}', nested inductive datatypes parameters cannot contain local variables",
                                                self.env.name_str(self.env.consts[jrow as usize].name)
                                            ));
                                        }
                                    }
                                }
                                let mut e = env;
                                for _ in 0..depth {
                                    e = self.push_env(dummy, e);
                                }
                                let mut ds: Vec<V> = hv[..nh].to_vec();
                                for &a in &args[..na] {
                                    ds.push(self.thunk(a, e, ls)?);
                                }
                                self.nested_found_vals(ind, ds, jllr, jrow, &jall)?;
                                // Y3-1 fix: the remaining arguments (indices) are NOT scanned. Lean's replace_if_nested
                                // replaces `I As is` by `auxI As is` and `replace` does not descend into its result, so
                                // nested occurrences inside the indices are not eliminated (the CONST branch below does
                                // the same); scanning them added auxiliary types Lean does not have
                                return Ok(());
                            }
                        }
                    }
                }
            }
        }
        if !args.is_empty() && self.tk(f) == CONST {
            let jrow = self.env.row(self.ta(f));
            if jrow != NONE && self.visible(jrow) && !ind.canon.contains(&self.canon_of_row(jrow)) {
                if let CKind::Induct { nparams: jnp, all: jall, .. } = &self.env.consts[jrow as usize].kind {
                    let jnp = *jnp as usize;
                    let jall = jall.clone();
                    if args.len() >= jnp {
                        let mut nested = false;
                        for &a in &args[..jnp] {
                            if self.occ_term(a, env, depth, &ind.canon)? {
                                nested = true;
                            }
                        }
                        if nested {
                            return self.nested_found(ind, f, &args[..jnp], env, ls, depth, dummy, jrow, &jall);
                        }
                    }
                }
            }
        }
        let k = self.tk(t);
        match k {
            // a parameter of an auxiliary type stands for its argument (Lean
            // scans the constructor types with the parameters put in): the
            // argument is scanned where the variable stands
            BVAR => {
                let i = self.tp(t);
                if i >= depth {
                    let v = self.env_get(env, i - depth)?;
                    if let Val::Thunk { term, env: e2, ls: l2 } = self.val(v) {
                        return self.scan_nested(ind, term, e2, l2, 0, dummy);
                    }
                    // X07 055(b) fix: Pi-typed arguments are closures (Val::Clo), not thunks; Lean's instantiated
                    // constructor type contains them literally and replace_all_nested looks inside
                    if let Val::Clo { term, env: e2, ls: l2 } = self.val(v) {
                        return self.scan_nested(ind, term, e2, l2, 0, dummy);
                    }
                }
                Ok(())
            }
            APP => {
                self.scan_nested(ind, self.ta(t), env, ls, depth, dummy)?;
                self.scan_nested(ind, self.tb(t), env, ls, depth, dummy)
            }
            LET => {
                let b = self.let_body(t);
                self.scan_nested(ind, self.ta(t), env, ls, depth, dummy)?;
                self.scan_nested(ind, self.tb(t), env, ls, depth, dummy)?;
                self.scan_nested(ind, b, env, ls, depth + 1, dummy)
            }
            PROJ => self.scan_nested(ind, self.ta(t), env, ls, depth, dummy),
            k if is_lam(k) || is_pi(k) => {
                self.scan_nested(ind, self.ta(t), env, ls, depth, dummy)?;
                self.scan_nested(ind, self.tb(t), env, ls, depth + 1, dummy)
            }
            _ => Ok(()),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn nested_found(
        &mut self,
        ind: &mut Ind,
        f: u32,
        pargs: &[u32],
        env: u32,
        ls: u32,
        depth: u32,
        dummy: V,
        jrow: u32,
        jall: &[u32],
    ) -> R<()> {
        for &a in pargs {
            for d in 0..depth {
                if self.uses_var(a, d) {
                    return reject(format!(
                        "invalid nested inductive datatype '{}', nested inductive datatypes parameters cannot contain local variables",
                        self.env.name_str(self.env.consts[jrow as usize].name)
                    ));
                }
            }
        }
        let mut e = env;
        for _ in 0..depth {
            e = self.push_env(dummy, e);
        }
        let mut ds = Vec::new();
        for &a in pargs {
            ds.push(self.thunk(a, e, ls)?);
        }
        let jllr = self.lsub_ll(f, ls);
        self.nested_found_vals(ind, ds, jllr, jrow, jall)
    }

    /// X07 055 fix: the part of nested_found after the parameter arguments are values
    fn nested_found_vals(&mut self, ind: &mut Ind, ds: Vec<V>, jllr: u32, jrow: u32, jall: &[u32]) -> R<()> {
        // an equal occurrence already has its auxiliary type
        for j in 0..ind.types.len() {
            let ti = &ind.types[j];
            if !ti.aux || ti.row != jrow || self.ll_get(ti.llr) != self.ll_get(jllr) {
                continue;
            }
            let ti = ti.clone();
            let mut same = true;
            // milestone 24s: equal as terms (Lean's replace_if_nested looks
            // the occurrence up with `==`), not definitionally
            for i in 0..ds.len() {
                if !self.sx_eq(Sx::V(ds[i]), Sx::V(ti.pargs[i]))? {
                    same = false;
                    break;
                }
            }
            if same {
                // Y3-1 fix (letE.nondep): Lean finds the earlier auxiliary type with Expr == (expr_eq_fn), which
                // compares a let's nondep flag; the packed format carries no nondep, so two occurrences that differ
                // only there look equal here and would share one auxiliary type where Lean has two. If the export has
                // any `"nondep":true` let (the official exporters write false) and the parameters contain a let: no
                // verdict (decline), never a merge Lean would not make
                if susz::pack::saw_nondep_let() && self.vals_have_let(&ds)? {
                    return decline(
                        "a nested occurrence equals an earlier one up to a let in its parameters (letE.nondep is not in the packed export; Lean's == compares it): not decided",
                    );
                }
                return Ok(());
            }
        }
        // the whole mutual group of J, in its order
        for &m in jall {
            let mrow = self.env.row(m);
            if mrow == NONE || !self.visible(mrow) {
                return reject("invalid nested inductive datatype, ill-formed declaration");
            }
            let CKind::Induct { nparams, nindices, ctors, .. } = &self.env.consts[mrow as usize].kind else {
                return reject("invalid nested inductive datatype, ill-formed declaration");
            };
            if *nparams as usize != ds.len() {
                return reject("invalid nested inductive datatype, ill-formed declaration");
            }
            let crows: Vec<u32> = ctors.iter().map(|&c| self.env.row(c)).collect();
            if crows.contains(&NONE) {
                return reject("invalid nested inductive datatype, ill-formed declaration");
            }
            ind.types.push(TInfo { row: mrow, llr: jllr, pargs: ds.clone(), nidx: *nindices, ctors: crows, aux: true });
            if ind.types.len() > MAX_AUX {
                return decline("too many auxiliary types for a nested inductive");
            }
        }
        Ok(())
    }

    /// Y3-1: whether any of the values (their terms, followed through the
    /// environments' values) contains a let node. Each (term, env) pair and
    /// each value is visited once.
    fn vals_have_let(&mut self, vs: &[V]) -> R<bool> {
        let mut seen_t: rustc_hash::FxHashSet<(u32, u32)> = Default::default();
        let mut seen_v: rustc_hash::FxHashSet<V> = Default::default();
        let mut todo_v: Vec<V> = vs.to_vec();
        let mut todo_t: Vec<(u32, u32, u32)> = Vec::new();
        loop {
            self.tick()?;
            if let Some((t, e, depth)) = todo_t.pop() {
                if !seen_t.insert((t, e)) {
                    continue;
                }
                match self.tk(t) {
                    LET => return Ok(true),
                    BVAR => {
                        let i = self.tp(t);
                        if i >= depth {
                            todo_v.push(self.env_get(e, i - depth)?);
                        }
                    }
                    APP => {
                        todo_t.push((self.ta(t), e, depth));
                        todo_t.push((self.tb(t), e, depth));
                    }
                    PROJ => todo_t.push((self.ta(t), e, depth)),
                    k if is_lam(k) || is_pi(k) => {
                        todo_t.push((self.ta(t), e, depth));
                        todo_t.push((self.tb(t), e, depth + 1));
                    }
                    _ => {}
                }
                continue;
            }
            let Some(v) = todo_v.pop() else { return Ok(false) };
            if !seen_v.insert(v) {
                continue;
            }
            match self.val(v) {
                Val::Thunk { term, env, .. } | Val::Clo { term, env, .. } | Val::CloI { term, env, .. } => todo_t.push((term, env, 0)),
                Val::Sort(_) | Val::Lit(_) => {}
                Val::Neu { head, spine } => {
                    if let Head::Stuck(x) = head {
                        todo_v.push(x);
                    }
                    for e in self.spine(spine) {
                        if e & 0x8000_0000 == 0 {
                            todo_v.push(e);
                        }
                    }
                }
            }
        }
    }

    /// K02: whether term `t` (MAIN) mentions a constant or a projection
    /// structure whose name has `_nested` as its first component (Lean's
    /// `is_prefix_of(_nested, n)`), anywhere (Lean's `find`). Shared
    /// subterms are visited once.
    fn uses_nested_prefix(&self, t: u32) -> bool {
        let env = self.env;
        let cn = &env.st.canon;
        let nested_name = |raw: u32| -> bool {
            if (raw as usize) >= env.st.name_canon.len() {
                return false;
            }
            let mut x = env.st.name_canon[raw as usize];
            if x == susz::canon::ANON {
                return false;
            }
            while (x as usize) < cn.pre.len() && cn.pre[x as usize] != susz::canon::ANON {
                x = cn.pre[x as usize];
            }
            matches!(cn.part(env.bytes, x), susz::canon::Part::Str(b) if b == b"_nested")
        };
        let mut seen: rustc_hash::FxHashSet<u32> = Default::default();
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            if t as usize >= env.main.len() || !seen.insert(t) {
                continue;
            }
            match self.tk(t) {
                CONST => {
                    if nested_name(self.ta(t)) {
                        return true;
                    }
                }
                PROJ => {
                    if nested_name(self.tp(t)) {
                        return true;
                    }
                    todo.push(self.ta(t));
                }
                APP => {
                    todo.push(self.ta(t));
                    todo.push(self.tb(t));
                }
                LET => {
                    todo.push(self.ta(t));
                    todo.push(self.tb(t));
                    todo.push(self.let_body(t));
                }
                k if is_lam(k) || is_pi(k) => {
                    todo.push(self.ta(t));
                    todo.push(self.tb(t));
                }
                _ => {}
            }
        }
        false
    }

    /// K02: Lean 4.36's `check_uniform_ind_occs` on one constructor type
    /// `t` (MAIN): false when some occurrence of a type of the block
    /// (canonical names `inds`) with at most `np` arguments is not applied
    /// to exactly `np` arguments that are the variables of the outermost
    /// `np` binders, at the block's universe parameters (`lps`: their global
    /// level ids; None when one is not in the global table, so no level list
    /// of the file equals them). Over-applied occurrences are descended into
    /// (the parameter application is then a subterm). Visits each (term,
    /// binder depth) once.
    fn uniform_ind_occs(&self, t: u32, inds: &[u32], np: u32, lps: Option<&[u32]>) -> bool {
        let env = self.env;
        let mlen = env.main.len();
        let mut seen: rustc_hash::FxHashSet<(u32, u32)> = Default::default();
        let mut todo = vec![(t, 0u32)];
        let mut args: Vec<u32> = Vec::new();
        while let Some((t, off)) = todo.pop() {
            if t as usize >= mlen || !seen.insert((t, off)) {
                continue;
            }
            match self.tk(t) {
                APP | CONST => {
                    // the head and arguments (Lean's get_app_args)
                    args.clear();
                    let mut f = t;
                    while self.tk(f) == APP {
                        args.push(self.tb(f));
                        f = self.ta(f);
                    }
                    args.reverse();
                    let is_ind = self.tk(f) == CONST && {
                        let c = env.canon(self.ta(f));
                        inds.contains(&c)
                    };
                    if !is_ind || args.len() as u32 > np {
                        if self.tk(t) == APP {
                            todo.push((self.ta(t), off));
                            todo.push((self.tb(t), off));
                        }
                        continue;
                    }
                    // args.len() <= np: must be exactly the parameters
                    if args.len() as u32 != np || off < np {
                        return false;
                    }
                    let lo = self.tp(f) as usize;
                    let ls: &[u32] = if lo == 0 {
                        &[]
                    } else {
                        let n = env.side.lvls[lo] as usize;
                        &env.side.lvls[lo + 1..lo + 1 + n]
                    };
                    match lps {
                        Some(p) if p == ls => {}
                        _ => return false,
                    }
                    for (i, &a) in args.iter().enumerate() {
                        if self.tk(a) != BVAR || self.tp(a) != off - 1 - i as u32 {
                            return false;
                        }
                    }
                }
                LET => {
                    todo.push((self.ta(t), off));
                    todo.push((self.tb(t), off));
                    todo.push((self.let_body(t), off + 1));
                }
                PROJ => todo.push((self.ta(t), off)),
                k if is_lam(k) || is_pi(k) => {
                    todo.push((self.ta(t), off));
                    todo.push((self.tb(t), off + 1));
                }
                _ => {}
            }
        }
        true
    }

    pub fn check_inductive(&mut self, d: u32) -> R<()> {
        self.ind_memo.clear();
        self.ind_memo.on = false;
        self.ind_memo.n = 0;
        let r = self.check_inductive_in(d);
        self.ind_memo.clear();
        self.ind_memo.on = false;
        self.ind_memo.n = u32::MAX;
        r
    }

    fn check_inductive_in(&mut self, d: u32) -> R<()> {
        let env = self.env;
        let (first, n) = env.decl_rows[d as usize];
        let rows: Vec<u32> = (first..first + n).collect();
        let types: Vec<u32> = rows.iter().copied().filter(|&r| env.consts[r as usize].group == 0).collect();
        let ctors: Vec<u32> = rows.iter().copied().filter(|&r| env.consts[r as usize].group == 1).collect();
        let recs: Vec<u32> = rows.iter().copied().filter(|&r| env.consts[r as usize].group == 2).collect();
        if types.is_empty() {
            return reject("inductive declaration without types");
        }
        let t0 = &env.consts[types[0] as usize];
        let CKind::Induct { nparams: np, unsafe_, .. } = t0.kind else { unreachable!() };
        self.setup_decl(types[0], if unsafe_ { 1 } else { 0 });
        let lparams: Vec<u32> = t0.lparams.iter().map(|&x| env.canon(x)).collect();
        let canon: Vec<u32> = types.iter().map(|&r| self.canon_of_row(r)).collect();

        // ---- structural facts of the record
        let same_lp = |c: &ConstInfo| -> bool {
            c.lparams.len() == lparams.len() && c.lparams.iter().zip(lparams.iter()).all(|(&a, &b)| env.canon(a) == b)
        };
        let mut nidx = Vec::new();
        let mut ctor_order: Vec<u32> = Vec::new();
        let mut nnested_claim = Vec::new();
        for &r in &types {
            let c = &env.consts[r as usize];
            let CKind::Induct { nparams, nindices, all, ctors: cs, nnested, unsafe_: u2, .. } = &c.kind else {
                unreachable!()
            };
            nnested_claim.push(*nnested);
            if *nparams != np || *u2 != unsafe_ || !same_lp(c) {
                // F06 fix-068: Lean 4.36 replay builds the block from ONE type's record and never compares the others': decline
                return decline("types of a mutual block disagree on parameters, universes or safety (records not compared by Lean 4.36)");
            }
            if all.len() != canon.len() || all.iter().zip(canon.iter()).any(|(&a, &b)| env.canon(a) != b) {
                // F06 fix-068: the other types' `all` records are never compared by Lean 4.36 replay: decline
                return decline("inductive type: `all` list differs (records not compared by Lean 4.36)");
            }
            nidx.push(*nindices);
            for &cn in cs.iter() {
                let cr = env.row(cn);
                if cr == NONE || env.consts[cr as usize].decl != d || env.consts[cr as usize].group != 1 {
                    return reject("inductive type lists a constructor that is not in its declaration");
                }
                if ctor_order.contains(&cr) {
                    return reject("constructor listed twice");
                }
                ctor_order.push(cr);
            }
        }
        if ctor_order.len() != ctors.len() {
            return reject("constructor not listed by its inductive type");
        }
        let mut tinfos = Vec::new();
        for (ti, &r) in types.iter().enumerate() {
            let CKind::Induct { ctors: cs, .. } = &env.consts[r as usize].kind else { unreachable!() };
            let mut crows = Vec::new();
            for (ci, &cn) in cs.iter().enumerate() {
                let cr = env.row(cn);
                let c = &env.consts[cr as usize];
                let CKind::Ctor { induct, cidx, nparams, unsafe_: u2, .. } = c.kind else { unreachable!() };
                if env.canon(induct) != canon[ti] || cidx as usize != ci || nparams != np || u2 != unsafe_ || !same_lp(c) {
                    return reject("constructor facts (inductive, index, parameters, universes, safety) are wrong");
                }
                crows.push(cr);
            }
            tinfos.push(crows);
        }

        // ---- Lean 4.36's add_inductive starts with check_no_nested_aux on
        // every type and constructor type: no constant, and no projection's
        // structure, may have a name under the reserved prefix `_nested`
        // (where the kernel puts the auxiliary types of nested inductives).
        // K02 (K07's finding): gruszka accepted such blocks.
        for &r in types.iter().chain(ctor_order.iter()) {
            if self.uses_nested_prefix(env.consts[r as usize].ty) {
                return reject(format!(
                    "invalid declaration '{}', it uses the reserved prefix '_nested'",
                    env.name_str(env.consts[r as usize].name)
                ));
            }
        }

        // ---- Lean 4.36's check_uniform_ind_occs (add_inductive, before the
        // nested elimination): in every constructor type, every occurrence
        // of a type of the block that is not over-applied is applied to
        // exactly the parameters (the ctor's first binders, as variables)
        // and the block's universe parameters. K02 (K04's finding):
        // gruszka accepted `L (E (W.mk false))` inside a constructor.
        {
            let lps: Option<Vec<u32>> = lparams.iter().map(|&p| env.lvl_intern.get(&(4u8, p, 0u32)).copied()).collect();
            for &cr in &ctor_order {
                if !self.uniform_ind_occs(env.consts[cr as usize].ty, &canon, np, lps.as_deref()) {
                    return reject(format!(
                        "invalid occurrence of datatype being declared in '{}': it must be applied to the parameters and universe levels of the mutual declaration",
                        env.name_str(env.consts[cr as usize].name)
                    ));
                }
            }
        }

        // ---- the types
        let lvls: Vec<u32> = lparams.iter().map(|&p| self.lv.param(p)).collect();
        let llr = self.ll_intern(&lvls);
        let ann = [
            self.find_name(&["outParam"]),
            self.find_name(&["semiOutParam"]),
            self.find_name(&["optParam"]),
            self.find_name(&["autoParam"]),
        ];
        let mut ind = Ind { types: vec![], canon: canon.clone(), np, params: vec![], llr, lvls, result: 0, unsafe_, ann };
        let mut param_tys: Vec<V> = Vec::new();
        for (j, &r) in types.iter().enumerate() {
            let ty = env.consts[r as usize].ty;
            self.check_type(ty)?;
            // milestone 24s: Lean's elim_nested_inductive takes the first
            // type's parameters syntactically (get_params: a Pi binder each,
            // no whnf) before check_inductive_types walks the types with
            // whnf; `id (∀ α, Sort 1)` with one parameter is rejected there
            if j == 0 {
                let mut t = ty;
                for _ in 0..np {
                    if !is_pi(self.tk(t)) {
                        return reject("invalid inductive datatype declaration, incorrect number of parameters");
                    }
                    t = self.tb(t);
                }
            }
            // the binders are found after whnf, one at a time (Lean's
            // check_inductive_types, Pestka's walkType): a type such as
            // `Presieve X`, a definition of a Pi, has its indices there
            let mut v = self.eval(ty, EMPTY, 0)?;
            for i in 0..np as usize {
                let w = self.whnf(v)?;
                if !self.is_pi_val(w) {
                    return reject("number of parameters mismatch in inductive type");
                }
                let dv = self.bind_dom(w)?;
                if j == 0 {
                    let x = self.fresh(dv)?;
                    ind.params.push(x);
                    param_tys.push(dv);
                } else if !self.defeq(dv, param_tys[i])? {
                    return reject("parameters of all inductive types must match");
                }
                v = self.bind_body(w, ind.params[i])?;
            }
            let mut k = 0;
            let mut w = self.whnf(v)?;
            while self.is_pi_val(w) {
                let dv = self.bind_dom(w)?;
                let x = self.fresh(dv)?;
                let b = self.bind_body(w, x)?;
                w = self.whnf(b)?;
                k += 1;
            }
            if k != nidx[j] {
                // F06 fix-068: Lean 4.36 replay recomputes numIndices and never compares the record's: decline
                return decline("number of indices differs from the record (not compared by Lean 4.36)");
            }
            let l = self.sort_of(w, "inductive type result")?;
            if j == 0 {
                ind.result = l;
            } else if !self.lv.equiv(l, ind.result) {
                return reject("mutually inductive types must live in the same universe");
            }
        }
        for (j, &r) in types.iter().enumerate() {
            ind.types.push(TInfo {
                row: r,
                llr,
                pargs: ind.params.clone(),
                nidx: nidx[j],
                ctors: tinfos[j].clone(),
                aux: false,
            });
        }

        // ---- constructor types (the block's types visible now)
        self.self_vis = 1;
        for &cr in &ctor_order {
            self.check_type(env.consts[cr as usize].ty)?;
        }

        // ---- nested occurrences: auxiliary types, until none is new
        let dummy = self.mk(Val::Sort(crate::level::ZERO))?;
        let mut q = 0;
        while q < ind.types.len() {
            for c in ind.types[q].ctors.clone() {
                let (t, e, ls) = self.open_params(&ind, q, c)?;
                self.scan_nested(&mut ind, t, e, ls, 0, dummy)?;
            }
            q += 1;
        }
        let naux = (ind.types.len() - types.len()) as u32;
        if nnested_claim.iter().any(|&x| x != naux) {
            // F06 fix-068: Lean 4.36 replay recomputes numNested and never compares the record's: decline, not reject
            return decline("numNested differs from the nested occurrences (not compared by Lean 4.36)");
        }
        // auxiliary types live in the block's universe
        for j in types.len()..ind.types.len() {
            let row = ind.types[j].row;
            let mut v = self.open_params_val(&ind, j, row)?;
            for _ in 0..ind.types[j].nidx {
                let w = self.whnf(v)?;
                if !self.is_pi_val(w) {
                    return reject("nested occurrence: index binders");
                }
                let dv = self.bind_dom(w)?;
                let x = self.fresh(dv)?;
                v = self.bind_body(w, x)?;
            }
            let l = self.sort_of(v, "nested type result")?;
            if !self.lv.equiv(l, ind.result) {
                return reject("nested occurrence: the nested type must live in the block's universe");
            }
        }

        // ---- constructors of the enlarged block
        let mut is_rec = false;
        let mut is_reflexive = false;
        for ti in 0..ind.types.len() {
            let aux = ind.types[ti].aux;
            for c in ind.types[ti].ctors.clone() {
                let cname = env.consts[c as usize].name;
                let ls = self.ls_for(&ind, ti, c);
                let mut t = env.consts[c as usize].ty;
                let mut e = EMPTY;
                let mut i = 0u32;
                let npj = ind.types[ti].pargs.len() as u32;
                while is_pi(self.tk(t)) {
                    let dom = self.ta(t);
                    if (!aux || i >= npj) && self.occ_term(dom, e, 0, &canon)? {
                        // Lean's is_rec looks at every binder domain
                        is_rec = true;
                        // X07 058 fix: Lean decides reflexivity on the auxiliary constructor type with the
                        // parameters INSTANTIATED (elim_nested_inductive); a parameter BVAR stands for its argument
                        let mut d = dom;
                        let mut de = e;
                        let mut refl = is_pi(self.tk(d));
                        while !refl && self.tk(d) == BVAR {
                            let v = self.env_get(de, self.tp(d))?;
                            match self.val(v) {
                                Val::Thunk { term, env: e2, .. } => {
                                    d = term;
                                    de = e2;
                                    refl = is_pi(self.tk(d));
                                }
                                Val::Clo { term, .. } => {
                                    refl = is_pi(self.tk(term));
                                    break;
                                }
                                _ => break,
                            }
                        }
                        if refl {
                            is_reflexive = true;
                        }
                    }
                    let dv = self.thunk(dom, e, ls)?;
                    if i < npj {
                        if !aux && !self.defeq(dv, param_tys[i as usize])? {
                            return reject(format!(
                                "argument {} of constructor {} does not match the inductive type's parameters",
                                i + 1,
                                env.name_str(cname)
                            ));
                        }
                        e = self.push_env(ind.types[ti].pargs[i as usize], e);
                    } else {
                        let s = self.infer(dom, e, ls, !aux)?;
                        let sl = self.sort_of(s, "constructor field")?;
                        if !(self.lv.geq(ind.result, sl) || self.lv.zeroish(ind.result)) {
                            return reject(format!(
                                "universe level of field {} of {} is too big for the inductive type",
                                i + 1,
                                env.name_str(cname)
                            ));
                        }
                        if !unsafe_ {
                            self.positivity(&ind, dv)?;
                        }
                        let x = self.fresh(dv)?;
                        e = self.push_env(x, e);
                    }
                    t = self.tb(t);
                    i += 1;
                }
                if i < npj {
                    return reject("constructor has fewer binders than parameters");
                }
                if !aux {
                    if !self.valid_ind_app_term(&ind, t, i, ti, e)? {
                        return reject(format!("invalid return type for constructor {}", env.name_str(cname)));
                    }
                    let CKind::Ctor { nfields, .. } = env.consts[c as usize].kind else { unreachable!() };
                    if i - np != nfields {
                        return reject(format!("wrong number of fields for constructor {}", env.name_str(cname)));
                    }
                }
            }
        }
        for &r in &types {
            let CKind::Induct { is_rec: ir, is_reflexive: rf, .. } = env.consts[r as usize].kind else { unreachable!() };
            if ir != is_rec || rf != is_reflexive {
                // F06 fix-068: Lean 4.36 replay recomputes isRec / isReflexive and never compares the record's: decline
                return decline("isRec / isReflexive differ from the declaration (not compared by Lean 4.36)");
            }
        }

        // ---- recursors (types and constructors visible)
        self.self_vis = 2;
        self.check_recursors(&ind, types.len(), &param_tys, &recs)
    }

    fn elim_only_at_zero(&mut self, ind: &Ind) -> R<bool> {
        if self.lv.is_not_zero(ind.result) {
            return Ok(false);
        }
        if ind.types.len() > 1 {
            return Ok(true);
        }
        let ctors = ind.types[0].ctors.clone();
        if ctors.len() > 1 {
            return Ok(true);
        }
        if ctors.is_empty() {
            return Ok(false);
        }
        let cr = ctors[0];
        let mut t = self.env.consts[cr as usize].ty;
        let mut e = EMPTY;
        let mut i = 0u32;
        let mut to_check = Vec::new();
        while is_pi(self.tk(t)) {
            let dom = self.ta(t);
            let dv = self.thunk(dom, e, 0)?;
            if i >= ind.np {
                let s = self.infer(dom, e, 0, false)?;
                let l = self.sort_of(s, "field")?;
                if !self.lv.zeroish(l) {
                    to_check.push(i);
                }
            }
            let x = self.fresh(dv)?;
            e = self.push_env(x, e);
            t = self.tb(t);
            i += 1;
        }
        let depth = i;
        let mut args = Vec::new();
        let mut f = t;
        while self.tk(f) == APP {
            args.push(self.tb(f));
            f = self.ta(f);
        }
        for j in to_check {
            let found = args.iter().any(|&a| self.tk(a) == BVAR && self.tp(a) == depth - 1 - j);
            if !found {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn ind_app(&mut self, ind: &Ind, j: usize, idx: &[V]) -> R<V> {
        let c = self.mk_const(ind.types[j].row, ind.types[j].llr)?;
        let c = self.mk_app(c, &ind.types[j].pargs.clone())?;
        self.mk_app(c, idx)
    }

    /// Canonical name of the recursor of block type `j`: `I_j.rec` for the
    /// block's own, `I_0.rec_k` for the k-th auxiliary type.
    fn rec_name(&self, ind: &Ind, j: usize, nreal: usize) -> u32 {
        let (pre, s) = if j < nreal { (ind.canon[j], "rec".to_string()) } else { (ind.canon[0], format!("rec_{}", j - nreal + 1)) };
        self.env.st.canon.find(self.env.bytes, pre, susz::canon::Part::Str(s.as_bytes())).unwrap_or(NONE)
    }

    /// Milestone 24s: each recursor is compared with the one Lean's kernel
    /// generates (inductive.cpp mk_rec_infos, declare_recursors,
    /// mk_rec_rules), structurally: Lean's replay rejects a recursor that
    /// is not `==` to the generated one (Replay.checkPostponedRecursors), so
    /// a type or rule that is only definitionally equal is rejected too.
    /// The file's type is walked as a term (a Pi binder each, no whnf), and
    /// every binder domain and the result compared with the canonical part,
    /// built from the values the block's checks made (parameters and indices
    /// of the types after whnf, constructor fields as stated, binder
    /// domains with `consume_type_annotations`). Each rule must be the
    /// canonical right-hand side: lambdas over the parameters, motives and
    /// minor premises (domains those of the recursor type), and over the
    /// fields, then the minor premise applied to the fields and to one
    /// recursor application per recursive field.
    fn check_recursors(&mut self, ind: &Ind, nreal: usize, param_tys: &[V], recs: &[u32]) -> R<()> {
        let env = self.env;
        let nt = ind.types.len();
        if recs.len() != nt {
            return reject("expected one recursor per inductive type (auxiliary ones included)");
        }
        let elim_zero = self.elim_only_at_zero(ind)?;
        let all_ctors: Vec<(usize, u32)> =
            (0..nt).flat_map(|j| ind.types[j].ctors.iter().map(move |&c| (j, c)).collect::<Vec<_>>()).collect();
        let mut k_target = nt == 1 && self.lv.zeroish(ind.result);
        if k_target {
            let cs = &ind.types[0].ctors;
            k_target = cs.len() == 1 && matches!(env.consts[cs[0] as usize].kind, CKind::Ctor { nfields: 0, .. });
        }
        let nminors = all_ctors.len() as u32;
        // recursors by name, one per block type
        let mut rec_rows = Vec::new();
        for j in 0..nt {
            let want = self.rec_name(ind, j, nreal);
            match recs.iter().find(|&&r| self.canon_of_row(r) == want) {
                Some(&r) if want != NONE => rec_rows.push(r),
                _ => return reject("recursor names are not <type>.rec / <type>.rec_k"),
            }
        }
        let r0 = &env.consts[rec_rows[0] as usize];
        let lp: Vec<u32> = r0.lparams.iter().map(|&x| env.canon(x)).collect();
        let ilp: Vec<u32> = env.consts[ind.types[0].row as usize].lparams.iter().map(|&x| env.canon(x)).collect();
        let elim_level = if elim_zero {
            if lp != ilp {
                return reject("recursor universe parameters must be the inductive's");
            }
            crate::level::ZERO
        } else {
            if lp.len() != ilp.len() + 1 || lp[1..] != ilp[..] || ilp.contains(&lp[0]) {
                return reject("recursor universe parameters must be a fresh motive universe and the inductive's");
            }
            // milestone 24s: Lean names it `u`, or `u_1`, `u_2`, ... the
            // first that is not a parameter of the inductive type
            let mut i = 0u32;
            let want = loop {
                let s = if i == 0 { "u".to_string() } else { format!("u_{i}") };
                let c = self.find_name(&[s.as_str()]);
                if c == NONE || !ilp.contains(&c) {
                    break c;
                }
                i += 1;
            };
            if lp[0] != want {
                return reject("recursor motive universe is not named as Lean's kernel names it");
            }
            self.lv.param(lp[0])
        };
        let rec_lvls: Vec<u32> = lp.iter().map(|&p| self.lv.param(p)).collect();
        let rec_llr = self.ll_intern(&rec_lvls);
        for j in 0..nt {
            let rr = rec_rows[j];
            let c = &env.consts[rr as usize];
            let CKind::Rec { all, nparams, nindices, nmotives, nminors: nm, rules, k, unsafe_: u2 } = &c.kind else {
                unreachable!()
            };
            let clp: Vec<u32> = c.lparams.iter().map(|&x| env.canon(x)).collect();
            if clp != lp {
                return reject("recursors of a mutual block disagree on universe parameters");
            }
            if *nparams != ind.np
                || *nindices != ind.types[j].nidx
                || *nmotives != nt as u32
                || *nm != nminors
                || *k != k_target
                || *u2 != ind.unsafe_
            {
                return reject("recursor facts (params, indices, motives, minors, K, safety) are wrong");
            }
            if all.len() != nreal || all.iter().zip(ind.canon.iter()).any(|(&a, &b)| env.canon(a) != b) {
                return reject("recursor: wrong `all` list");
            }
            if self.trng(c.ty) != 0 {
                return reject("recursor type has loose bound variables");
            }
            self.set_lparams(lp.clone());
            // structurally equal to the generated type, the file's type is
            // well formed as that one is; release-da checks it anyway
            if cfg!(debug_assertions) {
                self.check_type(c.ty)?;
            }
            // ---- the type, as a telescope of Pi terms
            let mut a = c.ty;
            let mut ea = EMPTY;
            // (domain, environment) of the parameter, motive and minor binders
            let mut doms: Vec<(u32, u32)> = Vec::new();
            for i in 0..ind.np as usize {
                a = self.rec_pi(a, "parameter")?;
                let want = self.sx_consume(ind, Sx::V(param_tys[i]))?;
                if !self.sx_eq(Sx::T(self.ta(a), ea, 0), want)? {
                    return reject("recursor type: parameter mismatch");
                }
                doms.push((self.ta(a), ea));
                ea = self.push_env(ind.params[i], ea);
                a = self.tb(a);
            }
            let mut motives = Vec::new();
            for m in 0..nt {
                a = self.rec_pi(a, "motive")?;
                let md = self.ta(a);
                let r = self.rec_motive(ind, m, md, ea, elim_level);
                if m >= nreal && r == Err(Stop::Reject) {
                    // Z04-9 fix (F06 fix-068 extended from the count to the order): the motives of the auxiliary
                    // types follow the order in which Lean's elim_nested_inductive met the nested occurrences.
                    // gruszka re-implements that search; when its auxiliary list differs from the export's in
                    // order or shape (the count was already compared: numNested), its model, not the export, may
                    // be wrong. Lean 4.36 replay compares every recursor with the one its own kernel generates,
                    // so this is a decline (veto, never an accept), not a kernel verdict
                    let msg = stop_msg();
                    return decline(format!(
                        "auxiliary type {} of the nested block: {msg} (gruszka's nested-occurrence model differs from the export's order; not compared as a kernel verdict)",
                        m - nreal + 1
                    ));
                }
                r?;
                doms.push((md, ea));
                let mty = self.thunk(md, ea, 0)?;
                let cv = self.fresh(mty)?;
                motives.push(cv);
                ea = self.push_env(cv, ea);
                a = self.tb(a);
            }
            let mut minors = Vec::new();
            for &(cj, cr) in &all_ctors {
                a = self.rec_pi(a, "minor premise")?;
                let md = self.ta(a);
                self.s_minor(ind, cj, cr, md, ea, &motives)?;
                doms.push((md, ea));
                let mty = self.thunk(md, ea, 0)?;
                let mv = self.fresh(mty)?;
                minors.push(mv);
                ea = self.push_env(mv, ea);
                a = self.tb(a);
            }
            let (idx, rest, re) = self.s_indices(ind, j, a, ea)?;
            let p = self.rec_pi(rest, "major premise")?;
            let iapp = self.ind_app(ind, j, &idx)?;
            if !self.sx_eq(Sx::T(self.ta(p), re, 0), Sx::V(iapp))? {
                return reject("recursor type: major premise type mismatch");
            }
            let major = self.fresh(iapp)?;
            let re = self.push_env(major, re);
            let mut exp = self.mk_app(motives[j], &idx)?;
            exp = self.apply(exp, major)?;
            if !self.sx_eq(Sx::T(self.tb(p), re, 0), Sx::V(exp))? {
                return reject("recursor type: result mismatch");
            }

            // ---- the rules, for the constructors of type j
            let cs = ind.types[j].ctors.clone();
            if rules.len() != cs.len() {
                return reject("recursor: wrong number of rules");
            }
            self.self_vis = 3;
            let ctx = RuleCtx { doms: &doms, motives: &motives, minors: &minors, rec_rows: &rec_rows, rec_llr };
            for (ri, &(rctor, rnf, rhs)) in rules.iter().enumerate() {
                let cr = cs[ri];
                if !self.same_name(rctor, env.consts[cr as usize].name) {
                    return reject("recursor rule for the wrong constructor");
                }
                let CKind::Ctor { nfields, .. } = env.consts[cr as usize].kind else { unreachable!() };
                if rnf != nfields {
                    return reject("recursor rule: wrong number of fields");
                }
                if (rhs as usize) >= env.main.len() || self.trng(rhs) != 0 {
                    return reject("recursor rule has loose bound variables");
                }
                if let Some(n) = self.undeclared_const(rhs) {
                    return reject(format!("recursor rule names {} which is not declared", env.name_str(n)));
                }
                let mi = all_ctors.iter().position(|&x| x == (j, cr)).unwrap();
                self.s_rule(ind, j, cr, rhs, mi, &ctx)?;
            }
            self.self_vis = 2;
        }
        Ok(())
    }

    /// The motive binder domain `md` (in `ea`) of block type `m`: the index
    /// binders, the major premise `T pargs indices`, and the elimination
    /// universe as result.
    fn rec_motive(&mut self, ind: &Ind, m: usize, md: u32, ea: u32, elim_level: u32) -> R<()> {
        let (idx, rest, re) = self.s_indices(ind, m, md, ea)?;
        let q = self.rec_pi(rest, "motive major")?;
        let iapp = self.ind_app(ind, m, &idx)?;
        if !self.sx_eq(Sx::T(self.ta(q), re, 0), Sx::V(iapp))? {
            return reject("recursor type: motive major type mismatch");
        }
        let x = self.fresh(iapp)?;
        let re = self.push_env(x, re);
        let s = self.mk(Val::Sort(elim_level))?;
        if !self.sx_eq(Sx::T(self.tb(q), re, 0), Sx::V(s))? {
            return reject("recursor type: motive must return the elimination universe");
        }
        Ok(())
    }

    /// The Pi term `a` (the file's recursor type is never reduced).
    fn rec_pi(&self, a: u32, what: &str) -> R<u32> {
        if !is_pi(self.tk(a)) {
            return reject(format!("recursor type: {what} binder expected"));
        }
        Ok(a)
    }

    /// The index binders of block type `j` at the start of the file's term
    /// `t` (in `e`): each domain the canonical one (the type's index binders
    /// after whnf, as Lean's mk_rec_infos walks it). Returns the index
    /// variables and the rest of the term with its environment.
    fn s_indices(&mut self, ind: &Ind, j: usize, mut t: u32, mut e: u32) -> R<(Vec<V>, u32, u32)> {
        let row = ind.types[j].row;
        let mut v = self.open_params_val(ind, j, row)?;
        let mut xs = Vec::new();
        for _ in 0..ind.types[j].nidx {
            let tw = self.whnf(v)?;
            if !self.is_pi_val(tw) {
                return reject("inductive: index binders");
            }
            let de = self.bind_dom(tw)?;
            t = self.rec_pi(t, "index")?;
            let want = self.sx_consume(ind, Sx::V(de))?;
            if !self.sx_eq(Sx::T(self.ta(t), e, 0), want)? {
                return reject("recursor type: index type mismatch");
            }
            let x = self.fresh(de)?;
            xs.push(x);
            v = self.bind_body(tw, x)?;
            e = self.push_env(x, e);
            t = self.tb(t);
        }
        Ok((xs, t, e))
    }

    /// The fields of constructor `cr` of block type `j` against the binders
    /// of the file's term `t` (in `e`, Pi binders, or lambdas for a rule):
    /// each domain the field's, with type annotations consumed. Returns the
    /// fields, the recursive ones, the constructor's result (term, env,
    /// level substitution), and the rest of `t` with its environment.
    #[allow(clippy::type_complexity)]
    fn s_fields(
        &mut self,
        ind: &Ind,
        j: usize,
        cr: u32,
        mut t: u32,
        mut e: u32,
        lam: bool,
    ) -> R<(Vec<V>, Vec<V>, (u32, u32, u32), u32, u32)> {
        let (mut ct, mut ce, ls) = self.open_params(ind, j, cr)?;
        let mut fields = Vec::new();
        let mut recf = Vec::new();
        while is_pi(self.tk(ct)) {
            let k = self.tk(t);
            if (lam && !is_lam(k)) || (!lam && !is_pi(k)) {
                return reject(if lam { "recursor rule: field binder expected" } else { "recursor type: minor field binder expected" });
            }
            let want = self.sx_consume(ind, Sx::T(self.ta(ct), ce, ls))?;
            if !self.sx_eq(Sx::T(self.ta(t), e, 0), want)? {
                return reject(if lam { "recursor rule: field type mismatch" } else { "recursor type: minor premise field mismatch" });
            }
            // the variable's type is the consumed domain; Lean's
            // is_rec_argument looks at the domain as stated
            let dv = self.sx_value(want)?;
            let x = self.fresh(dv)?;
            let stated = self.thunk(self.ta(ct), ce, ls)?;
            if self.rec_argument(ind, stated)?.is_some() {
                recf.push(x);
            }
            fields.push(x);
            ce = self.push_env(x, ce);
            e = self.push_env(x, e);
            ct = self.tb(ct);
            t = self.tb(t);
        }
        Ok((fields, recf, (ct, ce, ls), t, e))
    }

    /// The minor premise of constructor `cr` of block type `j`: fields,
    /// induction hypotheses, then the motive applied to the constructor.
    fn s_minor(&mut self, ind: &Ind, j: usize, cr: u32, t: u32, e: u32, motives: &[V]) -> R<()> {
        let (fields, recf, (ct, ce, ls), mut t, mut e) = self.s_fields(ind, j, cr, t, e, false)?;
        let mut args = Vec::new();
        let mut f = ct;
        while self.tk(f) == APP {
            args.push(self.tb(f));
            f = self.ta(f);
        }
        args.reverse();
        let npj = ind.types[j].pargs.len();
        if args.len() < npj {
            return reject("constructor result");
        }
        let mut cidx = Vec::new();
        for &a in &args[npj..] {
            cidx.push(self.thunk(a, ce, ls)?);
        }
        // induction hypotheses: Π ys, motive_it uidx (u ys)
        for &u in &recf {
            t = self.rec_pi(t, "induction hypothesis")?;
            let (ys, it, uidx, ht, he) = self.s_ih_binders(ind, u, Sx::T(self.ta(t), e, 0), false)?;
            let mut exp = self.mk_app(motives[it], &uidx)?;
            let uapp = self.mk_app(u, &ys)?;
            exp = self.apply(exp, uapp)?;
            if !self.sx_eq(Sx::T(ht, he, 0), Sx::V(exp))? {
                return reject("recursor type: induction hypothesis mismatch");
            }
            let ihd = self.thunk(self.ta(t), e, 0)?;
            let ih = self.fresh(ihd)?;
            e = self.push_env(ih, e);
            t = self.tb(t);
        }
        let c = self.mk_const(cr, ind.types[j].llr)?;
        let c = self.mk_app(c, &ind.types[j].pargs.clone())?;
        let capp = self.mk_app(c, &fields)?;
        let mut exp = self.mk_app(motives[j], &cidx)?;
        exp = self.apply(exp, capp)?;
        if !self.sx_eq(Sx::T(t, e, 0), Sx::V(exp))? {
            return reject("recursor type: minor premise result mismatch");
        }
        Ok(())
    }

    /// The binders `ys` of an induction hypothesis for recursive field `u`
    /// (Pi binders in a minor premise, lambdas in a rule) at the start of
    /// `x`: the binders of u's type after whnf, domains consumed. Returns
    /// the variables, the block type `u` belongs to, its indices, and the
    /// rest of `x` as (term, env).
    #[allow(clippy::type_complexity)]
    fn s_ih_binders(&mut self, ind: &Ind, u: V, x: Sx, lam: bool) -> R<(Vec<V>, usize, Vec<V>, u32, u32)> {
        let uty = self.fv_type(u);
        let mut ut = self.whnf(uty)?;
        let mut ys = Vec::new();
        let Sx::T(mut t, mut e, 0) = self.sx_norm(x)? else {
            return reject("recursor: induction hypothesis shape");
        };
        while self.is_pi_val(ut) {
            let k = self.tk(t);
            if (lam && !is_lam(k)) || (!lam && !is_pi(k)) {
                return reject("recursor: induction hypothesis binder expected");
            }
            let ud = self.bind_dom(ut)?;
            let want = self.sx_consume(ind, Sx::V(ud))?;
            if !self.sx_eq(Sx::T(self.ta(t), e, 0), want)? {
                return reject("recursor: induction hypothesis argument mismatch");
            }
            let y = self.fresh(ud)?;
            ys.push(y);
            e = self.push_env(y, e);
            t = self.tb(t);
            let ub = self.bind_body(ut, y)?;
            ut = self.whnf(ub)?;
        }
        let Some(it) = self.valid_ind_app_val(ind, ut)? else { return reject("recursive field") };
        let (_, _, usp) = self.const_head(ut).unwrap();
        let uargs = self.app_args(usp).unwrap();
        let uidx: Vec<V> = uargs[ind.types[it].pargs.len()..].to_vec();
        Ok((ys, it, uidx, t, e))
    }

    /// Rule `rhs` for constructor `cr` (minor premise `mi`) of block type `j`.
    fn s_rule(&mut self, ind: &Ind, j: usize, cr: u32, rhs: u32, mi: usize, cx: &RuleCtx<'_>) -> R<()> {
        let np = ind.np as usize;
        let nmot = cx.motives.len();
        let mut r = rhs;
        let mut er = EMPTY;
        for (k, &(dt, de)) in cx.doms.iter().enumerate() {
            if !is_lam(self.tk(r)) {
                return reject("recursor rule: binder expected");
            }
            if !self.sx_eq(Sx::T(self.ta(r), er, 0), Sx::T(dt, de, 0))? {
                return reject("recursor rule: binder type differs from the recursor's");
            }
            let var = if k < np {
                ind.params[k]
            } else if k < np + nmot {
                cx.motives[k - np]
            } else {
                cx.minors[k - np - nmot]
            };
            er = self.push_env(var, er);
            r = self.tb(r);
        }
        let (fields, recf, _, r, er) = self.s_fields(ind, j, cr, r, er, true)?;
        let Some((h, args)) = self.sx_view(Sx::T(r, er, 0))? else {
            return reject("recursor rule does not apply the minor premise");
        };
        if !self.sx_eq(h, Sx::V(cx.minors[mi]))? {
            return reject("recursor rule applies the wrong minor premise");
        }
        if args.len() != fields.len() + recf.len() {
            return reject("recursor rule: wrong number of arguments to the minor premise");
        }
        for (i, &f) in fields.iter().enumerate() {
            if !self.sx_eq(args[i], Sx::V(f))? {
                return reject("recursor rule: field argument mismatch");
            }
        }
        for (k, &u) in recf.iter().enumerate() {
            let (ys, it, uidx, ht, he) = self.s_ih_binders(ind, u, args[fields.len() + k], true)?;
            let rc = self.mk_const(cx.rec_rows[it], cx.rec_llr)?;
            let mut exp = self.mk_app(rc, &ind.params.clone())?;
            exp = self.mk_app(exp, cx.motives)?;
            exp = self.mk_app(exp, cx.minors)?;
            exp = self.mk_app(exp, &uidx)?;
            let uapp = self.mk_app(u, &ys)?;
            exp = self.apply(exp, uapp)?;
            if !self.sx_eq(Sx::T(ht, he, 0), Sx::V(exp))? {
                return reject("recursor rule: induction hypothesis argument mismatch");
            }
        }
        Ok(())
    }

    pub fn fv_type(&self, v: V) -> V {
        match self.val(v) {
            Val::Neu { head: Head::FVar(i), .. } => self.fv_ty[i as usize],
            _ => v,
        }
    }

    /// A constant in term `t` that is unknown or not visible here.
    fn undeclared_const(&mut self, t: u32) -> Option<u32> {
        let mut seen = rustc_hash::FxHashSet::default();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.tk(t) {
                CONST => {
                    let r = self.env.row(self.ta(t));
                    if r == NONE || !self.visible(r) {
                        return Some(self.ta(t));
                    }
                }
                APP => {
                    stack.push(self.ta(t));
                    stack.push(self.tb(t));
                }
                LET => {
                    stack.push(self.ta(t));
                    stack.push(self.tb(t));
                    stack.push(self.let_body(t));
                }
                PROJ => stack.push(self.ta(t)),
                k if is_lam(k) || is_pi(k) => {
                    stack.push(self.ta(t));
                    stack.push(self.tb(t));
                }
                _ => {}
            }
        }
        None
    }

    // ---- milestone 24s: structural comparison of syntactic closures

    /// A variable read through its environment, a thunk as its term.
    fn sx_norm(&mut self, mut x: Sx) -> R<Sx> {
        loop {
            match x {
                Sx::T(t, e, _) if self.tk(t) == BVAR => x = Sx::V(self.env_get(e, self.tp(t))?),
                Sx::V(v) => match self.val(v) {
                    Val::Thunk { term, env, ls } => x = Sx::T(term, env, ls),
                    _ => return Ok(x),
                },
                _ => return Ok(x),
            }
        }
    }

    fn sx_value(&mut self, x: Sx) -> R<V> {
        match x {
            Sx::T(t, e, ls) => self.thunk(t, e, ls),
            Sx::V(v) => Ok(v),
        }
    }

    /// `x` (normalized) is an application.
    fn sx_is_app(&self, x: Sx) -> bool {
        match x {
            Sx::T(t, _, _) => self.tk(t) == APP,
            Sx::V(v) => matches!(self.val(v), Val::Neu { spine, .. } if spine != EMPTY),
        }
    }

    /// Head and arguments of `x`, its applications flattened through
    /// variables bound to applications. None: a spine with a projection.
    fn sx_view(&mut self, x: Sx) -> R<Option<(Sx, Vec<Sx>)>> {
        let mut args = Vec::new();
        let mut cur = self.sx_norm(x)?;
        loop {
            match cur {
                Sx::T(t, e, ls) if self.tk(t) == APP => {
                    args.push(Sx::T(self.tb(t), e, ls));
                    cur = self.sx_norm(Sx::T(self.ta(t), e, ls))?;
                }
                Sx::V(v) => {
                    if let Val::Neu { head, spine } = self.val(v) {
                        if spine != EMPTY {
                            let Some(sp) = self.app_args(spine) else { return Ok(None) };
                            for &a in sp.iter().rev() {
                                args.push(Sx::V(a));
                            }
                            cur = Sx::V(self.intern(Val::Neu { head, spine: EMPTY })?);
                        }
                    }
                    break;
                }
                _ => break,
            }
        }
        args.reverse();
        Ok(Some((cur, args)))
    }

    /// What a normalized closure that is not an application is.
    fn sx_atom(&mut self, x: Sx) -> Atom {
        match x {
            Sx::T(t, e, ls) => {
                let n = self.node(t);
                match n.kind {
                    CONST => {
                        let llr = self.lsub_ll(t, ls);
                        Atom::Const(self.env.canon(n.a), smallvec::SmallVec::from_slice(self.ll_get(llr)))
                    }
                    SORT => Atom::Sort(self.lsub(n.p, ls)),
                    NAT | STR => Atom::Lit(n.p),
                    PROJ => Atom::Proj(self.env.canon(n.p), n.b, Sx::T(n.a, e, ls)),
                    LET => Atom::Let(t, e, ls),
                    k if is_lam(k) || is_pi(k) => Atom::Bind(t, e, ls),
                    _ => Atom::None,
                }
            }
            Sx::V(v) => match self.val(v) {
                Val::Neu { head: Head::Const(r, l), spine: EMPTY } => {
                    Atom::Const(self.canon_of_row(r), smallvec::SmallVec::from_slice(self.ll_get(l)))
                }
                Val::Neu { head: Head::FVar(i), spine: EMPTY } => Atom::FVar(i),
                Val::Sort(l) => Atom::Sort(l),
                Val::Lit(i) => Atom::Lit(i),
                Val::Clo { term, env, ls } | Val::CloI { term, env, ls } => Atom::Bind(term, env, ls),
                _ => Atom::None,
            },
        }
    }

    fn sx_lit_eq(&self, i: u32, j: u32) -> bool {
        i == j
            || match (self.lit(i), self.lit(j)) {
                (LitVal::Nat(a), LitVal::Nat(b)) => a == b,
                (LitVal::Str(a), LitVal::Str(b)) => a == b,
                _ => false,
            }
    }

    /// Structural equality of `x` and `y`, binder names and infos aside.
    fn sx_eq(&mut self, x: Sx, y: Sx) -> R<bool> {
        if x == y {
            return Ok(true);
        }
        self.tick()?;
        let x = self.sx_norm(x)?;
        let y = self.sx_norm(y)?;
        if x == y {
            return Ok(true);
        }
        if !self.ind_memo.use_memo() {
            return self.sx_eq_go(x, y);
        }
        if self.ind_memo.eq.contains(&(x, y)) {
            #[cfg(debug_assertions)]
            assert!(self.sx_eq_go(x, y)?, "structural equality memo: a pair found equal is not");
            return Ok(true);
        }
        let b = self.sx_eq_go(x, y)?;
        if b {
            self.ind_memo.eq.insert((x, y));
        }
        Ok(b)
    }

    fn sx_eq_go(&mut self, x: Sx, y: Sx) -> R<bool> {
        if let (Sx::T(a, _, la), Sx::T(b, _, lb)) = (x, y) {
            if a == b && la == lb && self.trng(a) == 0 {
                return Ok(true);
            }
        }
        let (xa, ya) = (self.sx_is_app(x), self.sx_is_app(y));
        if xa || ya {
            if !(xa && ya) {
                return Ok(false);
            }
            let Some((hx, ax)) = self.sx_view(x)? else { return Ok(false) };
            let Some((hy, ay)) = self.sx_view(y)? else { return Ok(false) };
            if ax.len() != ay.len() || !self.sx_eq(hx, hy)? {
                return Ok(false);
            }
            for i in 0..ax.len() {
                if !self.sx_eq(ax[i], ay[i])? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        Ok(match (self.sx_atom(x), self.sx_atom(y)) {
            (Atom::Const(a, la), Atom::Const(b, lb)) => a == b && la == lb,
            (Atom::FVar(a), Atom::FVar(b)) => a == b,
            (Atom::Sort(a), Atom::Sort(b)) => a == b,
            (Atom::Lit(a), Atom::Lit(b)) => self.sx_lit_eq(a, b),
            (Atom::Proj(sa, ia, xa), Atom::Proj(sb, ib, xb)) => sa == sb && ia == ib && self.sx_eq(xa, xb)?,
            (Atom::Bind(ta, ea, la), Atom::Bind(tb, eb, lb)) => {
                if is_pi(self.tk(ta)) != is_pi(self.tk(tb)) {
                    return Ok(false);
                }
                if !self.sx_eq(Sx::T(self.ta(ta), ea, la), Sx::T(self.ta(tb), eb, lb))? {
                    return Ok(false);
                }
                let v = self.sx_var()?;
                let (ea2, eb2) = (self.push_env(v, ea), self.push_env(v, eb));
                self.sx_eq(Sx::T(self.tb(ta), ea2, la), Sx::T(self.tb(tb), eb2, lb))?
            }
            (Atom::Let(ta, ea, la), Atom::Let(tb, eb, lb)) => {
                if !self.sx_eq(Sx::T(self.ta(ta), ea, la), Sx::T(self.ta(tb), eb, lb))?
                    || !self.sx_eq(Sx::T(self.tb(ta), ea, la), Sx::T(self.tb(tb), eb, lb))?
                {
                    return Ok(false);
                }
                let v = self.sx_var()?;
                let (ea2, eb2) = (self.push_env(v, ea), self.push_env(v, eb));
                let (ba, bb) = (self.let_body(ta), self.let_body(tb));
                self.sx_eq(Sx::T(ba, ea2, la), Sx::T(bb, eb2, lb))?
            }
            _ => false,
        })
    }

    /// A variable for a binder entered on both sides of a comparison.
    fn sx_var(&mut self) -> R<V> {
        let d = self.mk(Val::Sort(crate::level::ZERO))?;
        self.fresh(d)
    }

    /// Lean's `consume_type_annotations`: `outParam α`, `semiOutParam α`,
    /// `optParam α d`, `autoParam α t` are `α` (by the constant's name).
    fn sx_consume(&mut self, ind: &Ind, mut x: Sx) -> R<Sx> {
        loop {
            let n = self.sx_norm(x)?;
            if !self.sx_is_app(n) {
                return Ok(n);
            }
            let Some((h, args)) = self.sx_view(n)? else { return Ok(n) };
            let Atom::Const(c, _) = self.sx_atom(h) else { return Ok(n) };
            if args.len() == 1 && (c == ind.ann[0] || c == ind.ann[1]) {
                x = args[0];
            } else if args.len() == 2 && (c == ind.ann[2] || c == ind.ann[3]) {
                x = args[0];
            } else {
                return Ok(n);
            }
        }
    }
}
