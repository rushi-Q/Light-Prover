use super::FxHashMap;
use super::arena::Arena;
use super::expr::{Expr, LetData, Meta, mk};
use super::intern::{Dag, Store};
use super::level::{IMAX_HASH, Level, MAX_HASH, PARAM_HASH, SUCC_HASH};
use super::name::{Name, STR_HASH as NAME_STR_HASH};
use super::ptr::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use crate::hash64;
use num_bigint::BigUint;

pub struct Ctx<'t, 'a: 't> {
    pub store: &'a Store<'a>,
    pub arena: &'t Arena,
    pub dag: Dag<'t>,
    pub(crate) memo: FxHashMap<(ExprPtr<'t>, u64), (u32, ExprPtr<'t>)>,
    pub(crate) generation: u32,
    pub(crate) inst_cache: FxHashMap<(ExprPtr<'t>, ExprPtr<'t>), ExprPtr<'t>>,
    pub(crate) subst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) simp_cache: FxHashMap<LevelPtr<'t>, LevelPtr<'t>>,
    /// Set by a lift whose variable index would exceed the binder limit.
    pub(crate) overflow: bool,
}

impl<'t, 'a: 't> Ctx<'t, 'a> {
    pub fn new(store: &'a Store<'a>, arena: &'t Arena) -> Self {
        Self {
            store,
            arena,
            dag: Dag::default(),
            memo: FxHashMap::default(),
            generation: 0,
            inst_cache: FxHashMap::default(),
            subst_cache: FxHashMap::default(),
            simp_cache: FxHashMap::default(),
            overflow: false,
        }
    }

    pub fn anon(&self) -> NamePtr<'t> {
        self.store.anon
    }

    pub fn zero(&self) -> LevelPtr<'t> {
        self.store.zero
    }

    pub fn name(&mut self, n: Name<'t>) -> NamePtr<'t> {
        if let Some(p) = self.store.dag.find_name(&n) {
            return p;
        }
        self.dag.intern_name(self.arena, n)
    }

    pub fn str_name(&mut self, pfx: NamePtr<'t>, s: StringPtr<'t>) -> NamePtr<'t> {
        self.name(Name::Str(pfx, s, hash64!(NAME_STR_HASH, pfx, s)))
    }

    pub fn string(&mut self, s: &str) -> StringPtr<'t> {
        if let Some(p) = self.store.dag.find_str(s) {
            return p;
        }
        self.dag.intern_str(self.arena, s)
    }

    pub fn str1(&mut self, s: &str) -> NamePtr<'t> {
        let s = self.string(s);
        let anon = self.anon();
        self.str_name(anon, s)
    }

    pub fn level(&mut self, l: Level<'t>) -> LevelPtr<'t> {
        if let Some(p) = self.store.dag.find_level(&l) {
            return p;
        }
        self.dag.intern_level(self.arena, l)
    }

    pub fn succ(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        self.level(Level::Succ(l, hash64!(SUCC_HASH, l)))
    }

    /// Lean 4.36 `mk_max` (level.cpp), so levels built by substitution and inference have exactly
    /// the shapes the 4.36 kernel gives them: its level comparison is not complete, so the shapes
    /// decide what it accepts (K07: 4.36 conformance).
    pub fn max(&mut self, l1: LevelPtr<'t>, l2: LevelPtr<'t>) -> LevelPtr<'t> {
        if let (Some(a), Some(b)) = (explicit_depth(l1), explicit_depth(l2)) {
            return if a >= b { l1 } else { l2 };
        }
        if l1 == l2 {
            return l1;
        }
        if matches!(*l1, Level::Zero) {
            return l2;
        }
        if matches!(*l2, Level::Zero) {
            return l1;
        }
        if let Level::Max(a, b, _) = *l2
            && (a == l1 || b == l1)
        {
            return l2;
        }
        if let Level::Max(a, b, _) = *l1
            && (a == l2 || b == l2)
        {
            return l1;
        }
        let (b1, k1) = to_offset(l1);
        let (b2, k2) = to_offset(l2);
        if b1 == b2 {
            return if k1 > k2 { l1 } else { l2 };
        }
        self.level(Level::Max(l1, l2, hash64!(MAX_HASH, l1, l2)))
    }

    /// Lean 4.36 `mk_imax`.
    pub fn imax(&mut self, l1: LevelPtr<'t>, l2: LevelPtr<'t>) -> LevelPtr<'t> {
        if is_not_zero(l2) {
            return self.max(l1, l2);
        }
        if matches!(*l2, Level::Zero) {
            return l2;
        }
        if matches!(*l1, Level::Zero) || explicit_depth(l1) == Some(1) {
            return l2;
        }
        if l1 == l2 {
            return l1;
        }
        self.level(Level::IMax(l1, l2, hash64!(IMAX_HASH, l1, l2)))
    }

    pub fn param(&mut self, n: NamePtr<'t>) -> LevelPtr<'t> {
        self.level(Level::Param(n, hash64!(PARAM_HASH, n)))
    }

    pub fn levels(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        if let Some(p) = self.store.dag.find_levels(ls) {
            return p;
        }
        self.dag.intern_levels(self.arena, ls)
    }

    pub fn nat(&mut self, n: BigUint) -> BigUintPtr<'t> {
        if let Some(p) = self.store.dag.find_nat(&n) {
            return p;
        }
        self.dag.intern_nat(self.arena, n)
    }

    #[inline]
    fn expr(&mut self, (e, meta): (Expr<'t>, Meta)) -> ExprPtr<'t> {
        self.dag.intern_expr(self.arena, e, meta)
    }

    pub fn var(&mut self, idx: u16) -> ExprPtr<'t> {
        self.expr(mk::var(idx))
    }

    pub fn sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::sort(level))
    }

    pub fn prop(&mut self) -> ExprPtr<'t> {
        let z = self.zero();
        self.sort(z)
    }

    pub fn konst(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::konst(name, levels))
    }

    pub fn app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::app(fun, arg))
    }

    pub fn apps(&mut self, mut f: ExprPtr<'t>, args: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for &a in args {
            f = self.app(f, a);
        }
        f
    }

    pub fn lam(&mut self, ty: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::lam(ty, body))
    }

    pub fn pi(&mut self, ty: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::pi(ty, body))
    }

    pub fn let_(
        &mut self,
        ty: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool,
    ) -> ExprPtr<'t> {
        let probe = LetData {
            ty,
            val,
            body,
            nondep,
        };
        let (hash, sup, nlb) = mk::let_(probe);
        let e = Expr::Let {
            data: &probe,
            hash,
            sup,
        };
        if let Some(p) = self.dag.find_expr(&e) {
            return p;
        }
        let data = self.arena.alloc(probe);
        self.dag
            .add_expr(self.arena, Expr::Let { data, hash, sup }, nlb)
    }

    pub fn proj(&mut self, name: NamePtr<'t>, idx: u16, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::proj(name, idx, e))
    }

    pub fn nat_lit(&mut self, n: BigUint) -> ExprPtr<'t> {
        let n = self.nat(n);
        self.expr(mk::nat(n))
    }

    pub fn local(&mut self, id: u32, ty: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::local(id, ty))
    }
}


/// `succ^k zero` gives `Some(k)` (Lean's `is_explicit`, with its depth).
pub fn explicit_depth(mut l: LevelPtr<'_>) -> Option<u32> {
    let mut k = 0;
    loop {
        match *l {
            Level::Zero => return Some(k),
            Level::Succ(a, _) => {
                k += 1;
                l = a;
            }
            _ => return None,
        }
    }
}

/// Lean's `to_offset`: `succ^k l` as `(l, k)`.
pub fn to_offset(mut l: LevelPtr<'_>) -> (LevelPtr<'_>, u32) {
    let mut k = 0;
    while let Level::Succ(a, _) = *l {
        l = a;
        k += 1;
    }
    (l, k)
}

/// Lean 4.36 `is_not_zero`: not zero under any assignment, read syntactically.
pub fn is_not_zero(l: LevelPtr<'_>) -> bool {
    match *l {
        Level::Zero | Level::Param(..) => false,
        Level::Succ(..) => true,
        Level::Max(a, b, _) => is_not_zero(a) || is_not_zero(b),
        Level::IMax(_, b, _) => is_not_zero(b),
    }
}

/// Lean 4.36 `normalizes_to_zero`.
pub fn normalizes_to_zero(l: LevelPtr<'_>) -> bool {
    match *l {
        Level::Zero => true,
        Level::Param(..) | Level::Succ(..) => false,
        Level::Max(a, b, _) => normalizes_to_zero(a) && normalizes_to_zero(b),
        Level::IMax(_, b, _) => normalizes_to_zero(b),
    }
}
