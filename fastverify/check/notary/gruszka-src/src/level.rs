//! Universe levels: a per-worker interner on top of the global (MAIN) level
//! table, Lean's simplifying constructors, normalization, equivalence and
//! `is_geq`. Equal structure means equal id, in both tables. The worker
//! table is never cleared, so memos keyed by level ids stay valid.

use rustc_hash::FxHashMap;

pub const ZERO: u32 = 0;
pub const K_ZERO: u8 = 0;
pub const K_SUCC: u8 = 1;
pub const K_MAX: u8 = 2;
pub const K_IMAX: u8 = 3;
pub const K_PARAM: u8 = 4;

pub struct Levels<'e> {
    g: &'e [(u8, u32, u32)],
    gmap: &'e FxHashMap<(u8, u32, u32), u32>,
    loc: Vec<(u8, u32, u32)>,
    lmap: FxHashMap<(u8, u32, u32), u32>,
    norm_memo: FxHashMap<u32, u32>,
    /// K02: the file's canonical names and bytes, to order parameters as
    /// Lean's `is_norm_lt` does (by `name::cmp`); None: by canonical id
    /// (unit tests only)
    names: Option<(&'e susz::canon::Canon, &'e [u8])>,
}

impl<'e> Levels<'e> {
    pub fn new(g: &'e [(u8, u32, u32)], gmap: &'e FxHashMap<(u8, u32, u32), u32>) -> Levels<'e> {
        Levels { g, gmap, loc: Vec::new(), lmap: FxHashMap::default(), norm_memo: FxHashMap::default(), names: None }
    }
    /// K02: parameters ordered by their names (`name_cmp`).
    pub fn with_names(mut self, cn: &'e susz::canon::Canon, src: &'e [u8]) -> Levels<'e> {
        self.names = Some((cn, src));
        self
    }
    /// K02: Lean 4.36's `name::cmp` (util/name.cpp `cmp_core`) on two
    /// canonical names: components compared from the root, a numeral
    /// before a string, numerals by value, strings by their bytes (unsigned,
    /// a prefix before its extensions), and a name before its extensions.
    /// `is_norm_lt` orders parameters by it, and level normalization (so
    /// `is_equivalent`, which is incomplete) depends on that order: with
    /// canonical ids (intern order) gruszka rejected what Lean accepts and
    /// accepted what it rejects (K04's lvlname tests).
    fn name_cmp(&self, a: u32, b: u32) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        if a == b {
            return Equal;
        }
        let Some((cn, src)) = self.names else { return a.cmp(&b) };
        let chain = |mut x: u32| -> smallvec::SmallVec<[u32; 8]> {
            let mut v = smallvec::SmallVec::new();
            while x != susz::canon::ANON && (x as usize) < cn.pre.len() {
                v.push(x);
                x = cn.pre[x as usize];
            }
            v.reverse();
            v
        };
        let (ca, cb) = (chain(a), chain(b));
        for (&x, &y) in ca.iter().zip(cb.iter()) {
            if x == y {
                continue;
            }
            use susz::canon::Part;
            let o = match (cn.part(src, x), cn.part(src, y)) {
                (Part::Num(p), Part::Num(q)) => p.cmp(&q),
                (Part::Num(_), Part::Str(_)) => Less,
                (Part::Str(_), Part::Num(_)) => Greater,
                (Part::Str(s), Part::Str(t)) => s.cmp(t),
            };
            if o != Equal {
                return o;
            }
        }
        ca.len().cmp(&cb.len())
    }
    /// Milestone 37: bytes held (room included)
    pub fn held_bytes(&self) -> usize {
        self.loc.capacity() * 12 + self.lmap.capacity() * 17 + self.norm_memo.capacity() * 9
    }
    /// Worker-made levels and memo entries.
    pub fn len(&self) -> usize {
        self.loc.len() + self.norm_memo.len()
    }
    #[inline(always)]
    pub fn get(&self, l: u32) -> (u8, u32, u32) {
        let gl = self.g.len() as u32;
        if l < gl { self.g[l as usize] } else { self.loc[(l - gl) as usize] }
    }
    pub fn kind(&self, l: u32) -> u8 {
        self.get(l).0
    }
    pub fn mk(&mut self, k: u8, a: u32, b: u32) -> u32 {
        let key = (k, a, b);
        if let Some(&x) = self.gmap.get(&key) {
            return x;
        }
        if let Some(&x) = self.lmap.get(&key) {
            return x;
        }
        let id = self.g.len() as u32 + self.loc.len() as u32;
        self.loc.push(key);
        self.lmap.insert(key, id);
        id
    }
    pub fn succ(&mut self, l: u32) -> u32 {
        self.mk(K_SUCC, l, 0)
    }
    pub fn param(&mut self, canon_name: u32) -> u32 {
        self.mk(K_PARAM, canon_name, 0)
    }
    pub fn is_zero(&self, l: u32) -> bool {
        self.kind(l) == K_ZERO
    }
    /// Zero for every assignment, by the reference kernel's syntactic test
    /// (Pestka's `normalizesToZero`): an imax with a zero right side is zero.
    pub fn zeroish(&self, l: u32) -> bool {
        let (k, a, b) = self.get(l);
        match k {
            K_ZERO => true,
            K_MAX => self.zeroish(a) && self.zeroish(b),
            K_IMAX => self.zeroish(b),
            _ => false,
        }
    }
    pub fn is_not_zero(&self, l: u32) -> bool {
        let (k, a, b) = self.get(l);
        match k {
            K_ZERO | K_PARAM => false,
            K_SUCC => true,
            K_MAX => self.is_not_zero(a) || self.is_not_zero(b),
            _ => self.is_not_zero(b),
        }
    }
    pub fn to_offset(&self, mut l: u32) -> (u32, u32) {
        let mut k = 0;
        loop {
            let (kk, a, _) = self.get(l);
            if kk == K_SUCC {
                l = a;
                k += 1;
            } else {
                return (l, k);
            }
        }
    }
    pub fn is_explicit(&self, l: u32) -> bool {
        self.is_zero(self.to_offset(l).0)
    }
    pub fn succ_n(&mut self, mut l: u32, n: u32) -> u32 {
        for _ in 0..n {
            l = self.succ(l);
        }
        l
    }
    /// Lean's `mk_max` (with simplifications).
    pub fn max(&mut self, l1: u32, l2: u32) -> u32 {
        if self.is_explicit(l1) && self.is_explicit(l2) {
            return if self.to_offset(l1).1 >= self.to_offset(l2).1 { l1 } else { l2 };
        }
        if l1 == l2 {
            return l1;
        }
        if self.is_zero(l1) {
            return l2;
        }
        if self.is_zero(l2) {
            return l1;
        }
        let (k2, a2, b2) = self.get(l2);
        if k2 == K_MAX && (a2 == l1 || b2 == l1) {
            return l2;
        }
        let (k1, a1, b1) = self.get(l1);
        if k1 == K_MAX && (a1 == l2 || b1 == l2) {
            return l1;
        }
        let p1 = self.to_offset(l1);
        let p2 = self.to_offset(l2);
        if p1.0 == p2.0 {
            return if p1.1 > p2.1 { l1 } else { l2 };
        }
        self.mk(K_MAX, l1, l2)
    }
    /// Lean's `mk_imax` (with simplifications).
    pub fn imax(&mut self, l1: u32, l2: u32) -> u32 {
        if self.is_not_zero(l2) {
            self.max(l1, l2)
        } else if self.is_zero(l2) || self.is_zero(l1) || self.get(l1) == (K_SUCC, ZERO, 0) {
            l2
        } else if l1 == l2 {
            l1
        } else {
            self.mk(K_IMAX, l1, l2)
        }
    }

    fn push_max_args(&self, l: u32, out: &mut Vec<u32>) {
        let (k, a, b) = self.get(l);
        if k == K_MAX {
            self.push_max_args(a, out);
            self.push_max_args(b, out);
        } else {
            out.push(l);
        }
    }

    /// Lean's `is_norm_lt`: a total order on levels (parameters by name,
    /// Lean's `name::cmp`; K02: was by canonical name id).
    fn norm_cmp(&self, a: u32, b: u32) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        if a == b {
            return Equal;
        }
        let (l1, o1) = self.to_offset(a);
        let (l2, o2) = self.to_offset(b);
        if l1 != l2 {
            let (k1, a1, b1) = self.get(l1);
            let (k2, a2, b2) = self.get(l2);
            if k1 != k2 {
                return k1.cmp(&k2);
            }
            match k1 {
                K_PARAM => self.name_cmp(a1, a2),
                K_MAX | K_IMAX => {
                    if a1 != a2 {
                        self.norm_cmp(a1, a2)
                    } else {
                        self.norm_cmp(b1, b2)
                    }
                }
                _ => Equal,
            }
        } else {
            o1.cmp(&o2)
        }
    }

    pub fn normalize(&mut self, l: u32) -> u32 {
        if let Some(&r) = self.norm_memo.get(&l) {
            return r;
        }
        let r = self.normalize_core(l);
        self.norm_memo.insert(l, r);
        r
    }

    fn normalize_core(&mut self, l: u32) -> u32 {
        let (r, k) = self.to_offset(l);
        let (kind, a, b) = self.get(r);
        match kind {
            K_ZERO | K_PARAM => l,
            K_IMAX => {
                let l1 = self.normalize(a);
                let l2 = self.normalize(b);
                let im = self.imax(l1, l2);
                self.succ_n(im, k)
            }
            _ => {
                // K_MAX
                let mut todo = Vec::new();
                self.push_max_args(r, &mut todo);
                let mut args = Vec::new();
                for x in todo {
                    let n = self.normalize(x);
                    self.push_max_args(n, &mut args);
                }
                args.sort_by(|x, y| self.norm_cmp(*x, *y));
                let mut rargs: Vec<u32> = Vec::new();
                let mut i = 0;
                if self.is_explicit(args[i]) {
                    while i + 1 < args.len() && self.is_explicit(args[i + 1]) {
                        i += 1;
                    }
                    let kk = self.to_offset(args[i]).1;
                    let mut j = i + 1;
                    while j < args.len() {
                        if self.to_offset(args[j]).1 >= kk {
                            break;
                        }
                        j += 1;
                    }
                    if j < args.len() {
                        i += 1;
                    }
                }
                rargs.push(args[i]);
                let mut prev = self.to_offset(args[i]);
                i += 1;
                while i < args.len() {
                    let cur = self.to_offset(args[i]);
                    if prev.0 == cur.0 {
                        if prev.1 < cur.1 {
                            prev = cur;
                            rargs.pop();
                            rargs.push(args[i]);
                        }
                    } else {
                        prev = cur;
                        rargs.push(args[i]);
                    }
                    i += 1;
                }
                for x in rargs.iter_mut() {
                    *x = self.succ_n(*x, k);
                }
                // mk_big_max
                let mut acc = *rargs.last().unwrap();
                for idx in (0..rargs.len() - 1).rev() {
                    acc = self.max(rargs[idx], acc);
                }
                acc
            }
        }
    }

    pub fn equiv(&mut self, a: u32, b: u32) -> bool {
        a == b || self.normalize(a) == self.normalize(b)
    }

    pub fn geq(&mut self, a: u32, b: u32) -> bool {
        let a = self.normalize(a);
        let b = self.normalize(b);
        self.geq_core(a, b)
    }

    fn geq_core(&mut self, l1: u32, l2: u32) -> bool {
        if l1 == l2 || self.is_zero(l2) {
            return true;
        }
        let (k2, a2, b2) = self.get(l2);
        if k2 == K_MAX {
            return self.geq(l1, a2) && self.geq(l1, b2);
        }
        let (k1, a1, b1) = self.get(l1);
        if k1 == K_MAX && (self.geq(a1, l2) || self.geq(b1, l2)) {
            return true;
        }
        if k2 == K_IMAX {
            return self.geq(l1, a2) && self.geq(l1, b2);
        }
        if k1 == K_IMAX {
            return self.geq(b1, l2);
        }
        let p1 = self.to_offset(l1);
        let p2 = self.to_offset(l2);
        // milestone 29: Lean's rule tests the base of `l2` (k >= n when `l2`
        // is the constant n); the base of `l1` was tested here, which
        // refused u+2 >= 1 and let n >= u+k through for n >= k
        if p1.0 == p2.0 || self.is_zero(p2.0) {
            return p1.1 >= p2.1;
        }
        if p1.1 == p2.1 && p1.1 > 0 {
            return self.geq(p1.0, p2.0);
        }
        false
    }

    /// Milestone 23: `subst` without the memo while the level has at most
    /// `budget` nodes (levels are small trees); None past it (the caller
    /// then runs `subst`, whose memo bounds a shared DAG).
    pub fn subst_small(&mut self, l: u32, f: &dyn Fn(u32) -> Option<u32>, budget: &mut u32) -> Option<u32> {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let (k, a, b) = self.get(l);
        Some(match k {
            K_ZERO => l,
            K_PARAM => f(a).unwrap_or(l),
            K_SUCC => {
                let x = self.subst_small(a, f, budget)?;
                if x == a { l } else { self.succ(x) }
            }
            _ => {
                let x = self.subst_small(a, f, budget)?;
                let y = self.subst_small(b, f, budget)?;
                if x == a && y == b {
                    l
                } else if k == K_MAX {
                    self.max(x, y)
                } else {
                    self.imax(x, y)
                }
            }
        })
    }
    /// Substitutes parameters: `f(canon_name)` gives the replacement.
    pub fn subst(&mut self, l: u32, f: &dyn Fn(u32) -> Option<u32>, memo: &mut FxHashMap<u32, u32>) -> u32 {
        if let Some(&r) = memo.get(&l) {
            return r;
        }
        let (k, a, b) = self.get(l);
        let r = match k {
            K_ZERO => l,
            K_PARAM => f(a).unwrap_or(l),
            K_SUCC => {
                let x = self.subst(a, f, memo);
                if x == a { l } else { self.succ(x) }
            }
            _ => {
                let x = self.subst(a, f, memo);
                let y = self.subst(b, f, memo);
                if x == a && y == b {
                    l
                } else if k == K_MAX {
                    self.max(x, y)
                } else {
                    self.imax(x, y)
                }
            }
        };
        memo.insert(l, r);
        r
    }

    /// Calls `f` on every parameter name in `l`.
    pub fn params_in(&self, l: u32, f: &mut dyn FnMut(u32) -> bool) -> bool {
        let (k, a, b) = self.get(l);
        match k {
            K_ZERO => true,
            K_PARAM => f(a),
            K_SUCC => self.params_in(a, f),
            _ => self.params_in(a, f) && self.params_in(b, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Milestone 29: `geq` against Lean's is_geq_core (offsets compare when
    /// the bases are equal or the right side's base is zero).
    #[test]
    fn geq_offsets() {
        let g = vec![(K_ZERO, 0, 0)];
        let gmap: FxHashMap<(u8, u32, u32), u32> = [((K_ZERO, 0, 0), 0)].into_iter().collect();
        let mut lv = Levels::new(&g, &gmap);
        let z = 0;
        let one = lv.succ(z);
        let two = lv.succ(one);
        let three = lv.succ(two);
        let u = lv.param(1);
        let v = lv.param(2);
        let u1 = lv.succ(u);
        let u2 = lv.succ(u1);
        let v1 = lv.succ(v);
        let muv = lv.max(u, v);
        let muv1 = lv.succ(muv);
        let iuv1 = lv.imax(u, v1);
        let cases = [
            (u2, one, true), // FLT's DoubleComplex.Bounded: Sort (u+2) holds Nat
            (u2, two, true),
            (u1, two, false),
            (two, u2, false), // a constant does not bound a parameter
            (three, u1, false),
            (one, u, false),
            (u1, u, true),
            (u, u1, false),
            (three, one, true),
            (one, three, false),
            (u, z, true),
            (muv1, u1, true),
            (u1, muv, false),
            (iuv1, v1, true),
            (v1, iuv1, false),
        ];
        for (a, b, want) in cases {
            assert_eq!(lv.geq(a, b), want, "geq({a}, {b})");
        }
    }
}
