//! Spines as slices (milestone 12). A neutral value's eliminations
//! (arguments and projections, first applied first) are one run of words.
//! Neutral values with a non-empty spine are hash-consed here as a whole,
//! head and elims hashed once: one probe per neutral, where cons cells took
//! one probe per cell plus one for the value. Equal heads and elims still
//! give one value id; a spine id belongs to its neutral value.

use super::{Head, V, Val};

pub const EMPTY: u32 = u32::MAX;
const PROJ_BIT: u32 = 0x8000_0000;
const LEN_MASK: u32 = (1 << 28) - 1;
/// a projection among the elims
pub const F_PROJ: u32 = 1 << 28;
/// `F_FV` is known (an argument has a free variable)
pub const F_FV_KNOWN: u32 = 1 << 29;
pub const F_FV: u32 = 1 << 30;
const FREE: (u32, u32) = (0, EMPTY);
/// room of a worker's spine words (16 GiB of address space)
pub const SPINE_WORDS: usize = 1 << 32;

#[derive(Default)]
pub struct Spines {
    /// per spine: a header (length | flags) followed by its elims
    d: crate::env::Slab<u32>,
    /// neutral values by head and elims; open addressing with linear
    /// probing: (hash tag, value id)
    tab: Vec<(u32, u32)>,
    n: usize,
    bits: u32,
    /// milestone 36: growths of `tab` (a region's slots are undone only
    /// when it did not grow since the region opened)
    pub grows: u32,
}

#[inline(always)]
fn mix(h: u64, x: u32) -> u64 {
    (h.rotate_left(5) ^ x as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95)
}

#[inline(always)]
fn head_words(h: Head) -> (u32, u32, u32) {
    match h {
        Head::FVar(i) => (4, i, 0),
        Head::Const(r, l) => (5, r, l),
        Head::Stuck(x) => (6, x, 0),
    }
}

/// Where a missing neutral goes in the table (see `Spines::find`).
pub struct Slot(usize, u32);

impl Spines {
    /// Milestone 15: the header word of spine `s`, read without a bounds
    /// check. Invariant (S): a spine id other than EMPTY was returned by
    /// `make` in the current session (`d` only grows until `clear`, which
    /// happens at a session boundary with the value arena), and `make`
    /// writes the header and all `n` elims, so `s + 1 + n <= d.len()`.
    /// Debug builds assert it.
    #[inline(always)]
    fn head_word(&self, s: u32) -> u32 {
        debug_assert!((s as usize) < self.d.len(), "spine id {s} out of range ({})", self.d.len());
        // SAFETY: invariant (S)
        unsafe { *self.d.get_unchecked(s as usize) }
    }
    #[inline(always)]
    /// milestone 47: the spine table past seven eighths of its room
    pub fn over_soft(&self) -> bool {
        self.d.over_soft()
    }
    pub fn len(&self, s: u32) -> usize {
        if s == EMPTY { 0 } else { (self.head_word(s) & LEN_MASK) as usize }
    }
    #[inline(always)]
    pub fn args(&self, s: u32) -> &[u32] {
        if s == EMPTY {
            return &[];
        }
        let i = s as usize;
        let n = (self.head_word(s) & LEN_MASK) as usize;
        debug_assert!(i + 1 + n <= self.d.len());
        // SAFETY: invariant (S)
        unsafe { self.d.get_unchecked(i + 1..i + 1 + n) }
    }
    #[inline(always)]
    pub fn flags(&self, s: u32) -> u32 {
        if s == EMPTY { 0 } else { self.head_word(s) & !LEN_MASK }
    }
    #[inline(always)]
    pub fn set_flags(&mut self, s: u32, f: u32) {
        self.d[s as usize] |= f;
    }
    /// neutral values in the table
    /// Milestone 19: the spine words in a reserved range (`Slab`).
    pub fn new(cap: usize) -> Spines {
        Spines { d: crate::env::Slab::new(cap), ..Default::default() }
    }
    /// bytes held by entries (words and table slots in use)
    pub fn bytes(&self) -> usize {
        self.d.len() * 4 + self.n * 16
    }
    /// milestone 37: bytes held (room included)
    pub fn held_bytes(&self) -> usize {
        self.d.held_bytes() + self.tab.capacity() * 8
    }

    /// Empties the table, keeping at most `keep` bytes of room for each part.
    pub fn clear(&mut self, keep: usize) {
        self.d.clear();
        self.d.shrink(keep);
        let n = self.n;
        self.n = 0;
        let max = ((keep / 8).next_power_of_two() / 2).max(1 << 10);
        if self.tab.len() > max || (self.tab.len() > (1 << 16) && self.tab.len() > 16 * n) {
            let len = (n * 4).next_power_of_two().clamp(1 << 10, max);
            self.tab = vec![FREE; len];
            self.bits = len.trailing_zeros();
        } else if n > 0 {
            self.tab.fill(FREE);
        }
    }

    /// SK_POISON: shift the next ids by one word.
    pub fn poison(&mut self) {
        self.d.push(0);
    }

    #[inline]
    fn hash(&self, head: Head, s: u32, extra: &[u32]) -> u64 {
        let (k, a, b) = head_words(head);
        let mut h = mix(mix(mix(0x2545_f491_4f6c_dd1d, k), a), b);
        for &x in self.args(s) {
            h = mix(h, x);
        }
        for &x in extra {
            h = mix(h, x);
        }
        mix(h, (self.len(s) + extra.len()) as u32)
    }

    fn grow(&mut self, vals: &[super::Rec]) {
        self.grows = self.grows.wrapping_add(1);
        let old = std::mem::take(&mut self.tab);
        let len = (old.len() * 2).max(1 << 10);
        self.tab = vec![FREE; len];
        self.bits = len.trailing_zeros();
        let mask = len - 1;
        for &(_, v) in old.iter().filter(|e| e.1 != EMPTY) {
            let Val::Neu { head, spine } = vals[v as usize].v else { unreachable!() };
            let h = self.hash(head, spine, &[]);
            let mut j = (h >> (64 - self.bits)) as usize;
            while self.tab[j].1 != EMPTY {
                j = (j + 1) & mask;
            }
            self.tab[j] = (h as u32, v);
        }
    }

    /// The neutral value `head` applied to spine `base` (EMPTY: none) and
    /// then `extra` (not both empty): `Ok(value)` when it exists, else where
    /// to put it (`add`, with no other call in between).
    pub fn find(&mut self, vals: &[super::Rec], head: Head, base: u32, extra: &[u32]) -> Result<V, Slot> {
        if (self.n + 1) * 2 > self.tab.len() {
            self.grow(vals);
        }
        let bl = self.len(base);
        let n = bl + extra.len();
        let h = self.hash(head, base, extra);
        let tag = h as u32;
        let mask = self.tab.len() - 1;
        let mut j = (h >> (64 - self.bits)) as usize;
        loop {
            debug_assert!(j < self.tab.len());
            // SAFETY: j is masked by tab.len() - 1 (a power of two)
            let (t, v) = unsafe { *self.tab.get_unchecked(j) };
            if v == EMPTY {
                return Err(Slot(j, tag));
            }
            if t == tag {
                debug_assert!((v as usize) < vals.len());
                // SAFETY: the table holds value ids of this session (tc.rs
                // invariant (A)); it is emptied with the arena
                if let Val::Neu { head: h2, spine } = unsafe { vals.get_unchecked(v as usize).v } {
                    if h2 == head && self.len(spine) == n {
                        // word by word (short runs: no memcmp call)
                        let a = self.args(spine);
                        let b = self.args(base);
                        let mut same = true;
                        for k in 0..bl {
                            if a[k] != b[k] {
                                same = false;
                                break;
                            }
                        }
                        if same {
                            for k in 0..extra.len() {
                                if a[bl + k] != extra[k] {
                                    same = false;
                                    break;
                                }
                            }
                        }
                        if same {
                            return Ok(v);
                        }
                    }
                }
            }
            j = (j + 1) & mask;
        }
    }

    /// A new spine: `base` followed by `extra`.
    pub fn make(&mut self, base: u32, extra: &[u32]) -> u32 {
        let bl = self.len(base);
        let n = bl + extra.len();
        let id = self.d.len();
        assert!(id + n + 1 < EMPTY as usize && n <= LEN_MASK as usize, "spine arena limit");
        let proj = (self.flags(base) & F_PROJ != 0) || extra.iter().any(|&e| e & PROJ_BIT != 0);
        self.d.push(n as u32 | if proj { F_PROJ } else { 0 });
        if bl > 0 {
            let b = base as usize + 1;
            self.d.extend_from_within(b..b + bl);
        }
        self.d.extend_from_slice(extra);
        id as u32
    }

    /// Records the new neutral value `v` at the slot `find` returned
    /// (returned: milestone 36 logs it).
    pub fn add(&mut self, slot: Slot, v: V) -> usize {
        self.tab[slot.0] = (slot.1, v);
        self.n += 1;
        slot.0
    }

    /// Milestone 36 (checks): the values in the table.
    pub fn entries(&self) -> impl Iterator<Item = u32> + '_ {
        self.tab.iter().filter(|e| e.1 != EMPTY).map(|e| e.1)
    }
    /// Milestone 36: words of the spine arena (a region's mark).
    pub fn words(&self) -> usize {
        self.d.len()
    }
    /// Milestone 36: the spines past word `n` go (a region's rollback; the
    /// table no longer holds their values: `unadd` or `rebuild_below`).
    pub fn truncate(&mut self, n: usize) {
        self.d.truncate(n);
    }
    /// Milestone 36: frees the slot `add` took. Undone in the reverse order
    /// of the adds, with no growth in between, linear probing returns to
    /// the exact table before them.
    pub fn unadd(&mut self, slot: usize) {
        debug_assert!(self.tab[slot].1 != EMPTY);
        self.tab[slot] = FREE;
        self.n -= 1;
    }
    /// Milestone 37: takes the neutral value `v` out of the table, if there
    /// (backward-shift deletion: later entries of its probe run move up, so
    /// the table is as if `v` had never been added). Moves slots: `grows`
    /// is bumped, so open regions do not undo by slot any more.
    pub fn remove_value(&mut self, vals: &[super::Rec], v: V) {
        let Val::Neu { head, spine } = vals[v as usize].v else { return };
        if self.tab.is_empty() {
            return;
        }
        let mask = self.tab.len() - 1;
        let h = self.hash(head, spine, &[]);
        let mut i = (h >> (64 - self.bits)) as usize;
        loop {
            let e = self.tab[i].1;
            if e == EMPTY {
                return;
            }
            if e == v {
                break;
            }
            i = (i + 1) & mask;
        }
        self.grows = self.grows.wrapping_add(1);
        self.n -= 1;
        let mut k = i;
        loop {
            k = (k + 1) & mask;
            let (t, x) = self.tab[k];
            if x == EMPTY {
                self.tab[i] = FREE;
                return;
            }
            let Val::Neu { head: hx, spine: sx } = vals[x as usize].v else { unreachable!() };
            let home = (self.hash(hx, sx, &[]) >> (64 - self.bits)) as usize;
            // x may move to i unless its home lies cyclically in (i, k]
            if (k.wrapping_sub(home) & mask) >= (k.wrapping_sub(i) & mask) {
                self.tab[i] = (t, x);
                i = k;
            }
        }
    }
    /// Milestone 36: the table with only the values below `vm` (after a
    /// growth inside a region: its slots moved).
    pub fn rebuild_below(&mut self, vals: &[super::Rec], vm: u32) {
        let old = std::mem::take(&mut self.tab);
        let len = old.len().max(1 << 10);
        self.tab = vec![FREE; len];
        self.bits = len.trailing_zeros();
        self.n = 0;
        let mask = len - 1;
        for &(_, v) in old.iter().filter(|e| e.1 != EMPTY && e.1 < vm) {
            let Val::Neu { head, spine } = vals[v as usize].v else { unreachable!() };
            let h = self.hash(head, spine, &[]);
            let mut j = (h >> (64 - self.bits)) as usize;
            while self.tab[j].1 != EMPTY {
                j = (j + 1) & mask;
            }
            self.tab[j] = (h as u32, v);
            self.n += 1;
        }
    }
}
