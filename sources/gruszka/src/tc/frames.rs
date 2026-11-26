//! Environments cut to the entries a term reads (milestone 13). A cut
//! environment is a frame: a run of `eslots` where the entries the term
//! never reads are `HOLE`, ending at the last one it reads. Frames are
//! hash-consed by content, so two environments that agree on what a term
//! reads give one frame id for it.

pub const FREE: (u32, u32) = (0, u32::MAX);

#[derive(Default)]
pub struct FrameTab {
    /// open addressing with linear probing: (hash tag, environment id)
    tab: Vec<(u32, u32)>,
    n: usize,
    /// milestone 36: growths of `tab` (see `Spines::grows`)
    pub grows: u32,
}

#[inline(always)]
pub fn fmix(h: u64, x: u32) -> u64 {
    (h.rotate_left(5) ^ x as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95)
}

#[inline(always)]
pub fn fhash(c: &[u32]) -> u64 {
    let mut h = 0x2545_f491_4f6c_dd1d_u64;
    for &x in c {
        h = fmix(h, x);
    }
    fmix(h, c.len() as u32)
}

impl FrameTab {
    pub fn bytes(&self) -> usize {
        self.n * 16
    }
    /// milestone 37: bytes held (room included)
    pub fn held_bytes(&self) -> usize {
        self.tab.capacity() * 8
    }
    pub fn clear(&mut self, keep: usize) {
        let n = self.n;
        self.n = 0;
        let max = ((keep / 8).next_power_of_two() / 2).max(1 << 10);
        if self.tab.len() > max || (self.tab.len() > (1 << 16) && self.tab.len() > 16 * n) {
            let len = (n * 4).next_power_of_two().clamp(1 << 10, max);
            self.tab = vec![FREE; len];
        } else if n > 0 {
            self.tab.fill(FREE);
        }
    }

    /// The frame with content `c` (oldest entry first), or the slot where
    /// it goes. `run(e)` is environment e's content.
    #[inline]
    pub fn find<'a>(&self, h: u64, c: &[u32], run: impl Fn(u32) -> &'a [u32]) -> Result<u32, usize> {
        if self.tab.is_empty() {
            return Err(usize::MAX);
        }
        let mask = self.tab.len() - 1;
        let tag = (h >> 32) as u32;
        let mut i = (h as usize) & mask;
        loop {
            let (t, e) = self.tab[i];
            if e == u32::MAX {
                return Err(i);
            }
            if t == tag && run(e) == c {
                return Ok(e);
            }
            i = (i + 1) & mask;
        }
    }

    /// Records frame `e` (hash `h`) at `slot` from `find`; grows the table
    /// first when it is half full (`hash_of` rehashes old entries). The
    /// slot taken, None after a growth (milestone 36 logs it).
    pub fn insert(&mut self, h: u64, slot: usize, e: u32, hash_of: impl Fn(u32) -> u64) -> Option<usize> {
        if slot == usize::MAX || (self.n + 1) * 2 > self.tab.len() {
            self.grows = self.grows.wrapping_add(1);
            let len = (self.tab.len() * 2).max(1 << 10);
            let old = std::mem::replace(&mut self.tab, vec![FREE; len]);
            self.n = 0;
            for (_, x) in old {
                if x != u32::MAX {
                    let hx = hash_of(x);
                    self.place(hx, x);
                }
            }
            self.place(h, e);
            return None;
        }
        self.tab[slot] = ((h >> 32) as u32, e);
        self.n += 1;
        Some(slot)
    }

    /// Milestone 36 (checks): the frames in the table.
    pub fn entries(&self) -> impl Iterator<Item = u32> + '_ {
        self.tab.iter().filter(|e| e.1 != u32::MAX).map(|e| e.1)
    }
    /// Milestone 36: frees a slot `insert` took (in reverse order, no
    /// growth in between: see `Spines::unadd`).
    pub fn unadd(&mut self, slot: usize) {
        debug_assert!(self.tab[slot].1 != u32::MAX);
        self.tab[slot] = FREE;
        self.n -= 1;
    }
    /// Milestone 37: takes frame `e` (hash `h`) out of the table, if there
    /// (backward-shift deletion, as `Spines::remove_value`; bumps `grows`).
    pub fn remove(&mut self, h: u64, e: u32, hash_of: impl Fn(u32) -> u64) {
        if self.tab.is_empty() {
            return;
        }
        let mask = self.tab.len() - 1;
        let mut i = (h as usize) & mask;
        loop {
            let x = self.tab[i].1;
            if x == u32::MAX {
                return;
            }
            if x == e {
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
            if x == u32::MAX {
                self.tab[i] = FREE;
                return;
            }
            let home = (hash_of(x) as usize) & mask;
            if (k.wrapping_sub(home) & mask) >= (k.wrapping_sub(i) & mask) {
                self.tab[i] = (t, x);
                i = k;
            }
        }
    }
    /// Milestone 36: the table with only the frames below `em`.
    pub fn rebuild_below(&mut self, em: u32, hash_of: impl Fn(u32) -> u64) {
        let old = std::mem::take(&mut self.tab);
        self.tab = vec![FREE; old.len().max(1 << 10)];
        self.n = 0;
        for (_, x) in old {
            if x != u32::MAX && x < em {
                self.place(hash_of(x), x);
            }
        }
    }

    fn place(&mut self, h: u64, e: u32) {
        let mask = self.tab.len() - 1;
        let mut i = (h as usize) & mask;
        while self.tab[i].1 != u32::MAX {
            i = (i + 1) & mask;
        }
        self.tab[i] = ((h >> 32) as u32, e);
        self.n += 1;
    }
}
