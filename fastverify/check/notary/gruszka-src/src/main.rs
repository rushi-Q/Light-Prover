//! gruszka: a Lean 4 kernel built around Susz.
//!
//!   gruszka FILE [WORKERS]
//!
//! WORKERS defaults to the number of cores (`available_parallelism`); an
//! `.ndjson` file is packed on that many threads too.
//! FILE is a `.susz` file (or a lean4export `.ndjson`, packed in-process).
//! Prints `accepted`, `rejected: <decl>: <why>` or `declined: <why>` and
//! exits 0, 1 or 2.
//!
//!   gruszka --only NAME[,NAME...] FILE.susz [WORKERS]
//!
//! (milestone 26, Pestka's subset check) checks the named declarations,
//! found through the file's INDEX, against the environment of everything
//! before them; prints `checked: NAMES (subset; N earlier declarations
//! admitted unchecked)` (0), `rejected: ...` (1), `declined: ...` (2) or
//! `index invalid: ...` (2), never `accepted`. README, "Checking part of a
//! file".
//!
//! `--progress[=SECS]` (milestone 37), anywhere: a progress line on stderr
//! every SECS seconds (default 10).
//!
//! `GRUSZKA_STACK_MB` (milestone 42): each worker's stack in MiB (default
//! 1024). Recursion that reaches its limit (the stack less a quarter of it,
//! at most 64 MiB) declines the declaration.

mod env;
mod env_digest;
mod induct;
mod level;
mod quot;
mod tc;

#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: Split = Split;

/// K01: mimalloc for everything but very large blocks, which go to the
/// system allocator (fresh mappings). The in-process packer's columns (GBs,
/// filled by its workers, walked back on one thread) were walked 2.5x slower
/// in mimalloc's memory than in the system's. The size of a block decides
/// both its allocation and its release, so each block stays with one
/// allocator; a reallocation across the threshold moves the block.
#[cfg(feature = "mimalloc")]
struct Split;

#[cfg(feature = "mimalloc")]
const SPLIT_BYTES: usize = 64 << 20;

/// K02: transparent huge pages for the system allocator's large blocks
/// (K02_THP; set by main before anything large is allocated)
static BIG_THP: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
#[cfg(target_os = "linux")]
#[inline(never)]
fn big_thp(p: *mut u8, n: usize) {
    unsafe extern "C" {
        fn madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
    }
    const H: usize = 1 << 21;
    let a = (p as usize + H - 1) & !(H - 1);
    let e = (p as usize + n) & !(H - 1);
    if !p.is_null() && e > a {
        unsafe { madvise(a as *mut u8, e - a, 14) };
    }
}
#[cfg(not(target_os = "linux"))]
fn big_thp(_p: *mut u8, _n: usize) {}

#[cfg(feature = "mimalloc")]
unsafe impl std::alloc::GlobalAlloc for Split {
    #[inline(always)]
    unsafe fn alloc(&self, l: std::alloc::Layout) -> *mut u8 {
        unsafe {
            if l.size() >= SPLIT_BYTES {
                let p = std::alloc::System.alloc(l);
                if BIG_THP.load(std::sync::atomic::Ordering::Relaxed) {
                    big_thp(p, l.size());
                }
                p
            } else {
                mimalloc::MiMalloc.alloc(l)
            }
        }
    }
    #[inline(always)]
    unsafe fn alloc_zeroed(&self, l: std::alloc::Layout) -> *mut u8 {
        unsafe {
            if l.size() >= SPLIT_BYTES {
                let p = std::alloc::System.alloc_zeroed(l);
                if BIG_THP.load(std::sync::atomic::Ordering::Relaxed) {
                    big_thp(p, l.size());
                }
                p
            } else {
                mimalloc::MiMalloc.alloc_zeroed(l)
            }
        }
    }
    #[inline(always)]
    unsafe fn dealloc(&self, p: *mut u8, l: std::alloc::Layout) {
        unsafe {
            if l.size() >= SPLIT_BYTES {
                std::alloc::System.dealloc(p, l)
            } else {
                mimalloc::MiMalloc.dealloc(p, l)
            }
        }
    }
    #[inline(always)]
    unsafe fn realloc(&self, p: *mut u8, l: std::alloc::Layout, new_size: usize) -> *mut u8 {
        unsafe {
            let (old_big, new_big) = (l.size() >= SPLIT_BYTES, new_size >= SPLIT_BYTES);
            if old_big == new_big {
                return if old_big {
                    std::alloc::System.realloc(p, l, new_size)
                } else {
                    mimalloc::MiMalloc.realloc(p, l, new_size)
                };
            }
            let nl = std::alloc::Layout::from_size_align_unchecked(new_size, l.align());
            let q = self.alloc(nl);
            if !q.is_null() {
                std::ptr::copy_nonoverlapping(p, q, l.size().min(new_size));
                self.dealloc(p, l);
            }
            q
        }
    }
}

use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, AtomicU32, Ordering};
use std::time::Instant;
use tc::{Stop, Worker};

const ST_OK: u8 = 1;
const ST_REJECT: u8 = 2;
const ST_DECLINE: u8 = 3;
const ST_CANCEL: u8 = 4;

#[cfg(target_os = "macos")]
fn instr_now() -> u64 {
    // this thread's instructions (thread_selfcounts, as thread_counts): the
    // process-wide proc_pid_rusage summed the other workers in and cost
    // more per call than a small declaration
    thread_counts().0
}
#[cfg(not(target_os = "macos"))]
fn instr_now() -> u64 {
    0
}

/// Maps the file again over its own mapping (same address, same bytes):
/// the pages read so far stop counting as this process's resident memory
/// (the system keeps them in its file cache). Readers in other threads see
/// the same bytes before and after.
#[cfg(unix)]
fn remap(bytes: &[u8], path: &str) -> bool {
    use std::os::fd::AsRawFd;
    unsafe extern "C" {
        fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    }
    #[cfg(target_os = "macos")]
    const MAP_FIXED: i32 = 0x10;
    #[cfg(not(target_os = "macos"))]
    const MAP_FIXED: i32 = 0x10;
    const PROT_READ: i32 = 1;
    const MAP_SHARED: i32 = 1;
    let Ok(f) = std::fs::File::open(path) else { return false };
    match f.metadata() {
        Ok(m) if m.len() as usize == bytes.len() => {}
        _ => return false,
    }
    let p = bytes.as_ptr() as *mut u8;
    let r = unsafe { mmap(p, bytes.len(), PROT_READ, MAP_SHARED | MAP_FIXED, f.as_raw_fd(), 0) };
    r == p
}
#[cfg(not(unix))]
fn remap(_bytes: &[u8], _path: &str) -> bool {
    false
}

/// Milestone 24: this thread's (instructions, cycles) retired so far
/// (macOS `thread_selfcounts`), and its CPU time in ns; zeros elsewhere.
#[cfg(target_os = "macos")]
fn thread_counts() -> (u64, u64, u64) {
    unsafe extern "C" {
        fn thread_selfcounts(kind: i32, buf: *mut u64, n: usize) -> i32;
        fn clock_gettime_nsec_np(clock: u32) -> u64;
    }
    let mut b = [0u64; 2];
    unsafe {
        thread_selfcounts(1, b.as_mut_ptr(), 16);
        (b[0], b[1], clock_gettime_nsec_np(16))
    }
}
#[cfg(not(target_os = "macos"))]
fn thread_counts() -> (u64, u64, u64) {
    (0, 0, 0)
}

/// K02: the CPUs this process may run on, ordered for pinning: grouped by
/// (socket, APIC id / 16) — on Zen 4/5 one CCD (8 cores x 2 threads, its own
/// L3) — inside a group first one hardware thread of every core (APIC id
/// bit 0 = SMT thread), then the siblings. From /proc/cpuinfo (sysfs is not
/// visible in the sandbox); without it, the allowed CPUs in order. Only
/// placement: the verdict does not depend on it.
#[cfg(target_os = "linux")]
fn pin_order() -> Vec<usize> {
    unsafe extern "C" {
        fn sched_getaffinity(pid: i32, size: usize, mask: *mut u64) -> i32;
    }
    let mut m = [0u64; 64];
    if unsafe { sched_getaffinity(0, std::mem::size_of_val(&m), m.as_mut_ptr()) } != 0 {
        return Vec::new();
    }
    let allowed = |c: usize| c < 4096 && m[c / 64] >> (c % 64) & 1 == 1;
    let mut info: Vec<(usize, usize, usize, usize)> = Vec::new(); // (group, rank, apic, cpu)
    if let Ok(t) = std::fs::read_to_string("/proc/cpuinfo") {
        let (mut cpu, mut phys, mut apic) = (usize::MAX, usize::MAX, usize::MAX);
        let mut flush = |cpu: usize, phys: usize, apic: usize, info: &mut Vec<(usize, usize, usize, usize)>| {
            if cpu != usize::MAX && allowed(cpu) {
                if apic != usize::MAX && phys != usize::MAX {
                    info.push(((phys << 20) | (apic >> 4), apic & 1, apic, cpu));
                } else {
                    info.push((0, 0, cpu, cpu));
                }
            }
        };
        for line in t.lines() {
            let mut kv = line.splitn(2, ':');
            let (k, v) = (kv.next().unwrap_or("").trim(), kv.next().unwrap_or("").trim());
            match k {
                "processor" => {
                    flush(cpu, phys, apic, &mut info);
                    cpu = v.parse().unwrap_or(usize::MAX);
                    phys = usize::MAX;
                    apic = usize::MAX;
                }
                "physical id" => phys = v.parse().unwrap_or(usize::MAX),
                "apicid" => apic = v.parse().unwrap_or(usize::MAX),
                _ => {}
            }
        }
        flush(cpu, phys, apic, &mut info);
    }
    if info.is_empty() {
        return (0..4096).filter(|&c| allowed(c)).collect();
    }
    info.sort();
    info.into_iter().map(|k| k.3).collect()
}
#[cfg(not(target_os = "linux"))]
fn pin_order() -> Vec<usize> {
    Vec::new()
}
#[cfg(target_os = "linux")]
fn pin_to(cpu: usize) {
    unsafe extern "C" {
        fn sched_setaffinity(pid: i32, size: usize, mask: *const u64) -> i32;
    }
    let mut m = [0u64; 64];
    if cpu < 4096 {
        m[cpu / 64] |= 1 << (cpu % 64);
        unsafe { sched_setaffinity(0, std::mem::size_of_val(&m), m.as_ptr()) };
    }
}
#[cfg(not(target_os = "linux"))]
fn pin_to(_cpu: usize) {}

fn finish(code: i32, msg: &str) -> ! {
    println!("{msg}");
    std::process::exit(code)
}

/// Declarations grouped by namespace (see `main`), from the canonical
/// name chains (milestone 24); the order only steers cache reuse, any
/// order is sound.
fn ns_order_fast<'f>(env: &env::Env<'f>) -> Vec<u32> {
    use susz::canon::Part;
    let nd = env.decl_rows.len();
    let cn = &env.st.canon;
    let src = env.bytes;
    // a component as a key: string bytes, or a number (tagged apart)
    #[derive(Hash, PartialEq, Eq, Clone, Copy)]
    enum K<'a> {
        S(&'a [u8]),
        N(u64),
    }
    let key_of = |c: u32| -> K<'f> { match cn.part(src, c) { Part::Str(b) => K::S(b), Part::Num(k) => K::N(k) } };
    // K02: the group key of declaration d (first two components of its
    // namespace), computed on several threads; the group ids are then
    // given in order of first appearance on one thread, so the order is
    // exactly the one-thread order
    let key = |d: usize, chain: &mut Vec<u32>, pcs: &mut Vec<K<'f>>| -> (K<'f>, Option<K<'f>>) {
        let (first, _) = env.decl_rows[d];
        let raw = env.consts[first as usize].name;
        chain.clear();
        if (raw as usize) < env.st.name_canon.len() {
            let mut x = env.st.name_canon[raw as usize];
            while x != susz::canon::ANON {
                chain.push(x);
                x = cn.pre[x as usize];
            }
        }
        // the dotted form's pieces: string components split at '.' too
        pcs.clear();
        for &c in chain.iter().rev() {
            match key_of(c) {
                K::S(b) => pcs.extend(b.split(|&ch| ch == b'.').map(K::S)),
                k => pcs.push(k),
            }
        }
        if pcs.is_empty() {
            pcs.push(K::S(b"[anonymous]"));
        }
        let mut comps: &[K<'f>] = pcs;
        if comps.len() >= 2 && comps[0] == K::S(b"_private") {
            // `_private.<module>.0.<name>`: the name after the first lone 0
            let rest = &comps[1..];
            let z = (1..rest.len().saturating_sub(1)).find(|&i| matches!(rest[i], K::N(0) | K::S(b"0")));
            comps = match z { Some(i) => &rest[i + 1..], None => rest };
        }
        let ns = if comps.len() > 1 { &comps[..comps.len() - 1] } else { comps };
        match ns.len() {
            0 => (K::S(b""), None),
            1 => (ns[0], None),
            _ => (ns[0], Some(ns[1])),
        }
    };
    let t0 = Instant::now();
    let threads = env::LOAD_THREADS.load(Ordering::Relaxed).clamp(1, 64);
    let threads = if nd < 1 << 14 { 1 } else { threads };
    // per chunk: each declaration's local group id, and the chunk's groups
    // in order of first appearance in the chunk
    type Key<'f> = (K<'f>, Option<K<'f>>);
    let c = nd.div_ceil(threads).max(1);
    let mut lgid: Vec<u32> = vec![0; nd];
    let chunk_groups: Vec<Vec<Key<'f>>> = std::thread::scope(|sc| {
        let key = &key;
        let hs: Vec<_> = lgid
            .chunks_mut(c)
            .enumerate()
            .map(|(ci, ch)| {
                sc.spawn(move || {
                    let (mut chain, mut pcs) = (Vec::new(), Vec::new());
                    let mut local: rustc_hash::FxHashMap<Key<'f>, u32> = Default::default();
                    let mut order: Vec<Key<'f>> = Vec::new();
                    for (i, g) in ch.iter_mut().enumerate() {
                        let k = key(ci * c + i, &mut chain, &mut pcs);
                        let n = order.len() as u32;
                        *g = *local.entry(k).or_insert_with(|| {
                            order.push(k);
                            n
                        });
                    }
                    order
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().expect("order thread")).collect()
    });
    let t1 = t0.elapsed().as_secs_f64();
    // global ids in order of first appearance: chunks in file order, a
    // chunk's groups in their order of first appearance in it
    let mut groups: rustc_hash::FxHashMap<Key<'f>, u32> = Default::default();
    let mut gid: Vec<u32> = Vec::with_capacity(nd);
    for (ci, cg) in chunk_groups.iter().enumerate() {
        let map: Vec<u32> = cg
            .iter()
            .map(|k| {
                let n = groups.len() as u32;
                *groups.entry(*k).or_insert(n)
            })
            .collect();
        let lo = ci * c;
        let hi = (lo + c).min(nd);
        gid.extend(lgid[lo..hi].iter().map(|&l| map[l as usize]));
    }
    let t2 = t0.elapsed().as_secs_f64();
    if std::env::var_os("K02_TIMES").is_some() { eprintln!("K02 order keys {t1:.3} groups {t2:.3} ({} groups)", groups.len()); }
    // stable counting sort by group (groups in order of first appearance)
    let ng = groups.len();
    let mut start = vec![0u32; ng + 1];
    for &g in &gid {
        start[g as usize + 1] += 1;
    }
    for i in 0..ng {
        start[i + 1] += start[i];
    }
    let mut out = vec![0u32; nd];
    for (d, &g) in gid.iter().enumerate() {
        out[start[g as usize] as usize] = d as u32;
        start[g as usize] += 1;
    }
    out
}

/// K02: the one-thread order (kept to check the parallel one: K02_ORDER_CHECK)
fn ns_order_serial(env: &env::Env) -> Vec<u32> {
    use susz::canon::Part;
    let nd = env.decl_rows.len();
    let cn = &env.st.canon;
    let src = env.bytes;
    // a component as a key: string bytes, or a number (tagged apart)
    #[derive(Hash, PartialEq, Eq, Clone, Copy)]
    enum K<'a> {
        S(&'a [u8]),
        N(u64),
    }
    let key_of = |c: u32| -> K { match cn.part(src, c) { Part::Str(b) => K::S(b), Part::Num(k) => K::N(k) } };
    let mut groups: rustc_hash::FxHashMap<(K, Option<K>), u32> = Default::default();
    let mut gid: Vec<u32> = Vec::with_capacity(nd);
    let mut chain: Vec<u32> = Vec::new();
    let mut pcs: Vec<K> = Vec::new();
    for d in 0..nd {
        let (first, _) = env.decl_rows[d];
        let raw = env.consts[first as usize].name;
        chain.clear();
        if (raw as usize) < env.st.name_canon.len() {
            let mut x = env.st.name_canon[raw as usize];
            while x != susz::canon::ANON {
                chain.push(x);
                x = cn.pre[x as usize];
            }
        }
        // the dotted form's pieces: string components split at '.' too
        pcs.clear();
        for &c in chain.iter().rev() {
            match key_of(c) {
                K::S(b) => pcs.extend(b.split(|&ch| ch == b'.').map(K::S)),
                k => pcs.push(k),
            }
        }
        if pcs.is_empty() {
            pcs.push(K::S(b"[anonymous]"));
        }
        let mut comps: &[K] = &pcs;
        if comps.len() >= 2 && comps[0] == K::S(b"_private") {
            // `_private.<module>.0.<name>`: the name after the first lone 0
            let rest = &comps[1..];
            let z = (1..rest.len().saturating_sub(1)).find(|&i| matches!(rest[i], K::N(0) | K::S(b"0")));
            comps = match z { Some(i) => &rest[i + 1..], None => rest };
        }
        let ns = if comps.len() > 1 { &comps[..comps.len() - 1] } else { comps };
        let k = match ns.len() {
            0 => (K::S(b""), None),
            1 => (ns[0], None),
            _ => (ns[0], Some(ns[1])),
        };
        let n = groups.len() as u32;
        gid.push(*groups.entry(k).or_insert(n));
    }
    // stable counting sort by group (groups in order of first appearance)
    let ng = groups.len();
    let mut start = vec![0u32; ng + 1];
    for &g in &gid {
        start[g as usize + 1] += 1;
    }
    for i in 0..ng {
        start[i + 1] += start[i];
    }
    let mut out = vec![0u32; nd];
    for (d, &g) in gid.iter().enumerate() {
        out[start[g as usize] as usize] = d as u32;
        start[g as usize] += 1;
    }
    out
}

/// Milestone 26: the names after `--only`, split at commas, empty ones
/// dropped; `None` without the flag, no names when it ends the arguments
/// (Pestka's `onlyOf`).
fn only_of(args: &[String]) -> Option<Vec<String>> {
    let i = args.iter().position(|a| a == "--only")?;
    Some(match args.get(i + 1) {
        None => Vec::new(),
        Some(n) => n.split(',').filter(|s| !s.is_empty()).map(String::from).collect(),
    })
}

/// The arguments without `--only` and the names after it (Pestka's
/// `withoutOnly`).
fn without_only(args: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--only" {
            i += 2;
        } else {
            out.push(args[i].clone());
            i += 1;
        }
    }
    out
}

/// Milestone 26: what a subset check asks for, found in INDEX (decoded
/// whole and checked by the susz crate: sizes, front coding, strictly
/// increasing keys, declarations in range). `Foo.*` asks for every name
/// under `Foo` (a longer key starting with Foo's: components delimit
/// themselves). The targets in increasing order, and what MAIN is to be
/// held to; Err is the verdict line and exit code.
fn plan_of(bytes: &[u8], path: &str, names: &[String]) -> Result<(env::Part, Vec<u32>), (i32, String)> {
    let file = susz::read::File::open(bytes).map_err(|f| {
        if f.class.declines() { (2, format!("declined: {f}")) } else { (1, format!("rejected: {f}")) }
    })?;
    let at = file.section(susz::format::SEC_INDEX).map_or(0, |s| s.offset);
    let ix = match susz::index::parse(&file) {
        Ok(ix) => ix,
        Err(susz::index::IndexError::Absent) => {
            return Err((2, format!("declined: {path} has no INDEX section, which checking part of a file needs: pack it without --no-index")))
        }
        Err(susz::index::IndexError::Invalid(m)) => return Err((2, format!("index invalid: INDEX @ {at}: {m}"))),
        Err(e) => return Err((2, format!("index invalid: INDEX @ {at}: {e}"))),
    };
    // (text, key, under)
    let asks: Vec<(&str, Vec<u8>, bool)> = names
        .iter()
        .map(|n| match n.strip_suffix(".*") {
            Some(p) => (n.as_str(), susz::index::key_of_dotted(p), true),
            None => (n.as_str(), susz::index::key_of_dotted(n), false),
        })
        .collect();
    let mut hit = vec![false; asks.len()];
    let mut by_decl: rustc_hash::FxHashMap<u32, Vec<Vec<u8>>> = Default::default();
    let _ = ix.try_for_each(|k, d| -> Result<(), ()> {
        let mut any = false;
        for (j, (_, key, under)) in asks.iter().enumerate() {
            let yes = if *under { k.len() > key.len() && k.starts_with(key) } else { k == key.as_slice() };
            if yes {
                hit[j] = true;
                any = true;
            }
        }
        if any {
            by_decl.entry(d).or_default().push(k.to_vec());
        }
        Ok(())
    });
    let miss: Vec<&str> = asks.iter().zip(&hit).filter(|(_, h)| !**h).map(|(a, _)| a.0).collect();
    if !miss.is_empty() {
        return Err((2, format!("declined: not found: {}: the file's INDEX declares no such name", miss.join(", "))));
    }
    let mut targets: Vec<u32> = by_decl.keys().copied().collect();
    targets.sort_unstable();
    let up_to = targets.last().map_or(0, |&t| t + 1);
    let marks = by_decl.into_iter().map(|(d, keys)| (d, (ix.entries[d as usize], keys))).collect();
    Ok((env::Part { up_to, marks, index_at: at }, targets))
}

/// Unsafe or partial: Gruszka keeps it out of the logical environment.
fn unsafe_or_partial(c: &env::ConstInfo) -> bool {
    match &c.kind {
        env::CKind::Defn { safety, .. } => *safety != 0,
        _ => c.is_unsafe(),
    }
}

/// Milestone 37: `--progress[=SECS]` anywhere in the arguments: a progress
/// line on stderr every SECS seconds (default 10); None when absent.
fn progress_of(args: &[String]) -> (Option<u64>, Vec<String>) {
    let mut every = None;
    let mut rest = Vec::new();
    for a in args {
        if a == "--progress" {
            every = Some(10);
        } else if let Some(v) = a.strip_prefix("--progress=") {
            match v.parse::<u64>() {
                Ok(n) if n > 0 => every = Some(n),
                _ => {
                    eprintln!("--progress=SECS: SECS is a whole number of seconds, at least 1");
                    std::process::exit(2);
                }
            }
        } else {
            rest.push(a.clone());
        }
    }
    (every, rest)
}

/// This process's resident memory now, in bytes (0 where unknown).
fn rss_now() -> u64 {
    #[cfg(target_os = "macos")]
    {
        // proc_pid_rusage: ri_phys_footprint, as `time -l` reports it
        unsafe extern "C" {
            fn proc_pid_rusage(pid: i32, flavor: i32, buf: *mut u64) -> i32;
        }
        let mut b = [0u64; 64];
        // RUSAGE_INFO_V0: ri_phys_footprint is the 9th u64 (after the uuid)
        if unsafe { proc_pid_rusage(std::process::id() as i32, 0, b.as_mut_ptr()) } == 0 {
            return b[9];
        }
        0
    }
    #[cfg(target_os = "linux")]
    {
        std::fs::read_to_string("/proc/self/statm")
            .ok()
            .and_then(|s| s.split_whitespace().nth(1).and_then(|x| x.parse::<u64>().ok()))
            .map_or(0, |p| p * 4096)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        0
    }
}

fn main() {
    let t_start = Instant::now();
    let k02t = std::env::var_os("K02_TIMES").is_some();
    if std::env::var_os("K02_THP").is_some() {
        BIG_THP.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    let gz_time = k02t || std::env::var_os("GZ_TIME").is_some();
    let (progress, args) = progress_of(&std::env::args().collect::<Vec<_>>());
    // milestone 26: `--only NAME[,NAME...]` anywhere, as Pestka takes it
    let only_names: Option<Vec<String>> = only_of(&args[1..]);
    let args: Vec<String> = match &only_names {
        Some(_) => std::iter::once(args[0].clone()).chain(without_only(&args[1..])).collect(),
        None => args,
    };
    if only_names.is_some() && !(2..=3).contains(&args.len()) {
        finish(2, "declined: usage: gruszka --only NAME[,NAME...] FILE.susz [WORKERS]; NAME may be Foo.* for every name under Foo");
    }
    if args.len() < 2 {
        eprintln!("usage: gruszka [--progress[=SECS]] FILE [WORKERS] | gruszka --only NAME[,NAME...] FILE.susz [WORKERS]");
        std::process::exit(2);
    }
    let path = &args[1];
    if only_names.as_ref().is_some_and(|n| n.is_empty()) {
        finish(2, "declined: --only needs at least one name");
    }
    // milestone 24 (owner's decision): all cores by default; an explicit
    // WORKERS argument wins
    let workers: usize = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
        .max(1);
    // SK_DECL_INSTR=1: per declaration, this thread's instructions retired
    // and nanoseconds, on stderr:
    // DI<TAB>index<TAB>name<TAB>instructions<TAB>ns<TAB>counters
    let decl_instr = std::env::var("SK_DECL_INSTR").is_ok();
    let mut mapped = false;
    const NOT_SUSZ: &str =
        "declined: --only checks part of a Susz file, by its INDEX: pack the export first (susz pack FILE.ndjson FILE.susz)";
    // K01: an export is packed in this process: a file named .ndjson, or
    // any file whose first byte is '{' (a Susz file starts with its magic)
    let is_ndjson = path.ends_with(".ndjson") || {
        use std::io::Read;
        let mut b = [0u8; 1];
        std::fs::File::open(path).and_then(|mut f| f.read_exact(&mut b)).is_ok() && b[0] == b'{'
    };
    if only_names.is_some() && is_ndjson {
        finish(2, NOT_SUSZ);
    }
    // K01: where the packer's MAIN segments start (for the parallel load)
    let mut seg_starts: Vec<susz::read::SegStart> = Vec::new();
    let bytes: &'static [u8] = if is_ndjson {
        // milestone 24: packed on as many threads as there are workers
        let opts = susz::pack::Options { index: false, threads: workers };
        match susz::pack::pack_to_vec_segs(path, &opts) {
            Ok((v, _, ss)) => {
                seg_starts = ss;
                Box::leak(v.into_boxed_slice())
            }
            Err(e) => match e.fault {
                // F06 fix-039: the official export parser is more lenient than the packer (sparse/non-dense indices,
                // unknown keys, duplicate records, ...), so a format-level fault is a decline, never a verdict
                susz::pack::Fault::Invalid => finish(2, &format!("declined: the packer finds the export invalid (format level; the official parser may accept it): {}", e.msg)),
                susz::pack::Fault::Cannot => finish(2, &format!("declined: cannot pack: {}", e.msg)),
            },
        }
    } else {
        // Y3-1: a .susz file does not record whether the source export had nondep lets: assume it may have
        susz::pack::ANY_NONDEP_LET.store(true, Ordering::SeqCst);
        match unsafe { susz::open_mmap(path) } {
            Ok(m) => {
                let m: &'static susz::Mapped = Box::leak(Box::new(m));
                mapped = m.is_mapped();
                m
            }
            Err(e) => finish(2, &format!("declined: cannot open {path}: {e}")),
        }
    };
    if gz_time { eprintln!("T bytes {:.3}", t_start.elapsed().as_secs_f64()); }
    env::LOAD_THREADS.store(workers, Ordering::Relaxed);
    if k02t { eprintln!("K02 t opened {:.3}", t_start.elapsed().as_secs_f64()); }
    // milestone 26: a subset check finds its targets in INDEX first
    let part: Option<(env::Part, Vec<u32>)> = only_names.as_ref().map(|names| {
        if !bytes.starts_with(&susz::format::MAGIC) {
            finish(2, NOT_SUSZ);
        }
        match plan_of(bytes, path, names) {
            Ok(p) => p,
            Err((code, m)) => finish(code, &m),
        }
    });
    // K01: the whole file in parallel when the packer said where MAIN's
    // segments start (GZ_SEQ_LOAD=1: never); the sequential load gives the
    // exact result whenever the parallel one gives up
    let par = if part.is_none() && !seg_starts.is_empty() && std::env::var_os("GZ_SEQ_LOAD").is_none() {
        let r = env::load_par(bytes, &seg_starts, workers);
        if r.is_none() {
            eprintln!("note: parallel load gave up; loading sequentially");
        }
        r
    } else {
        None
    };
    if gz_time { eprintln!("T par-load {:.3} {}", t_start.elapsed().as_secs_f64(), par.is_some()); }
    // K01 GZ_VERIFY_LOAD=1: the parallel load compared with the sequential one
    if std::env::var_os("GZ_VERIFY_LOAD").is_some() {
        if let Some(Ok(e)) = &par {
            let f1 = e.fingerprint();
            let e2 = env::load_part(bytes, None);
            match e2 {
                Ok(e2) => {
                    let f2 = e2.fingerprint();
                    let same = f1 == f2;
                    for (a, b) in f1.iter().zip(&f2) {
                        if a != b {
                            eprintln!("VERIFY differs: {} {:x} {:x}", a.0, a.1, b.1);
                        }
                    }
                    eprintln!("VERIFY parallel load {}", if same { "identical" } else { "DIFFERS" });
                    if !same {
                        std::process::exit(3);
                    }
                    std::mem::forget(e2);
                }
                Err(_) => {
                    eprintln!("VERIFY DIFFERS: sequential load failed");
                    std::process::exit(3);
                }
            }
        } else {
            eprintln!("VERIFY: no parallel load to compare");
        }
    }
    let loaded = match par {
        Some(r) => r,
        None => env::load_part(bytes, part.as_ref().map(|p| &p.0)),
    };
    let env = match loaded {
        Ok(e) => e,
        // F06 fix-039: load-level (structural) faults are declines too; only the kernel's own checks reject
        Err(env::LoadError::Reject(m)) => finish(2, &format!("declined: load-level fault (not a kernel verdict): {m}")),
        Err(env::LoadError::Decline(m)) => finish(2, &format!("declined: {m}")),
        Err(env::LoadError::IndexInvalid(m)) => finish(2, &format!("index invalid: {m}")),
    };
    let env: &'static env::Env<'static> = Box::leak(Box::new(env));
    if k02t { eprintln!("K02 t loaded {:.3}", t_start.elapsed().as_secs_f64()); }
    // milestone 18: block arenas after MAIN in the term range, two per worker
    // (milestone 35: and the two overflow arenas before them; fewer workers
    // when their arenas do not fit)
    let workers = match env::region().layout(env.main.len(), workers) {
        Ok(w) => {
            if w < workers {
                eprintln!("note: {w} workers (the block arenas of {workers} do not fit)");
            }
            w
        }
        Err(m) => finish(2, &format!("declined: {m}")),
    };
    // the MAIN pages were copied into columns: let them go
    let remap_on = mapped;
    if remap_on && !remap(bytes, path) {
        eprintln!("note: could not map the file again");
    }
    let nd = env.decl_rows.len();
    if k02t { eprintln!("K02 t layout+remap {:.3}", t_start.elapsed().as_secs_f64()); }
    tc::set_workers(workers);
    let shared: &'static tc::Shared = Box::leak(Box::new(tc::Shared::new(env.main.len(), env.consts.len())));
    let first_fail: &'static AtomicU32 = Box::leak(Box::new(AtomicU32::new(u32::MAX)));
    let status: Vec<AtomicU8> = (0..nd).map(|_| AtomicU8::new(0)).collect();
    let msgs: Mutex<Vec<(u32, String)>> = Mutex::new(Vec::new());
    // the order declarations are handed out in: by default grouped by
    // namespace (first two components of the namespace; a declaration goes
    // with the names under it), groups in order of first appearance, file
    // order inside a group (milestone 16; SK_ORDER=ns names it too); with
    // SK_ORDER=file in file order. The kept caches are stamped with
    // declaration indices, so any order is sound.
    if k02t { eprintln!("K02 t shared {:.3}", t_start.elapsed().as_secs_f64()); }
    let order: Vec<u32> = match std::env::var("SK_ORDER").as_deref() {
        Ok("file") => (0..nd as u32).collect(),
        Ok("ns") | Err(_) => {
            let o = ns_order_fast(env);
            if std::env::var_os("K02_ORDER_CHECK").is_some() {
                let o1 = ns_order_serial(env);
                eprintln!("K02 order check: {}", if o1 == o { "same" } else { "DIFFERENT" });
            }
            o
        }
        Ok(o) => { eprintln!("SK_ORDER={o}: expected file or ns"); std::process::exit(2) }
    };
    // milestone 26: a subset check checks the targets, and before the last
    // of them the inductive blocks and the quotient package (reduction
    // relies on the rules they add). Every other declaration read is
    // admitted as stated (type and value unchecked, a theorem's proof not
    // decoded unless a check unfolds it); unsafe and partial ones are
    // skipped. Universe parameters must still be distinct; names are new
    // by the reader.
    let mut unchecked = 0usize;
    let order: Vec<u32> = match &part {
        None => order,
        Some((_, targets)) => {
            println!("subset: {} declarations asked for; the first {nd} declarations of the file read", targets.len());
            for &t in targets {
                let c = &env.consts[env.decl_rows[t as usize].0 as usize];
                if unsafe_or_partial(c) {
                    finish(2, &format!("declined: {} is unsafe or partial, which Gruszka does not check", env.name_str(c.name)));
                }
            }
            let mut sel = vec![false; nd];
            for &t in targets {
                sel[t as usize] = true;
            }
            for d in 0..nd {
                if sel[d] {
                    continue;
                }
                let c = &env.consts[env.decl_rows[d].0 as usize];
                let skipped = unsafe_or_partial(c);
                if !skipped && matches!(c.kind, env::CKind::Quot { .. } | env::CKind::Induct { .. }) {
                    sel[d] = true;
                    continue;
                }
                // admitted (counted) or skipped (unsafe, partial: not counted)
                unchecked += !skipped as usize;
                if env.decl_dup_params[d] {
                    status[d].store(ST_REJECT, Ordering::Relaxed);
                    msgs.lock().unwrap().push((d as u32, "universe parameters named twice".into()));
                    first_fail.fetch_min(d as u32, Ordering::Relaxed);
                } else {
                    status[d].store(ST_OK, Ordering::Relaxed);
                }
            }
            order.into_iter().filter(|&d| sel[d as usize]).collect()
        }
    };
    if k02t { eprintln!("K02 t order {:.3}", t_start.elapsed().as_secs_f64()); }
    let no = order.len();
    const CHUNK: usize = 32;
    // milestone 24: each worker starts on its own contiguous part of the
    // order and takes chunks from its front; a worker whose part is empty
    // takes the back half of the largest part left (neighbours in namespace
    // order share lemmas: mathlib w8 -5% instructions against chunks dealt
    // round robin)
    let parts: Mutex<Vec<(usize, usize)>> =
        Mutex::new((0..workers).map(|i| (no * i / workers, no * (i + 1) / workers)).collect());
    let take = |wi: usize| -> Option<(usize, usize)> {
        let mut p = parts.lock().unwrap();
        if p[wi].0 >= p[wi].1 {
            let (mut best, mut len) = (usize::MAX, 0);
            for (i, &(lo, hi)) in p.iter().enumerate() {
                if hi - lo > len {
                    (best, len) = (i, hi - lo);
                }
            }
            if best == usize::MAX {
                return None;
            }
            let (lo, hi) = p[best];
            let mid = if len <= CHUNK { lo } else { lo + len / 2 };
            p[best].1 = mid;
            p[wi] = (mid, hi);
        }
        let (lo, hi) = p[wi];
        let e = (lo + CHUNK).min(hi);
        p[wi].0 = e;
        Some((lo, e))
    };
    // milestone 16: a declaration that runs longer than this hands the rest
    // of its chunk to the other workers (`spill`), so a few heavy
    // declarations next to each other (reachability's `decide` proofs) do
    // not run one after another on one worker
    const SPILL_MS: u128 = 20;
    let spill: Mutex<Vec<u32>> = Mutex::new(Vec::new());
    // milestone 42: GRUSZKA_STACK_MB (the deep vectors run at 16 MiB)
    let stack: usize = std::env::var("GRUSZKA_STACK_MB")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&m| (4..=1 << 20).contains(&m))
        .map_or(1 << 30, |m| m << 20);
    let stack_limit = stack - (stack / 4).min(64 << 20);
    // per worker: declaration being checked (u32::MAX: none)
    let running: Vec<AtomicU32> = (0..workers).map(|_| AtomicU32::new(u32::MAX)).collect();
    // milestone 37: when each worker's current declaration began (ms since
    // `t_run`), for the progress line
    let t_run = Instant::now();
    let began: Vec<std::sync::atomic::AtomicU64> = (0..workers).map(|_| std::sync::atomic::AtomicU64::new(0)).collect();
    let done = std::sync::atomic::AtomicUsize::new(0);
    // milestone 43: declarations not checked because an earlier one (in
    // file order) failed, for the progress line: on AWS a decline left 31
    // of 32 workers idle with 73% of CFSG "to do" and no word of why
    let cancelled = std::sync::atomic::AtomicUsize::new(0);
    let all_done = std::sync::atomic::AtomicBool::new(false);
    // milestone 37: SK_MEM_REPORT=1: each worker's held bytes by group at its end
    let mem_report = std::env::var_os("SK_MEM_REPORT").is_some();

    if k02t { eprintln!("K02 t prepared {:.3}", t_start.elapsed().as_secs_f64()); }
    // K02: K02_PIN=1 pins worker i to the i-th CPU of the allowed set, ordered so that
    // consecutive workers share a last-level cache (see `pin_order`)
    let pin_cpus: Vec<usize> = if std::env::var_os("K02_PIN").is_some() { pin_order() } else { Vec::new() };
    if k02t && !pin_cpus.is_empty() { eprintln!("K02 pin {:?}", pin_cpus); }
    let pin_cpus = &pin_cpus;
    std::thread::scope(|s| {
        let mut remap_thread = None;
        // milestone 37: `--progress`: declarations checked out of those to
        // check, memory, and the longest-running declarations in flight
        let mut progress_thread = None;
        if let Some(every) = progress {
            let (all_done, running, began, done, cancelled) = (&all_done, &running, &began, &done, &cancelled);
            progress_thread = Some(s.spawn(move || {
                let mut next = every;
                while !all_done.load(Ordering::Relaxed) {
                    let left = std::time::Duration::from_secs(next).saturating_sub(t_run.elapsed());
                    if !left.is_zero() {
                        std::thread::park_timeout(left);
                        continue;
                    }
                    next += every;
                    let now = t_run.elapsed().as_millis() as u64;
                    let mut fl: Vec<(u64, u32)> = Vec::new();
                    for (r, b) in running.iter().zip(began) {
                        let d = r.load(Ordering::Relaxed);
                        if d != u32::MAX {
                            fl.push((now.saturating_sub(b.load(Ordering::Relaxed)), d));
                        }
                    }
                    fl.sort_unstable_by(|a, b| b.cmp(a));
                    let longest: Vec<String> = fl
                        .iter()
                        .take(3)
                        .map(|&(ms, d)| {
                            let (first, _) = env.decl_rows[d as usize];
                            format!("{} ({:.1} s)", env.name_str(env.consts[first as usize].name), ms as f64 / 1000.0)
                        })
                        .collect();
                    let n = done.load(Ordering::Relaxed);
                    let nc = cancelled.load(Ordering::Relaxed);
                    eprintln!(
                        "progress: {:.0} s, {n}/{no} declarations ({:.1}%){}, {} workers busy, {:.2} GB; longest: {}",
                        now as f64 / 1000.0,
                        100.0 * n as f64 / no.max(1) as f64,
                        if nc > 0 { format!(", {nc} not checked after a failure") } else { String::new() },
                        fl.len(),
                        rss_now() as f64 / 1e9,
                        if longest.is_empty() { "-".to_string() } else { longest.join(", ") }
                    );
                }
            }));
        }
        if remap_on {
            // proof blocks are read from the mapping as declarations need
            // them: map it again once a second, so pages read once do not
            // stay resident for the rest of the run
            // (milestone 24: parked, and woken when the workers are done,
            // instead of polling every 50 ms: the run ended up to 50 ms late)
            let all_done = &all_done;
            remap_thread = Some(s.spawn(move || {
                let mut last = Instant::now();
                while !all_done.load(Ordering::Relaxed) {
                    std::thread::park_timeout(std::time::Duration::from_millis(1000).saturating_sub(last.elapsed()));
                    if !all_done.load(Ordering::Relaxed) && last.elapsed().as_millis() >= 1000 {
                        remap(bytes, path);
                        last = Instant::now();
                    }
                }
            }));
        }
        let mut handles = Vec::new();
        for wi in 0..workers {
            let (status, msgs, running, order, spill, take) = (&status, &msgs, &running, &order, &spill, &take);
            let (began, done, cancelled) = (&began, &done, &cancelled);
            let h = std::thread::Builder::new()
                .stack_size(stack)
                .spawn_scoped(s, move || {
                    if let Some(c) = pin_cpus.get(wi % pin_cpus.len().max(1)) {
                        pin_to(*c);
                    }
                    let mut w = Worker::new(env, shared, first_fail, stack_limit);
                    if tc::KNOBS && wi == 0 {
                        w.show_consts();
                    }
                    let mut batch: Vec<u32> = Vec::with_capacity(CHUNK);
                    loop {
                        // spilled declarations first (one at a time), then a new chunk
                        batch.clear();
                        if let Some(d) = spill.lock().unwrap().pop() {
                            batch.push(d);
                        } else {
                            let Some((start, end)) = take(wi) else {
                                // others may still spill: wait while any worker runs
                                if running.iter().all(|r| r.load(Ordering::Relaxed) == u32::MAX) && spill.lock().unwrap().is_empty() {
                                    break;
                                }
                                std::thread::sleep(std::time::Duration::from_millis(1));
                                continue;
                            };
                            batch.extend_from_slice(&order[start..end]);
                        }
                        let mut bi = 0;
                        while bi < batch.len() {
                            let d32 = batch[bi];
                            bi += 1;
                            let d = d32 as usize;
                            if d32 > first_fail.load(Ordering::Relaxed) {
                                status[d].store(ST_CANCEL, Ordering::Relaxed);
                                cancelled.fetch_add(1, Ordering::Relaxed);
                                continue;
                            }
                            began[wi].store(t_run.elapsed().as_millis() as u64, Ordering::Relaxed);
                            running[wi].store(d32, Ordering::Relaxed);
                            let t0 = Instant::now();
                            let st0 = if decl_instr { Some((w.stats.clone(), w.ticks)) } else { None };
                            let i0 = if decl_instr { instr_now() } else { 0 };
                            let mut r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| w.check_decl(d32)));
                            // milestone 35: a block did not fit the worker's arena: the
                            // declaration runs again in the overflow arenas, whose size
                            // does not depend on the number of workers
                            if w.arena_full && !matches!(r, Ok(Ok(()) | Err(Stop::Cancel))) {
                                if r.is_err() {
                                    w.after_panic();
                                }
                                let mut g = env::region().big.lock().unwrap_or_else(|e| e.into_inner());
                                let big = g.as_mut().expect("overflow arenas taken before the layout");
                                w.swap_big(big);
                                r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| w.check_decl(d32)));
                                if r.is_err() {
                                    w.after_panic();
                                }
                                // a block left out (a theorem not unfolded) may have
                                // led to a rejection: declined
                                if w.arena_full && matches!(r, Ok(Err(Stop::Reject))) {
                                    r = Ok(tc::decline("the block arena is full"));
                                }
                                w.swap_big(big);
                                w.stats.big_runs += 1;
                            }
                            if decl_instr {
                                let i1 = instr_now();
                                let (first, _) = env.decl_rows[d];
                                let (a, tk0) = st0.unwrap();
                                let b = &w.stats;
                                eprintln!(
                                    "DI\t{d}\t{}\t{}\t{}\tticks {}\twhnf {}\tunfold {}\tdeq {}\tdeq_hit {}\tinfer {}\tinfer_calls {}\teval {}\tinterns {}\t{}",
                                    env.name_str(env.consts[first as usize].name),
                                    i1.wrapping_sub(i0),
                                    t0.elapsed().as_nanos(),
                                    w.ticks.wrapping_sub(tk0),
                                    b.whnf_misses - a.whnf_misses,
                                    b.unfolds - a.unfolds,
                                    b.defeq_calls - a.defeq_calls,
                                    b.defeq_cache_hits - a.defeq_cache_hits,
                                    b.infer_misses - a.infer_misses,
                                    b.infer_calls - a.infer_calls,
                                    b.evals - a.evals,
                                    b.interns - a.interns,
                                    w.table_report()
                                );
                            }
                            let (st, msg) = match r {
                                Ok(Ok(())) => (ST_OK, None),
                                Ok(Err(Stop::Reject)) => (ST_REJECT, Some(tc::stop_msg())),
                                Ok(Err(Stop::Decline)) => (ST_DECLINE, Some(tc::stop_msg())),
                                Ok(Err(Stop::Cancel)) => (ST_CANCEL, None),
                                Ok(Err(Stop::Budget)) => (ST_DECLINE, Some("probe budget escaped".into())),
                                Ok(Err(Stop::Deep)) => (ST_DECLINE, Some("deep whnf escaped".into())),
                                Ok(Err(Stop::Ground)) => (ST_DECLINE, Some("ground machine stop escaped".into())),
                                Ok(Err(Stop::DeepInfer)) => (ST_DECLINE, Some("deep inference escaped".into())),
                                Ok(Err(Stop::DeepDefeq)) => (ST_DECLINE, Some("deep comparison escaped".into())),
                                Err(p) => {
                                    w.after_panic();
                                    let m = p
                                        .downcast_ref::<String>()
                                        .cloned()
                                        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                                        .unwrap_or_default();
                                    (ST_DECLINE, Some(format!("internal error: {m}")))
                                }
                            };
                            if st == ST_REJECT || st == ST_DECLINE {
                                let before = first_fail.fetch_min(d32, Ordering::Relaxed);
                                let msg = msg.unwrap();
                                // milestone 43: with --progress, a failure is told when
                                // it happens (the run still waits for the declarations
                                // before it in the file, to name the first failure)
                                if progress.is_some() && d32 < before {
                                    let (first, _) = env.decl_rows[d];
                                    eprintln!(
                                        "progress: {} {}: {msg} (the declarations after it in the file are not checked)",
                                        if st == ST_REJECT { "rejected" } else { "declined" },
                                        env.name_str(env.consts[first as usize].name)
                                    );
                                }
                                msgs.lock().unwrap().push((d32, msg));
                            }
                            status[d].store(st, Ordering::Relaxed);
                            done.fetch_add(1, Ordering::Relaxed);
                            if t0.elapsed().as_millis() > SPILL_MS && bi < batch.len() {
                                // hand the rest over before this worker says it is idle
                                spill.lock().unwrap().extend(batch[bi..].iter().rev());
                                bi = batch.len();
                            }
                            running[wi].store(u32::MAX, Ordering::Relaxed);
                        }
                    }
                    if k02t { eprintln!("K02 worker {wi} done {:.3}", t_start.elapsed().as_secs_f64()); }
                    // milestone 24: the process exits after the verdict; freeing
                    // a worker's tables here only delayed it
                    w.dump_unfold_hist();
                    if mem_report {
                        eprintln!("MEM worker {wi}: {} deep_up {} ckpts {} late {}/{}", w.mem_report(), w.stats.deep_up, w.stats.ckpts, w.stats.late, w.stats.late_ld);
                    }
                    if tc::KNOBS && (w.stats.pfirst[0] > 0 || w.stats.ktrap[0] > 0 || w.stats.natwait[0] + w.stats.natwait[2] + w.stats.headprobe[0] + w.stats.dovetail[0] > 0) {
                        eprintln!("PFIRST worker {wi}: taken {} equal {} ktrap {} ticks {} natwait {:?} headprobe {:?} dovetail {:?}", w.stats.pfirst[0], w.stats.pfirst[1], w.stats.ktrap[0], w.stats.ktrap[1], w.stats.natwait, w.stats.headprobe, w.stats.dovetail);
                    }
                    if w.stats.big_runs > 0 {
                        eprintln!("note: worker {wi}: {} declarations ran in the overflow arenas", w.stats.big_runs);
                    }
                    std::mem::forget(w);
                })
                .expect("spawn");
            handles.push(h);
        }
        for h in handles {
            let _ = h.join();
        }
        all_done.store(true, Ordering::Relaxed);
        if let Some(h) = &remap_thread {
            h.thread().unpark();
        }
        if let Some(h) = &progress_thread {
            h.thread().unpark();
        }
    });
    #[cfg(feature = "cnt")]
    if decl_instr {
        for (i, c) in tc::THUNK_KINDS.iter().enumerate().take(1024) {
            let c = c.load(Ordering::Relaxed);
            if c > 0 {
                eprintln!("TK term kind {} head kind {} head val {} count {c}", i / 64, (i % 64) / 5, (i % 64) % 5);
            }
        }
        let made = tc::THUNK_KINDS[tc::P_MADE].load(Ordering::Relaxed).max(1);
        let mut tot = 0u64;
        for (k, name) in tc::P_NAMES_LIST.iter().enumerate() {
            let c = tc::THUNK_KINDS[tc::P_BASE + k].load(Ordering::Relaxed);
            if c > 0 {
                if tc::P_BASE + k != tc::P_MADE && tc::P_BASE + k != tc::P_INTERN_CALLS {
                    tot += c;
                }
                eprintln!("PR {:<20} {:>12} {:>7.3} per value", name, c, c as f64 / made as f64);
            }
        }
        eprintln!("PR {:<20} {:>12} {:>7.3} per value (values made {})", "TOTAL probes", tot, tot as f64 / made as f64, made);
    }
    if k02t { eprintln!("K02 t checked {:.3}", t_start.elapsed().as_secs_f64()); }
    let msgs = msgs.into_inner().unwrap();
    for d in 0..nd {
        match status[d].load(Ordering::Relaxed) {
            ST_OK => continue,
            ST_REJECT | ST_DECLINE => {
                let m = msgs.iter().find(|x| x.0 == d as u32).map(|x| x.1.clone()).unwrap_or_default();
                let (first, _) = env.decl_rows[d];
                let name = env.name_str(env.consts[first as usize].name);
                if status[d].load(Ordering::Relaxed) == ST_REJECT {
                    finish(1, &format!("rejected: {name}: {m}"));
                } else {
                    finish(2, &format!("declined: {name}: {m}"));
                }
            }
            _ => finish(2, &format!("declined: declaration {d} was not checked (internal)")),
        }
    }
    // milestone 26: a subset check never says accepted
    if let (Some(names), Some((_, targets))) = (&only_names, &part) {
        let n = targets.len();
        let many = if n == 1 { String::new() } else { format!("{n} declarations; ") };
        finish(0, &format!("checked: {} ({many}subset; {unchecked} earlier declarations admitted unchecked)", names.join(",")));
    }
    // PLAN R7: write canonical env SHA-256 digest before accepting when requested
    if let Ok(digest_path) = std::env::var("GRUSZKA_DIGEST_OUT") {
        if !digest_path.is_empty() {
            match env_digest::compute_and_write(env, workers, &digest_path) {
                Ok((hex, cnt, ms)) => eprintln!("[gruszka] env_sha256_v1={hex} ({cnt} consts, {ms} ms)"),
                Err(e) => finish(2, &format!("declined: env digest failed: {e}")),
            }
        }
    }
    finish(0, "accepted");
}
