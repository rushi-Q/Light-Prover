// Native core of lean4export (format 3.1.0): a C++ port of A01's "olex" (LINE A, lineA/tools/olex).
//
// It reads the imported .olean files directly (mmap of the compacted regions; Lean object layout from lean.h),
// builds the import order and the constant map exactly like `importModules` (post-order DFS, finalizeImport's
// duplicate-theorem rule), interns every expression of the export closure in parallel (structural classes =
// `Expr.eqv` classes: mdata stripped, binder names/infos ignored), and then replays lean4export's sequential
// `dumpConstant` DFS (getUsedConstants order, inductive blocks, getIdx post-order numbering, sorted JSON keys,
// Lean's Json string escaping), so the NDJSON written to stdout is byte-identical to the Lean implementation in
// Export.lean.  Only the speed differs: no Json objects, no structural `HashMap Expr` lookups, no per-expression
// `removeMData` maps, no re-traversal of already exported subterms in getUsedConstants, parallel interning.
//
// The metadata line is printed by Main.lean before this code runs.
#include "nostdcxx.h"  // first: no libstdc++ runtime dependency (see there)

#include <lean/lean.h>

#include <algorithm>
#include <atomic>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <mutex>
#include <string>
#include <unordered_map>
#include <vector>

#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <poll.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>

#include "osink.h"  // ordered output sink

namespace lean4export_native {

typedef const uint8_t* P;
static const uint32_t NONE = 0xffffffffu;
// F04: githash of the Lean toolchain this exporter is built with (lakefile passes -DF04_EXPECTED_GITHASH=Lean.githash);
// every imported .olean must carry exactly this githash, as the official reader requires.
#ifndef F04_EXPECTED_GITHASH
#error "F04_EXPECTED_GITHASH must be defined (lakefile.lean passes Lean.githash)"
#endif
static_assert(sizeof(F04_EXPECTED_GITHASH) == 41, "F04_EXPECTED_GITHASH must be a 40-character githash");

[[noreturn]] static void die(const std::string& msg) {
    fprintf(stderr, "lean4export (native): %s\n", msg.c_str());
    fflush(stderr);
    _exit(1);
}

// X01 fix (findings 010): strings that are not valid UTF-8 cannot be rendered byte-for-byte like the official exporter
// (Json.renderString decodes and re-encodes them); give up so the reference implementation writes them.
static bool utf8_ok(const uint8_t* p, size_t n) {
    size_t i = 0;
    while (i < n) {
        uint8_t c = p[i];
        if (c < 0x80) { i++; continue; }
        size_t k; uint32_t cp;
        if ((c & 0xE0) == 0xC0) { k = 1; cp = c & 0x1F; }
        else if ((c & 0xF0) == 0xE0) { k = 2; cp = c & 0x0F; }
        else if ((c & 0xF8) == 0xF0) { k = 3; cp = c & 0x07; }
        else return false;
        if (i + k >= n) return false;
        for (size_t j = 1; j <= k; j++) {
            uint8_t d = p[i + j];
            if ((d & 0xC0) != 0x80) return false;
            cp = (cp << 6) | (d & 0x3F);
        }
        if (k == 1 && cp < 0x80) return false;
        if (k == 2 && (cp < 0x800 || (cp >= 0xD800 && cp <= 0xDFFF))) return false;
        if (k == 3 && (cp < 0x10000 || cp > 0x10FFFF)) return false;
        i += k + 1;
    }
    return true;
}

static double now_s() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static double g_t0 = 0;
static bool g_verbose = false;
static double cpu_s(int who) {
    struct rusage ru;
    getrusage(who, &ru);
    return ru.ru_utime.tv_sec + ru.ru_utime.tv_usec * 1e-6 + ru.ru_stime.tv_sec + ru.ru_stime.tv_usec * 1e-6;
}
// THP diagnostics for the log (cheap): the system settings and the vmstat THP fault counters
static std::string read_small(const char* path) {
    char buf[8192];
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return std::string();
    ssize_t n = read(fd, buf, sizeof buf - 1);
    close(fd);
    if (n <= 0) return std::string();
    buf[n] = 0;
    return std::string(buf);
}
static std::string thp_setting(const char* path) {  // "[madvise]" part of "always [madvise] never"
    std::string s = read_small(path);
    size_t a = s.find('['), b = s.find(']');
    if (a == std::string::npos || b == std::string::npos || b < a) return "?";
    return s.substr(a + 1, b - a - 1);
}
static uint64_t vmstat_val(const std::string& vm, const char* key) {
    size_t k = vm.find(key);
    if (k == std::string::npos) return 0;
    uint64_t v = 0;
    for (size_t i = k + strlen(key); i < vm.size() && vm[i] >= '0' && vm[i] <= '9'; i++) v = v * 10 + (uint64_t)(vm[i] - '0');
    return v;
}
static uint64_t meminfo_kb(const std::string& mi, const char* key) {
    size_t k = mi.find(key);
    if (k == std::string::npos) return 0;
    size_t i = k + strlen(key);
    while (i < mi.size() && mi[i] == ' ') i++;
    uint64_t v = 0;
    for (; i < mi.size() && mi[i] >= '0' && mi[i] <= '9'; i++) v = v * 10 + (uint64_t)(mi[i] - '0');
    return v;
}
static std::string thp_faults() {
    std::string vm = read_small("/proc/vmstat");
    std::string mi = read_small("/proc/meminfo");
    return "thp_fault_alloc " + std::to_string(vmstat_val(vm, "\nthp_fault_alloc ")) + " thp_fault_fallback " +
           std::to_string(vmstat_val(vm, "\nthp_fault_fallback ")) + " system AnonHugePages " +
           std::to_string(meminfo_kb(mi, "\nAnonHugePages:") >> 10) + " MB, HugePages_Total " +
           std::to_string(meminfo_kb(mi, "\nHugePages_Total:")) + " (" + std::to_string(meminfo_kb(mi, "\nHugepagesize:")) + " kB)";
}
static void logf(const char* fmt, const std::string& s = "") {
    if (!g_verbose) return;
    fprintf(stderr, "lean4export (native) [%.2fs wall, %.2fs cpu, %.2fs thread] ", now_s() - g_t0, cpu_s(RUSAGE_SELF),
            cpu_s(RUSAGE_THREAD));
    fprintf(stderr, fmt, s.c_str());
    fputc('\n', stderr);
}

// ------------------------------------------------------------------------------------------------
// hashing
static inline uint64_t rotl(uint64_t x, int r) { return (x << r) | (x >> (64 - r)); }
static inline uint64_t hmix(uint64_t h, uint64_t v) { return (rotl(h, 5) ^ v) * 0x517cc1b727220a95ULL; }
static inline uint64_t hfin(uint64_t x) {
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return x;
}
static inline uint64_t hbytes(uint64_t h, const uint8_t* p, size_t n) {
    while (n >= 8) {
        uint64_t v;
        memcpy(&v, p, 8);
        h = hmix(h, v);
        p += 8;
        n -= 8;
    }
    if (n) {
        uint64_t v = 0;
        memcpy(&v, p, n);
        h = hmix(h, v ^ ((uint64_t)n << 56));
    }
    return h;
}

// ------------------------------------------------------------------------------------------------
// Lean object layout (lean.h): header 8 bytes (rc 4, cs_sz 2, m_other = #objs 1, m_tag 1), then fields
static const uint8_t T_ARRAY = 246;
static const uint8_t T_STRING = 249;
static const uint8_t T_MPZ = 250;
static inline uint8_t tag(P o) { return o[7]; }
static inline size_t nobjs(P o) { return o[6]; }
static inline uint64_t rawf(P o, size_t i) {
    uint64_t v;
    memcpy(&v, o + 8 + 8 * i, 8);
    return v;
}
static inline uint8_t sc_u8(P o, size_t off) { return o[8 + 8 * nobjs(o) + off]; }
static inline uint32_t sc_u32(P o, size_t off) {
    uint32_t v;
    memcpy(&v, o + 8 + 8 * nobjs(o) + off, 4);
    return v;
}
static inline uint64_t sc_u64(P o, size_t off) {
    uint64_t v;
    memcpy(&v, o + 8 + 8 * nobjs(o) + off, 8);
    return v;
}
static inline bool is_scalar(uint64_t r) { return (r & 1) == 1; }
static inline size_t str_len(P s) {  // bytes without the NUL
    uint64_t size;
    memcpy(&size, s + 8, 8);
    return (size_t)size - 1;
}
static inline P str_data(P s) { return s + 32; }
static inline size_t arr_size(P a) {
    uint64_t v;
    memcpy(&v, a + 8, 8);
    return (size_t)v;
}
static inline uint64_t arr_raw(P a, size_t i) {
    uint64_t v;
    memcpy(&v, a + 24 + 8 * i, 8);
    return v;
}

// ------------------------------------------------------------------------------------------------
// registry of the big mappings (olean files, tables, BigVecs): after the last output byte is written, the child
// releases them from all threads in parallel instead of leaving ~10-20 GB to the single-threaded exit_mmap of _exit
// (see fast_teardown).  Every mapping made with reg_mmap must be released with reg_munmap.
static std::mutex g_reg_mu;
static std::unordered_map<uintptr_t, size_t>* g_reg = nullptr;
static void* reg_mmap(size_t len, int prot, int flags, int fd) {
    void* m = mmap(nullptr, len, prot, flags, fd, 0);
    if (m != MAP_FAILED && len > 0) {
        std::lock_guard<std::mutex> g(g_reg_mu);
        if (!g_reg) g_reg = new std::unordered_map<uintptr_t, size_t>();
        (*g_reg)[(uintptr_t)m] = len;
    }
    return m;
}
static void reg_add(void* p, size_t len) {  // a mapping made elsewhere that stays mapped until exit
    if (!p || len == 0) return;
    std::lock_guard<std::mutex> g(g_reg_mu);
    if (!g_reg) g_reg = new std::unordered_map<uintptr_t, size_t>();
    (*g_reg)[(uintptr_t)p] = len;
}
static std::vector<std::pair<uintptr_t, size_t>>* g_holes = nullptr;  // munmapped sub-ranges of registered mappings
static void reg_munmap(void* p, size_t len) {
    {
        std::lock_guard<std::mutex> g(g_reg_mu);
        if (g_reg) {
            auto it = g_reg->find((uintptr_t)p);
            if (it != g_reg->end() && it->second == len) {
                g_reg->erase(it);
            } else {  // part of a registered mapping (or not registered at all): never touch it in the teardown
                if (!g_holes) g_holes = new std::vector<std::pair<uintptr_t, size_t>>();
                g_holes->push_back({(uintptr_t)p, len});
            }
        }
    }
    munmap(p, len);
}

// ------------------------------------------------------------------------------------------------
// big lazily-committed arrays
template <class T>
struct BigVec {
    T* p = nullptr;
    size_t cap = 0;
    void init(size_t c) {
        cap = c;
        void* m = reg_mmap(c * sizeof(T), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1);
        if (m == MAP_FAILED) die("BigVec mmap failed");
#ifdef MADV_HUGEPAGE
        madvise(m, c * sizeof(T), MADV_HUGEPAGE);
#endif
        p = (T*)m;
    }
    inline T get(uint32_t i) const { return p[i]; }
    inline void set(uint32_t i, const T& v) {
        if ((size_t)i >= cap) die("BigVec capacity exceeded");
        p[i] = v;
    }
};

// ------------------------------------------------------------------------------------------------
// sharded open-addressing hash map K -> uint32.  Slots store value+1 (0 = empty), tables come from anonymous
// mmaps (zero pages, committed lazily), so creating the maps costs nothing.
static void* zalloc(size_t bytes) {
    void* m = reg_mmap(bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1);
    if (m == MAP_FAILED) die("out of memory (mmap)");
    return m;
}
// big zero-initialized tables that are touched all over: transparent huge pages (THP is usually in `madvise` mode)
// cut the zero-fill page faults by 512x and the TLB misses of the random probes
// (2 MB aligned).  Note: a READ fault in such a region maps the huge zero page and a later write splits it into 4K
// pages, so tables that are probed before they are written must be pre-faulted by writes (prefault_huge below).
static const size_t HUGE_SZ = (size_t)2 << 20;
static void* zalloc_huge(size_t bytes) {
    bytes = (bytes + HUGE_SZ - 1) & ~(HUGE_SZ - 1);
    char* m = (char*)zalloc(bytes + HUGE_SZ);
    char* a = (char*)(((uintptr_t)m + HUGE_SZ - 1) & ~(uintptr_t)(HUGE_SZ - 1));
#ifdef MADV_HUGEPAGE
    madvise(a, bytes, MADV_HUGEPAGE);
#endif
    return a;
}
static size_t pow2_at_least(size_t n) {
    size_t c = 1;
    while (c < n) c <<= 1;
    return c;
}

// Per-thread blocks of fresh ids (ids stay unique but are not dense: the counter is an upper bound of all ids).
static const uint32_t ID_BLOCK = 256;
struct IdBlock {
    uint32_t next = 0, end = 0;
};
static inline uint32_t take_id(std::atomic<uint32_t>& ctr, IdBlock& b) {
    if (b.next == b.end) {
        uint32_t s = ctr.fetch_add(ID_BLOCK, std::memory_order_relaxed);
        if (s > 0xffffffffu - 2 * ID_BLOCK) die("too many ids");
        b.next = s;
        b.end = s + ID_BLOCK;
    }
    return b.next++;
}

// Lock-free open-addressing hash map K -> id over a fixed power-of-two slot array (never grows: callers size it
// from an upper bound of the number of keys).  A slot is 0 (empty) or (hash >> 32) << 32 | (id + 1); the key of an
// id lives in the caller's key store, written BEFORE the slot is published with a release CAS, so a reader that
// acquires the slot sees the key.  Concurrent inserts of equal keys: exactly one CAS wins, the losers see the
// winner's slot during the probe, compare its key and return the winner's id (their own fresh id is kept for reuse).
struct LFMap {
    std::atomic<uint64_t>* slots = nullptr;
    size_t mask = 0;
    std::atomic<size_t> count{0};  // inserted keys (updated in per-thread batches)
    size_t limit = 0;              // count > limit: the table is (estimated to be) too small
    void init(size_t nkeys_max) {
        size_t cap = pow2_at_least(nkeys_max + nkeys_max / 7 + 1024);  // load <= 7/8 even at the bound
        slots = (std::atomic<uint64_t>*)zalloc_huge(cap * sizeof(uint64_t));
        mask = cap - 1;
        limit = cap / 8 * 7;
    }
    // eq(id) compares the stored key of `id` with the probe key; fresh() allocates an id and stores the key
    template <class Eq, class Fresh>
    inline uint32_t get_or_insert(uint64_t h, Eq eq, Fresh fresh, uint32_t& spare, bool& inserted) {
        uint64_t tagv = h & 0xffffffff00000000ULL;
        size_t j = (size_t)h & mask;
        size_t probes = 0;
        while (true) {
            uint64_t v = slots[j].load(std::memory_order_acquire);
            if (v == 0) {
                if (spare == NONE) spare = fresh(NONE);
                else fresh(spare);  // re-store the key under the reused id
                uint64_t nv = tagv | ((uint64_t)spare + 1);
                if (slots[j].compare_exchange_strong(v, nv, std::memory_order_acq_rel, std::memory_order_acquire)) {
                    uint32_t id = spare;
                    spare = NONE;
                    inserted = true;
                    return id;
                }
                // lost the race for this slot: v is the winner's value, examine it below
            }
            if ((v & 0xffffffff00000000ULL) == tagv) {
                uint32_t id = (uint32_t)(v & 0xffffffffu) - 1;
                if (eq(id)) {
                    inserted = false;
                    return id;
                }
            }
            j = (j + 1) & mask;
            if (++probes > mask) die("internal: lock-free table full");
        }
    }
    template <class Eq>
    inline bool get(uint64_t h, Eq eq, uint32_t& out) const {
        uint64_t tagv = h & 0xffffffff00000000ULL;
        size_t j = (size_t)h & mask;
        size_t probes = 0;
        while (true) {
            uint64_t v = slots[j].load(std::memory_order_acquire);
            if (v == 0) return false;
            if ((v & 0xffffffff00000000ULL) == tagv) {
                uint32_t id = (uint32_t)(v & 0xffffffffu) - 1;
                if (eq(id)) {
                    out = id;
                    return true;
                }
            }
            j = (j + 1) & mask;
            if (++probes > mask) return false;
        }
    }
};
template <class K, class Traits>
struct Sharded {
    static const size_t NSH = 4096;
    struct Slot {
        K key;
        uint32_t val1;  // value + 1, 0 = empty
    };
    struct alignas(64) Shard {
        std::mutex mu;
        Slot* slots = nullptr;
        size_t mask = 0;
        size_t size = 0;
    };
    Shard* sh = nullptr;

    void* region = nullptr;  // the initial slot arrays of all shards (one THP region)
    size_t region_bytes = 0;
    void init(size_t cap_total) {
        sh = new Shard[NSH];
        size_t per = cap_total / NSH;
        size_t c = 64;
        while (c < per * 2) c <<= 1;
        region_bytes = NSH * c * sizeof(Slot);
        region = zalloc_huge(region_bytes);
        for (size_t i = 0; i < NSH; i++) {
            sh[i].slots = (Slot*)((char*)region + i * c * sizeof(Slot));
            sh[i].mask = c - 1;
        }
    }
    static void grow(Shard& s) {
        size_t oc = s.mask + 1, nc = oc * 2;
        Slot* ns = (Slot*)zalloc(nc * sizeof(Slot));
        size_t nm = nc - 1;
        for (size_t i = 0; i < oc; i++) {
            if (s.slots[i].val1 == 0) continue;
            size_t j = (size_t)Traits::hash(s.slots[i].key) & nm;
            while (ns[j].val1 != 0) j = (j + 1) & nm;
            ns[j] = s.slots[i];
        }
        if (oc > 64 * 1024) reg_munmap(s.slots, oc * sizeof(Slot));  // small ones may live in the shared initial region
        s.slots = ns;
        s.mask = nm;
    }
    static inline size_t shard_of(uint64_t h) { return (size_t)(h >> 52) & (NSH - 1); }
    inline bool get(const K& k, uint32_t& out) {
        uint64_t h = Traits::hash(k);
        Shard& s = sh[shard_of(h)];
        std::lock_guard<std::mutex> g(s.mu);
        size_t j = (size_t)h & s.mask;
        while (true) {
            Slot& sl = s.slots[j];
            if (sl.val1 == 0) return false;
            if (Traits::eq(sl.key, k)) {
                out = sl.val1 - 1;
                return true;
            }
            j = (j + 1) & s.mask;
        }
    }
    inline void insert(const K& k, uint32_t v) {
        uint64_t h = Traits::hash(k);
        Shard& s = sh[shard_of(h)];
        std::lock_guard<std::mutex> g(s.mu);
        size_t j = (size_t)h & s.mask;
        while (true) {
            Slot& sl = s.slots[j];
            if (sl.val1 == 0) break;
            if (Traits::eq(sl.key, k)) {
                sl.val1 = v + 1;
                return;
            }
            j = (j + 1) & s.mask;
        }
        s.slots[j].key = k;
        s.slots[j].val1 = v + 1;
        if (++s.size * 4 > (s.mask + 1) * 3) grow(s);
    }
    // returns the value; `inserted` tells whether f() was called (under the shard lock)
    template <class F>
    inline uint32_t get_or_insert(const K& k, F f, bool& inserted) {
        uint64_t h = Traits::hash(k);
        Shard& s = sh[shard_of(h)];
        std::lock_guard<std::mutex> g(s.mu);
        size_t j = (size_t)h & s.mask;
        while (true) {
            Slot& sl = s.slots[j];
            if (sl.val1 == 0) break;
            if (Traits::eq(sl.key, k)) {
                inserted = false;
                return sl.val1 - 1;
            }
            j = (j + 1) & s.mask;
        }
        uint32_t v = f();
        s.slots[j].key = k;
        s.slots[j].val1 = v + 1;
        inserted = true;
        if (++s.size * 4 > (s.mask + 1) * 3) grow(s);
        return v;
    }
};

// target names as plain data (components root-first); run() never touches Lean objects
struct NameComp {
    uint8_t kind;  // 1 string, 2 number < 2^63 (lean_unbox), 3 bigger number (never found)
    std::string s;
    uint64_t num;
    bool operator==(const NameComp& o) const { return kind == o.kind && s == o.s && num == o.num; }
};
typedef std::vector<NameComp> NameArg;

// ------------------------------------------------------------------------------------------------
// keys
struct NKey {  // interned name: prefix id + component
    uint32_t pre;
    uint8_t kind;  // 1 str, 2 num
    uint32_t len;
    P ptr;         // string bytes (olean memory or caller memory for lookups)
    uint64_t num;
};
struct NKeyT {
    static inline uint64_t hash(const NKey& k) {
        uint64_t h = hmix(0x1234567, k.pre);
        if (k.kind == 1)
            h = hbytes(h, k.ptr, k.len);
        else
            h = hmix(h, k.num ^ 0x9e3779b97f4a7c15ULL);
        return hfin(h);
    }
    static inline bool eq(const NKey& a, const NKey& b) {
        if (a.pre != b.pre || a.kind != b.kind) return false;
        if (a.kind == 1) return a.len == b.len && memcmp(a.ptr, b.ptr, a.len) == 0;
        return a.num == b.num;
    }
};
struct NameE {
    NKey key;
    uint64_t hash;  // Lean's Name.hash (for Name.quickCmp)
};
struct PtrT {
    static inline uint64_t hash(const uint64_t& k) { return hfin(k); }
    static inline bool eq(const uint64_t& a, const uint64_t& b) { return a == b; }
};
struct LKey {  // level: kind (0 zero, 1 succ, 2 max, 3 imax, 4 param) + ids
    uint8_t kind;
    uint32_t a, b;
};
struct LKeyT {
    static inline uint64_t hash(const LKey& k) { return hfin(hmix(hmix(hmix(0x77, k.kind), k.a), k.b)); }
    static inline bool eq(const LKey& x, const LKey& y) { return x.kind == y.kind && x.a == y.a && x.b == y.b; }
};
struct LLKey {  // level list cell: head level id, tail list id (0 = nil)
    uint32_t h, t;
};
struct LLKeyT {
    static inline uint64_t hash(const LLKey& k) { return hfin(hmix(hmix(0x99, k.h), k.t)); }
    static inline bool eq(const LLKey& x, const LLKey& y) { return x.h == y.h && x.t == y.t; }
};
struct EKey {  // expression class: Expr ctor tag (12 = string literal) + child/payload ids
    uint8_t kind;
    uint32_t a, b, c;
};
struct EKeyT {
    static inline uint64_t hash(const EKey& k) { return hfin(hmix(hmix(hmix(hmix(0x55, k.kind), k.a), k.b), k.c)); }
    static inline bool eq(const EKey& x, const EKey& y) { return x.kind == y.kind && x.a == y.a && x.b == y.b && x.c == y.c; }
};
struct BKey {
    const uint8_t* ptr;
    uint32_t len;
    bool operator==(const BKey& o) const { return len == o.len && memcmp(ptr, o.ptr, len) == 0; }
};
struct BKeyH {
    size_t operator()(const BKey& k) const { return (size_t)hfin(hbytes(0x31, k.ptr, k.len)); }
};
struct NatKey {
    uint64_t small;  // UINT64_MAX for bignums
    BKey big;
    bool operator==(const NatKey& o) const { return small == o.small && big == o.big; }
};
struct NatKeyH {
    size_t operator()(const NatKey& k) const { return (size_t)hfin(hbytes(hmix(0x41, k.small), k.big.ptr, k.big.len)); }
};

struct CRef {
    uint32_t m;  // module index, NONE = absent
    P ci;        // ConstantInfo object
};

struct Part {
    uint64_t base;
    P ptr;
    uint64_t len;
    // pointer cache: id + 1 of the object at ptr + 16 * i (0 = not yet).  Only Name/Level/Expr/List objects are
    // cached and each of them takes >= 16 bytes, so two cached objects never share a cell.
    std::atomic<uint32_t>* side = nullptr;
};
struct Module {
    std::string name;
    std::vector<Part> parts;
    P data = nullptr;  // ModuleData of the most private part
    std::vector<std::string> comps;  // module name components
    std::vector<uint32_t> imps;      // module indices of ModuleData.imports, in order
};

// ------------------------------------------------------------------------------------------------
// output: big buffer + writer thread
struct Out {
    char* buf = nullptr;
    size_t len = 0, cap = 0;
    static const size_t CHUNK = 64u << 20;
    OSink* sink = nullptr;  // ordered output sink (native/osink.h); chunks numbered by `seq`
    uint64_t seq = 0;

    void start(size_t copiers = 8) {
        sink = new OSink();
        const char* om = getenv("LEAN4EXPORT_OUTPUT_WRITE");  // testing aid: force the write() back end
        sink->start_sink(copiers, (om && *om && strcmp(om, "0") != 0) ? 1 : 0);
        buf = sink->get_buffer(CHUNK + (16u << 20), cap);
    }
    void flush() {
        if (len == 0) return;
        sink->put(seq++, buf, len, cap);
        sink->wait_backlog(4);
        buf = sink->get_buffer(CHUNK + (16u << 20), cap);
        len = 0;
    }
    // queue an externally rendered malloc'ed buffer after everything written so far (the sink frees it)
    void push_owned(char* p, size_t n) {
        flush();
        sink->put(seq++, p, n, 0);
    }
    // reserve `k` consecutive chunk numbers after everything written so far: parallel producers then call
    // sink->put(first + i, buf, len, cap) in any order
    uint64_t reserve_seqs(uint64_t k) {
        flush();
        uint64_t first = seq;
        seq += k;
        return first;
    }
    void finish() {
        flush();
        uint64_t total = sink->finish();
        // the written range of the shared output mapping: released by fast_teardown (MADV_DONTNEED on MAP_SHARED only
        // drops the PTEs; the dirty pages stay in the page cache) instead of by the single-threaded exit_mmap
        if (sink->use_map) reg_add(sink->map, (size_t)((sink->start + total + 4095) & ~(uint64_t)4095));
        logf("output: %s", std::to_string(total) + " bytes via " +
                               (sink->use_dio ? (sink->dio_ok.load() ? "O_DIRECT" : "O_DIRECT->pwrite fallback")
                                              : sink->use_map ? "shared mapping" : "write()"));
    }
    // only used for very long lines (> 16 MiB slack)
    void reserve(size_t n) {
        if (len + n <= cap) return;
        if (sink) {
            buf = sink->grow(buf, cap, len + n + (1u << 20));
            return;
        }
        size_t nc = std::max(cap * 2, len + n + (1u << 20));
        char* nb = (char*)realloc(buf, nc);
        if (!nb) die("out of memory (output buffer)");
        buf = nb;
        cap = nc;
    }
    inline void s(const char* p, size_t n) {
        if (len + n > cap) reserve(n);
        memcpy(buf + len, p, n);
        len += n;
    }
    template <size_t N>
    inline void lit(const char (&p)[N]) {
        s(p, N - 1);
    }
    // decimal rendering: digit count from the bit length, then two digits per step from a table, in place
    static inline unsigned dec_len(uint64_t v) {
        static const uint64_t P10[20] = {1ull,
                                         10ull,
                                         100ull,
                                         1000ull,
                                         10000ull,
                                         100000ull,
                                         1000000ull,
                                         10000000ull,
                                         100000000ull,
                                         1000000000ull,
                                         10000000000ull,
                                         100000000000ull,
                                         1000000000000ull,
                                         10000000000000ull,
                                         100000000000000ull,
                                         1000000000000000ull,
                                         10000000000000000ull,
                                         100000000000000000ull,
                                         1000000000000000000ull,
                                         10000000000000000000ull};
        unsigned t = ((64 - (unsigned)__builtin_clzll(v | 1)) * 1233) >> 12;
        return t - (v < P10[t]) + 1;
    }
    static inline char* dec_put(char* end, uint64_t v) {  // writes v ending at `end`, returns the start
        static const char D2[201] =
            "00010203040506070809101112131415161718192021222324252627282930313233343536373839"
            "40414243444546474849505152535455565758596061626364656667686970717273747576777879"
            "8081828384858687888990919293949596979899";
        char* p = end;
        while (v >= 100000000ull) {  // 64-bit part: rarely taken (ids are < 2^32)
            uint64_t q = v / 100;
            unsigned r = (unsigned)(v - q * 100);
            p -= 2;
            memcpy(p, D2 + 2 * r, 2);
            v = q;
        }
        uint32_t w = (uint32_t)v;
        while (w >= 100) {
            uint32_t q = w / 100;
            unsigned r = w - q * 100;
            p -= 2;
            memcpy(p, D2 + 2 * r, 2);
            w = q;
        }
        if (w >= 10) {
            p -= 2;
            memcpy(p, D2 + 2 * w, 2);
        } else {
            *--p = (char)('0' + w);
        }
        return p;
    }
    inline void n(uint64_t v) {
        if (v < 10) {
            ch((char)('0' + v));
            return;
        }
        unsigned d = dec_len(v);
        if (len + d > cap) reserve(d);
        dec_put(buf + len + d, v);
        len += d;
    }
    inline void ch(char c) {
        if (len + 1 > cap) reserve(1);
        buf[len++] = c;
    }
    void jstr(const uint8_t* p, size_t n) {
        if (!utf8_ok(p, n)) die("string is not valid UTF-8");
        reserve(n * 6 + 2);
        char* o = buf + len;
        *o++ = '"';
        static const char HX[] = "0123456789abcdef";
        for (size_t i = 0; i < n; i++) {
            uint8_t c = p[i];
            if (c == '"') {
                *o++ = '\\';
                *o++ = '"';
            } else if (c == '\\') {
                *o++ = '\\';
                *o++ = '\\';
            } else if (c == '\n') {
                *o++ = '\\';
                *o++ = 'n';
            } else if (c == '\r') {
                *o++ = '\\';
                *o++ = 'r';
            } else if (c < 0x20) {
                *o++ = '\\';
                *o++ = 'u';
                *o++ = '0';
                *o++ = '0';
                *o++ = HX[c >> 4];
                *o++ = HX[c & 15];
            } else {
                *o++ = (char)c;
            }
        }
        *o++ = '"';
        len = o - buf;
    }
    inline void b(bool v) {
        if (v)
            lit("true");
        else
            lit("false");
    }
    inline void nl() {
        ch('\n');
        if (len >= CHUNK) flush();
    }
    void arr(const std::vector<uint32_t>& xs) {
        ch('[');
        for (size_t i = 0; i < xs.size(); i++) {
            if (i) ch(',');
            n(xs[i]);
        }
        ch(']');
    }
};

// ------------------------------------------------------------------------------------------------
// bignum -> decimal
static std::string big_to_dec(std::vector<uint64_t> limbs) {
    const uint64_t D = 10000000000000000000ULL;  // 10^19
    std::vector<uint64_t> chunks;
    auto nonzero = [&] {
        for (uint64_t x : limbs)
            if (x) return true;
        return false;
    };
    while (nonzero()) {
        unsigned __int128 rem = 0;
        for (size_t i = limbs.size(); i-- > 0;) {
            unsigned __int128 cur = (rem << 64) | limbs[i];
            limbs[i] = (uint64_t)(cur / D);
            rem = cur % D;
        }
        chunks.push_back((uint64_t)rem);
        while (!limbs.empty() && limbs.back() == 0) limbs.pop_back();
    }
    if (chunks.empty()) return "0";
    std::string s = std::to_string(chunks.back());
    char tmp[32];
    for (size_t i = chunks.size() - 1; i-- > 0;) {
        snprintf(tmp, sizeof tmp, "%019llu", (unsigned long long)chunks[i]);
        s += tmp;
    }
    return s;
}

// ------------------------------------------------------------------------------------------------
// interner: shared between the parallel intern phase and the sequential dump
// The expr table of a target-list export is sized from an estimate (the closure is not known in advance); if it gets
// too full during phase A (before anything is written), the child exits with EXIT_TABLE_FULL and the parent runs it
// again with the table sized from the olean-bytes bound.
static const int EXIT_TABLE_FULL = 4;  // (3 = E01: a root is missing in LEAN_PATH)
static bool g_emap_estimated = false;  // set in the child when the expr table is estimate-sized
static bool g_emap_use_bound = false;  // tables sized from the bounds right away (no restart possible: NOFORK)
static int g_size_attempt = 0;          // set in the parent before each fork: estimates grow 8x per restart
static std::atomic<bool> g_output_started{false};  // set right before phase B (the first byte of output)
static bool g_nmap_estimated = false;  // the name table is always estimate-sized, except after a restart
[[noreturn]] static void table_full(const char* which = "expr", bool estimated = g_emap_estimated) {
    if (!estimated || g_output_started.load()) die(std::string("internal: ") + which + " table full");
    fprintf(stderr, "lean4export (native): %s table estimate too small, restarting with 8x larger estimates\n", which);
    fflush(stderr);
    _exit(EXIT_TABLE_FULL);
}
struct In {
    std::vector<Module> mods;
    BigVec<NameE> names;
    std::atomic<uint32_t> nc{1};
    LFMap nmap;  // key of name id i = names[i].key
    BigVec<LKey> lkeys;
    std::atomic<uint32_t> lc{0};
    Sharded<LKey, LKeyT> lmap;
    BigVec<LLKey> llkeys;
    std::atomic<uint32_t> llc{1};
    Sharded<LLKey, LLKeyT> llmap;
    std::mutex natmu;
    std::unordered_map<NatKey, uint32_t, NatKeyH> natlit;
    std::deque<std::string> natbig;  // keeps the bytes behind bignum keys alive
    std::mutex strmu;
    std::unordered_map<BKey, uint32_t, BKeyH> strlit;
    BigVec<EKey> ekeys;
    std::atomic<uint32_t> ec{0};  // upper bound of all expr ids (ids come in per-thread blocks)
    LFMap emap;
    BigVec<std::atomic<uint8_t>> enq;
    std::vector<CRef> cmap;  // indexed by name id
    std::unordered_map<uint32_t, std::vector<uint32_t>> recmap;
    uint32_t n_nat = NONE, n_charofnat = NONE, n_stringoflist = NONE, n_eq = NONE;
    uint32_t n_quot[4] = {NONE, NONE, NONE, NONE};

    [[noreturn]] void dangling(uint32_t m, uint64_t a) const {
        char buf[64];
        snprintf(buf, sizeof buf, "%#llx", (unsigned long long)a);
        die(std::string("dangling pointer ") + buf + " in module " + mods[m].name);
    }
    inline P tr(uint32_t m, uint64_t a) const {
        const Module& md = mods[m];
        for (const Part& p : md.parts) {
            uint64_t off = a - p.base;
            if (off < p.len) return p.ptr + off;
        }
        dangling(m, a);
    }
    // translate a stored pointer and return the pointer-cache cell of its object
    inline P trs(uint32_t m, uint64_t a, std::atomic<uint32_t>*& cell) const {
        const Module& md = mods[m];
        for (const Part& p : md.parts) {
            uint64_t off = a - p.base;
            if (off < p.len) {
                cell = p.side + (off >> 4);
                return p.ptr + off;
            }
        }
        dangling(m, a);
    }
    // pointer-cache cell of an (already translated) object pointer
    inline std::atomic<uint32_t>* side_of(uint32_t m, P q) const {
        const Module& md = mods[m];
        for (const Part& p : md.parts) {
            size_t off = (size_t)(q - p.ptr);
            if (off < p.len) return p.side + (off >> 4);
        }
        die("internal: object outside of its module " + md.name);
    }
    inline P f(uint32_t m, P o, size_t i) const { return tr(m, rawf(o, i)); }
    uint64_t nat_small(uint32_t m, uint64_t r) const {
        if (is_scalar(r)) return r >> 1;
        P o = tr(m, r);
        die("unexpected bignum (tag " + std::to_string(tag(o)) + ") in small Nat position");
    }
    std::string nat_dec(uint32_t m, uint64_t r) const {
        if (is_scalar(r)) return std::to_string(r >> 1);
        P o = tr(m, r);
        if (tag(o) != T_MPZ) die("expected mpz");
        // mpz object: header(8) | int alloc | int size | limb* d ; the limbs follow in the region
        int32_t size;
        memcpy(&size, o + 12, 4);
        uint64_t d;
        memcpy(&d, o + 16, 8);
        if (size < 0) die("negative mpz in Nat");
        size_t n = (size_t)size;
        std::vector<uint64_t> limbs(n);
        if (n) {
            P lp = tr(m, d);
            memcpy(limbs.data(), lp, n * 8);
        }
        return big_to_dec(limbs);
    }
    bool cmap_has(uint32_t c) const { return c < cmap.size() && cmap[c].m != NONE; }

    uint32_t intern_name(uint32_t m, uint64_t r) {
        if (is_scalar(r)) return 0;
        std::atomic<uint32_t>* cell;
        P p = trs(m, r, cell);
        uint32_t cv = cell->load(std::memory_order_relaxed);
        if (cv) return cv - 1;
        uint32_t id;
        uint8_t t = tag(p);
        if (t == 0) return 0;
        uint32_t pre = intern_name(m, rawf(p, 0));
        uint64_t hash = sc_u64(p, 0);
        NKey key;
        key.pre = pre;
        if (t == 1) {
            P s = f(m, p, 1);
            key.kind = 1;
            key.ptr = str_data(s);
            key.len = (uint32_t)str_len(s);
            key.num = 0;
        } else if (t == 2) {
            key.kind = 2;
            key.ptr = nullptr;
            key.len = 0;
            key.num = nat_small(m, rawf(p, 1));
        } else {
            die("bad name tag " + std::to_string(t));
        }
        bool ins;
        static thread_local uint32_t nspare = NONE;
        id = nmap.get_or_insert(
            NKeyT::hash(key), [&](uint32_t i) { return NKeyT::eq(names.p[i].key, key); },
            [&](uint32_t i) {
                if (i == NONE) i = nc.fetch_add(1, std::memory_order_relaxed);
                names.set(i, NameE{key, hash});
                return i;
            },
            nspare, ins);
        if (ins) {
            static thread_local uint32_t nins = 0;
            if (++nins == 256) {
                nins = 0;
                if (nmap.count.fetch_add(256, std::memory_order_relaxed) + 256 > nmap.limit)
                    table_full("name", g_nmap_estimated);
            }
        }
        cell->store(id + 1, std::memory_order_relaxed);
        return id;
    }
    // lookup of a name given by components (no insertion)
    uint32_t lookup_name_str(const std::string& s) {
        uint32_t cur = 0;
        size_t i = 0;
        while (true) {
            size_t j = s.find('.', i);
            std::string comp = s.substr(i, j == std::string::npos ? std::string::npos : j - i);
            NKey k;
            k.pre = cur;
            k.kind = 1;
            k.ptr = (const uint8_t*)comp.data();
            k.len = (uint32_t)comp.size();
            k.num = 0;
            if (!nmap.get(NKeyT::hash(k), [&](uint32_t i) { return NKeyT::eq(names.p[i].key, k); }, cur)) return NONE;
            if (j == std::string::npos) return cur;
            i = j + 1;
        }
    }
    // lookup of a name given as plain components (no insertion)
    uint32_t lookup_name_arg(const NameArg& n) {
        uint32_t cur = 0;
        for (const NameComp& c : n) {
            NKey k;
            k.pre = cur;
            if (c.kind == 1) {
                k.kind = 1;
                k.ptr = (const uint8_t*)c.s.data();
                k.len = (uint32_t)c.s.size();
                k.num = 0;
            } else if (c.kind == 2) {
                k.kind = 2;
                k.ptr = nullptr;
                k.len = 0;
                k.num = c.num;
            } else {
                return NONE;
            }
            if (!nmap.get(NKeyT::hash(k), [&](uint32_t i) { return NKeyT::eq(names.p[i].key, k); }, cur)) return NONE;
        }
        return cur;
    }
    // lookup of a runtime Lean `Name` object (no insertion)
    uint32_t lookup_name_obj(b_lean_obj_arg n) {
        if (lean_is_scalar(n)) return 0;
        uint32_t pre = lookup_name_obj(lean_ctor_get(n, 0));
        if (pre == NONE) return NONE;
        NKey k;
        k.pre = pre;
        if (lean_ptr_tag(n) == 1) {
            b_lean_obj_arg s = lean_ctor_get(n, 1);
            k.kind = 1;
            k.ptr = (const uint8_t*)lean_string_cstr(s);
            k.len = (uint32_t)(lean_string_size(s) - 1);
            k.num = 0;
        } else {
            b_lean_obj_arg v = lean_ctor_get(n, 1);
            if (!lean_is_scalar(v)) return NONE;
            k.kind = 2;
            k.ptr = nullptr;
            k.len = 0;
            k.num = lean_unbox(v);
        }
        uint32_t id;
        if (!nmap.get(NKeyT::hash(k), [&](uint32_t i) { return NKeyT::eq(names.p[i].key, k); }, id)) return NONE;
        return id;
    }
    uint32_t level_key_insert(const LKey& key) {
        bool ins;
        return lmap.get_or_insert(
            key,
            [&] {
                uint32_t i = lc.fetch_add(1, std::memory_order_relaxed);
                lkeys.set(i, key);
                return i;
            },
            ins);
    }
    uint32_t intern_level(uint32_t m, uint64_t r) {
        if (is_scalar(r)) {
            if ((r >> 1) != 0) die("bad boxed level");
            return level_key_insert(LKey{0, 0, 0});
        }
        std::atomic<uint32_t>* cell;
        P p = trs(m, r, cell);
        uint32_t cv = cell->load(std::memory_order_relaxed);
        if (cv) return cv - 1;
        uint32_t id;
        uint8_t t = tag(p);
        LKey key;
        switch (t) {
            case 0: key = LKey{0, 0, 0}; break;
            case 1: key = LKey{1, intern_level(m, rawf(p, 0)), 0}; break;
            case 2:
            case 3: {
                uint32_t a = intern_level(m, rawf(p, 0));
                uint32_t b = intern_level(m, rawf(p, 1));
                key = LKey{t, a, b};
                break;
            }
            case 4: key = LKey{4, intern_name(m, rawf(p, 0)), 0}; break;
            default: die("unexpected level tag " + std::to_string(t));
        }
        id = level_key_insert(key);
        cell->store(id + 1, std::memory_order_relaxed);
        return id;
    }
    uint32_t intern_level_list(uint32_t m, uint64_t r) {
        if (is_scalar(r)) return 0;
        std::atomic<uint32_t>* cell;
        P p = trs(m, r, cell);
        uint32_t cv = cell->load(std::memory_order_relaxed);
        if (cv) return cv - 1;
        uint32_t id;
        uint32_t h = intern_level(m, rawf(p, 0));
        uint32_t t = intern_level_list(m, rawf(p, 1));
        LLKey key{h, t};
        bool ins;
        id = llmap.get_or_insert(
            key,
            [&] {
                uint32_t i = llc.fetch_add(1, std::memory_order_relaxed);
                llkeys.set(i, key);
                return i;
            },
            ins);
        cell->store(id + 1, std::memory_order_relaxed);
        return id;
    }
    inline P skip_mdata(uint32_t m, P p) const {
        while (tag(p) == 10) p = f(m, p, 1);
        return p;
    }
    inline P child(uint32_t m, P p, size_t i) const { return skip_mdata(m, f(m, p, i)); }

    // interns the structural class of an expression (mdata stripped, binder names/infos ignored);
    // newly created const classes push their constant name to `disc` (closure discovery).
    // The pointer-cache cell of an mdata object holds the class of the expression below the mdata, so a known
    // object is recognized from its cell alone, without reading the object (saves a cache miss per cache hit).
    uint32_t intern_expr(uint32_t m, P p0, std::vector<uint32_t>& disc) {
        std::atomic<uint32_t>* cell0 = side_of(m, p0);
        uint32_t cv = cell0->load(std::memory_order_relaxed);
        if (cv) return cv - 1;
        P p = p0;
        std::atomic<uint32_t>* cell = cell0;
        if (tag(p0) == 10) {
            p = skip_mdata(m, p0);
            cell = side_of(m, p);
            cv = cell->load(std::memory_order_relaxed);
            if (cv) {
                cell0->store(cv, std::memory_order_relaxed);
                return cv - 1;
            }
        }
        uint32_t id;
        uint8_t t = tag(p);
        EKey key{0, 0, 0, 0};
        switch (t) {
            case 0: {
                // F04 (fail closed): a de Bruijn index that does not fit in 32 bits is never truncated
                uint64_t b64 = nat_small(m, rawf(p, 0));
                if (b64 > 0xffffffffull) die("bound variable index does not fit in 32 bits");
                key = EKey{0, (uint32_t)b64, 0, 0};
                break;
            }
            case 3: key = EKey{3, intern_level(m, rawf(p, 0)), 0, 0}; break;
            case 4: {
                uint32_t n = intern_name(m, rawf(p, 0));
                uint32_t l = intern_level_list(m, rawf(p, 1));
                key = EKey{4, n, l, 0};
                break;
            }
            case 5: {
                P pa = f(m, p, 0), pb = f(m, p, 1);
                uint32_t a = intern_expr(m, pa, disc);
                uint32_t b = intern_expr(m, pb, disc);
                key = EKey{5, a, b, 0};
                break;
            }
            case 6:
            case 7: {
                P pa = f(m, p, 1), pb = f(m, p, 2);
                intern_name(m, rawf(p, 0));
                uint32_t a = intern_expr(m, pa, disc);
                uint32_t b = intern_expr(m, pb, disc);
                key = EKey{t, a, b, 0};
                break;
            }
            case 8: {
                P pa = f(m, p, 1), pb = f(m, p, 2), pc = f(m, p, 3);
                intern_name(m, rawf(p, 0));
                uint32_t a = intern_expr(m, pa, disc);
                uint32_t b = intern_expr(m, pb, disc);
                uint32_t c = intern_expr(m, pc, disc);
                key = EKey{8, a, b, c};
                break;
            }
            case 9: {
                P lit = f(m, p, 0);
                if (tag(lit) == 0) {
                    uint64_t r = rawf(lit, 0);
                    NatKey k;
                    std::string big;
                    if (is_scalar(r)) {
                        k.small = r >> 1;
                        k.big = BKey{nullptr, 0};
                    } else {
                        big = nat_dec(m, r);
                        k.small = UINT64_MAX;
                        k.big = BKey{(const uint8_t*)big.data(), (uint32_t)big.size()};
                    }
                    std::lock_guard<std::mutex> g(natmu);
                    auto it = natlit.find(k);
                    uint32_t lid;
                    if (it != natlit.end()) {
                        lid = it->second;
                    } else {
                        lid = (uint32_t)natlit.size();
                        if (k.small == UINT64_MAX) {
                            natbig.push_back(big);
                            k.big = BKey{(const uint8_t*)natbig.back().data(), (uint32_t)natbig.back().size()};
                        }
                        natlit.emplace(k, lid);
                        disc.push_back(n_nat);
                    }
                    key = EKey{9, lid, 0, 0};
                } else {
                    P s = f(m, lit, 0);
                    BKey k{str_data(s), (uint32_t)str_len(s)};
                    std::lock_guard<std::mutex> g(strmu);
                    auto it = strlit.find(k);
                    uint32_t sid;
                    if (it != strlit.end()) {
                        sid = it->second;
                    } else {
                        sid = (uint32_t)strlit.size();
                        strlit.emplace(k, sid);
                        disc.push_back(n_charofnat);
                        disc.push_back(n_stringoflist);
                    }
                    key = EKey{12, sid, 0, 0};
                }
                break;
            }
            case 11: {
                uint32_t n = intern_name(m, rawf(p, 0));
                uint64_t i64 = nat_small(m, rawf(p, 1));
                // X01 fix (finding 008): the index is a Nat; never truncate it (the reference implementation prints it whole)
                if (i64 > 0xffffffffull) die("projection index does not fit in 32 bits");
                uint32_t i = (uint32_t)i64;
                uint32_t e = intern_expr(m, f(m, p, 2), disc);
                key = EKey{11, n, i, e};
                break;
            }
            default: die("cannot export expr tag " + std::to_string(t));
        }
        bool inserted;
        static thread_local IdBlock eblk;
        static thread_local uint32_t espare = NONE;
        id = emap.get_or_insert(
            EKeyT::hash(key), [&](uint32_t i) { return EKeyT::eq(ekeys.p[i], key); },
            [&](uint32_t i) {
                if (i == NONE) i = take_id(ec, eblk);
                ekeys.set(i, key);
                return i;
            },
            espare, inserted);
        if (inserted) {
            static thread_local uint32_t nins = 0;
            if (++nins == 1024) {
                nins = 0;
                if (emap.count.fetch_add(1024, std::memory_order_relaxed) + 1024 > emap.limit) table_full();
            }
            if (key.kind == 4) disc.push_back(key.a);
        }
        cell->store(id + 1, std::memory_order_relaxed);
        if (cell0 != cell) cell0->store(id + 1, std::memory_order_relaxed);
        return id;
    }
    // Name.isInternal: some string component starts with '_' (String.front of "" is 'A')
    bool is_internal(uint32_t iid) const {
        while (iid != 0) {
            const NKey& k = names.p[iid].key;
            if (k.kind == 1 && k.len > 0 && k.ptr[0] == '_') return true;
            iid = k.pre;
        }
        return false;
    }
    std::string name_str(uint32_t iid) {
        if (iid == 0 || iid == NONE) return "[anonymous]";
        NKey k = names.get(iid).key;
        std::string comp = k.kind == 1 ? std::string((const char*)k.ptr, k.len) : std::to_string(k.num);
        if (k.pre == 0) return comp;
        return name_str(k.pre) + "." + comp;
    }
    // (val, cval) of a ConstantInfo
    inline void vals(const CRef& r, P& val, P& cval) const {
        val = f(r.m, r.ci, 0);
        cval = f(r.m, val, 0);
    }
    bool is_unsafe(const CRef& r) const {
        P val, cval;
        vals(r, val, cval);
        switch (tag(r.ci)) {
            case 0: return sc_u8(val, 0) != 0;  // axiom.isUnsafe
            case 1: return sc_u8(val, 0) == 0;  // defn.safety == unsafe
            case 2: return false;
            case 3: return sc_u8(val, 0) != 0;  // opaque.isUnsafe
            case 4: return false;
            case 5: return sc_u8(val, 1) != 0;  // induct: isRec, isUnsafe, isReflexive
            case 6: return sc_u8(val, 0) != 0;  // ctor.isUnsafe
            case 7: return sc_u8(val, 1) != 0;  // rec: k, isUnsafe
            default: die("bad ConstantInfo tag " + std::to_string(tag(r.ci)));
        }
    }
    void list_names(uint32_t m, uint64_t r, std::vector<uint32_t>& v) {
        while (!is_scalar(r)) {
            P c = tr(m, r);
            v.push_back(intern_name(m, rawf(c, 0)));
            r = rawf(c, 1);
        }
    }
    // phase A: intern everything the dump will touch for constant c, push discovered constants
    void intern_const(uint32_t c, std::vector<uint32_t>& disc) {
        if (!cmap_has(c)) return;
        CRef r = cmap[c];
        if (is_unsafe(r)) return;
        uint32_t m = r.m;
        P val, cval;
        vals(r, val, cval);
        intern_name(m, rawf(cval, 0));
        std::vector<uint32_t> tmp;
        list_names(m, rawf(cval, 1), tmp);
        intern_expr(m, f(m, cval, 2), disc);
        switch (tag(r.ci)) {
            case 1:
            case 2:
            case 3: intern_expr(m, f(m, val, 1), disc); break;
            case 4:
                disc.push_back(n_eq);
                for (int i = 0; i < 4; i++) disc.push_back(n_quot[i]);
                break;
            case 5: {
                list_names(m, rawf(val, 3), disc);
                list_names(m, rawf(val, 4), disc);
                auto it = recmap.find(c);
                if (it != recmap.end()) disc.insert(disc.end(), it->second.begin(), it->second.end());
                break;
            }
            case 6: disc.push_back(intern_name(m, rawf(val, 1))); break;
            case 7: {
                list_names(m, rawf(val, 1), disc);
                uint64_t rl = rawf(val, 6);
                while (!is_scalar(rl)) {
                    P cell = tr(m, rl);
                    P rule = f(m, cell, 0);
                    intern_name(m, rawf(rule, 0));
                    intern_expr(m, f(m, rule, 2), disc);
                    rl = rawf(cell, 1);
                }
                break;
            }
            default: break;
        }
    }
    inline bool try_enq(uint32_t n) {
        if (n == NONE || (size_t)n >= enq.cap) return false;
        return enq.p[n].exchange(1, std::memory_order_relaxed) == 0;
    }
};

// ------------------------------------------------------------------------------------------------
// threads with big stacks
static void* bigthread_tramp(void* arg) {
    auto* fn = (std::function<void()>*)arg;
    (*fn)();
    return nullptr;
}
static void run_with_stack(size_t stack, std::vector<std::function<void()>>& fns);
// write-touch every 2 MB block of a zalloc_huge region in parallel -> transparent huge pages from the start
static void prefault_huge(void* p, size_t bytes, size_t nthreads) {
    size_t nblk = (bytes + HUGE_SZ - 1) / HUGE_SZ;
    std::atomic<size_t> next{0};
    std::vector<std::function<void()>> fns;
    for (size_t k = 0; k < std::max((size_t)1, nthreads); k++)
        fns.push_back([&] {
            while (true) {
                size_t i = next.fetch_add(16);
                if (i >= nblk) break;
                for (size_t j = i; j < std::min(nblk, i + 16); j++) ((volatile char*)p)[j * HUGE_SZ] = 0;
            }
        });
    run_with_stack((size_t)1 << 20, fns);
}
static void run_with_stack(size_t stack, std::vector<std::function<void()>>& fns) {
    std::vector<pthread_t> ths(fns.size());
    for (size_t i = 0; i < fns.size(); i++) {
        pthread_attr_t at;
        pthread_attr_init(&at);
        pthread_attr_setstacksize(&at, stack);
        if (pthread_create(&ths[i], &at, bigthread_tramp, &fns[i]) != 0) die("pthread_create failed");
        pthread_attr_destroy(&at);
    }
    for (pthread_t& t : ths) pthread_join(t, nullptr);
}

// ------------------------------------------------------------------------------------------------
// parallel teardown.  Called by the child after the output is complete: drops the pages of every registered mapping
// (MADV_DONTNEED: anonymous pages are freed, file pages just unmapped) from `nthreads` threads in parallel, in chunks,
// so that the final exit_mmap has (almost) nothing left to free.  Only mmap_lock in read mode is needed, so the
// threads do not serialize.  Errors are ignored: this runs after the last output byte and can only save time.
// Safety: the threads run on stacks mapped here, the work list lives in a mapping made here, and any registered
// range overlapping those or the calling thread's stack is skipped (all other memory is dead at this point).
// LEAN4EXPORT_TEARDOWN=0 disables it.
struct TdChunk {
    uintptr_t p;
    size_t n;
};
struct TdCtx {
    TdChunk* chunks;
    size_t nchunks;
    std::atomic<size_t> next{0};
};
static void* td_worker(void* arg) {
    TdCtx* c = (TdCtx*)arg;
    while (true) {
        size_t i = c->next.fetch_add(1, std::memory_order_relaxed);
        if (i >= c->nchunks) break;
        madvise((void*)c->chunks[i].p, c->chunks[i].n, MADV_DONTNEED);
    }
    return nullptr;
}
static void fast_teardown(size_t nthreads) {
    const char* e = getenv("LEAN4EXPORT_TEARDOWN");
    if ((e && strcmp(e, "0") == 0) || nthreads < 2) return;
    double t0 = now_s();
    std::vector<std::pair<uintptr_t, size_t>> regs, holes;  // (allocated before the exclusion ranges below exist)
    {
        std::lock_guard<std::mutex> g(g_reg_mu);
        if (!g_reg) return;
        regs.reserve(g_reg->size());
        for (auto& kv : *g_reg) regs.push_back({kv.first, kv.second});
        holes.reserve((g_holes ? g_holes->size() : 0) + 3);
        if (g_holes) holes = *g_holes;
    }
    const size_t CH = (size_t)256 << 20;  // chunk size (madvise of an untouched range is cheap)
    const size_t page = 4096;
    size_t nchunks = 0;
    for (auto& r : regs) nchunks += (r.second + CH - 1) / CH;
    nchunks += 2 * (holes.capacity() + 3);  // every hole / exclusion can split one more piece
    const size_t STK = (size_t)1 << 20;
    size_t list_bytes = (nchunks * sizeof(TdChunk) + page - 1) & ~(page - 1);
    void* listm = mmap(nullptr, list_bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    void* stk = mmap(nullptr, STK * nthreads, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (listm == MAP_FAILED || stk == MAP_FAILED) return;
    // exclusions: munmapped sub-ranges (address space may have been reused), the work list, the worker stacks,
    // the calling thread's stack
    holes.push_back({(uintptr_t)listm, list_bytes});
    holes.push_back({(uintptr_t)stk, STK * nthreads});
    {
        pthread_attr_t at;
        void* sa = nullptr;
        size_t ss = 0;
        if (pthread_getattr_np(pthread_self(), &at) == 0) {
            if (pthread_attr_getstack(&at, &sa, &ss) != 0) ss = 0;
            pthread_attr_destroy(&at);
        }
        if (ss == 0) return;  // unknown stack: do nothing
        holes.push_back({(uintptr_t)sa, ss});
    }
    std::sort(holes.begin(), holes.end());
    {  // merge into disjoint intervals (then only the hole right before a region start can overlap it)
        size_t w = 0;
        for (size_t i = 0; i < holes.size(); i++) {
            if (w > 0 && holes[i].first <= holes[w - 1].first + holes[w - 1].second) {
                uintptr_t e = std::max(holes[w - 1].first + holes[w - 1].second, holes[i].first + holes[i].second);
                holes[w - 1].second = e - holes[w - 1].first;
            } else {
                holes[w++] = holes[i];
            }
        }
        holes.resize(w);
    }
    TdChunk* chunks = (TdChunk*)listm;
    size_t k = 0;
    for (auto& r : regs) {
        uintptr_t a = r.first, b = r.first + r.second;
        // pieces of [a, b) outside every hole (holes sorted by start)
        auto it = std::lower_bound(holes.begin(), holes.end(), std::make_pair(a, (size_t)0));
        if (it != holes.begin() && (it - 1)->first + (it - 1)->second > a) --it;
        uintptr_t cur = a;
        while (cur < b) {
            uintptr_t end = b;
            while (it != holes.end() && it->first + it->second <= cur) ++it;
            if (it != holes.end() && it->first < b) {
                if (it->first <= cur) {  // cur is inside a hole: skip it
                    cur = it->first + it->second;
                    ++it;
                    continue;
                }
                end = it->first;
            }
            for (uintptr_t q = cur; q < end && k < nchunks; q += CH) chunks[k++] = TdChunk{q, std::min((size_t)(end - q), CH)};
            cur = end;
        }
    }
    TdCtx ctx;
    ctx.chunks = chunks;
    ctx.nchunks = k;
    pthread_t ths[256];
    size_t nt = std::min(nthreads, (size_t)256), started = 0;
    for (size_t i = 1; i < nt; i++) {
        pthread_attr_t at;
        pthread_attr_init(&at);
        pthread_attr_setstack(&at, (char*)stk + i * STK, STK);
        if (pthread_create(&ths[started], &at, td_worker, &ctx) == 0) started++;
        pthread_attr_destroy(&at);
    }
    td_worker(&ctx);
    for (size_t i = 0; i < started; i++) pthread_join(ths[i], nullptr);
    logf("teardown: %s", std::to_string(k) + " chunks of " + std::to_string(regs.size()) + " mappings released in " +
                             std::to_string((int)((now_s() - t0) * 1000)) + " ms");
}

// phase A: parallel closure discovery + interning starting from the targets
static void phase_a(In* x, const std::vector<uint32_t>& targets, size_t nthreads) {
    std::mutex qmu;
    std::vector<uint32_t> queue;
    std::atomic<size_t> pending{0};
    std::atomic<size_t> processed{0};
    for (uint32_t t : targets) {
        if (x->cmap_has(t) && x->try_enq(t)) {
            queue.push_back(t);
            pending.fetch_add(1);
        }
    }
    std::vector<std::function<void()>> fns;
    for (size_t k = 0; k < nthreads; k++) {
        fns.push_back([&] {
            std::vector<uint32_t> disc, newq;
            while (true) {
                uint32_t c = NONE;
                {
                    std::lock_guard<std::mutex> g(qmu);
                    if (!queue.empty()) {
                        c = queue.back();
                        queue.pop_back();
                    }
                }
                if (c == NONE) {
                    if (pending.load() == 0) break;
                    usleep(200);
                    continue;
                }
                disc.clear();
                x->intern_const(c, disc);
                newq.clear();
                for (uint32_t d : disc)
                    if (x->cmap_has(d) && x->try_enq(d)) newq.push_back(d);
                if (!newq.empty()) {
                    pending.fetch_add(newq.size());
                    std::lock_guard<std::mutex> g(qmu);
                    queue.insert(queue.end(), newq.begin(), newq.end());
                }
                pending.fetch_sub(1);
                processed.fetch_add(1, std::memory_order_relaxed);
            }
        });
    }
    run_with_stack((size_t)4 << 30, fns);
    logf("phase A processed %s constants", std::to_string(processed.load()));
}

// ------------------------------------------------------------------------------------------------
// sequential dumper (exact lean4export order)
// zero-initialized uint32 array whose memory is committed lazily: resizing it is free (St's used-constant stamps;
// a filled std::vector of the expr-table size cost ~0.3 s of zero-filling whenever St ran after the parallel dump)
struct LazyU32 {
    static const size_t CAP = (size_t)1 << 32;
    uint32_t* p = nullptr;
    size_t n = 0;
    size_t size() const { return n; }
    uint32_t& operator[](size_t i) { return p[i]; }
    void resize(size_t m, uint32_t) {
        if (!p) p = (uint32_t*)zalloc(CAP * sizeof(uint32_t));
        if (m > CAP) die("LazyU32 capacity exceeded");
        if (m > n) n = m;
    }
    void zero_all() {
        if (p && n) madvise(p, n * sizeof(uint32_t), MADV_DONTNEED);  // private anonymous: reads back as zeros
    }
};

struct St {
    In* x;
    std::vector<uint32_t> exp_n;
    uint32_t cn = 1;
    std::vector<uint32_t> exp_l;
    uint32_t cl = 1;
    std::vector<uint32_t> exp_e;
    uint32_t ce = 0;
    LazyU32 eseen, cseen;
    uint32_t gen = 0;
    std::vector<uint8_t> visited;
    std::vector<uint32_t> disc;
    Out out;

    static inline void grow(std::vector<uint32_t>& v, size_t n) {
        if (v.size() < n) v.resize(n + (n >> 2) + 4096, NONE);
    }
    inline bool is_visited(uint32_t c) const { return c < visited.size() && visited[c]; }
    inline void set_visited(uint32_t c) {
        if (c >= visited.size()) visited.resize((size_t)c + (c >> 2) + 4096, 0);
        visited[c] = 1;
    }
    inline uint32_t intern_expr(uint32_t m, P p) {
        uint32_t i = x->intern_expr(m, p, disc);
        disc.clear();
        return i;
    }
    CRef get(uint32_t c) {
        if (!x->cmap_has(c)) return CRef{NONE, nullptr};
        return x->cmap[c];
    }
    uint32_t dump_name_iid(uint32_t iid) {
        grow(exp_n, (size_t)iid + 1);
        uint32_t e = exp_n[iid];
        if (e != NONE) return e;
        NKey key = x->names.get(iid).key;
        uint32_t pre = dump_name_iid(key.pre);
        uint32_t id = cn++;
        Out& o = out;
        o.lit("{\"in\":");
        o.n(id);
        if (key.kind == 1) {
            o.lit(",\"str\":{\"pre\":");
            o.n(pre);
            o.lit(",\"str\":");
            o.jstr(key.ptr, key.len);
            o.lit("}}");
        } else {
            o.lit(",\"num\":{\"i\":");
            o.n(key.num);
            o.lit(",\"pre\":");
            o.n(pre);
            o.lit("}}");
        }
        o.nl();
        exp_n[iid] = id;
        return id;
    }
    inline uint32_t dump_name(uint32_t m, uint64_t r) { return dump_name_iid(x->intern_name(m, r)); }

    uint32_t dump_level_iid(uint32_t iid) {
        grow(exp_l, (size_t)iid + 1);
        uint32_t e = exp_l[iid];
        if (e != NONE) return e;
        LKey k = x->lkeys.get(iid);
        uint32_t a = 0, b = 0;
        switch (k.kind) {
            case 1: a = dump_level_iid(k.a); break;
            case 2:
            case 3:
                a = dump_level_iid(k.a);
                b = dump_level_iid(k.b);
                break;
            case 4: a = dump_name_iid(k.a); break;
            default: die("dump of level zero/mvar");
        }
        uint32_t id = cl++;
        Out& o = out;
        o.lit("{\"il\":");
        o.n(id);
        switch (k.kind) {
            case 1:
                o.lit(",\"succ\":");
                o.n(a);
                break;
            case 2:
                o.lit(",\"max\":[");
                o.n(a);
                o.ch(',');
                o.n(b);
                o.ch(']');
                break;
            case 3:
                o.lit(",\"imax\":[");
                o.n(a);
                o.ch(',');
                o.n(b);
                o.ch(']');
                break;
            default:
                o.lit(",\"param\":");
                o.n(a);
                break;
        }
        o.ch('}');
        o.nl();
        exp_l[iid] = id;
        return id;
    }
    inline uint32_t next_e(uint32_t iid) {
        uint32_t id = ce++;
        exp_e[iid] = id;
        return id;
    }
    uint32_t dump_expr(uint32_t m, P p0) {
        P p = x->skip_mdata(m, p0);
        uint32_t iid = intern_expr(m, p);
        return dump_e(m, p, iid);
    }
    uint32_t dump_e(uint32_t m, P p, uint32_t iid) {
        grow(exp_e, (size_t)iid + 1);
        uint32_t e = exp_e[iid];
        if (e != NONE) return e;
        EKey k = x->ekeys.get(iid);
        uint8_t t = tag(p);
        Out& o = out;
        switch (t) {
            case 0: {
                uint32_t id = next_e(iid);
                o.lit("{\"bvar\":");
                o.n(k.a);
                o.lit(",\"ie\":");
                o.n(id);
                o.ch('}');
                o.nl();
                return id;
            }
            case 3: {
                uint32_t l = dump_level_iid(k.a);
                uint32_t id = next_e(iid);
                o.lit("{\"ie\":");
                o.n(id);
                o.lit(",\"sort\":");
                o.n(l);
                o.ch('}');
                o.nl();
                return id;
            }
            case 4: {
                uint32_t n = dump_name_iid(k.a);
                std::vector<uint32_t> us;
                uint32_t l = k.b;
                while (l != 0) {
                    LLKey c = x->llkeys.get(l);
                    us.push_back(dump_level_iid(c.h));
                    l = c.t;
                }
                uint32_t id = next_e(iid);
                o.lit("{\"const\":{\"name\":");
                o.n(n);
                o.lit(",\"us\":");
                o.arr(us);
                o.lit("},\"ie\":");
                o.n(id);
                o.ch('}');
                o.nl();
                return id;
            }
            case 5: {
                uint32_t fn = dump_e(m, x->child(m, p, 0), k.a);
                uint32_t a = dump_e(m, x->child(m, p, 1), k.b);
                uint32_t id = next_e(iid);
                o.lit("{\"app\":{\"arg\":");
                o.n(a);
                o.lit(",\"fn\":");
                o.n(fn);
                o.lit("},\"ie\":");
                o.n(id);
                o.ch('}');
                o.nl();
                return id;
            }
            case 6:
            case 7: {
                uint32_t n = dump_name(m, rawf(p, 0));
                uint32_t ty = dump_e(m, x->child(m, p, 1), k.a);
                uint32_t b = dump_e(m, x->child(m, p, 2), k.b);
                uint8_t bi = sc_u8(p, 8);
                uint32_t id = next_e(iid);
                if (t == 6) {
                    o.lit("{\"ie\":");
                    o.n(id);
                    o.lit(",\"lam\":{\"binderInfo\":");
                } else {
                    o.lit("{\"forallE\":{\"binderInfo\":");
                }
                switch (bi) {
                    case 0: o.lit("\"default\""); break;
                    case 1: o.lit("\"implicit\""); break;
                    case 2: o.lit("\"strictImplicit\""); break;
                    case 3: o.lit("\"instImplicit\""); break;
                    default: die("bad binderInfo");
                }
                o.lit(",\"body\":");
                o.n(b);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"type\":");
                o.n(ty);
                if (t == 6) {
                    o.lit("}}");
                } else {
                    o.lit("},\"ie\":");
                    o.n(id);
                    o.ch('}');
                }
                o.nl();
                return id;
            }
            case 8: {
                uint32_t n = dump_name(m, rawf(p, 0));
                uint32_t ty = dump_e(m, x->child(m, p, 1), k.a);
                uint32_t v = dump_e(m, x->child(m, p, 2), k.b);
                uint32_t b = dump_e(m, x->child(m, p, 3), k.c);
                uint32_t id = next_e(iid);
                o.lit("{\"ie\":");
                o.n(id);
                o.lit(",\"letE\":{\"body\":");
                o.n(b);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"nondep\":false,\"type\":");
                o.n(ty);
                o.lit(",\"value\":");
                o.n(v);
                o.lit("}}");
                o.nl();
                return id;
            }
            case 9: {
                P lit = x->f(m, p, 0);
                if (tag(lit) == 0) {
                    // dumpNatDeps
                    if (!is_visited(x->n_nat) && x->cmap_has(x->n_nat)) dump_constant(x->n_nat);
                    std::string d = x->nat_dec(m, rawf(lit, 0));
                    uint32_t id = next_e(iid);
                    o.lit("{\"ie\":");
                    o.n(id);
                    o.lit(",\"natVal\":\"");
                    o.s(d.data(), d.size());
                    o.lit("\"}");
                    o.nl();
                    return id;
                } else {
                    // dumpStrDeps
                    if (!is_visited(x->n_charofnat) && x->cmap_has(x->n_charofnat)) dump_constant(x->n_charofnat);
                    if (!is_visited(x->n_stringoflist) && x->cmap_has(x->n_stringoflist)) dump_constant(x->n_stringoflist);
                    P s = x->f(m, lit, 0);
                    uint32_t id = next_e(iid);
                    o.lit("{\"ie\":");
                    o.n(id);
                    o.lit(",\"strVal\":");
                    o.jstr(str_data(s), str_len(s));
                    o.ch('}');
                    o.nl();
                    return id;
                }
            }
            case 11: {
                uint32_t n = dump_name_iid(k.a);
                uint32_t ex = dump_e(m, x->child(m, p, 2), k.c);
                uint32_t id = next_e(iid);
                o.lit("{\"ie\":");
                o.n(id);
                o.lit(",\"proj\":{\"idx\":");
                o.n(k.b);
                o.lit(",\"struct\":");
                o.n(ex);
                o.lit(",\"typeName\":");
                o.n(n);
                o.lit("}}");
                o.nl();
                return id;
            }
            default: die("cannot export expr tag " + std::to_string(t));
        }
    }

    // ---------------- constants
    // getUsedConstants: first occurrences in left-to-right order, mdata transparent; computed on the interned
    // DAG.  Visiting by structural class instead of by pointer, and skipping already exported classes (all their
    // constants were dumped before them), does not change the order of first occurrences of unvisited constants.
    void used_consts(uint32_t root, std::vector<uint32_t>& outv) {
        gen++;
        if (gen == 0) {
            eseen.zero_all();
            cseen.zero_all();
            gen = 1;
        }
        uint32_t g = gen;
        size_t ne = x->ec.load(std::memory_order_relaxed);
        if (eseen.size() < ne) eseen.resize(ne + (ne >> 2) + 1024, 0);
        grow(exp_e, ne);
        size_t nn = x->nc.load(std::memory_order_relaxed);
        if (cseen.size() < nn) cseen.resize(nn + (nn >> 2) + 1024, 0);
        std::vector<uint32_t>& stack = ustack;
        stack.clear();
        stack.push_back(root);
        while (!stack.empty()) {
            uint32_t i = stack.back();
            stack.pop_back();
            if (eseen[i] == g) continue;
            eseen[i] = g;
            if (exp_e[i] != NONE) continue;
            EKey k = x->ekeys.get(i);
            switch (k.kind) {
                case 5:
                case 6:
                case 7:
                    stack.push_back(k.b);
                    stack.push_back(k.a);
                    break;
                case 8:
                    stack.push_back(k.c);
                    stack.push_back(k.b);
                    stack.push_back(k.a);
                    break;
                case 11: stack.push_back(k.c); break;
                case 4:
                    if (cseen[k.a] != g) {
                        cseen[k.a] = g;
                        outv.push_back(k.a);
                    }
                    break;
                default: break;
            }
        }
    }
    std::vector<uint32_t> ustack;
    void dump_deps(uint32_t m, P e) {
        uint32_t root = intern_expr(m, e);
        std::vector<uint32_t> cs;
        used_consts(root, cs);
        for (uint32_t c : cs) dump_constant(c);
    }
    std::vector<uint32_t> dump_names(uint32_t m, uint64_t r) {
        std::vector<uint32_t> ns;
        x->list_names(m, r, ns);
        for (auto& n : ns) n = dump_name_iid(n);
        return ns;
    }
    std::vector<uint32_t> dump_uparams(uint32_t m, uint64_t r) {
        std::vector<uint32_t> ns;
        x->list_names(m, r, ns);
        std::vector<uint32_t> ids;
        for (uint32_t n : ns) ids.push_back(dump_name_iid(n));
        for (uint32_t n : ns) dump_level_iid(x->level_key_insert(LKey{4, n, 0}));
        return ids;
    }
    // (name idx, levelParams idxs, type idx) of a ConstantVal, dumped in lean4export order
    void dump_cval(uint32_t m, P cval, uint32_t& n, std::vector<uint32_t>& lps, uint32_t& t) {
        n = dump_name(m, rawf(cval, 0));
        lps = dump_uparams(m, rawf(cval, 1));
        t = dump_expr(m, x->f(m, cval, 2));
    }
    void missing(uint32_t c) {
        // F04 (fail closed): the official exporter panics and continues here; its exact output on that path is not
        // reproduced natively -> decline (the wrapper runs the official exporter)
        die("constant " + x->name_str(c) + " not found in environment (declining)");
    }

    void dump_constant(uint32_t c) {
        CRef r = get(c);
        if (r.m == NONE) {
            missing(c);
            return;
        }
        if (is_visited(c) || x->is_unsafe(r)) return;  // cheap check first (is_unsafe reads the olean)
        set_visited(c);
        uint32_t m = r.m;
        P val, cval;
        x->vals(r, val, cval);
        P ty = x->f(m, cval, 2);
        switch (tag(r.ci)) {
            case 0: dump_deps(m, ty); own_simple(r); break;
            case 1:
            case 2:
            case 3:
                dump_deps(m, ty);
                dump_deps(m, x->f(m, val, 1));
                own_simple(r);
                break;
            case 4:
                dump_constant(x->n_eq);
                own_quot();
                break;
            case 5: dump_inductive(r); break;
            case 6: dump_constant(x->intern_name(m, rawf(val, 1))); break;
            case 7: {
                std::vector<uint32_t> all;
                x->list_names(m, rawf(val, 1), all);
                for (uint32_t ind : all) dump_constant(ind);
                break;
            }
            default: die("bad ConstantInfo tag");
        }
    }
    // own lines of an axiom/definition/theorem/opaque whose dependencies are already dumped
    void own_simple(const CRef& r) {
        uint32_t m = r.m;
        P val, cval;
        x->vals(r, val, cval);
        uint32_t n, t;
        std::vector<uint32_t> lps;
        switch (tag(r.ci)) {
            case 0: {
                dump_cval(m, cval, n, lps, t);
                Out& o = out;
                o.lit("{\"axiom\":{\"isUnsafe\":");
                o.b(sc_u8(val, 0) != 0);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"type\":");
                o.n(t);
                o.lit("}}");
                o.nl();
                break;
            }
            case 1: {
                P value = x->f(m, val, 1);
                dump_cval(m, cval, n, lps, t);
                uint32_t v = dump_expr(m, value);
                uint64_t hints = rawf(val, 2);
                std::vector<uint32_t> all = dump_names(m, rawf(val, 3));
                uint8_t safety = sc_u8(val, 0);
                Out& o = out;
                o.lit("{\"def\":{\"all\":");
                o.arr(all);
                o.lit(",\"hints\":");
                if (is_scalar(hints)) {
                    if ((hints >> 1) == 0)
                        o.lit("\"opaque\"");
                    else
                        o.lit("\"abbrev\"");
                } else {
                    o.lit("{\"regular\":");
                    o.n(sc_u32(x->tr(m, hints), 0));
                    o.ch('}');
                }
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"safety\":");
                if (safety == 0)
                    o.lit("\"unsafe\"");
                else if (safety == 1)
                    o.lit("\"safe\"");
                else
                    o.lit("\"partial\"");
                o.lit(",\"type\":");
                o.n(t);
                o.lit(",\"value\":");
                o.n(v);
                o.lit("}}");
                o.nl();
                break;
            }
            case 2: {
                P value = x->f(m, val, 1);
                dump_cval(m, cval, n, lps, t);
                uint32_t v = dump_expr(m, value);
                std::vector<uint32_t> all = dump_names(m, rawf(val, 2));
                Out& o = out;
                o.lit("{\"thm\":{\"all\":");
                o.arr(all);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"type\":");
                o.n(t);
                o.lit(",\"value\":");
                o.n(v);
                o.lit("}}");
                o.nl();
                break;
            }
            case 3: {
                P value = x->f(m, val, 1);
                dump_cval(m, cval, n, lps, t);
                uint32_t v = dump_expr(m, value);
                std::vector<uint32_t> all = dump_names(m, rawf(val, 2));
                Out& o = out;
                o.lit("{\"opaque\":{\"all\":");
                o.arr(all);
                o.lit(",\"isUnsafe\":");
                o.b(sc_u8(val, 0) != 0);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"type\":");
                o.n(t);
                o.lit(",\"value\":");
                o.n(v);
                o.lit("}}");
                o.nl();
                break;
            }
            default: die("own_simple: bad ConstantInfo tag");
        }
    }
    // own lines of the Quot block (Eq is already dumped)
    void own_quot() {
        for (int qi = 0; qi < 4; qi++) {
            uint32_t qn = x->n_quot[qi];
            CRef qr = get(qn);
            if (qr.m == NONE) {
                missing(qn);
                return;
            }
            if (tag(qr.ci) != 4) die("expected quotInfo");
            set_visited(qn);
            P qval, qcval;
            x->vals(qr, qval, qcval);
            uint32_t qn2, qt;
            std::vector<uint32_t> qlps;
            dump_cval(qr.m, qcval, qn2, qlps, qt);
            uint8_t kind = sc_u8(qval, 0);
            Out& o = out;
            o.lit("{\"quot\":{\"kind\":");
            if (kind == 0)
                o.lit("\"type\"");
            else if (kind == 1)
                o.lit("\"ctor\"");
            else if (kind == 2)
                o.lit("\"lift\"");
            else
                o.lit("\"ind\"");
            o.lit(",\"levelParams\":");
            o.arr(qlps);
            o.lit(",\"name\":");
            o.n(qn2);
            o.lit(",\"type\":");
            o.n(qt);
            o.lit("}}");
            o.nl();
        }
    }

    int quick_cmp(uint32_t a, uint32_t b) {
        if (a == b) return 0;
        uint64_t ha = a == 0 ? 1723 : x->names.get(a).hash;
        uint64_t hb = b == 0 ? 1723 : x->names.get(b).hash;
        if (ha < hb) return -1;
        if (ha > hb) return 1;
        return quick_cmp_aux(a, b);
    }
    int quick_cmp_aux(uint32_t a, uint32_t b) {
        if (a == 0 && b == 0) return 0;
        if (a == 0) return -1;
        if (b == 0) return 1;
        NKey ka = x->names.get(a).key;
        NKey kb = x->names.get(b).key;
        if (ka.kind == 2 && kb.kind == 2) {
            if (ka.num < kb.num) return -1;
            if (ka.num > kb.num) return 1;
            return quick_cmp_aux(ka.pre, kb.pre);
        }
        if (ka.kind == 2) return -1;  // num < str
        if (kb.kind == 2) return 1;
        size_t l = std::min(ka.len, kb.len);
        int c = memcmp(ka.ptr, kb.ptr, l);
        if (c == 0) c = ka.len < kb.len ? -1 : (ka.len > kb.len ? 1 : 0);
        if (c != 0) return c < 0 ? -1 : 1;
        return quick_cmp_aux(ka.pre, kb.pre);
    }

    // render into a separate buffer (inductive block parts are assembled after all sub-dumps)
    template <class F>
    std::string render(F fn) {
        Out tmp;
        tmp.cap = 1 << 12;
        tmp.buf = (char*)malloc(tmp.cap);
        fn(tmp);
        std::string s(tmp.buf, tmp.len);
        free(tmp.buf);
        tmp.buf = nullptr;
        return s;
    }

    struct IndLists {
        std::vector<uint32_t> inds, ctor_names, rec_names;
        std::vector<CRef> ind_vals, ctor_vals, rec_vals;
    };
    // the members of the inductive block of `base`: types, constructors, recursors (sorted by Name.quickCmp)
    void ind_lists(const CRef& base, IndLists& L) {
        P bval, bcval;
        x->vals(base, bval, bcval);
        uint32_t bm = base.m;
        uint32_t base_name = x->intern_name(bm, rawf(bcval, 0));
        x->list_names(bm, rawf(bval, 3), L.inds);
        for (uint32_t ind : L.inds) {
            CRef ir = get(ind);
            if (ir.m == NONE || tag(ir.ci) != 5) die("inductiveVal! failed");
            L.ind_vals.push_back(ir);
            P ival, icval;
            x->vals(ir, ival, icval);
            std::vector<uint32_t> ctors;
            x->list_names(ir.m, rawf(ival, 4), ctors);
            for (uint32_t ct : ctors) {
                CRef cr = get(ct);
                if (cr.m == NONE || tag(cr.ci) != 6) die("Expected a ConstantInfo.ctorInfo");
                L.ctor_vals.push_back(cr);
            }
            auto it = x->recmap.find(base_name);
            if (it != x->recmap.end()) {
                for (uint32_t rn : it->second)
                    if (std::find(L.rec_names.begin(), L.rec_names.end(), rn) == L.rec_names.end()) L.rec_names.push_back(rn);
            } else if (!L.ctor_vals.empty() && !x->is_unsafe(base)) {
                // F04 (fail closed): official `assert! ctorVals.size == 0` fails (panic-and-continue path) -> decline
                die("inductive block without recursor but with constructors (declining)");
            }
        }
        // F04 (fail closed): the official exporter asserts that no member of a safe block (it never dumps unsafe
        // bases) is unsafe; on that panic path its output is not reproduced natively -> decline
        const bool base_safe = !x->is_unsafe(base);
        if (base_safe) {
            for (const CRef& r : L.ind_vals) if (x->is_unsafe(r)) die("unsafe inductive in a block (declining)");
            for (const CRef& r : L.ctor_vals) if (x->is_unsafe(r)) die("unsafe constructor in a block (declining)");
        }
        for (const CRef& cr : L.ctor_vals) {
            P cval_, ccval;
            x->vals(cr, cval_, ccval);
            L.ctor_names.push_back(x->intern_name(cr.m, rawf(ccval, 0)));
        }
        std::sort(L.rec_names.begin(), L.rec_names.end(), [&](uint32_t a, uint32_t b) { return quick_cmp(a, b) < 0; });
        for (uint32_t rn : L.rec_names) {
            CRef rr = get(rn);
            if (rr.m == NONE || tag(rr.ci) != 7) die("expected a constantinfo.recinfo");
            if (base_safe && x->is_unsafe(rr)) die("unsafe recursor in a block (declining)");
            L.rec_vals.push_back(rr);
        }
    }

    void dump_inductive(const CRef& base) {
        IndLists L;
        ind_lists(base, L);
        for (size_t i = 0; i < L.ind_vals.size(); i++) {
            const CRef& ir = L.ind_vals[i];
            P ival, icval;
            x->vals(ir, ival, icval);
            set_visited(L.inds[i]);
            dump_deps(ir.m, x->f(ir.m, icval, 2));
        }
        for (size_t i = 0; i < L.ctor_vals.size(); i++) {
            const CRef& cr = L.ctor_vals[i];
            P cval_, ccval;
            x->vals(cr, cval_, ccval);
            set_visited(L.ctor_names[i]);
            dump_deps(cr.m, x->f(cr.m, ccval, 2));
        }
        for (size_t i = 0; i < L.rec_vals.size(); i++) {
            set_visited(L.rec_names[i]);
            P rval, rcval;
            x->vals(L.rec_vals[i], rval, rcval);
            dump_deps(L.rec_vals[i].m, x->f(L.rec_vals[i].m, rcval, 2));
        }
        for (const CRef& rr : L.rec_vals) {
            P rval, rcval;
            x->vals(rr, rval, rcval);
            uint64_t rl = rawf(rval, 6);
            while (!is_scalar(rl)) {
                P cell = x->tr(rr.m, rl);
                P rule = x->f(rr.m, cell, 0);
                dump_deps(rr.m, x->f(rr.m, rule, 2));
                rl = rawf(cell, 1);
            }
        }
        own_inductive(L);
    }
    // own lines of an inductive block whose dependencies are already dumped (members are marked visited)
    void own_inductive(const IndLists& L) {
        const std::vector<CRef>& ind_vals = L.ind_vals;
        const std::vector<CRef>& ctor_vals = L.ctor_vals;
        const std::vector<CRef>& rec_vals = L.rec_vals;
        // JSON parts (dump order per type: name, levelParams, type, all, ctors)
        std::vector<std::string> tj, cj, rj;
        for (const CRef& ir : ind_vals) {
            P ival, icval;
            x->vals(ir, ival, icval);
            uint32_t m = ir.m;
            uint32_t n, t;
            std::vector<uint32_t> lps;
            dump_cval(m, icval, n, lps, t);
            std::vector<uint32_t> all2 = dump_names(m, rawf(ival, 3));
            std::vector<uint32_t> ctors = dump_names(m, rawf(ival, 4));
            uint64_t np = x->nat_small(m, rawf(ival, 1));
            uint64_t ni = x->nat_small(m, rawf(ival, 2));
            uint64_t nn = x->nat_small(m, rawf(ival, 5));
            bool is_rec = sc_u8(ival, 0) != 0, is_unsafe = sc_u8(ival, 1) != 0, is_refl = sc_u8(ival, 2) != 0;
            tj.push_back(render([&](Out& o) {
                o.lit("{\"all\":");
                o.arr(all2);
                o.lit(",\"ctors\":");
                o.arr(ctors);
                o.lit(",\"isRec\":");
                o.b(is_rec);
                o.lit(",\"isReflexive\":");
                o.b(is_refl);
                o.lit(",\"isUnsafe\":");
                o.b(is_unsafe);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"numIndices\":");
                o.n(ni);
                o.lit(",\"numNested\":");
                o.n(nn);
                o.lit(",\"numParams\":");
                o.n(np);
                o.lit(",\"type\":");
                o.n(t);
                o.ch('}');
            }));
        }
        for (const CRef& cr : ctor_vals) {
            P cv, ccval;
            x->vals(cr, cv, ccval);
            uint32_t m = cr.m;
            uint32_t n, t;
            std::vector<uint32_t> lps;
            dump_cval(m, ccval, n, lps, t);
            uint32_t induct = dump_name(m, rawf(cv, 1));
            uint64_t cidx = x->nat_small(m, rawf(cv, 2));
            uint64_t np = x->nat_small(m, rawf(cv, 3));
            uint64_t nf = x->nat_small(m, rawf(cv, 4));
            bool uns = sc_u8(cv, 0) != 0;
            cj.push_back(render([&](Out& o) {
                o.lit("{\"cidx\":");
                o.n(cidx);
                o.lit(",\"induct\":");
                o.n(induct);
                o.lit(",\"isUnsafe\":");
                o.b(uns);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"numFields\":");
                o.n(nf);
                o.lit(",\"numParams\":");
                o.n(np);
                o.lit(",\"type\":");
                o.n(t);
                o.ch('}');
            }));
        }
        for (const CRef& rr : rec_vals) {
            P rval, rcval;
            x->vals(rr, rval, rcval);
            uint32_t m = rr.m;
            uint32_t n, t;
            std::vector<uint32_t> lps;
            dump_cval(m, rcval, n, lps, t);
            std::vector<uint32_t> all2 = dump_names(m, rawf(rval, 1));
            struct Rule {
                uint32_t ctor;
                uint64_t nf;
                uint32_t rhs;
            };
            std::vector<Rule> rules;
            uint64_t rl = rawf(rval, 6);
            while (!is_scalar(rl)) {
                P cell = x->tr(m, rl);
                P rule = x->f(m, cell, 0);
                uint32_t ctor = dump_name(m, rawf(rule, 0));
                uint64_t nf = x->nat_small(m, rawf(rule, 1));
                uint32_t rhs = dump_expr(m, x->f(m, rule, 2));
                rules.push_back(Rule{ctor, nf, rhs});
                rl = rawf(cell, 1);
            }
            uint64_t np = x->nat_small(m, rawf(rval, 2));
            uint64_t ni = x->nat_small(m, rawf(rval, 3));
            uint64_t nmo = x->nat_small(m, rawf(rval, 4));
            uint64_t nmi = x->nat_small(m, rawf(rval, 5));
            bool kk = sc_u8(rval, 0) != 0, uns = sc_u8(rval, 1) != 0;
            rj.push_back(render([&](Out& o) {
                o.lit("{\"all\":");
                o.arr(all2);
                o.lit(",\"isUnsafe\":");
                o.b(uns);
                o.lit(",\"k\":");
                o.b(kk);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"numIndices\":");
                o.n(ni);
                o.lit(",\"numMinors\":");
                o.n(nmi);
                o.lit(",\"numMotives\":");
                o.n(nmo);
                o.lit(",\"numParams\":");
                o.n(np);
                o.lit(",\"rules\":[");
                for (size_t i = 0; i < rules.size(); i++) {
                    if (i) o.ch(',');
                    o.lit("{\"ctor\":");
                    o.n(rules[i].ctor);
                    o.lit(",\"nfields\":");
                    o.n(rules[i].nf);
                    o.lit(",\"rhs\":");
                    o.n(rules[i].rhs);
                    o.ch('}');
                }
                o.lit("],\"type\":");
                o.n(t);
                o.ch('}');
            }));
        }
        Out& o = out;
        o.lit("{\"inductive\":{\"ctors\":[");
        for (size_t i = 0; i < cj.size(); i++) {
            if (i) o.ch(',');
            o.s(cj[i].data(), cj[i].size());
        }
        o.lit("],\"recs\":[");
        for (size_t i = 0; i < rj.size(); i++) {
            if (i) o.ch(',');
            o.s(rj[i].data(), rj[i].size());
        }
        o.lit("],\"types\":[");
        for (size_t i = 0; i < tj.size(); i++) {
            if (i) o.ch(',');
            o.s(tj[i].data(), tj[i].size());
        }
        o.lit("]}}");
        o.nl();
    }
};

// ------------------------------------------------------------------------------------------------
// parallel dump (phase B on many threads) -- produces exactly St's output.
//
// St's output is a sequence of "units" (an axiom/definition/theorem/opaque, the Quot block, an inductive block): a
// unit first dumps its dependencies (other units, recursively), then its OWN lines (the names, levels and
// expressions that were not dumped before, in DFS order, then the constant line).
//  B1 (parallel)   the used-constant lists of every constant of the closure (full walk of each root's class DAG:
//                  St prunes already exported subterms, which never changes the order of the constants that are
//                  not visited yet, so the full lists replay identically), plus "contains a Nat/String literal".
//  B2 (sequential) St's dump_constant recursion replayed on those lists (same visited set) -> the unit order.
//  epoch (parallel, for a run of units u0..u1):
//   P1  owner(class) = first unit whose own-line expressions contain it (atomic min, pruned below classes that
//       already have a smaller owner or were exported before the epoch);
//   P2  each unit walks its owned classes in exact dump order from the real occurrences (the first occurrence is the
//       one printed: binder names/infos), recording events (name/level references, expression lines, constant
//       lines); names and levels get owners by atomic min the same way; expressions get unit-local numbers;
//   P3  unit-local numbers of the owned names/levels (first reference in event order, prefix/children first);
//   P4  prefix sums over the units -> global ids;  P5 global ids of all owned items;
//   P6  every unit renders its lines from the events (chunks of units in parallel), queued in order.
// A unit whose own lines would dump Nat/Char.ofNat/String.ofList in the middle of an expression (dumpNatDeps/
// dumpStrDeps: a literal while that constant is not visited yet) is dumped by St itself between two epochs.
struct RBuf {  // render buffer (same rendering as Out); memory from the output sink if `sink` is set
    char* buf = nullptr;
    size_t len = 0, cap = 0;
    OSink* sink = nullptr;
    void init(size_t c) {
        len = 0;
        if (sink) {
            buf = sink->get_buffer(c, cap);
            return;
        }
        cap = c;
        buf = (char*)malloc(cap);
        if (!buf) die("out of memory (render buffer)");
    }
    void reserve(size_t n) {
        if (len + n <= cap) return;
        if (sink) {
            buf = sink->grow(buf, cap, len + n + (1u << 20));
            return;
        }
        size_t nc = std::max(cap * 2, len + n + (1u << 20));
        char* nb = (char*)realloc(buf, nc);
        if (!nb) die("out of memory (render buffer)");
        buf = nb;
        cap = nc;
    }
    inline void s(const char* p, size_t n) {
        reserve(n);
        memcpy(buf + len, p, n);
        len += n;
    }
    template <size_t N>
    inline void lit(const char (&p)[N]) {
        s(p, N - 1);
    }
    inline void n(uint64_t v) {  // = Out::n
        unsigned d = v < 10 ? 1 : Out::dec_len(v);
        reserve(d);
        Out::dec_put(buf + len + d, v);
        len += d;
    }
    inline void ch(char c) {
        reserve(1);
        buf[len++] = c;
    }
    void jstr(const uint8_t* p, size_t n) {  // = Out::jstr
        if (!utf8_ok(p, n)) die("string is not valid UTF-8");
        reserve(n * 6 + 2);
        char* o = buf + len;
        *o++ = '"';
        static const char HX[] = "0123456789abcdef";
        for (size_t i = 0; i < n; i++) {
            uint8_t c = p[i];
            if (c == '"') {
                *o++ = '\\';
                *o++ = '"';
            } else if (c == '\\') {
                *o++ = '\\';
                *o++ = '\\';
            } else if (c == '\n') {
                *o++ = '\\';
                *o++ = 'n';
            } else if (c == '\r') {
                *o++ = '\\';
                *o++ = 'r';
            } else if (c < 0x20) {
                *o++ = '\\';
                *o++ = 'u';
                *o++ = '0';
                *o++ = '0';
                *o++ = HX[c >> 4];
                *o++ = HX[c & 15];
            } else {
                *o++ = (char)c;
            }
        }
        *o++ = '"';
        len = o - buf;
    }
    inline void b(bool v) {
        if (v)
            lit("true");
        else
            lit("false");
    }
    inline void nl() { ch('\n'); }
    void arr(const std::vector<uint32_t>& xs) {
        ch('[');
        for (size_t i = 0; i < xs.size(); i++) {
            if (i) ch(',');
            n(xs[i]);
        }
        ch(']');
    }
};

// small open-addressing set of ids (B1's per-constant visited sets): stays in L1/L2 for a typical constant (a few
// hundred classes) instead of one random access per class into a table of all classes
struct VisSet {
    uint32_t* t = nullptr;  // id + 1, 0 = empty
    uint32_t mask = 0, n = 0;
    std::vector<uint32_t> used;  // occupied slots (cheap clear)
    void init(uint32_t cap) {
        t = (uint32_t*)calloc(cap, sizeof(uint32_t));
        if (!t) die("out of memory (VisSet)");
        mask = cap - 1;
        n = 0;
        used.clear();
        used.reserve(cap / 2 + 1);
    }
    static inline uint32_t h(uint32_t x) { return (x * 0x9E3779B1u) ^ (x >> 13); }
    inline bool insert(uint32_t id) {  // true if id was not in the set
        uint32_t k = id + 1, j = h(id) & mask;
        while (true) {
            uint32_t v = t[j];
            if (v == k) return false;
            if (v == 0) break;
            j = (j + 1) & mask;
        }
        t[j] = k;
        used.push_back(j);
        if (++n * 2 > mask) grow();
        return true;
    }
    void grow() {
        uint32_t nc = (mask + 1) * 2;
        uint32_t* nt = (uint32_t*)calloc(nc, sizeof(uint32_t));
        if (!nt) die("out of memory (VisSet)");
        std::vector<uint32_t> nu;
        nu.reserve(nc / 2 + 1);
        for (uint32_t j : used) {
            uint32_t k = t[j], i = h(k - 1) & (nc - 1);
            while (nt[i]) i = (i + 1) & (nc - 1);
            nt[i] = k;
            nu.push_back(i);
        }
        free(t);
        t = nt;
        mask = nc - 1;
        used.swap(nu);
    }
    void clear() {
        if (mask + 1 > (1u << 16)) {  // after a huge constant: back to a cache-sized table
            free(t);
            init(1u << 12);
            return;
        }
        for (uint32_t j : used) t[j] = 0;
        used.clear();
        n = 0;
    }
};

template <class F>
static void par_run(size_t nthreads, size_t stack, F body) {  // body(thread index) on nthreads threads
    std::vector<std::function<void()>> fns;
    for (size_t t = 0; t < nthreads; t++) fns.push_back([&body, t] { body(t); });
    run_with_stack(stack, fns);
}

struct PD {
    In* x;
    St* st;
    size_t nthreads;
    double t_last = 0;

    // ---- B1: used-constant lists
    struct DL {
        uint32_t off = 0, n1 = 0, n2 = 0;  // n1 entries for the type, then n2 for the value / recursor rules,
        uint32_t n3 = 0;                     // then n3 "members": ctor: [induct]; recursor: all; inductive: see b1
        uint16_t tid = 0;                    // dlbuf index (= B1 / phase-A worker); F04: was uint8_t (wrapped at > 256
                                             // threads -> used-constant lists of the wrong worker -> missing constants;
                                             // team E's fix 65bbc36 was not in f581123)
        uint8_t lit = 0;                     // lit: 1 = contains a Nat literal, 2 = a String literal
        uint8_t kind = 0xff;                 // ConstantInfo tag (0xff = not a safe closure constant)
    };
    std::vector<DL> dl;
    std::vector<std::vector<uint32_t>> dlbuf;  // per B1 thread
    inline const uint32_t* dl_ptr(const DL& d) const { return dlbuf[d.tid].data() + d.off; }

    // ---- B2: units
    struct Unit {
        uint32_t c;    // constant (inductive: the base given to dump_inductive; quot: the constant hit)
        uint8_t kind;  // 0 axiom/defn/thm/opaque, 1 quot, 2 inductive
    };
    std::vector<Unit> units;
    size_t epoch_start = 0;
    size_t n_epochs = 0, n_special = 0;

    // ---- epoch state (sized once; owners are global unit indices, stored as NONE - k so that 0 = none)
    struct OL {  // per expr class: owner (NONE - unit, 0 = none) and unit-local index + 1 (0 = none), one cache line
        std::atomic<uint32_t> own;
        uint32_t loc;
    };
    OL* ol = nullptr;
    std::atomic<uint32_t>* own_n = nullptr;
    std::atomic<uint32_t>* own_l = nullptr;
    uint32_t* loc_n = nullptr;
    uint32_t* loc_l = nullptr;
    size_t ne = 0, nn = 0, nl = 0;

    struct Ev {
        uint32_t iid;  // expr class / name / level id
        uint32_t aux;  // EV_EXPR: binder name id (binders), literal index (literals); EV_LINE: line index
        uint8_t kind;
        uint8_t bi;
    };
    enum : uint8_t { EV_NAME = 0, EV_LEVEL = 1, EV_EXPR = 2, EV_LINE = 3 };
    struct EvArena {  // per-thread event storage of an epoch (huge pages, first touch = write)
        Ev* p = nullptr;
        size_t n = 0, cap = 0;
        std::vector<std::pair<uint32_t, P>> lits;  // (module, Expr.lit object), indexed by Ev::aux
        void init(size_t c) {
            cap = c;
            n = 0;
            const char* e = getenv("LEAN4EXPORT_ARENA_THP");
            p = (Ev*)((e && e[0] == '0') ? zalloc(c * sizeof(Ev)) : zalloc_huge(c * sizeof(Ev)));
        }
        inline void push(const Ev& e) {
            if (n == cap) {
                Ev* q = (Ev*)zalloc_huge(cap * 2 * sizeof(Ev));
                memcpy(q, p, n * sizeof(Ev));
                p = q;  // (old region left to the teardown; growth is rare: arenas start at 2x the fair share)
                cap *= 2;
            }
            p[n++] = e;
        }
    };
    std::vector<EvArena> arenas;  // per thread
    struct UData {
        size_t off = 0;                   // events: arenas[tid].p[off .. off + nev)
        uint32_t nev = 0, tid = 0;
        uint32_t ce = 0, cn = 0, cl = 0;  // own expressions / names / levels
        uint32_t be = 0, bn = 0, bl = 0;  // global base ids
        inline const Ev* ev(const PD& pd) const { return pd.arenas[tid].p + off; }
    };
    std::vector<UData> ud;  // per unit of the current epoch
    size_t u0 = 0;

    static inline uint32_t owner(const std::atomic<uint32_t>& a) { return NONE - a.load(std::memory_order_relaxed); }
    static inline bool lower(std::atomic<uint32_t>& a, uint32_t k) {  // owner := min(owner, k); true if it was > k
        uint32_t want = NONE - k;
        uint32_t cur = a.load(std::memory_order_relaxed);
        while (cur < want)
            if (a.compare_exchange_weak(cur, want, std::memory_order_relaxed)) return true;
        return false;
    }
    long flt_last = 0;
    double cpu_last = 0;
    void lap(const char* what) {
        double t = now_s();
        struct rusage ru;
        getrusage(RUSAGE_SELF, &ru);
        double cpu = ru.ru_utime.tv_sec + ru.ru_utime.tv_usec * 1e-6 + ru.ru_stime.tv_sec + ru.ru_stime.tv_usec * 1e-6;
        if (g_verbose)
            fprintf(stderr, "lean4export (native) [%.2fs wall] parallel dump: %s %.3f s (cpu %.1f s, minflt %ld)\n", t - g_t0, what,
                    t - t_last, cpu - cpu_last, ru.ru_minflt - flt_last);
        t_last = t;
        cpu_last = cpu;
        flt_last = ru.ru_minflt;
    }
    static void* big_zalloc(size_t bytes) { return zalloc_huge(bytes); }

    // ================================================================================================ B1
    // roots of constant c (dump_deps order): type; value (defn/thm/opaque) or rule right-hand sides (recursor)
    template <class F>
    void const_roots(uint32_t c, F f) {
        const CRef& r = x->cmap[c];
        uint32_t m = r.m;
        P val, cval;
        x->vals(r, val, cval);
        f(0, m, x->f(m, cval, 2));
        uint8_t tg = tag(r.ci);
        if (tg == 1 || tg == 2 || tg == 3) {
            f(1, m, x->f(m, val, 1));
        } else if (tg == 7) {
            uint64_t rl = rawf(val, 6);
            while (!is_scalar(rl)) {
                P cell = x->tr(m, rl);
                P rule = x->f(m, cell, 0);
                f(1, m, x->f(m, rule, 2));
                rl = rawf(cell, 1);
            }
        }
    }
    void b1(const std::vector<uint32_t>& closure) {
        dl.assign(x->cmap.size(), DL{});
        dlbuf.assign(nthreads, std::vector<uint32_t>());
        size_t nnc = x->nc.load() + 1;
        std::atomic<size_t> next{0};
        par_run(nthreads, (size_t)64 << 20, [&](size_t tid) {
            VisSet eseen, cseen;  // classes / constants seen for the current constant
            eseen.init(1u << 12);
            cseen.init(1u << 8);
            std::vector<uint32_t>& out = dlbuf[tid];
            std::vector<uint32_t> stack, disc, lps;
            while (true) {
                size_t j = next.fetch_add(32);
                if (j >= closure.size()) break;
                size_t je = std::min(closure.size(), j + 32);
                for (size_t q = j; q < je; q++) {
                    uint32_t c = closure[q];
                    DL d;
                    if (tid > 0xffff) die("internal: too many threads for the used-constant lists");
                    d.tid = (uint16_t)tid;
                    d.off = (uint32_t)out.size();
                    // One stamp for all roots of c: a constant already listed for an earlier root is visited when the
                    // later root's list is replayed, so it is dropped there, and classes seen in an earlier root are not
                    // walked again (their constants are all listed already; the order of the others is unchanged).
                    eseen.clear();
                    cseen.clear();
                    const_roots(c, [&](int which, uint32_t m, P e) {
                        uint32_t root = x->intern_expr(m, e, disc);
                        disc.clear();
                        size_t before = out.size();
                        stack.clear();
                        stack.push_back(root);
                        while (!stack.empty()) {  // = St::used_consts without the exported-class pruning
                            uint32_t i = stack.back();
                            stack.pop_back();
                            if (!eseen.insert(i)) continue;
                            EKey k = x->ekeys.get(i);
                            switch (k.kind) {
                                case 5:
                                case 6:
                                case 7:
                                    stack.push_back(k.b);
                                    stack.push_back(k.a);
                                    break;
                                case 8:
                                    stack.push_back(k.c);
                                    stack.push_back(k.b);
                                    stack.push_back(k.a);
                                    break;
                                case 11: stack.push_back(k.c); break;
                                case 4:
                                    if (cseen.insert(k.a)) out.push_back(k.a);
                                    break;
                                case 9: d.lit |= 1; break;
                                case 12: d.lit |= 2; break;
                                default: break;
                            }
                        }
                        uint32_t added = (uint32_t)(out.size() - before);
                        if (which == 0)
                            d.n1 += added;
                        else
                            d.n2 += added;
                    });
                    {
                        const CRef& r = x->cmap[c];
                        P val, cval;
                        x->vals(r, val, cval);
                        // the level `param u` of every universe parameter (dump_uparams creates it if no expression has it)
                        lps.clear();
                        x->list_names(r.m, rawf(cval, 1), lps);
                        for (uint32_t n : lps) x->level_key_insert(LKey{4, n, 0});
                        // members for B2 (so that the sequential replay touches no olean memory)
                        d.kind = tag(r.ci);
                        size_t before = out.size();
                        if (d.kind == 5) {  // [#types, types.., #ctors, ctors.., #recs, recs (sorted)..] = St::ind_lists
                            St::IndLists L;
                            st->ind_lists(r, L);
                            out.push_back((uint32_t)L.inds.size());
                            out.insert(out.end(), L.inds.begin(), L.inds.end());
                            out.push_back((uint32_t)L.ctor_names.size());
                            out.insert(out.end(), L.ctor_names.begin(), L.ctor_names.end());
                            out.push_back((uint32_t)L.rec_names.size());
                            out.insert(out.end(), L.rec_names.begin(), L.rec_names.end());
                        } else if (d.kind == 6) {
                            out.push_back(x->intern_name(r.m, rawf(val, 1)));
                        } else if (d.kind == 7) {
                            x->list_names(r.m, rawf(val, 1), out);
                        }
                        d.n3 = (uint32_t)(out.size() - before);
                    }
                    if (out.size() > (size_t)0xffffffffu) die("used-constant lists too large");
                    dl[c] = d;
                }
            }
            free(eseen.t);
            free(cseen.t);
        });
        if (x->nc.load() + 1 > nnc) die("internal: names created during B1");
    }

    // ================================================================================================ B2
    std::vector<uint8_t> unsafe_c;  // 1 = unsafe constant (dump_constant returns without marking it visited)
    // bit c = visited by B2 or unsafe (a compact filter in front of sim_constant's own checks; St's visits during
    // special units are not mirrored here, sim_constant still checks St's visited set)
    std::vector<uint64_t> skipb;
    size_t skip_lim = 0;
    inline bool visited(uint32_t c) const { return st->is_visited(c); }
    inline void mark_visited(uint32_t c) {
        st->set_visited(c);
        if (c < skip_lim) skipb[c >> 6] |= 1ull << (c & 63);
    }
    void sim_list(const uint32_t* p, uint32_t n) {
        const uint64_t* sb = skipb.data();
        for (uint32_t i = 0; i < n; i++) {
            uint32_t d = p[i];
            if (d < skip_lim && ((sb[d >> 6] >> (d & 63)) & 1)) continue;
            sim_constant(d);
        }
    }
    void sim_type(uint32_t c) {
        const DL& d = dl[c];
        sim_list(dl_ptr(d), d.n1);
    }
    void sim_value(uint32_t c) {
        const DL& d = dl[c];
        sim_list(dl_ptr(d) + d.n1, d.n2);
    }
    // would the own lines of this unit trigger dumpNatDeps / dumpStrDeps (literal while Nat/... not visited)?
    bool lit_trigger(uint8_t lit) const {
        if ((lit & 1) && x->cmap_has(x->n_nat) && !visited(x->n_nat)) return true;
        if ((lit & 2) && ((x->cmap_has(x->n_charofnat) && !visited(x->n_charofnat)) ||
                          (x->cmap_has(x->n_stringoflist) && !visited(x->n_stringoflist))))
            return true;
        return false;
    }
    void sim_constant(uint32_t c) {  // = St::dump_constant with the own lines deferred to units
        if (c < dl.size() && dl[c].kind != 0xff && dl[c].kind != 4) {  // safe closure constant (not Quot): precomputed data
            if (visited(c)) return;
            mark_visited(c);
            const DL& d = dl[c];
            const uint32_t* mem = dl_ptr(d) + d.n1 + d.n2;
            switch (d.kind) {
                case 0:
                    sim_type(c);
                    add_unit(Unit{c, 0}, lit_trigger(d.lit));
                    return;
                case 1:
                case 2:
                case 3:
                    sim_type(c);
                    sim_value(c);
                    add_unit(Unit{c, 0}, lit_trigger(d.lit));
                    return;
                case 5: {
                    uint8_t lit = 0;
                    uint32_t ni = mem[0];
                    const uint32_t* inds = mem + 1;
                    uint32_t nc_ = inds[ni];
                    const uint32_t* ctors = inds + ni + 1;
                    uint32_t nr = ctors[nc_];
                    const uint32_t* recs = ctors + nc_ + 1;
                    for (uint32_t i = 0; i < ni; i++) {
                        mark_visited(inds[i]);
                        sim_type(inds[i]);
                        lit |= dl[inds[i]].lit;
                    }
                    for (uint32_t i = 0; i < nc_; i++) {
                        mark_visited(ctors[i]);
                        sim_type(ctors[i]);
                        lit |= dl[ctors[i]].lit;
                    }
                    for (uint32_t i = 0; i < nr; i++) {
                        mark_visited(recs[i]);
                        sim_type(recs[i]);
                        lit |= dl[recs[i]].lit;
                    }
                    for (uint32_t i = 0; i < nr; i++) sim_value(recs[i]);
                    add_unit(Unit{c, 2}, lit_trigger(lit));
                    return;
                }
                case 6: sim_constant(mem[0]); return;
                case 7:
                    for (uint32_t i = 0; i < d.n3; i++) sim_constant(mem[i]);
                    return;
                default: die("sim_constant: bad kind");
            }
        }
        CRef r = st->get(c);
        if (r.m == NONE) {
            st->missing(c);
            return;
        }
        if (visited(c) || x->is_unsafe(r)) return;  // cheap check first (is_unsafe reads the olean)
        mark_visited(c);
        uint32_t m = r.m;
        P val, cval;
        x->vals(r, val, cval);
        switch (tag(r.ci)) {
            case 0:
                sim_type(c);
                add_unit(Unit{c, 0}, lit_trigger(dl[c].lit));
                break;
            case 1:
            case 2:
            case 3:
                sim_type(c);
                sim_value(c);
                add_unit(Unit{c, 0}, lit_trigger(dl[c].lit));
                break;
            case 4: {
                sim_constant(x->n_eq);
                bool special = false;
                for (int qi = 0; qi < 4; qi++) {
                    uint32_t qn = x->n_quot[qi];
                    if (!x->cmap_has(qn) || tag(x->cmap[qn].ci) != 4)
                        special = true;  // St reports / fails exactly
                    else if (lit_trigger(dl[qn].lit))
                        special = true;
                }
                if (!special)
                    for (int qi = 0; qi < 4; qi++) mark_visited(x->n_quot[qi]);
                add_unit(Unit{c, 1}, special);
                break;
            }
            case 5: sim_inductive(c); break;
            case 6: sim_constant(x->intern_name(m, rawf(val, 1))); break;
            case 7: {
                std::vector<uint32_t> all;
                x->list_names(m, rawf(val, 1), all);
                for (uint32_t ind : all) sim_constant(ind);
                break;
            }
            default: die("bad ConstantInfo tag");
        }
    }
    void sim_inductive(uint32_t c) {  // = St::dump_inductive
        St::IndLists L;
        st->ind_lists(x->cmap[c], L);
        uint8_t lit = 0;
        for (size_t i = 0; i < L.inds.size(); i++) {
            mark_visited(L.inds[i]);
            sim_type(L.inds[i]);
            lit |= dl[L.inds[i]].lit;
        }
        for (size_t i = 0; i < L.ctor_names.size(); i++) {
            mark_visited(L.ctor_names[i]);
            sim_type(L.ctor_names[i]);
            lit |= dl[L.ctor_names[i]].lit;
        }
        for (size_t i = 0; i < L.rec_names.size(); i++) {
            mark_visited(L.rec_names[i]);
            sim_type(L.rec_names[i]);
            lit |= dl[L.rec_names[i]].lit;
        }
        for (size_t i = 0; i < L.rec_names.size(); i++) sim_value(L.rec_names[i]);
        add_unit(Unit{c, 2}, lit_trigger(lit));
    }
    void add_unit(const Unit& u, bool special) {
        if (!special) {
            if (units.size() == units.capacity()) die("internal: unit vector full");  // (the P1 workers read it)
            units.push_back(u);
            p1_pub.store(units.size(), std::memory_order_release);
            return;
        }
        // run the pending units, then let St dump this unit's own lines (it dumps Nat & co. in the right place)
        flush_epoch();
        n_special++;
        if (g_verbose)
            fprintf(stderr, "lean4export (native) parallel dump: special unit %zu (kind %d) %s: dumped by St (Nat %d, Char.ofNat %d, String.ofList %d visited)\n",
                    units.size(), (int)u.kind, x->name_str(u.c).c_str(), (int)visited(x->n_nat), (int)visited(x->n_charofnat),
                    (int)visited(x->n_stringoflist));
        const CRef& r = x->cmap[u.c];
        if (u.kind == 0) {
            st->own_simple(r);
        } else if (u.kind == 1) {
            st->own_quot();
        } else {
            St::IndLists L;
            st->ind_lists(r, L);
            st->own_inductive(L);
        }
    }
    void flush_epoch() {
        if (units.size() > epoch_start) {
            p1_wait(units.size());
            run_epoch(epoch_start, units.size());
        }
        epoch_start = units.size();
    }

    // ---- P1 runs in the background while B2 produces the units (owners by atomic min do not depend on the order)
    std::atomic<size_t> p1_pub{0};   // units[0 .. p1_pub) are published to the P1 workers
    std::atomic<size_t> p1_next{0};  // next unit to claim
    std::atomic<size_t> p1_done{0};  // units whose P1 is complete (units >= p1_pub are never claimed-and-done)
    std::atomic<bool> p1_stop{false};
    NThread* p1_th = nullptr;
    size_t p1_nth = 0;
    double t_p1wait = 0;
    void p1_worker() {
        std::vector<uint32_t> stack, disc;
        while (true) {
            size_t k = p1_next.fetch_add(1, std::memory_order_relaxed);
            while (k >= p1_pub.load(std::memory_order_acquire)) {
                if (p1_stop.load(std::memory_order_acquire) && k >= p1_pub.load(std::memory_order_acquire)) return;
                usleep(50);
            }
            P1V v{this, (uint32_t)k, &stack, &disc};
            unit_ops(units[k], v);
            p1_done.fetch_add(1, std::memory_order_release);
        }
    }
    void p1_start() {
        units.reserve(dl.size() + 64);  // never reallocated while the workers read it (units <= constants)
        p1_nth = nthreads > 1 ? nthreads - 1 : 1;  // (B2 itself is on the critical path: leave it a core)
        p1_th = new NThread[p1_nth];
        for (size_t t = 0; t < p1_nth; t++) p1_th[t].start([this] { p1_worker(); }, (size_t)64 << 20);
    }
    void p1_wait(size_t b) {  // all units < b (= every published unit) have their owners
        double t0 = now_s();
        while (p1_done.load(std::memory_order_acquire) < b) usleep(20);
        t_p1wait += now_s() - t0;
    }
    void p1_finish() {
        p1_stop.store(true, std::memory_order_release);
        for (size_t t = 0; t < p1_nth; t++) p1_th[t].join();
    }

    // ================================================================================================ own lines
    // the own-line operations of a unit in St's order: name(m, raw), uparams(m, raw list), expr(m, root),
    // names(m, raw list), line(index)
    template <class V>
    void unit_ops(const Unit& u, V& v) {
        if (u.kind == 0) {
            const CRef& r = x->cmap[u.c];
            uint32_t m = r.m;
            P val, cval;
            x->vals(r, val, cval);
            v.name(m, rawf(cval, 0));
            v.uparams(m, rawf(cval, 1));
            v.expr(m, x->f(m, cval, 2));
            switch (tag(r.ci)) {
                case 0: break;
                case 1:
                    v.expr(m, x->f(m, val, 1));
                    v.names(m, rawf(val, 3));
                    break;
                case 2:
                case 3:
                    v.expr(m, x->f(m, val, 1));
                    v.names(m, rawf(val, 2));
                    break;
                default: die("unit_ops: bad tag");
            }
            v.line(0);
        } else if (u.kind == 1) {
            for (int qi = 0; qi < 4; qi++) {
                const CRef& qr = x->cmap[x->n_quot[qi]];
                P qval, qcval;
                x->vals(qr, qval, qcval);
                v.name(qr.m, rawf(qcval, 0));
                v.uparams(qr.m, rawf(qcval, 1));
                v.expr(qr.m, x->f(qr.m, qcval, 2));
                v.line((uint32_t)qi);
            }
        } else {
            St::IndLists L;
            st->ind_lists(x->cmap[u.c], L);
            for (const CRef& ir : L.ind_vals) {
                P ival, icval;
                x->vals(ir, ival, icval);
                v.name(ir.m, rawf(icval, 0));
                v.uparams(ir.m, rawf(icval, 1));
                v.expr(ir.m, x->f(ir.m, icval, 2));
                v.names(ir.m, rawf(ival, 3));
                v.names(ir.m, rawf(ival, 4));
            }
            for (const CRef& cr : L.ctor_vals) {
                P cv, ccval;
                x->vals(cr, cv, ccval);
                v.name(cr.m, rawf(ccval, 0));
                v.uparams(cr.m, rawf(ccval, 1));
                v.expr(cr.m, x->f(cr.m, ccval, 2));
                v.name(cr.m, rawf(cv, 1));
            }
            for (const CRef& rr : L.rec_vals) {
                P rval, rcval;
                x->vals(rr, rval, rcval);
                v.name(rr.m, rawf(rcval, 0));
                v.uparams(rr.m, rawf(rcval, 1));
                v.expr(rr.m, x->f(rr.m, rcval, 2));
                v.names(rr.m, rawf(rval, 1));
                uint64_t rl = rawf(rval, 6);
                while (!is_scalar(rl)) {
                    P cell = x->tr(rr.m, rl);
                    P rule = x->f(rr.m, cell, 0);
                    v.name(rr.m, rawf(rule, 0));
                    v.expr(rr.m, x->f(rr.m, rule, 2));
                    rl = rawf(cell, 1);
                }
            }
            v.line(0);
        }
    }

    // ---- P1: owners of expression classes
    struct P1V {
        PD* pd;
        uint32_t k;
        std::vector<uint32_t>* stack;
        std::vector<uint32_t>* disc;
        void name(uint32_t, uint64_t) {}
        void uparams(uint32_t, uint64_t) {}
        void names(uint32_t, uint64_t) {}
        void line(uint32_t) {}
        void expr(uint32_t m, P e) {
            In* x = pd->x;
            const std::vector<uint32_t>& exp_e = pd->st->exp_e;
            uint32_t root = x->intern_expr(m, e, *disc);
            disc->clear();
            std::vector<uint32_t>& s = *stack;
            s.clear();
            s.push_back(root);
            while (!s.empty()) {
                uint32_t i = s.back();
                s.pop_back();
                // classes exported before this epoch: owned in an earlier epoch (owner < k) or dumped by St (no owner)
                uint32_t cur = pd->ol[i].own.load(std::memory_order_relaxed);
                if (cur == 0 ? exp_e[i] != NONE : NONE - cur <= k) continue;
                if (!lower(pd->ol[i].own, k)) continue;
                EKey key = x->ekeys.get(i);
                switch (key.kind) {
                    case 5:
                    case 6:
                    case 7:
                        s.push_back(key.a);
                        s.push_back(key.b);
                        break;
                    case 8:
                        s.push_back(key.a);
                        s.push_back(key.b);
                        s.push_back(key.c);
                        break;
                    case 11: s.push_back(key.c); break;
                    default: break;
                }
            }
        }
    };

    // ---- P2: events of a unit (exact dump order over its owned classes) + name/level owner claims
    void claim_name(uint32_t n, uint32_t k) {
        while (n != 0) {
            if (st->exp_n[n] != NONE) return;
            if (!lower(own_n[n], k)) return;
            n = x->names.get(n).key.pre;
        }
    }
    void claim_level(uint32_t l, uint32_t k) {
        if (st->exp_l[l] != NONE) return;
        if (!lower(own_l[l], k)) return;
        LKey key = x->lkeys.get(l);
        switch (key.kind) {
            case 1: claim_level(key.a, k); break;
            case 2:
            case 3:
                claim_level(key.a, k);
                claim_level(key.b, k);
                break;
            case 4: claim_name(key.a, k); break;
            default: die("claim of level zero/mvar");
        }
    }
    struct P2V {
        PD* pd;
        uint32_t k;
        UData* U;
        EvArena* A;
        std::vector<uint32_t>* disc;
        std::vector<uint32_t> tmp;
        inline void nref(uint32_t n) {
            if (n >= pd->nn) die("internal: name id out of range");
            if (pd->st->exp_n[n] != NONE) return;
            A->push(Ev{n, 0, EV_NAME, 0});
            pd->claim_name(n, k);
        }
        inline void lref(uint32_t l) {
            if (l >= pd->nl) die("internal: level id out of range");
            if (pd->st->exp_l[l] != NONE) return;
            A->push(Ev{l, 0, EV_LEVEL, 0});
            pd->claim_level(l, k);
        }
        void name(uint32_t m, uint64_t r) { nref(pd->x->intern_name(m, r)); }
        void names(uint32_t m, uint64_t r) {
            tmp.clear();
            pd->x->list_names(m, r, tmp);
            for (uint32_t n : tmp) nref(n);
        }
        void uparams(uint32_t m, uint64_t r) {
            tmp.clear();
            pd->x->list_names(m, r, tmp);
            std::vector<uint32_t> ns = tmp;
            for (uint32_t n : ns) nref(n);
            for (uint32_t n : ns) lref(pd->x->level_key_insert(LKey{4, n, 0}));
        }
        void line(uint32_t i) { A->push(Ev{0, i, EV_LINE, 0}); }
        void expr(uint32_t m, P e) {
            P p = pd->x->skip_mdata(m, e);
            uint32_t iid = pd->x->intern_expr(m, p, *disc);
            disc->clear();
            OL& o = pd->ol[iid];
            if (owner(o.own) == k && o.loc == 0) dfs(m, p, iid, o);
        }
        // child `field` of p with class ci: ownership is checked on the class first, so the child object is only
        // read when unit k really dumps it (a class reached by k that k does not own is exported before it)
        inline void visit(uint32_t m, P p, size_t field, uint32_t ci) {
            OL& o = pd->ol[ci];
            if (owner(o.own) != k || o.loc != 0) return;
            dfs(m, pd->x->child(m, p, field), ci, o);
        }
        void dfs(uint32_t m, P p, uint32_t iid, OL& o) {  // = St::dump_e restricted to the classes owned by unit k
            In* x = pd->x;
            EKey key = x->ekeys.get(iid);
            Ev ev{iid, 0, EV_EXPR, 0};
            switch (tag(p)) {
                case 0: break;
                case 3: lref(key.a); break;
                case 4: {
                    nref(key.a);
                    uint32_t l = key.b;
                    while (l != 0) {
                        LLKey c = x->llkeys.get(l);
                        lref(c.h);
                        l = c.t;
                    }
                    break;
                }
                case 5:
                    visit(m, p, 0, key.a);
                    visit(m, p, 1, key.b);
                    break;
                case 6:
                case 7: {
                    uint32_t n = x->intern_name(m, rawf(p, 0));
                    nref(n);
                    visit(m, p, 1, key.a);
                    visit(m, p, 2, key.b);
                    ev.aux = n;
                    ev.bi = sc_u8(p, 8);
                    break;
                }
                case 8: {
                    uint32_t n = x->intern_name(m, rawf(p, 0));
                    nref(n);
                    visit(m, p, 1, key.a);
                    visit(m, p, 2, key.b);
                    visit(m, p, 3, key.c);
                    ev.aux = n;
                    break;
                }
                case 9:
                    ev.aux = (uint32_t)A->lits.size();
                    A->lits.push_back({m, p});
                    break;
                case 11:
                    nref(key.a);
                    visit(m, p, 2, key.c);
                    break;
                default: die("cannot export expr tag " + std::to_string(tag(p)));
            }
            o.loc = ++U->ce;
            A->push(ev);
        }
    };

    // ---- P3: local numbers of the owned names and levels
    void num_name(uint32_t k, UData& U, uint32_t n) {
        if (n == 0 || st->exp_n[n] != NONE) return;
        if (owner(own_n[n]) != k || loc_n[n] != 0) return;
        num_name(k, U, x->names.get(n).key.pre);
        loc_n[n] = ++U.cn;
    }
    void num_level(uint32_t k, UData& U, uint32_t l) {
        if (st->exp_l[l] != NONE) return;
        if (owner(own_l[l]) != k || loc_l[l] != 0) return;
        LKey key = x->lkeys.get(l);
        switch (key.kind) {
            case 1: num_level(k, U, key.a); break;
            case 2:
            case 3:
                num_level(k, U, key.a);
                num_level(k, U, key.b);
                break;
            case 4: num_name(k, U, key.a); break;
            default: die("numbering of level zero/mvar");
        }
        loc_l[l] = ++U.cl;
    }

    // ---- P6: rendering
    struct RenderCtx {
        PD* pd;
        uint32_t k;
        UData* U;
        RBuf* o;
        std::vector<uint32_t> disc;
    };
    inline uint32_t gid_n(uint32_t n) const {
        uint32_t v = st->exp_n[n];
        if (v == NONE) die("internal: name without id");
        return v;
    }
    inline uint32_t gid_l(uint32_t l) const {
        uint32_t v = st->exp_l[l];
        if (v == NONE) die("internal: level without id");
        return v;
    }
    inline uint32_t gid_e(uint32_t e) const {
        uint32_t v = st->exp_e[e];
        if (v == NONE) die("internal: expr without id");
        return v;
    }
    void r_name(RenderCtx& R, uint32_t n) {  // = St::dump_name_iid (owned, not yet rendered)
        if (n == 0) return;
        if (owner(own_n[n]) != R.k || loc_n[n] == 0) return;
        NKey key = x->names.get(n).key;
        r_name(R, key.pre);
        loc_n[n] = 0;
        RBuf& o = *R.o;
        uint32_t id = gid_n(n), pre = gid_n(key.pre);
        o.lit("{\"in\":");
        o.n(id);
        if (key.kind == 1) {
            o.lit(",\"str\":{\"pre\":");
            o.n(pre);
            o.lit(",\"str\":");
            o.jstr(key.ptr, key.len);
            o.lit("}}");
        } else {
            o.lit(",\"num\":{\"i\":");
            o.n(key.num);
            o.lit(",\"pre\":");
            o.n(pre);
            o.lit("}}");
        }
        o.nl();
    }
    void r_level(RenderCtx& R, uint32_t l) {  // = St::dump_level_iid
        if (owner(own_l[l]) != R.k || loc_l[l] == 0) return;
        LKey k = x->lkeys.get(l);
        switch (k.kind) {
            case 1: r_level(R, k.a); break;
            case 2:
            case 3:
                r_level(R, k.a);
                r_level(R, k.b);
                break;
            case 4: r_name(R, k.a); break;
            default: die("dump of level zero/mvar");
        }
        loc_l[l] = 0;
        uint32_t id = gid_l(l);
        RBuf& o = *R.o;
        o.lit("{\"il\":");
        o.n(id);
        switch (k.kind) {
            case 1:
                o.lit(",\"succ\":");
                o.n(gid_l(k.a));
                break;
            case 2:
                o.lit(",\"max\":[");
                o.n(gid_l(k.a));
                o.ch(',');
                o.n(gid_l(k.b));
                o.ch(']');
                break;
            case 3:
                o.lit(",\"imax\":[");
                o.n(gid_l(k.a));
                o.ch(',');
                o.n(gid_l(k.b));
                o.ch(']');
                break;
            default:
                o.lit(",\"param\":");
                o.n(gid_n(k.a));
                break;
        }
        o.ch('}');
        o.nl();
    }
    // raw line writing (one capacity check per line)
    template <size_t N>
    static inline char* W(char* p, const char (&lit)[N]) {
        memcpy(p, lit, N - 1);
        return p + N - 1;
    }
    static inline char* Wn(char* p, uint64_t v) {
        unsigned d = v < 10 ? 1 : Out::dec_len(v);
        Out::dec_put(p + d, v);
        return p + d;
    }
    static inline const char* bi_str(uint8_t bi, size_t& n) {
        switch (bi) {
            case 0: n = 9; return "\"default\"";
            case 1: n = 10; return "\"implicit\"";
            case 2: n = 16; return "\"strictImplicit\"";
            case 3: n = 14; return "\"instImplicit\"";
            default: die("bad binderInfo");
        }
    }
    void r_expr(RenderCtx& R, const Ev& ev) {  // = the line of St::dump_e
        EKey k = x->ekeys.get(ev.iid);
        uint32_t id = gid_e(ev.iid);
        RBuf& o = *R.o;
        if (k.kind == 9 || k.kind == 12) {
            const std::pair<uint32_t, P>& lp = arenas[R.U->tid].lits[ev.aux];
            uint32_t m = lp.first;
            P lit = x->f(m, lp.second, 0);
            if (tag(lit) == 0) {
                std::string dd = x->nat_dec(m, rawf(lit, 0));
                o.lit("{\"ie\":");
                o.n(id);
                o.lit(",\"natVal\":\"");
                o.s(dd.data(), dd.size());
                o.lit("\"}");
            } else {
                P sp = x->f(m, lit, 0);
                o.lit("{\"ie\":");
                o.n(id);
                o.lit(",\"strVal\":");
                o.jstr(str_data(sp), str_len(sp));
                o.ch('}');
            }
            o.nl();
            return;
        }
        size_t maxlen = 192;
        if (k.kind == 4)
            for (uint32_t l = k.b; l != 0; l = x->llkeys.get(l).t) maxlen += 12;
        o.reserve(maxlen);
        char* p = o.buf + o.len;
        switch (k.kind) {
            case 0:
                p = W(p, "{\"bvar\":");
                p = Wn(p, k.a);
                p = W(p, ",\"ie\":");
                p = Wn(p, id);
                *p++ = '}';
                break;
            case 3:
                p = W(p, "{\"ie\":");
                p = Wn(p, id);
                p = W(p, ",\"sort\":");
                p = Wn(p, gid_l(k.a));
                *p++ = '}';
                break;
            case 4: {
                p = W(p, "{\"const\":{\"name\":");
                p = Wn(p, gid_n(k.a));
                p = W(p, ",\"us\":[");
                uint32_t l = k.b;
                bool first = true;
                while (l != 0) {
                    LLKey c = x->llkeys.get(l);
                    if (!first) *p++ = ',';
                    first = false;
                    p = Wn(p, gid_l(c.h));
                    l = c.t;
                }
                p = W(p, "]},\"ie\":");
                p = Wn(p, id);
                *p++ = '}';
                break;
            }
            case 5:
                p = W(p, "{\"app\":{\"arg\":");
                p = Wn(p, gid_e(k.b));
                p = W(p, ",\"fn\":");
                p = Wn(p, gid_e(k.a));
                p = W(p, "},\"ie\":");
                p = Wn(p, id);
                *p++ = '}';
                break;
            case 6:
            case 7: {
                if (k.kind == 6) {
                    p = W(p, "{\"ie\":");
                    p = Wn(p, id);
                    p = W(p, ",\"lam\":{\"binderInfo\":");
                } else {
                    p = W(p, "{\"forallE\":{\"binderInfo\":");
                }
                size_t bn;
                const char* bs = bi_str(ev.bi, bn);
                memcpy(p, bs, bn);
                p += bn;
                p = W(p, ",\"body\":");
                p = Wn(p, gid_e(k.b));
                p = W(p, ",\"name\":");
                p = Wn(p, gid_n(ev.aux));
                p = W(p, ",\"type\":");
                p = Wn(p, gid_e(k.a));
                if (k.kind == 6) {
                    p = W(p, "}}");
                } else {
                    p = W(p, "},\"ie\":");
                    p = Wn(p, id);
                    *p++ = '}';
                }
                break;
            }
            case 8:
                p = W(p, "{\"ie\":");
                p = Wn(p, id);
                p = W(p, ",\"letE\":{\"body\":");
                p = Wn(p, gid_e(k.c));
                p = W(p, ",\"name\":");
                p = Wn(p, gid_n(ev.aux));
                p = W(p, ",\"nondep\":false,\"type\":");
                p = Wn(p, gid_e(k.a));
                p = W(p, ",\"value\":");
                p = Wn(p, gid_e(k.b));
                p = W(p, "}}");
                break;
            case 11:
                p = W(p, "{\"ie\":");
                p = Wn(p, id);
                p = W(p, ",\"proj\":{\"idx\":");
                p = Wn(p, k.b);
                p = W(p, ",\"struct\":");
                p = Wn(p, gid_e(k.c));
                p = W(p, ",\"typeName\":");
                p = Wn(p, gid_n(k.a));
                p = W(p, "}}");
                break;
            default: die("cannot render expr kind " + std::to_string(k.kind));
        }
        *p++ = '\n';
        o.len = (size_t)(p - o.buf);
    }
    // ids of already dumped items for the constant lines
    uint32_t L_name(uint32_t m, uint64_t r) { return gid_n(x->intern_name(m, r)); }
    std::vector<uint32_t> L_names(uint32_t m, uint64_t r) {
        std::vector<uint32_t> ns;
        x->list_names(m, r, ns);
        for (auto& n : ns) n = gid_n(n);
        return ns;
    }
    uint32_t L_expr(RenderCtx& R, uint32_t m, P e) {
        uint32_t i = x->intern_expr(m, e, R.disc);
        R.disc.clear();
        return gid_e(i);
    }
    void L_cval(RenderCtx& R, uint32_t m, P cval, uint32_t& n, std::vector<uint32_t>& lps, uint32_t& t) {
        n = L_name(m, rawf(cval, 0));
        lps = L_names(m, rawf(cval, 1));
        t = L_expr(R, m, x->f(m, cval, 2));
    }
    void r_line(RenderCtx& R, const Unit& u, uint32_t idx) {
        RBuf& o = *R.o;
        if (u.kind == 0) {  // = St::own_simple
            const CRef& r = x->cmap[u.c];
            uint32_t m = r.m;
            P val, cval;
            x->vals(r, val, cval);
            uint32_t n, t;
            std::vector<uint32_t> lps;
            L_cval(R, m, cval, n, lps, t);
            switch (tag(r.ci)) {
                case 0:
                    o.lit("{\"axiom\":{\"isUnsafe\":");
                    o.b(sc_u8(val, 0) != 0);
                    o.lit(",\"levelParams\":");
                    o.arr(lps);
                    o.lit(",\"name\":");
                    o.n(n);
                    o.lit(",\"type\":");
                    o.n(t);
                    o.lit("}}");
                    o.nl();
                    break;
                case 1: {
                    uint32_t v = L_expr(R, m, x->f(m, val, 1));
                    uint64_t hints = rawf(val, 2);
                    std::vector<uint32_t> all = L_names(m, rawf(val, 3));
                    uint8_t safety = sc_u8(val, 0);
                    o.lit("{\"def\":{\"all\":");
                    o.arr(all);
                    o.lit(",\"hints\":");
                    if (is_scalar(hints)) {
                        if ((hints >> 1) == 0)
                            o.lit("\"opaque\"");
                        else
                            o.lit("\"abbrev\"");
                    } else {
                        o.lit("{\"regular\":");
                        o.n(sc_u32(x->tr(m, hints), 0));
                        o.ch('}');
                    }
                    o.lit(",\"levelParams\":");
                    o.arr(lps);
                    o.lit(",\"name\":");
                    o.n(n);
                    o.lit(",\"safety\":");
                    if (safety == 0)
                        o.lit("\"unsafe\"");
                    else if (safety == 1)
                        o.lit("\"safe\"");
                    else
                        o.lit("\"partial\"");
                    o.lit(",\"type\":");
                    o.n(t);
                    o.lit(",\"value\":");
                    o.n(v);
                    o.lit("}}");
                    o.nl();
                    break;
                }
                case 2: {
                    uint32_t v = L_expr(R, m, x->f(m, val, 1));
                    std::vector<uint32_t> all = L_names(m, rawf(val, 2));
                    o.lit("{\"thm\":{\"all\":");
                    o.arr(all);
                    o.lit(",\"levelParams\":");
                    o.arr(lps);
                    o.lit(",\"name\":");
                    o.n(n);
                    o.lit(",\"type\":");
                    o.n(t);
                    o.lit(",\"value\":");
                    o.n(v);
                    o.lit("}}");
                    o.nl();
                    break;
                }
                case 3: {
                    uint32_t v = L_expr(R, m, x->f(m, val, 1));
                    std::vector<uint32_t> all = L_names(m, rawf(val, 2));
                    o.lit("{\"opaque\":{\"all\":");
                    o.arr(all);
                    o.lit(",\"isUnsafe\":");
                    o.b(sc_u8(val, 0) != 0);
                    o.lit(",\"levelParams\":");
                    o.arr(lps);
                    o.lit(",\"name\":");
                    o.n(n);
                    o.lit(",\"type\":");
                    o.n(t);
                    o.lit(",\"value\":");
                    o.n(v);
                    o.lit("}}");
                    o.nl();
                    break;
                }
                default: die("r_line: bad tag");
            }
        } else if (u.kind == 1) {  // = St::own_quot, line idx
            const CRef& qr = x->cmap[x->n_quot[idx]];
            P qval, qcval;
            x->vals(qr, qval, qcval);
            uint32_t qn2, qt;
            std::vector<uint32_t> qlps;
            L_cval(R, qr.m, qcval, qn2, qlps, qt);
            uint8_t kind = sc_u8(qval, 0);
            o.lit("{\"quot\":{\"kind\":");
            if (kind == 0)
                o.lit("\"type\"");
            else if (kind == 1)
                o.lit("\"ctor\"");
            else if (kind == 2)
                o.lit("\"lift\"");
            else
                o.lit("\"ind\"");
            o.lit(",\"levelParams\":");
            o.arr(qlps);
            o.lit(",\"name\":");
            o.n(qn2);
            o.lit(",\"type\":");
            o.n(qt);
            o.lit("}}");
            o.nl();
        } else {  // = St::own_inductive
            St::IndLists L;
            st->ind_lists(x->cmap[u.c], L);
            o.lit("{\"inductive\":{\"ctors\":[");
            for (size_t i = 0; i < L.ctor_vals.size(); i++) {
                const CRef& cr = L.ctor_vals[i];
                if (i) o.ch(',');
                P cv, ccval;
                x->vals(cr, cv, ccval);
                uint32_t m = cr.m;
                uint32_t n, t;
                std::vector<uint32_t> lps;
                L_cval(R, m, ccval, n, lps, t);
                uint32_t induct = L_name(m, rawf(cv, 1));
                uint64_t cidx = x->nat_small(m, rawf(cv, 2));
                uint64_t np = x->nat_small(m, rawf(cv, 3));
                uint64_t nf = x->nat_small(m, rawf(cv, 4));
                bool uns = sc_u8(cv, 0) != 0;
                o.lit("{\"cidx\":");
                o.n(cidx);
                o.lit(",\"induct\":");
                o.n(induct);
                o.lit(",\"isUnsafe\":");
                o.b(uns);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"numFields\":");
                o.n(nf);
                o.lit(",\"numParams\":");
                o.n(np);
                o.lit(",\"type\":");
                o.n(t);
                o.ch('}');
            }
            o.lit("],\"recs\":[");
            for (size_t i = 0; i < L.rec_vals.size(); i++) {
                const CRef& rr = L.rec_vals[i];
                if (i) o.ch(',');
                P rval, rcval;
                x->vals(rr, rval, rcval);
                uint32_t m = rr.m;
                uint32_t n, t;
                std::vector<uint32_t> lps;
                L_cval(R, m, rcval, n, lps, t);
                std::vector<uint32_t> all2 = L_names(m, rawf(rval, 1));
                uint64_t np = x->nat_small(m, rawf(rval, 2));
                uint64_t ni = x->nat_small(m, rawf(rval, 3));
                uint64_t nmo = x->nat_small(m, rawf(rval, 4));
                uint64_t nmi = x->nat_small(m, rawf(rval, 5));
                bool kk = sc_u8(rval, 0) != 0, uns = sc_u8(rval, 1) != 0;
                o.lit("{\"all\":");
                o.arr(all2);
                o.lit(",\"isUnsafe\":");
                o.b(uns);
                o.lit(",\"k\":");
                o.b(kk);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"numIndices\":");
                o.n(ni);
                o.lit(",\"numMinors\":");
                o.n(nmi);
                o.lit(",\"numMotives\":");
                o.n(nmo);
                o.lit(",\"numParams\":");
                o.n(np);
                o.lit(",\"rules\":[");
                uint64_t rl = rawf(rval, 6);
                bool first = true;
                while (!is_scalar(rl)) {
                    P cell = x->tr(m, rl);
                    P rule = x->f(m, cell, 0);
                    if (!first) o.ch(',');
                    first = false;
                    o.lit("{\"ctor\":");
                    o.n(L_name(m, rawf(rule, 0)));
                    o.lit(",\"nfields\":");
                    o.n(x->nat_small(m, rawf(rule, 1)));
                    o.lit(",\"rhs\":");
                    o.n(L_expr(R, m, x->f(m, rule, 2)));
                    o.ch('}');
                    rl = rawf(cell, 1);
                }
                o.lit("],\"type\":");
                o.n(t);
                o.ch('}');
            }
            o.lit("],\"types\":[");
            for (size_t i = 0; i < L.ind_vals.size(); i++) {
                const CRef& ir = L.ind_vals[i];
                if (i) o.ch(',');
                P ival, icval;
                x->vals(ir, ival, icval);
                uint32_t m = ir.m;
                uint32_t n, t;
                std::vector<uint32_t> lps;
                L_cval(R, m, icval, n, lps, t);
                std::vector<uint32_t> all2 = L_names(m, rawf(ival, 3));
                std::vector<uint32_t> ctors = L_names(m, rawf(ival, 4));
                uint64_t np = x->nat_small(m, rawf(ival, 1));
                uint64_t ni = x->nat_small(m, rawf(ival, 2));
                uint64_t nn_ = x->nat_small(m, rawf(ival, 5));
                bool is_rec = sc_u8(ival, 0) != 0, is_unsafe = sc_u8(ival, 1) != 0, is_refl = sc_u8(ival, 2) != 0;
                o.lit("{\"all\":");
                o.arr(all2);
                o.lit(",\"ctors\":");
                o.arr(ctors);
                o.lit(",\"isRec\":");
                o.b(is_rec);
                o.lit(",\"isReflexive\":");
                o.b(is_refl);
                o.lit(",\"isUnsafe\":");
                o.b(is_unsafe);
                o.lit(",\"levelParams\":");
                o.arr(lps);
                o.lit(",\"name\":");
                o.n(n);
                o.lit(",\"numIndices\":");
                o.n(ni);
                o.lit(",\"numNested\":");
                o.n(nn_);
                o.lit(",\"numParams\":");
                o.n(np);
                o.lit(",\"type\":");
                o.n(t);
                o.ch('}');
            }
            o.lit("]}}");
            o.nl();
        }
    }

    // ================================================================================================ epoch
    double t_epochs = 0;
    void run_epoch(size_t a, size_t b) {
        double t_ep0 = now_s();
        n_epochs++;
        // (St may have run between two epochs; everything it dumps was interned by phase A / B1)
        if (x->ec.load() > ne || x->nc.load() + 1 > nn || x->lc.load() + 1 > nl) die("internal: id space grew during the dump");
        u0 = a;
        size_t nu = b - a;
        ud.clear();
        ud.resize(nu);
        t_last = now_s();
        // (P1 was done by the background workers, see p1_worker)
        // P2
        {
            std::atomic<size_t> next{a};
            if (arenas.size() != nthreads) {
                arenas.resize(nthreads);
                for (EvArena& A : arenas) A.init(2 * (ne + nn) / nthreads + (1u << 20));
            }
            for (EvArena& A : arenas) {
                A.n = 0;
                A.lits.clear();
            }
            par_run(nthreads, (size_t)4 << 30, [&](size_t t) {
                std::vector<uint32_t> disc;
                EvArena* A = &arenas[t];
                while (true) {
                    size_t j = next.fetch_add(4);
                    if (j >= b) break;
                    for (size_t q = j; q < std::min(b, j + 4); q++) {
                        UData* U = &ud[q - a];
                        U->tid = (uint32_t)t;
                        U->off = A->n;
                        P2V v{this, (uint32_t)q, U, A, &disc, {}};
                        unit_ops(units[q], v);
                        U->nev = (uint32_t)(A->n - U->off);
                    }
                }
            });
        }
        lap("P2 walks");
        // P3
        {
            std::atomic<size_t> next{a};
            par_run(nthreads, (size_t)64 << 20, [&](size_t) {
                while (true) {
                    size_t j = next.fetch_add(16);
                    if (j >= b) break;
                    for (size_t q = j; q < std::min(b, j + 16); q++) {
                        UData& U = ud[q - a];
                        const Ev* evs = U.ev(*this);
                        for (uint32_t ei = 0; ei < U.nev; ei++) {
                            const Ev& ev = evs[ei];
                            if (ev.kind == EV_NAME)
                                num_name((uint32_t)q, U, ev.iid);
                            else if (ev.kind == EV_LEVEL)
                                num_level((uint32_t)q, U, ev.iid);
                        }
                    }
                }
            });
        }
        lap("P3 numbering");
        // P4
        uint64_t te = st->ce, tn = st->cn, tl = st->cl, tev = 0;
        for (size_t i = 0; i < nu; i++) {
            UData& U = ud[i];
            U.be = (uint32_t)te;
            U.bn = (uint32_t)tn;
            U.bl = (uint32_t)tl;
            te += U.ce;
            tn += U.cn;
            tl += U.cl;
            tev += U.nev;
        }
        if (te >= NONE || tn >= NONE || tl >= NONE) die("too many ids");
        st->ce = (uint32_t)te;
        st->cn = (uint32_t)tn;
        st->cl = (uint32_t)tl;
        // P5
        {
            std::atomic<size_t> next{0};
            par_run(nthreads, (size_t)64 << 20, [&](size_t) {
                while (true) {
                    size_t j = next.fetch_add(64);
                    if (j >= nu) break;
                    for (size_t q = j; q < std::min(nu, j + 64); q++) {
                        UData& U = ud[q];
                        const Ev* evs = U.ev(*this);
                        for (uint32_t ei = 0; ei < U.nev; ei++)
                            if (evs[ei].kind == EV_EXPR) st->exp_e[evs[ei].iid] = U.be + ol[evs[ei].iid].loc - 1;
                    }
                }
            });
            for (size_t n = 1; n < nn; n++) {
                uint32_t o = owner(own_n[n]);
                if (o < a || o >= b || st->exp_n[n] != NONE) continue;
                if (loc_n[n] == 0) die("internal: owned name without number");
                st->exp_n[n] = ud[o - a].bn + loc_n[n] - 1;
            }
            for (size_t l = 0; l < nl; l++) {
                uint32_t o = owner(own_l[l]);
                if (o < a || o >= b || st->exp_l[l] != NONE) continue;
                if (loc_l[l] == 0) die("internal: owned level without number");
                st->exp_l[l] = ud[o - a].bl + loc_l[l] - 1;
            }
        }
        lap("P4/P5 ids");
        // P6: chunks of consecutive units with ~equal event counts, rendered in parallel, queued in order
        {
            size_t target = std::max<size_t>(1 << 16, (size_t)(tev / (nthreads * 8) + 1));
            std::vector<size_t> cuts;  // chunk i = units [cuts[i], cuts[i+1])
            cuts.push_back(0);
            size_t acc = 0;
            for (size_t i = 0; i < nu; i++) {
                acc += ud[i].nev + 1;
                if (acc >= target) {
                    cuts.push_back(i + 1);
                    acc = 0;
                }
            }
            if (cuts.back() != nu) cuts.push_back(nu);
            size_t nch = cuts.size() - 1;
            // chunk ci is output chunk seq0 + ci: the sink writes them in order whatever order they finish in
            uint64_t seq0 = st->out.reserve_seqs(nch);
            std::atomic<size_t> next{0};
            par_run(nthreads, (size_t)64 << 20, [&](size_t) {
                while (true) {
                    size_t ci = next.fetch_add(1);
                    if (ci >= nch) break;
                    RBuf o;
                    o.sink = st->out.sink;
                    size_t evs = 0;
                    for (size_t i = cuts[ci]; i < cuts[ci + 1]; i++) evs += ud[i].nev;
                    o.init(evs * 56 + 4096);  // ~53 bytes per event on Mathlib
                    for (size_t i = cuts[ci]; i < cuts[ci + 1]; i++) {
                        RenderCtx R{this, (uint32_t)(a + i), &ud[i], &o, {}};
                        const Unit& u = units[a + i];
                        const Ev* uev = ud[i].ev(*this);
                        for (uint32_t ei = 0; ei < ud[i].nev; ei++) {
                            const Ev& ev = uev[ei];
                            switch (ev.kind) {
                                case EV_NAME: r_name(R, ev.iid); break;
                                case EV_LEVEL: r_level(R, ev.iid); break;
                                case EV_EXPR: r_expr(R, ev); break;
                                default: r_line(R, u, ev.aux); break;
                            }
                        }
                    }
                    st->out.sink->put(seq0 + ci, o.buf, o.len, o.cap);
                }
            });
        }
        lap("P6 render");
        if (g_verbose)
            fprintf(stderr, "lean4export (native) parallel dump: epoch %zu: units %zu..%zu, %llu events, ids e %u n %u l %u\n",
                    n_epochs, a, b, (unsigned long long)tev, st->ce, st->cn, st->cl);
        ud.clear();
        ud.shrink_to_fit();
        t_epochs += now_s() - t_ep0;
    }

    // ================================================================================================ driver
    void run(const std::vector<uint32_t>& tids) {
        t_last = now_s();
        // closure = everything phase A enqueued (= every constant the dump can reach)
        std::vector<uint32_t> closure;
        unsafe_c.assign(x->cmap.size(), 0);
        for (uint32_t c = 0; c < x->cmap.size(); c++)
            if (x->cmap_has(c) && (size_t)c < x->enq.cap && x->enq.p[c].load(std::memory_order_relaxed)) {
                if (x->is_unsafe(x->cmap[c]))
                    unsafe_c[c] = 1;
                else
                    closure.push_back(c);
            }
        if (st->visited.size() < x->cmap.size() + 1) st->visited.resize(x->cmap.size() + 1, 0);
        skip_lim = x->cmap.size();
        skipb.assign(skip_lim / 64 + 1, 0);
        for (size_t c = 0; c < skip_lim; c++)
            if (unsafe_c[c] || st->visited[c]) skipb[c >> 6] |= 1ull << (c & 63);
        ne = x->ec.load();
        NThread prep;  // the big expr-id table fill overlaps B1 (no expressions are created after phase A)
        size_t eown = (ne * 4 + 64 + HUGE_SZ - 1) & ~(HUGE_SZ - 1);
        ol = (OL*)big_zalloc(2 * eown);
        prep.start([this, eown] {
            St::grow(st->exp_e, ne + 1);
            // write-fault the owner/local tables of the expressions as huge pages (P1/P2 read them before writing)
            for (size_t o = 0; o < 2 * eown; o += HUGE_SZ) ((volatile char*)ol)[o] = 0;
        });
        b1(closure);
        lap("B1 used-constant lists");
        prep.join();
        nn = x->nc.load() + 1;
        nl = x->lc.load() + 1;
        St::grow(st->exp_n, nn + 1);
        St::grow(st->exp_l, nl + 1);
        own_n = (std::atomic<uint32_t>*)big_zalloc(nn * 4 + 64);
        loc_n = (uint32_t*)big_zalloc(nn * 4 + 64);
        own_l = (std::atomic<uint32_t>*)big_zalloc(nl * 4 + 64);
        loc_l = (uint32_t*)big_zalloc(nl * 4 + 64);
        lap("setup");
        double tb2 = now_s();
        p1_start();
        for (uint32_t c : tids) {
            if (c == NONE) continue;
            sim_constant(c);
        }
        if (g_verbose)
            fprintf(stderr, "lean4export (native) parallel dump: B2 %zu units, %zu special, %.3f s (incl. %.3f s in %zu epochs before the last)\n",
                    units.size(), n_special, now_s() - tb2, t_epochs, n_epochs);
        t_last = now_s();
        t_p1wait = 0;
        p1_wait(units.size());
        p1_finish();
        lap("P1 owners (overlapped with B2; tail)");
        flush_epoch();
    }
};

// ------------------------------------------------------------------------------------------------
// loading
static bool g_populate = false;
// F04: read() fallback buffers come from ONE big MAP_NORESERVE anonymous reservation (bump allocation) instead of one
// malloc per file: glibc serves large mallocs with mmap, so once vm.max_map_count (65,530 on most hosts) is exhausted by
// the per-file mappings, malloc failed too and the export declined (full RH: ~450k olean parts). Contents are identical
// (the bytes of the file); only where they live changes.
static char* arena_alloc(size_t len) {
    static std::atomic<char*> base{nullptr};
    static std::atomic<size_t> off{0};
    static std::mutex mu;
    const size_t CAP = (size_t)4 << 40;  // 4 TiB of address space; pages are only committed when read into
    char* b = base.load(std::memory_order_acquire);
    if (!b) {
        std::lock_guard<std::mutex> g(mu);
        b = base.load(std::memory_order_acquire);
        if (!b) {
            void* m = mmap(nullptr, CAP, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
            if (m == MAP_FAILED) return nullptr;
            b = (char*)m;
            base.store(b, std::memory_order_release);
        }
    }
    size_t a = (len + 4095) & ~(size_t)4095;
    size_t o = off.fetch_add(a, std::memory_order_relaxed);
    if (o + a > CAP) return nullptr;
    return b + o;
}
static Part read_part(const std::string& path) {
    int fd = open(path.c_str(), O_RDONLY | O_CLOEXEC);
    if (fd < 0) die("object file '" + path + "' does not exist or cannot be opened");
    struct stat st;
    if (fstat(fd, &st) != 0) die("fstat " + path);
    size_t len = (size_t)st.st_size;
    if (len < 0x60) die(path + ": not an olean");
    static const bool test_read = getenv("LEAN4EXPORT_TEST_READ") != nullptr;  // testing aid for the fallback below
    void* m = test_read ? MAP_FAILED : reg_mmap(len, PROT_READ, MAP_PRIVATE | (g_populate ? MAP_POPULATE : 0), fd);
    if (m == MAP_FAILED) {
        // e.g. ENOMEM when vm.max_map_count is reached (full-RH scale: ~450k parts): read the file instead, as Lean does
        char* b = arena_alloc(len);
        if (!b) die("mmap " + path + " failed and out of memory");
        size_t off = 0;
        while (off < len) {
            ssize_t r = pread(fd, b + off, len - off, (off_t)off);
            if (r < 0 && errno == EINTR) continue;
            if (r <= 0) die("mmap and read of " + path + " failed");
            off += (size_t)r;
        }
        m = b;
    }
    close(fd);
    P p = (P)m;
    if (memcmp(p, "olean", 5) != 0) die(path + ": not an olean");
    if (p[5] != 2) die(path + ": unsupported olean version " + std::to_string(p[5]));
    // F04 (fail closed): the official reader (src/library/module.cpp, release builds with LEAN_CHECK_OLEAN_VERSION and
    // GMP) also rejects an .olean whose flags byte differs from 1 or whose githash differs from the githash of the Lean
    // the exporter was built with ("incompatible header"); the native core used to accept any githash (oleans of another
    // Lean version) -> decline in exactly those cases (the official exporter then reports the error).
    if (p[6] != 1) die(path + ": olean flags byte " + std::to_string(p[6]) + " != 1 (declining)");
    if (strncmp((const char*)p + 0x28, F04_EXPECTED_GITHASH, 40) != 0)
        die(path + ": olean githash differs from the exporter's Lean githash (declining)");
    uint64_t base;
    memcpy(&base, p + 0x50, 8);
    return Part{base, p, (uint64_t)len};
}

static bool is_dir(const std::string& p) {
    struct stat st;
    return stat(p.c_str(), &st) == 0 && S_ISDIR(st.st_mode);
}
static bool exists(const std::string& p) {
    struct stat st;
    return stat(p.c_str(), &st) == 0;
}
// module name components -> .olean path (SearchPath.findWithExt "olean")
// The search path entry only depends on the root component: it is resolved once per root (thread-safe cache).
static std::mutex g_rootmu;
static std::unordered_map<std::string, int>* g_rootsp = nullptr;  // pointer: see EARLY START (no dynamic init)
static bool g_sp_partial = false;
static std::string find_olean(const std::vector<std::string>& sp, const std::vector<std::string>& comps) {
    const std::string& root = comps[0];
    int found = -1;
    {
        std::lock_guard<std::mutex> g(g_rootmu);
        if (!g_rootsp) g_rootsp = new std::unordered_map<std::string, int>();
        auto it = g_rootsp->find(root);
        if (it != g_rootsp->end()) {
            found = it->second;
        } else {
            for (size_t i = 0; i < sp.size(); i++) {
                const std::string& p = sp[i];
                if (is_dir(p + "/" + root) || exists(p + "/" + root + ".olean")) {
                    found = (int)i;
                    break;
                }
            }
            g_rootsp->emplace(root, found);
        }
    }
    if (found >= 0) {
        std::string path = sp[found];
        for (const std::string& c : comps) path += "/" + c;
        return path + ".olean";
    }
    std::string nm;
    for (size_t i = 0; i < comps.size(); i++) nm += (i ? "." : "") + comps[i];
    if (g_sp_partial) {
        // the search path lacks the toolchain's own entry (Main.lean did not compute the sysroot yet): exit 3 before
        // anything was written; the caller retries with the complete search path
        fflush(stderr);
        _exit(3);
    }
    die("unknown module prefix '" + root + "' (module " + nm + ")");
}

static P tr_mods(const std::vector<Module>& mods, uint32_t m, uint64_t a) {
    const Module& md = mods[m];
    for (const Part& p : md.parts) {
        uint64_t off = a - p.base;
        if (off < p.len) return p.ptr + off;
    }
    die("dangling pointer in module " + md.name);
}
static void name_comps_raw(const std::vector<Module>& mods, uint32_t m, uint64_t r, std::vector<std::string>& out) {
    if (is_scalar(r)) return;
    P p = tr_mods(mods, m, r);
    uint8_t t = tag(p);
    if (t == 0) return;
    name_comps_raw(mods, m, rawf(p, 0), out);
    if (t == 1) {
        P s = tr_mods(mods, m, rawf(p, 1));
        out.push_back(std::string((const char*)str_data(s), str_len(s)));
    } else {
        out.push_back(std::to_string(rawf(p, 1) >> 1));
    }
}
static std::string join_comps(const std::vector<std::string>& c) {
    std::string s;
    for (size_t i = 0; i < c.size(); i++) {
        if (i) s += '\x01';
        s += c[i];
    }
    return s;
}
static std::string pretty_comps(const std::vector<std::string>& c) {
    std::string s;
    for (size_t i = 0; i < c.size(); i++) {
        if (i) s += '.';
        s += c[i];
    }
    return s;
}

// ---- F04 (fail closed): what the official importModules (globalLevel .private, as lean4export calls it) reads beyond the
// native core's needs.  (1) For EVERY visited module it also loads the IR parts (`readIRPartsOfMod`: if `X.ir.sig` exists,
// `X.ir.sig` and `X.ir` are read with the same header checks, a missing `X.ir` is an error).  (2) finalizeImport
// dereferences `extraConstNames` (Names, hashed/compared for const2ModIdx) and `entries` (Name x Array, extension
// lookup by name) of the main data (private part for module files) and of the `.ir` data.  The native core used to
// ignore all of that, so an .ir/.ir.sig file with a bad header (other Lean, garbage) or a ModuleData whose entries are
// broken made the official exporter fail while the native one succeeded.  Now: header checks exactly as for .olean
// files, and a structural validation of the objects the official code touches; anything off -> decline.
static P tr_parts(const std::vector<Part>& parts, uint64_t a, size_t need, const std::string& what) {
    for (const Part& p : parts) {
        uint64_t off = a - p.base;
        if (off < p.len) {
            if (need > p.len - off) die("object crosses the end of its region in " + what + " (declining)");
            return p.ptr + off;
        }
    }
    die("dangling pointer in " + what + " (declining)");
}
static void validate_name(const std::vector<Part>& parts, uint64_t r, const std::string& what) {
    size_t guard = 0;
    while (!is_scalar(r)) {
        if (++guard > 100000) die("name too deep in " + what + " (declining)");
        P p = tr_parts(parts, r, 8 + 16 + 8, what);
        uint8_t t = tag(p);
        if ((t != 1 && t != 2) || nobjs(p) != 2) die("malformed Name in " + what + " (declining)");
        uint64_t f1 = rawf(p, 1);
        if (t == 1) {
            if (is_scalar(f1)) die("malformed Name string in " + what + " (declining)");
            P sh = tr_parts(parts, f1, 32, what);
            if (tag(sh) != T_STRING) die("malformed Name string in " + what + " (declining)");
            uint64_t sz;
            memcpy(&sz, sh + 8, 8);
            if (sz == 0) die("malformed Name string in " + what + " (declining)");
            tr_parts(parts, f1, 32 + sz, what);
        } else if (!is_scalar(f1)) {
            P nn = tr_parts(parts, f1, 24, what);
            if (tag(nn) != T_MPZ) die("malformed Name number in " + what + " (declining)");
        }
        r = rawf(p, 0);
    }
    if (r != 1) die("malformed Name (scalar " + std::to_string(r) + ") in " + what + " (declining)");
}
static void validate_md(const std::vector<Part>& parts, uint64_t root, const std::string& what) {
    P d = tr_parts(parts, root, 8 + 5 * 8 + 1, what);
    if (tag(d) != 0 || nobjs(d) != 5) die("malformed ModuleData in " + what + " (declining)");
    for (size_t k = 0; k < 5; k++)
        if (is_scalar(rawf(d, k))) die("malformed ModuleData field in " + what + " (declining)");
    auto array = [&](uint64_t r) {
        P a = tr_parts(parts, r, 24, what);
        if (tag(a) != T_ARRAY) die("malformed array in " + what + " (declining)");
        size_t n = arr_size(a);
        if (n > ((uint64_t)1 << 40)) die("malformed array size in " + what + " (declining)");
        tr_parts(parts, r, 24 + 8 * n, what);
        return a;
    };
    for (size_t k = 0; k < 3; k++) array(rawf(d, k));  // imports, constNames, constants (shapes; read natively)
    P extra = array(rawf(d, 3));                        // extraConstNames
    for (size_t i = 0; i < arr_size(extra); i++) validate_name(parts, arr_raw(extra, i), what);
    P ents = array(rawf(d, 4));                         // entries : Array (Name x Array EnvExtensionEntry)
    for (size_t i = 0; i < arr_size(ents); i++) {
        uint64_t e = arr_raw(ents, i);
        if (is_scalar(e)) die("malformed entries in " + what + " (declining)");
        P pr = tr_parts(parts, e, 8 + 16, what);
        if (tag(pr) != 0 || nobjs(pr) != 2 || is_scalar(rawf(pr, 1))) die("malformed entries pair in " + what + " (declining)");
        validate_name(parts, rawf(pr, 0), what);
        array(rawf(pr, 1));
    }
}

// loads the module of slot `mi` (mods[mi].comps set by the caller; the slot already exists)
static void load_module(std::vector<Module>& mods, const std::vector<std::string>& sp, uint32_t mi) {
    const std::vector<std::string>& comps = mods[mi].comps;
    std::string path = find_olean(sp, comps);
    Part main = read_part(path);
    mods[mi].name = pretty_comps(comps);
    mods[mi].parts.push_back(main);
    uint64_t root;
    memcpy(&root, main.ptr + 0x58, 8);
    P d0 = tr_mods(mods, mi, root);
    bool is_module = sc_u8(d0, 0) != 0;  // ModuleData.isModule (only scalar field)
    P data = d0;
    if (is_module) {
        Part s = read_part(path + ".server");
        Part p = read_part(path + ".private");
        uint64_t proot;
        memcpy(&proot, p.ptr + 0x58, 8);
        mods[mi].parts.push_back(s);
        mods[mi].parts.push_back(p);
        data = tr_mods(mods, mi, proot);
        validate_md(mods[mi].parts, proot, path + ".private");
    } else {
        validate_md(mods[mi].parts, root, path);
    }
    mods[mi].data = data;
    // IR parts (official readIRPartsOfMod: `mFile.withExtension "ir.sig"`, then "ir")
    std::string base = path.substr(0, path.size() - 6);  // strip ".olean"
    if (exists(base + ".ir.sig")) {
        std::vector<Part> ir;
        ir.push_back(read_part(base + ".ir.sig"));  // header checks (marker, version, flags, githash) as for .olean
        ir.push_back(read_part(base + ".ir"));      // must exist (the official read fails otherwise)
        uint64_t iroot;
        memcpy(&iroot, ir[1].ptr + 0x58, 8);
        validate_md(ir, iroot, base + ".ir");
    }
}
static void imports_of(const std::vector<Module>& mods, uint32_t mi, std::vector<std::vector<std::string>>& out) {
    P d = mods[mi].data;
    P arr = tr_mods(mods, mi, rawf(d, 0));  // ModuleData.imports
    size_t n = arr_size(arr);
    for (size_t i = 0; i < n; i++) {
        P imp = tr_mods(mods, mi, arr_raw(arr, i));
        std::vector<std::string> c;
        name_comps_raw(mods, mi, rawf(imp, 0), c);  // Import.module
        out.push_back(c);
    }
}

static size_t env_size(const char* name, size_t dflt) {  // decimal env value (no strtol: see nostdcxx.h / glibc 2.38)
    const char* e = getenv(name);
    if (!e || !*e) return dflt;
    size_t v = 0;
    for (; *e >= '0' && *e <= '9'; e++) v = v * 10 + (size_t)(*e - '0');
    return v;
}

static size_t default_threads() {
    cpu_set_t cs;
    CPU_ZERO(&cs);
    size_t n = 8;
    if (sched_getaffinity(0, sizeof cs, &cs) == 0) n = (size_t)CPU_COUNT(&cs);
    if (n < 1) n = 1;
    if (n > 64) n = 64;
    return n;
}

static void name_comps_obj(b_lean_obj_arg n, std::vector<std::string>& out) {
    if (lean_is_scalar(n)) return;
    name_comps_obj(lean_ctor_get(n, 0), out);
    if (lean_ptr_tag(n) == 1) {
        out.push_back(std::string(lean_string_cstr(lean_ctor_get(n, 1))));
    } else {
        b_lean_obj_arg v = lean_ctor_get(n, 1);
        out.push_back(lean_is_scalar(v) ? std::to_string(lean_unbox(v)) : std::string("?"));
    }
}

static int g_gate_fd = -1;  // early child: read end of the gate pipe (see EARLY START)
static const int EXIT_EARLY_ABORT = 5;
static void gate_wait() {
    if (g_gate_fd < 0) return;
    char c = 0;
    ssize_t r;
    do {
        r = read(g_gate_fd, &c, 1);
    } while (r < 0 && errno == EINTR);
    close(g_gate_fd);
    g_gate_fd = -1;
    if (r != 1 || c != 'G') _exit(EXIT_EARLY_ABORT);
    logf("early child released by the parent%s", "");
}

struct Args {
    std::vector<std::string> sp;
    std::vector<std::vector<std::string>> roots;
    std::vector<NameArg> targets;
    bool whole_env = false;  // no target list: export every non-internal constant in `env.constants.toList` order
    size_t nthreads;
    bool list_mode = false;
};


// ------------------------------------------------------------------------------------------------
// F04 (finding 013): Lean's finalizeImport duplicate-constant rule (Environment.lean v4.33.1 subsumesInfo), decided
// natively only where it can be decided exactly; everything else declines (die -> the official exporter runs).
// StrictEq is a sufficient condition for Lean's `==`: structural equality of Name / Level / List Name (all fields,
// cached hashes) and, for Expr, the rules of Expr.eqv (kernel/expr_eq_fn.cpp, expr_eq_fn<false>: binder names and
// binder infos ignored, letE nondep compared, mdata KVMaps without Syntax values) plus a full compare of the cached
// Expr.Data word; fvar and mvar are never matched. StrictEq(a, b) => (a == b) in Lean; a mismatch is NOT proof of inequality -> decline.
struct StrictEq {
    In* x;
    uint64_t budget = 50000000;  // object comparisons; exhausted -> decline
    const char* why = "";        // diagnostics only
    std::unordered_map<uintptr_t, uintptr_t> memo;  // Expr object pa -> an object pb proven strictly equal to it
    bool tick() { return budget-- > 0; }
    bool nat(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        if (is_scalar(a) || is_scalar(b)) return a == b;
        P pa = x->tr(ma, a), pb = x->tr(mb, b);
        if (tag(pa) != T_MPZ || tag(pb) != T_MPZ) return false;
        int32_t sa, sb;
        memcpy(&sa, pa + 12, 4);
        memcpy(&sb, pb + 12, 4);
        if (sa != sb || sa < 0) return false;
        uint64_t da, db;
        memcpy(&da, pa + 16, 8);
        memcpy(&db, pb + 16, 8);
        if (sa == 0) return true;
        return memcmp(x->tr(ma, da), x->tr(mb, db), (size_t)sa * 8) == 0;
    }
    bool str(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        if (is_scalar(a) || is_scalar(b)) return false;
        P pa = x->tr(ma, a), pb = x->tr(mb, b);
        if (tag(pa) != T_STRING || tag(pb) != T_STRING) return false;
        size_t la = str_len(pa), lb = str_len(pb);
        return la == lb && memcmp(str_data(pa), str_data(pb), la) == 0;
    }
    bool name(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        if (!tick()) return false;
        if (is_scalar(a) || is_scalar(b)) return a == b;  // Name.anonymous = box(0)
        P pa = x->tr(ma, a), pb = x->tr(mb, b);
        uint8_t t = tag(pa);
        if (t != tag(pb) || nobjs(pa) != 2 || nobjs(pb) != 2) return false;
        if (sc_u64(pa, 0) != sc_u64(pb, 0)) { why = "name hash"; return false; }  // cached hash
        if (t == 1) { if (!str(ma, rawf(pa, 1), mb, rawf(pb, 1))) { why = "name str"; return false; } }
        else if (t == 2) { if (!nat(ma, rawf(pa, 1), mb, rawf(pb, 1))) { why = "name num"; return false; } }
        else return false;
        return name(ma, rawf(pa, 0), mb, rawf(pb, 0));
    }
    bool level(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        if (!tick()) return false;
        if (is_scalar(a) || is_scalar(b)) return a == b;
        P pa = x->tr(ma, a), pb = x->tr(mb, b);
        uint8_t t = tag(pa);
        if (t != tag(pb) || nobjs(pa) != nobjs(pb)) { why = "level tag"; return false; }
        if (sc_u64(pa, 0) != sc_u64(pb, 0)) { why = "level data"; return false; }  // cached Level.Data
        switch (t) {
            case 0: return nobjs(pa) == 0;
            case 1: return nobjs(pa) == 1 && level(ma, rawf(pa, 0), mb, rawf(pb, 0));
            case 2: case 3:
                return nobjs(pa) == 2 && level(ma, rawf(pa, 0), mb, rawf(pb, 0)) && level(ma, rawf(pa, 1), mb, rawf(pb, 1));
            case 4: return nobjs(pa) == 1 && name(ma, rawf(pa, 0), mb, rawf(pb, 0));
            default: return false;  // mvar: decline
        }
    }
    template <class F>
    bool list(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b, F elem) {
        while (true) {
            if (!tick()) return false;
            if (is_scalar(a) || is_scalar(b)) return a == b;  // List.nil = box(0)
            P pa = x->tr(ma, a), pb = x->tr(mb, b);
            if (tag(pa) != 1 || tag(pb) != 1 || nobjs(pa) != 2 || nobjs(pb) != 2) return false;
            if (!elem(rawf(pa, 0), rawf(pb, 0))) return false;
            a = rawf(pa, 1);
            b = rawf(pb, 1);
        }
    }
    // DataValue (deriving BEq): ofString 0, ofBool 1, ofName 2, ofNat 3, ofInt 4; ofSyntax 5 is never matched
    bool dval(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        if (is_scalar(a) || is_scalar(b)) return false;
        P pa = x->tr(ma, a), pb = x->tr(mb, b);
        uint8_t t = tag(pa);
        if (t != tag(pb) || nobjs(pa) != nobjs(pb)) return false;
        switch (t) {
            case 0: return nobjs(pa) == 1 && str(ma, rawf(pa, 0), mb, rawf(pb, 0));
            case 1: return nobjs(pa) == 0 && sc_u8(pa, 0) == sc_u8(pb, 0);
            case 2: return nobjs(pa) == 1 && name(ma, rawf(pa, 0), mb, rawf(pb, 0));
            case 3: case 4: return nobjs(pa) == 1 && nat(ma, rawf(pa, 0), mb, rawf(pb, 0));  // Int: scalar or mpz >= 0
            default: return false;
        }
    }
    // KVMap = List (Name x DataValue); C++ kvmap == compares the lists element-wise (name ==, data_value ==)
    bool kvmap(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        return list(ma, a, mb, b, [&](uint64_t u, uint64_t v) {
            if (is_scalar(u) || is_scalar(v)) return false;
            P qa = x->tr(ma, u), qb = x->tr(mb, v);
            if (tag(qa) != 0 || tag(qb) != 0 || nobjs(qa) != 2 || nobjs(qb) != 2) return false;
            return name(ma, rawf(qa, 0), mb, rawf(qb, 0)) && dval(ma, rawf(qa, 1), mb, rawf(qb, 1));
        });
    }
    bool names(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        return list(ma, a, mb, b, [&](uint64_t u, uint64_t v) { return name(ma, u, mb, v); });
    }
    bool expr(uint32_t ma, uint64_t a, uint32_t mb, uint64_t b) {
        if (!tick()) return false;
        if (is_scalar(a) || is_scalar(b)) return false;
        P pa = x->tr(ma, a), pb = x->tr(mb, b);
        auto it = memo.find((uintptr_t)pa);
        if (it != memo.end() && it->second == (uintptr_t)pb) return true;  // exact pair proven equal before
        uint8_t t = tag(pa);
        if (t != tag(pb) || nobjs(pa) != nobjs(pb)) { why = "expr tag"; return false; }
        if (sc_u64(pa, 0) != sc_u64(pb, 0)) { why = "expr data"; return false; }  // cached Expr.Data (hash, flags, ranges)
        bool ok;
        switch (t) {
            case 0: ok = nobjs(pa) == 1 && nat(ma, rawf(pa, 0), mb, rawf(pb, 0)); break;
            case 3: ok = nobjs(pa) == 1 && level(ma, rawf(pa, 0), mb, rawf(pb, 0)); break;
            case 4:
                ok = nobjs(pa) == 2 && name(ma, rawf(pa, 0), mb, rawf(pb, 0)) &&
                     list(ma, rawf(pa, 1), mb, rawf(pb, 1), [&](uint64_t u, uint64_t v) { return level(ma, u, mb, v); });
                break;
            case 5: ok = nobjs(pa) == 2 && expr(ma, rawf(pa, 0), mb, rawf(pb, 0)) && expr(ma, rawf(pa, 1), mb, rawf(pb, 1)); break;
            case 6: case 7:  // Expr.eqv (expr_eq_fn<false>): binder names and binder infos are NOT compared
                ok = nobjs(pa) == 3 && expr(ma, rawf(pa, 1), mb, rawf(pb, 1)) && expr(ma, rawf(pa, 2), mb, rawf(pb, 2));
                break;
            case 8:  // Expr.eqv: type, value, body and the nondep flag (scalar byte after Data); not the name
                ok = nobjs(pa) == 4 && sc_u8(pa, 8) == sc_u8(pb, 8) && expr(ma, rawf(pa, 1), mb, rawf(pb, 1)) &&
                     expr(ma, rawf(pa, 2), mb, rawf(pb, 2)) && expr(ma, rawf(pa, 3), mb, rawf(pb, 3));
                break;
            case 9: {
                if (nobjs(pa) != 1) { ok = false; break; }
                uint64_t la = rawf(pa, 0), lb = rawf(pb, 0);
                if (is_scalar(la) || is_scalar(lb)) { ok = false; break; }
                P qa = x->tr(ma, la), qb = x->tr(mb, lb);
                if (tag(qa) != tag(qb) || nobjs(qa) != 1 || nobjs(qb) != 1) { ok = false; break; }
                if (tag(qa) == 0) ok = nat(ma, rawf(qa, 0), mb, rawf(qb, 0));
                else if (tag(qa) == 1) ok = str(ma, rawf(qa, 0), mb, rawf(qb, 0));
                else ok = false;
                break;
            }
            case 11:
                ok = nobjs(pa) == 3 && name(ma, rawf(pa, 0), mb, rawf(pb, 0)) && nat(ma, rawf(pa, 1), mb, rawf(pb, 1)) &&
                     expr(ma, rawf(pa, 2), mb, rawf(pb, 2));
                break;
            case 10:  // mdata: expr_eq_fn compares the inner expression and the KVMap (C++ kvmap ==)
                ok = nobjs(pa) == 2 && expr(ma, rawf(pa, 1), mb, rawf(pb, 1)) && kvmap(ma, rawf(pa, 0), mb, rawf(pb, 0));
                break;
            default: ok = false;  // fvar, mvar: decline
        }
        if (ok) memo[(uintptr_t)pa] = (uintptr_t)pb;  // exact pair (no hashing of the pair: no collisions)
        return ok;
    }
};
// 1: the new constant replaces the previous one; 0: the previous one stays; -1: decline (cannot decide natively, or
// Lean throws "import failed, environment already contains ...": the official exporter reproduces that error)
static int dup_rule(In* x, uint32_t mn, P cin, uint32_t mp, P cip, const char*& why) {
    uint8_t tn = tag(cin), tp = tag(cip);
    why = "kinds";
    if (!((tn == 2 || tn == 0) && (tp == 2 || tp == 0))) return -1;
    why = "axiom/axiom";
    if (tn == 0 && tp == 0) return -1;  // axiom/axiom needs isPropCheap: decline
    P vn = x->f(mn, cin, 0), vp = x->f(mp, cip, 0);
    P cn = x->f(mn, vn, 0), cp = x->f(mp, vp, 0);  // ConstantVal {name, levelParams, type}
    StrictEq q{x};
    why = "name";
    if (!q.name(mn, rawf(cn, 0), mp, rawf(cp, 0))) return -1;
    why = "type";
    if (!q.expr(mn, rawf(cn, 2), mp, rawf(cp, 2))) { if (*q.why) why = q.why; return -1; }
    why = "levelParams";
    if (!q.names(mn, rawf(cn, 1), mp, rawf(cp, 1))) return -1;
    why = "all/unsafe";
    if (tn == 2 && tp == 2) {  // TheoremVal {toConstantVal, value, all}: all == all -> the new one wins
        return q.names(mn, rawf(vn, 2), mp, rawf(vp, 2)) ? 1 : -1;
    }
    // theorem/axiom pair: thm.all == [ax.name] && !ax.isUnsafe
    uint32_t mt = tn == 2 ? mn : mp, ma = tn == 2 ? mp : mn;
    P vt = tn == 2 ? vn : vp, va = tn == 2 ? vp : vn, ca = tn == 2 ? cp : cn;
    if (sc_u8(va, 0) != 0) return -1;  // AxiomVal.isUnsafe
    uint64_t all = rawf(vt, 2);
    if (is_scalar(all)) return -1;
    P cell = x->tr(mt, all);
    if (tag(cell) != 1 || nobjs(cell) != 2 || rawf(cell, 1) != 1) return -1;  // exactly one element (tail = nil = box(0))
    if (!q.name(mt, rawf(cell, 0), ma, rawf(ca, 0))) return -1;
    return tn == 2 ? 1 : 0;  // new theorem over axiom: new wins; new axiom after theorem: the theorem stays
}

static void run(Args& a) {
    size_t nthreads = a.nthreads;
    logf("start: %s threads", std::to_string(nthreads));
    if (g_verbose)
        logf("thp: %s", "enabled=" + thp_setting("/sys/kernel/mm/transparent_hugepage/enabled") +
                            " defrag=" + thp_setting("/sys/kernel/mm/transparent_hugepage/defrag") + " " + thp_faults());
    // ---- import graph: modules are discovered and loaded (open + mmap + imports) in parallel; then the import order
    //      is the post-order DFS of importModulesCore with globalLevel = private (every module loaded with importAll,
    //      visited once, pushed after its imports, imports in ModuleData order), computed sequentially in memory.
    In* x = new In();
    std::vector<Module>& mods = x->mods;
    const size_t MAXMODS = (size_t)1 << 21;
    mods.reserve(MAXMODS);  // never reallocated while loader threads hold references into it
    std::vector<uint32_t> order;
    std::vector<uint32_t> root_slots;
    {
        std::mutex lmu;  // guards idx_of, mods.size()/emplace_back and the work queue
        std::unordered_map<std::string, uint32_t> idx_of;
        std::vector<uint32_t> queue;
        std::atomic<size_t> pending{0};
        auto slot_of = [&](const std::vector<std::string>& comps) -> uint32_t {  // call with lmu held
            std::string key = join_comps(comps);
            auto it = idx_of.find(key);
            if (it != idx_of.end()) return it->second;
            if (mods.size() >= MAXMODS) die("too many modules");
            uint32_t i = (uint32_t)mods.size();
            mods.emplace_back();
            mods[i].comps = comps;
            idx_of.emplace(key, i);
            queue.push_back(i);
            pending.fetch_add(1);
            return i;
        };
        {
            std::lock_guard<std::mutex> g(lmu);
            for (const auto& r : a.roots) root_slots.push_back(slot_of(r));
        }
        std::vector<std::function<void()>> fns;
        for (size_t k = 0; k < nthreads; k++) {
            fns.push_back([&] {
                std::vector<std::vector<std::string>> imps;
                while (true) {
                    uint32_t mi = NONE;
                    {
                        std::lock_guard<std::mutex> g(lmu);
                        if (!queue.empty()) {
                            mi = queue.back();
                            queue.pop_back();
                        }
                    }
                    if (mi == NONE) {
                        if (pending.load() == 0) break;
                        usleep(50);
                        continue;
                    }
                    load_module(mods, a.sp, mi);
                    imps.clear();
                    imports_of(mods, mi, imps);
                    std::vector<uint32_t> idx(imps.size());
                    {
                        std::lock_guard<std::mutex> g(lmu);
                        for (size_t i = 0; i < imps.size(); i++) idx[i] = slot_of(imps[i]);
                    }
                    mods[mi].imps = std::move(idx);
                    pending.fetch_sub(1);
                }
            });
        }
        run_with_stack((size_t)64 << 20, fns);
        // post-order DFS
        std::vector<uint8_t> done(mods.size(), 0);
        struct Frame {
            uint32_t mi;  // NONE = the virtual root (imports = roots)
            size_t next;
        };
        std::vector<Frame> stack;
        stack.push_back(Frame{NONE, 0});
        while (!stack.empty()) {
            Frame& top = stack.back();
            const std::vector<uint32_t>& imps = top.mi == NONE ? root_slots : mods[top.mi].imps;
            if (top.next < imps.size()) {
                uint32_t mi = imps[top.next];
                top.next++;
                if (done[mi] == 2) continue;
                if (done[mi] == 1) die("import cycle at " + mods[mi].name);
                done[mi] = 1;
                stack.push_back(Frame{mi, 0});
            } else {
                uint32_t mi = top.mi;
                stack.pop_back();
                if (mi != NONE) {
                    done[mi] = 2;
                    order.push_back(mi);
                }
            }
        }
    }
    // ---- table sizes.  The olean bytes bound the number of objects of every kind: every Expr object takes >= 24
    //      bytes (header + one field + cached data), so the lock-free expr table can never fill up.
    size_t total_bytes = 0, side_cells = 0, nconst_total = 0;
    for (Module& md : mods)
        for (Part& pt : md.parts) {
            total_bytes += pt.len;
            side_cells += (pt.len + 15) / 16;
        }
    auto* side = (std::atomic<uint32_t>*)zalloc_huge(side_cells * sizeof(uint32_t));
    {
        size_t at = 0;
        for (Module& md : mods)
            for (Part& pt : md.parts) {
                pt.side = side + at;
                at += (pt.len + 15) / 16;
            }
    }
    for (uint32_t mi : order) nconst_total += arr_size(x->f(mi, mods[mi].data, 1));
    logf("%s modules loaded", std::to_string(order.size()) + " (" + std::to_string(total_bytes >> 20) + " MB, " +
                                  std::to_string(nconst_total) + " constants)");
    x->names.init((size_t)1 << 31);
    {
        // names: estimate 16 per constant (Mathlib: 4.5M names for 0.77M constants); past 3/4 -> restart with the
        // bound (every Name object takes >= 32 bytes)
        // (a restart multiplies the estimate by 8 until it reaches the bound: full-RH-scale exports must not get a
        // bound-sized table of tens of GB right away)
        size_t nest = std::max((size_t)1 << 22, nconst_total * 16), nbound = std::max(nest, total_bytes / 32);
        for (int k = 0; k < g_size_attempt && nest < nbound; k++) nest *= 8;
        g_nmap_estimated = nthreads > 1 && !g_emap_use_bound && nest < nbound;  // (1 thread: no phase A, no restart)
        x->nmap.init(g_nmap_estimated ? nest : nbound);
        if (g_nmap_estimated) x->nmap.limit = (x->nmap.mask + 1) / 4 * 3;
    }
    x->lkeys.init((size_t)1 << 28);
    x->lmap.init((size_t)1 << 12);
    x->llkeys.init((size_t)1 << 28);
    x->llmap.init((size_t)1 << 12);
    x->ekeys.init((size_t)1 << 32);
    {
        // bound: every Expr object takes >= 24 bytes.  Estimates (restart with the bound if phase A passes 3/4 of
        // the slots): whole environment 1 key per 48 olean bytes (Mathlib: 1 per 65), target list 32M keys (the
        // closure is unknown and usually much smaller)
        size_t bound = total_bytes / 24, est = a.whole_env ? total_bytes / 48 : (size_t)1 << 25;
        if (const char* e = getenv("LEAN4EXPORT_EXPR_ESTIMATE_LOG2")) {  // testing aid (no atoi: see nostdcxx.h)
            unsigned v = 0;
            for (const char* q = e; *q >= '0' && *q <= '9'; q++) v = v * 10 + (unsigned)(*q - '0');
            if (v >= 10 && v <= 40) est = (size_t)1 << v;
        }
        for (int k = 0; k < g_size_attempt && est < bound; k++) est *= 8;  // restarts: 8x per attempt, up to the bound
        g_emap_estimated = nthreads > 1 && !g_emap_use_bound && bound > est;
        x->emap.init(g_emap_estimated ? est : bound);
        if (g_emap_estimated) x->emap.limit = (x->emap.mask + 1) / 4 * 3;
        logf("expr table: %s", std::to_string((x->emap.mask + 1) >> 20) + "M slots" + (g_emap_estimated ? " (estimate)" : ""));
    }
    x->enq.init((size_t)1 << 31);
    if (!getenv("LEAN4EXPORT_NO_PREFAULT")) {
        prefault_huge(side, side_cells * sizeof(uint32_t), nthreads);
        prefault_huge(x->emap.slots, (x->emap.mask + 1) * sizeof(uint64_t), nthreads);
        prefault_huge(x->nmap.slots, (x->nmap.mask + 1) * sizeof(uint64_t), nthreads);
        logf("prefault done%s", "");
    }
    logf("interner tables created%s", "");
    x->names.set(0, NameE{NKey{0, 0, 0, nullptr, 0}, 1723});
    x->llkeys.set(0, LLKey{NONE, NONE});
    if (x->level_key_insert(LKey{0, 0, 0}) != 0) die("internal: level zero id");

    // ---- constant names, interned in parallel per module; then finalizeImport's duplicate rule in import order
    std::vector<std::vector<std::pair<uint32_t, P>>> per_mod(order.size());
    {
        std::atomic<size_t> next{0};
        std::vector<std::function<void()>> fns;
        for (size_t k = 0; k < nthreads; k++) {
            fns.push_back([&] {
                while (true) {
                    size_t i = next.fetch_add(1);
                    if (i >= order.size()) break;
                    uint32_t mi = order[i];
                    P d = mods[mi].data;
                    P names = x->f(mi, d, 1);   // ModuleData.constNames
                    P consts = x->f(mi, d, 2);  // ModuleData.constants
                    size_t n = arr_size(consts);
                    if (arr_size(names) != n) die("constNames/constants size mismatch in " + mods[mi].name);
                    auto& v = per_mod[i];
                    v.reserve(n);
                    for (size_t j = 0; j < n; j++) {
                        uint32_t nm = x->intern_name(mi, arr_raw(names, j));
                        P ci = x->tr(mi, arr_raw(consts, j));
                        v.push_back({nm, ci});
                    }
                }
            });
        }
        run_with_stack((size_t)256 << 20, fns);
    }
    logf("constant names interned%s", "");
    size_t nconst = 0, nuniq = 0, ndup = 0;
    std::vector<uint32_t> first_order;  // whole-env mode: constant names in first-insertion order
    x->cmap.assign(x->nc.load(), CRef{NONE, nullptr});
    for (size_t k = 0; k < order.size(); k++) {
        uint32_t mi = order[k];
        for (auto& pr : per_mod[k]) {
            uint32_t nm = pr.first;
            P ci = pr.second;
            nconst++;
            CRef& slot = x->cmap[nm];
            if (slot.m == NONE) {
                slot = CRef{mi, ci};
                nuniq++;
                if (a.whole_env) first_order.push_back(nm);
            } else {
                // F04 (finding 013): exact subsumesInfo on strictly equal type/levelParams/all, else decline
                ndup++;
                const char* why = "";
                int r = dup_rule(x, mi, ci, slot.m, slot.ci, why);
                if (r < 0)
                    die("duplicate constant '" + x->name_str(nm) + "' (tags " + std::to_string(tag(ci)) + "/" +
                        std::to_string(tag(slot.ci)) + ", " + why + ") not decidable natively (declining)");
                if (r == 1) slot = CRef{mi, ci};
            }
        }
    }
    // ---- whole-environment mode: the order of `env.constants.toList.map Prod.fst |>.filter (!·.isInternal)`.
    // `env.constants` of an imported environment is `SMap.fromHashMap privateConstantMap false` (finalizeImport):
    // map₂ is empty, so `toList` = `map₁.fold (fun es a b => (a, b) :: es) []` = the Std.HashMap fold order reversed.
    // The HashMap was created with `emptyWithCapacity numPrivateConsts` (= total number of constants of all modules,
    // duplicates included), i.e. nextPowerOfTwo (n * 4 / 3) buckets; it never expands (expandIfNecessary needs
    // size * 4 / 3 > #buckets).  Keys were inserted in import order x constNames order with `getThenInsertIfNew?`
    // (AssocList.cons at the bucket head); a duplicate replaces in place (`insert` -> `replace`), keeping the position
    // of the first insertion.  fold visits buckets 0..N-1, each from head (newest) to tail, so the reversed list is
    // buckets N-1..0, each in first-insertion order.  Bucket index = mkIdx: scrambleHash (Name.hash) &&& (N - 1).
    logf("constant map built%s", (" (" + std::to_string(ndup) + " duplicate names resolved)").c_str());
    std::vector<uint32_t> env_order;
    if (a.whole_env) {
        uint64_t want = (uint64_t)nconst * 4 / 3;
        uint64_t nb = 1;
        while (nb < want) nb <<= 1;
        // sort key = (N-1-bucket) << 32 | first-insertion position; internal names dropped (parallel chunks)
        size_t nf = first_order.size();
        size_t nch = nthreads * 4;
        std::vector<std::vector<uint64_t>> keys(nch);
        std::atomic<size_t> next{0};
        std::vector<std::function<void()>> fns;
        for (size_t k = 0; k < nthreads; k++) {
            fns.push_back([&] {
                while (true) {
                    size_t ch = next.fetch_add(1);
                    if (ch >= nch) break;
                    size_t lo = nf * ch / nch, hi = nf * (ch + 1) / nch;
                    for (size_t i = lo; i < hi; i++) {
                        uint32_t nm = first_order[i];
                        if (x->is_internal(nm)) continue;
                        uint64_t h = x->names.get(nm).hash;
                        uint64_t f = h ^ (h >> 32);
                        f ^= f >> 16;
                        keys[ch].push_back(((nb - 1 - (f & (nb - 1))) << 32) | (uint64_t)i);
                    }
                }
            });
        }
        run_with_stack((size_t)64 << 20, fns);
        std::vector<uint64_t> all;
        for (auto& kv : keys) all.insert(all.end(), kv.begin(), kv.end());
        std::sort(all.begin(), all.end());
        env_order.reserve(all.size());
        for (uint64_t kk : all) env_order.push_back(first_order[(uint32_t)kk]);
        if (nf != nuniq || nf >= ((uint64_t)1 << 32)) die("internal: whole-env order");
        logf("whole-env order: %s", std::to_string(env_order.size()) + " of " + std::to_string(nf) +
                                         " constants (buckets " + std::to_string(nb) + ")");
    }
    per_mod.clear();
    per_mod.shrink_to_fit();
    // recursor map: inductive name -> recursors whose `all` mentions it (scan in parallel chunks, merged in
    // ascending constant order = the order of the sequential loop)
    {
        size_t ncm = x->cmap.size();
        size_t nch = nthreads * 4;
        std::vector<std::vector<std::pair<uint32_t, uint32_t>>> found(nch);
        std::atomic<size_t> next{0};
        std::vector<std::function<void()>> fns;
        for (size_t k = 0; k < nthreads; k++) {
            fns.push_back([&] {
                std::vector<uint32_t> all;
                while (true) {
                    size_t ch = next.fetch_add(1);
                    if (ch >= nch) break;
                    size_t lo = ncm * ch / nch, hi = ncm * (ch + 1) / nch;
                    for (size_t c = lo; c < hi; c++) {
                        const CRef& r = x->cmap[c];
                        if (r.m == NONE || tag(r.ci) != 7) continue;
                        P val, cval;
                        x->vals(r, val, cval);
                        all.clear();
                        x->list_names(r.m, rawf(val, 1), all);
                        for (uint32_t ind : all) found[ch].push_back({ind, (uint32_t)c});
                    }
                }
            });
        }
        run_with_stack((size_t)64 << 20, fns);
        for (auto& f : found)
            for (auto& pr : f) {
                auto& v = x->recmap[pr.first];
                if (std::find(v.begin(), v.end(), pr.second) == v.end()) v.push_back(pr.second);
            }
    }
    logf("%s constants", std::to_string(nconst) + " (" + std::to_string(nuniq) + " unique), " +
                             std::to_string(x->nc.load()) + " names");
    x->n_nat = x->lookup_name_str("Nat");
    x->n_charofnat = x->lookup_name_str("Char.ofNat");
    x->n_stringoflist = x->lookup_name_str("String.ofList");
    x->n_eq = x->lookup_name_str("Eq");
    const char* qs[4] = {"Quot", "Quot.mk", "Quot.lift", "Quot.ind"};
    for (int i = 0; i < 4; i++) x->n_quot[i] = x->lookup_name_str(qs[i]);

    if (a.list_mode) {  // testing aid: list the constants of the root modules (kind tag, name)
        Out o;
        o.start();
        for (size_t k = 0; k < order.size(); k++) {
            uint32_t mi = order[k];
            bool is_root = false;
            for (auto& r : a.roots)
                if (pretty_comps(r) == mods[mi].name) is_root = true;
            if (!is_root) continue;
            P d = mods[mi].data;
            P names = x->f(mi, d, 1);
            P consts = x->f(mi, d, 2);
            for (size_t j = 0; j < arr_size(names); j++) {
                P ci = x->tr(mi, arr_raw(consts, j));
                uint32_t nm = x->intern_name(mi, arr_raw(names, j));
                o.n(tag(ci));
                o.ch('\t');
                std::string s = x->name_str(nm);
                o.s(s.data(), s.size());
                o.nl();
            }
        }
        o.finish();
        return;
    }
    // ---- targets
    std::vector<uint32_t> tids;
    if (a.whole_env) tids = env_order;
    size_t nt = a.whole_env ? 0 : a.targets.size();
    for (size_t i = 0; i < nt; i++) {
        uint32_t id = x->lookup_name_arg(a.targets[i]);
        if (id == NONE) {
            std::vector<std::string> c;
            for (const NameComp& nc : a.targets[i])
                c.push_back(nc.kind == 1 ? nc.s : nc.kind == 2 ? std::to_string(nc.num) : std::string("?"));
            // F04 (fail closed): decline before any output; the official exporter defines this path
            die("target constant " + pretty_comps(c) + " not found in environment (declining)");
        }
        tids.push_back(id);
    }
    // ---- phase A (parallel interning of the closure)
    if (nthreads > 1) {
        phase_a(x, tids, nthreads);
        if (g_verbose) logf("thp: %s", thp_faults());
        logf("phase A done: %s", "names " + std::to_string(x->nc.load()) + " exprs " + std::to_string(x->ec.load()) +
                                      " levels " + std::to_string(x->lc.load()));
    }
    // ---- phase B (dump in lean4export order)
    gate_wait();  // early child: wait until the parent has written the metadata line and confirmed the arguments
    g_output_started.store(true);  // from here on the child may write: no restart (EXIT_TABLE_FULL) any more
    St* st = new St();
    st->x = x;
    st->exp_n.assign(1, 0);
    st->exp_l.assign(1, 0);
    st->out.start(std::min<size_t>(12, std::max<size_t>(4, nthreads / 2)));  // copier threads of the output sink
    {
        // output size estimate ~54 bytes per interned expression/name (Mathlib 56, rh-mid 52 per output line)
        uint64_t est = 54 * ((uint64_t)x->ec.load() + (uint64_t)x->nc.load());
        size_t k = env_size("LEAN4EXPORT_PREPOP", std::max<size_t>(2, nthreads / 8));
        bool idle = env_size("LEAN4EXPORT_PREPOP_IDLE", 0) != 0;
        st->out.sink->prepopulate(est, k, idle);
    }
    const char* sf = getenv("LEAN4EXPORT_SELFTEST_FAIL");  // testing aid for the fallback path
    bool selftest_fail = sf && *sf && strcmp(sf, "0") != 0;
    const char* pdv = getenv("LEAN4EXPORT_PAR_DUMP");  // 0 = sequential dump (St only)
    bool par_dump = nthreads > 1 && !selftest_fail && !(pdv && strcmp(pdv, "0") == 0);
    if (par_dump) {
        PD* pd = new PD();
        pd->x = x;
        pd->st = st;
        pd->nthreads = nthreads;
        pd->run(tids);
        tids.clear();
    }
    for (uint32_t c : tids) {
        if (c == NONE) continue;
        st->dump_constant(c);
        if (selftest_fail) {
            st->out.flush();
            usleep(100000);
            die("selftest failure");
        }
    }
    st->out.finish();
    {
        struct rusage ru;
        getrusage(RUSAGE_SELF, &ru);
        logf("done: %s", "names " + std::to_string(st->cn) + " levels " + std::to_string(st->cl) + " exprs " +
                             std::to_string(st->ce) + " (interned exprs " + std::to_string(x->ec.load()) + "), maxrss " +
                             std::to_string(ru.ru_maxrss / 1024) + " MB, user " + std::to_string(ru.ru_utime.tv_sec) +
                             " s, sys " + std::to_string(ru.ru_stime.tv_sec) + " s");
        // diagnostics for the benchmark log: page faults and whether transparent huge pages are in effect
        std::string thp;
        const char* mi = getenv("LEAN4EXPORT_MEMINFO");  // smaps_rollup costs ~0.2 s with a 10 GB address space
        if (FILE* f = (mi && *mi && strcmp(mi, "0") != 0) ? fopen("/proc/self/smaps_rollup", "r") : nullptr) {
            char line[256];
            while (fgets(line, sizeof line, f))
                if (!strncmp(line, "Rss:", 4) || !strncmp(line, "AnonHugePages:", 14) || !strncmp(line, "Anonymous:", 10)) {
                    std::string l(line);
                    while (!l.empty() && (l.back() == '\n' || l.back() == ' ')) l.pop_back();
                    size_t k = 0;
                    std::string c;
                    for (char ch : l)
                        if (!(ch == ' ' && k++ && !c.empty() && c.back() == ' ')) c += ch;
                    thp += " " + c;
                }
            fclose(f);
        }
        if (const char* sp = getenv("LEAN4EXPORT_SMAPS")) {  // debugging aid: copy /proc/self/smaps to a file
            FILE* in = fopen("/proc/self/smaps", "r");
            FILE* outf = fopen(sp, "w");
            if (in && outf) {
                char buf[1 << 16];
                size_t k;
                while ((k = fread(buf, 1, sizeof buf, in)) > 0) fwrite(buf, 1, k, outf);
            }
            if (in) fclose(in);
            if (outf) fclose(outf);
        }
        logf("mem: %s", "minflt " + std::to_string(ru.ru_minflt) + " majflt " + std::to_string(ru.ru_majflt) + thp);
    }
    // everything is intentionally leaked (the process exits right after), but the pages are released in parallel
    fast_teardown(nthreads);
}

}  // namespace lean4export_native

using namespace lean4export_native;

// ------------------------------------------------------------------------------------------------
// EARLY START.  lean4export spends ~30-40 ms in the Lean runtime/module initializers before Main.lean reaches
// lean4export_fast_main.  When the command line is simple enough to be decoded without Lean (no options, plain dotted
// ASCII names, LEAN_PATH set), a static constructor forks the native child right at process start: it loads and
// interns while the parent initializes Lean, and blocks before its first output byte (gate_wait) until the parent has
// printed the metadata line and checked that Main.lean's decoded arguments are exactly the ones the child guessed
// ('G'); on any difference the child is killed and the normal path runs.  The child never touches the Lean runtime.
// NOTE: code reachable from run() must not rely on dynamically initialized namespace-scope objects of this file (the
// early child starts before they are constructed): use plain data, pointers or function-local statics.
// LEAN4EXPORT_EARLY=0 disables it.
struct Early {
    pid_t pid = -1;
    int gate = -1;  // write end of the gate pipe
    Args a;
    uint32_t nthreads_raw = 0;
};
static Early* g_early = nullptr;

static bool ascii_alpha(unsigned char c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'); }
static bool ascii_digit(unsigned char c) { return c >= '0' && c <= '9'; }
// conservative guess of Syntax.decodeNameLit ("`" ++ s): dotted identifiers of [A-Za-z_][A-Za-z0-9_'!?]*
// (the parent verifies the guess against the real decoding, so this only decides whether to try)
static bool plain_name(const char* s, NameArg& out) {
    size_t n = strlen(s), i = 0;
    if (n == 0) return false;
    while (i <= n) {
        size_t j = i;
        while (j < n && s[j] != '.') j++;
        if (j == i) return false;
        unsigned char c0 = (unsigned char)s[i];
        if (!(ascii_alpha(c0) || c0 == '_')) return false;
        for (size_t k = i; k < j; k++) {
            unsigned char c = (unsigned char)s[k];
            if (!(ascii_alpha(c) || ascii_digit(c) || c == '_' || c == '\'' || c == '!' || c == '?')) return false;
        }
        NameComp nc;
        nc.kind = 1;
        nc.s = std::string(s + i, j - i);
        nc.num = 0;
        out.push_back(nc);
        i = j + 1;
    }
    return true;
}

__attribute__((constructor(102))) static void early_start(int argc, char** argv) {
    auto off = [](const char* k) {
        const char* v = getenv(k);
        return v && strcmp(v, "0") == 0;
    };
    auto on = [](const char* k) {
        const char* v = getenv(k);
        return v && *v && strcmp(v, "0") != 0;
    };
    // Main.lean takes the native path iff LEAN4EXPORT_NATIVE != "0" and there are no options
    if (off("LEAN4EXPORT_NATIVE") || off("LEAN4EXPORT_EARLY") || on("LEAN4EXPORT_NOFORK") ) return;
    const char* lp = getenv("LEAN_PATH");
    if (!lp || argc < 2) return;
    uint32_t nraw = 0;
    if (const char* t = getenv("LEAN4EXPORT_THREADS")) {
        size_t n = strlen(t);
        if (n == 0 || n > 9) return;
        for (size_t i = 0; i < n; i++) {
            if (!ascii_digit((unsigned char)t[i])) return;
            nraw = nraw * 10 + (uint32_t)(t[i] - '0');
        }
    }
    Early* e = new Early();
    bool sep = false;
    for (int i = 1; i < argc; i++) {
        const char* s = argv[i];
        size_t n = strlen(s);
        if (n >= 3 && s[0] == '-' && s[1] == '-') {  // an option: no native path
            delete e;
            return;
        }
        if (!sep && strcmp(s, "--") == 0) {
            sep = true;
            continue;
        }
        NameArg na;
        if (!plain_name(s, na)) {
            delete e;
            return;
        }
        if (sep) {
            e->a.targets.push_back(na);
        } else {
            std::vector<std::string> c;
            for (const NameComp& nc : na) c.push_back(nc.s);
            e->a.roots.push_back(c);
        }
    }
    // SearchPath.parse: split at ':' (empty entries kept)
    {
        const char* p = lp;
        while (true) {
            const char* q = strchr(p, ':');
            if (!q) {
                e->a.sp.push_back(std::string(p));
                break;
            }
            e->a.sp.push_back(std::string(p, q - p));
            p = q + 1;
        }
    }
    e->a.whole_env = !sep;
    e->nthreads_raw = nraw;
    e->a.nthreads = nraw ? (size_t)nraw : default_threads();
    int gp[2];
    if (pipe2(gp, O_CLOEXEC) != 0) {
        delete e;
        return;
    }
    const char* v = getenv("LEAN4EXPORT_VERBOSE");
    g_verbose = !(v && strcmp(v, "0") == 0);
    const char* pp = getenv("LEAN4EXPORT_POPULATE");
    g_populate = pp && *pp && strcmp(pp, "0") != 0;
    g_t0 = now_s();
    pid_t pid = fork();
    if (pid == 0) {
        close(gp[1]);
        g_gate_fd = gp[0];
        g_sp_partial = true;  // Main.lean's first call passes only the LEAN_PATH entries
        logf("early start: native child forked at process start%s", "");
        const char* tc = getenv("LEAN4EXPORT_EARLY_TEST_CRASH");  // testing aid: the early child dies before output
        if (tc && *tc && strcmp(tc, "0") != 0) abort();
        std::vector<std::function<void()>> fns;
        fns.push_back([e] { run(e->a); });  // big stack: deep expressions recurse
        run_with_stack((size_t)64 << 30, fns);
        _exit(0);
    }
    close(gp[0]);
    if (pid < 0) {
        close(gp[1]);
        delete e;
        return;
    }
    e->pid = pid;
    e->gate = gp[1];
    g_early = e;
}

static bool early_matches(const Early* e, const Args& a, bool sp_partial, uint32_t nthreads_raw) {
    const char* fm = getenv("LEAN4EXPORT_EARLY_TEST_MISMATCH");  // testing aid: pretend the guess was wrong
    if (fm && *fm && strcmp(fm, "0") != 0) return false;
    return sp_partial && e->nthreads_raw == nthreads_raw && e->a.whole_env == a.whole_env && e->a.sp == a.sp &&
           e->a.roots == a.roots && e->a.targets == a.targets && !a.list_mode;
}

// Lean Name -> plain components
static void name_arg_obj(b_lean_obj_arg n, NameArg& out) {
    if (lean_is_scalar(n)) return;
    name_arg_obj(lean_ctor_get(n, 0), out);
    NameComp c;
    c.num = 0;
    if (lean_ptr_tag(n) == 1) {
        b_lean_obj_arg s = lean_ctor_get(n, 1);
        c.kind = 1;
        c.s = std::string(lean_string_cstr(s), lean_string_size(s) - 1);
    } else {
        b_lean_obj_arg v = lean_ctor_get(n, 1);
        if (lean_is_scalar(v)) {
            c.kind = 2;
            c.num = lean_unbox(v);
        } else {
            c.kind = 3;
        }
    }
    out.push_back(c);
}

// lean4export_fast_main (sp : @& Array String) (spPartial : Bool) (roots targets : @& Array Name) (wholeEnv : Bool)
//   (nthreads : UInt32) : IO UInt32
// spPartial: `sp` is only the LEAN_PATH part of the search path; if a module root is not found in it, nothing is
// written and 3 is returned (the caller then computes the complete search path and calls again).
extern "C" LEAN_EXPORT lean_obj_res lean4export_fast_main(b_lean_obj_arg sp, uint8_t sp_partial, b_lean_obj_arg roots,
                                                           b_lean_obj_arg targets, uint8_t whole_env, uint32_t nthreads) {
    g_sp_partial = sp_partial != 0;
    Args a;
    for (size_t i = 0; i < lean_array_size(sp); i++) a.sp.push_back(lean_string_cstr(lean_array_get_core(sp, i)));
    for (size_t i = 0; i < lean_array_size(roots); i++) {
        std::vector<std::string> c;
        name_comps_obj(lean_array_get_core(roots, i), c);
        a.roots.push_back(c);
    }
    if (whole_env == 0) {
        size_t nt = lean_array_size(targets);
        a.targets.resize(nt);
        for (size_t i = 0; i < nt; i++) name_arg_obj(lean_array_get_core(targets, i), a.targets[i]);
    }
    a.whole_env = whole_env != 0;
    a.nthreads = nthreads ? (size_t)nthreads : default_threads();
    // phase timings go to stderr by default (the benchmark logs show them); LEAN4EXPORT_VERBOSE=0 silences them
    const char* v = getenv("LEAN4EXPORT_VERBOSE");
    g_verbose = !(v && strcmp(v, "0") == 0);
    g_t0 = now_s();  // shared by the parent (watchdog) and the forked child
    const char* pp = getenv("LEAN4EXPORT_POPULATE");
    g_populate = pp && *pp && strcmp(pp, "0") != 0;
    a.list_mode = false;  // F04: LEAN4EXPORT_LIST (testing aid, different output) removed from the production binary
    // The native exporter runs in a forked child (before any of its threads exist).  If it fails in any way (fatal
    // error, crash, OOM kill), stdout is truncated and Main.lean falls back to the reference implementation, so a bug
    // here can cost time but cannot lose the export.  LEAN4EXPORT_NOFORK=1 runs it in-process (debugging).
    auto work = [&] {
        std::vector<std::function<void()>> fns;
        fns.push_back([&] { run(a); });  // big stack: deep expressions recurse
        run_with_stack((size_t)64 << 30, fns);
    };
    const char* nf = getenv("LEAN4EXPORT_NOFORK");
    if (nf && *nf && strcmp(nf, "0") != 0) {
        g_emap_use_bound = true;
        work();
        return lean_io_result_mk_ok(lean_box_uint32(0));
    }
    fflush(stdout);
    fflush(stderr);
    pid_t pid = -1;
    int status = 0;
    bool timed_out = false;
    double timeout = 2700;
    // watchdog: a hang must not stall the pipeline (the reference implementation needs ~1.3 h on the full RH export,
    // the native one minutes); default 45 min, LEAN4EXPORT_NATIVE_TIMEOUT=<seconds> overrides (0 = none)
    if (const char* ts = getenv("LEAN4EXPORT_NATIVE_TIMEOUT")) timeout = atof(ts);
    double t_start = now_s();
    // the retries below (exit 3 / EXIT_TABLE_FULL) are only correct if the child wrote nothing: remember where
    // stdout is (offset and size; both -1 for a pipe) and check it after the child exited
    struct stat st0;
    off_t off0 = lseek(1, 0, SEEK_CUR);
    off_t size0 = fstat(1, &st0) == 0 && S_ISREG(st0.st_mode) ? st0.st_size : (off_t)-1;
    auto stdout_unchanged = [&]() {
        struct stat st1;
        off_t off1 = lseek(1, 0, SEEK_CUR);
        off_t size1 = fstat(1, &st1) == 0 && S_ISREG(st1.st_mode) ? st1.st_size : (off_t)-1;
        return off0 >= 0 && size0 >= 0 && off1 == off0 && size1 == size0;
    };
    // the early child (if any) is used for the first attempt iff it guessed exactly these arguments
    bool early = false;
    if (g_early) {
        early = early_matches(g_early, a, sp_partial != 0, nthreads);
        if (!early) {
            logf("early child guessed different arguments: killed, normal start%s", "");
            kill(g_early->pid, SIGKILL);
            close(g_early->gate);
            g_early = nullptr;  // (reaped by nobody: exits with the process)
        }
    }
    // another attempt only if the child exited with EXIT_TABLE_FULL (before writing anything): an estimate-sized
    // table was too small -> run again with 8x larger estimates (at most the bounds, which cannot overflow)
    for (int attempt = 0; attempt < 6; attempt++) {
        g_size_attempt = attempt;
        g_emap_use_bound = attempt == 5;
        if (early) {
            pid = g_early->pid;
            // (SIGPIPE ignored around the write: the child may have died, and that must not kill us)
            struct sigaction ign, old;
            memset(&ign, 0, sizeof ign);
            ign.sa_handler = SIG_IGN;
            sigemptyset(&ign.sa_mask);
            bool restore = sigaction(SIGPIPE, &ign, &old) == 0;
            ssize_t w;
            do {
                w = write(g_early->gate, "G", 1);
            } while (w < 0 && errno == EINTR);
            if (restore) sigaction(SIGPIPE, &old, nullptr);
            close(g_early->gate);
            g_early = nullptr;
            if (w != 1) {  // cannot release it (it died?): reap it and start normally
                logf("early child could not be released: normal start%s", "");
                kill(pid, SIGKILL);
                while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {
                }
                early = false;
                attempt--;
                continue;
            }
        } else {
            pid = fork();
            if (pid == 0) {
                work();
                _exit(0);
            }
        }
        if (pid < 0) {
            fprintf(stderr, "lean4export: fork failed (%s), declining\n", strerror(errno));
            return lean_io_result_mk_ok(lean_box_uint32(2));
        }
        status = 0;
        // wake up as soon as the child exits: poll a pidfd (Linux >= 5.3), else fall back to 1 ms polling
        int pidfd = -1;
#ifdef SYS_pidfd_open
        pidfd = (int)syscall(SYS_pidfd_open, pid, 0);
#endif
        while (true) {
            pid_t r = waitpid(pid, &status, WNOHANG);
            if (r == pid) break;
            if (r < 0 && errno != EINTR) {
                status = -1;
                break;
            }
            if (timeout > 0 && now_s() - t_start > timeout) {
                kill(pid, SIGKILL);
                while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {
                }
                timed_out = true;
                break;
            }
            if (pidfd >= 0) {
                struct pollfd pf;
                pf.fd = pidfd;
                pf.events = POLLIN;
                pf.revents = 0;
                if (poll(&pf, 1, 1000) < 0 && errno != EINTR) {
                    close(pidfd);
                    pidfd = -1;
                }
            } else {
                usleep(1000);
            }
        }
        if (pidfd >= 0) close(pidfd);
        if (early) {
            early = false;
            // the early child failed before writing anything (not one of the planned exits): start normally
            bool planned = WIFEXITED(status) && (WEXITSTATUS(status) == 0 || WEXITSTATUS(status) == 3 ||
                                                 WEXITSTATUS(status) == EXIT_TABLE_FULL);
            if (!timed_out && status != -1 && !planned && stdout_unchanged()) {
                logf("early child failed (status %s) before writing: normal start", std::to_string(status));
                attempt--;
                continue;
            }
        }
        if (timed_out || status == -1 || !WIFEXITED(status) || WEXITSTATUS(status) != EXIT_TABLE_FULL) break;
        if (!stdout_unchanged()) {  // cannot happen by construction (table_full refuses once output started)
            fprintf(stderr, "lean4export: native exporter wrote output before EXIT_TABLE_FULL\n");
            status = -1;
            break;
        }
    }
    if (!timed_out && status != -1 && WIFEXITED(status) && WEXITSTATUS(status) == 3 && g_sp_partial &&
        (stdout_unchanged() || (off0 < 0 && size0 < 0))) {
        logf("module root not in LEAN_PATH: retrying with the complete search path%s", "");
        return lean_io_result_mk_ok(lean_box_uint32(3));
    }
    logf("native child reaped (status %s)", std::to_string(status));
    if (timed_out) fprintf(stderr, "lean4export: native exporter exceeded %.0f s, killed\n", timeout);
    if (!timed_out && status != -1 && WIFEXITED(status) && WEXITSTATUS(status) == 0)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    if (status != -1 && WIFSIGNALED(status))
        fprintf(stderr, "lean4export: native exporter killed by signal %d\n", WTERMSIG(status));
    else
        fprintf(stderr, "lean4export: native exporter failed (status %d)\n", status);
    if (ftruncate(1, 0) != 0 || lseek(1, 0, SEEK_SET) < 0) {
        fprintf(stderr, "lean4export: cannot rewind stdout (%s), giving up\n", strerror(errno));
        return lean_io_result_mk_ok(lean_box_uint32(1));
    }
    fprintf(stderr, "lean4export: native core failed, declining (no reference fallback in this binary)\n");
    return lean_io_result_mk_ok(lean_box_uint32(2));
}
