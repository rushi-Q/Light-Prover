// Ordered output sink for native/fast_export.cpp (include after nostdcxx.h).
//
// Chunks numbered 0, 1, 2, ... are handed over with put(seq, buf, len) by any thread in any order; they are written to
// fd 1, starting at its current file offset, in sequence order, so the bytes on fd 1 are exactly chunk 0 ++ chunk 1 ++ ...
// regardless of the order of the put() calls.  put() takes ownership of a malloc'ed buffer; once written it is kept for
// reuse by get_buffer() (bounded free list of 2 MB-aligned THP mappings, avoids page-faulting fresh buffers).
//
// Two back ends, chosen in start():
//  * MAP: fd 1 is a regular file (not O_APPEND, not shared with fd 2) that can be reopened read-write through
//    /proc/self/fd/1: the file is mapped MAP_SHARED and several copier threads memcpy chunks to their offsets in parallel
//    (offsets are assigned as soon as the lengths of all preceding chunks are known).  Buffered writes to a single file
//    are serialized by the inode lock (parallel pwrite does not scale), page faults into a shared mapping do:
//    6 GB on XFS (local NVMe):       write() 1.7-1.8 s, pwrite x8 1.75 s, mmap+memcpy x8-16 1.05 s.
//  * WRITE: anything else (pipe, tty, /dev/null, O_APPEND, ...): one writer thread write()s the chunks in order.
// finish() waits until everything is written, trims the file to its exact length and leaves fd 1's offset at the end.
// Any I/O error is fatal (die): the caller's fork/fallback machinery then reruns the reference exporter.
#pragma once

#include <fcntl.h>
#include <sched.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <atomic>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <vector>

namespace lean4export_native {

struct OSink {
    struct Chunk {
        char* buf = nullptr;
        size_t len = 0;
        size_t cap = 0;
        uint64_t off = 0;
        bool present = false;
    };
    std::vector<std::pair<char*, size_t>> freel;  // written buffers for reuse (guarded by mu)
    size_t max_free = 64;
    // configuration
    bool use_map = false;
    // DIO back end (opt-in, LEAN4EXPORT_ODIRECT=1): the ordered stream is assembled into 64 MB 4K-aligned staging
    // blocks that copier threads write with O_DIRECT pwrite (no page cache: nothing to populate, no dirty mapping to
    // tear down).  [start, dio_a) (up to the first 4K boundary) and the bytes after the last 4K boundary of the
    // output are written with buffered pwrite on fd 1.  If an O_DIRECT write is refused (EINVAL), buffered pwrite.
    bool use_dio = false;
    int dfd = -1;
    std::atomic<bool> dio_ok{true};
    static const uint64_t DB = (uint64_t)64 << 20;
    uint64_t dio_a = 0;
    alignas(4096) char dio_head[4096];
    std::atomic<uint64_t> head_filled{0};
    struct DBlock {
        std::atomic<char*> buf{nullptr};
        std::atomic<uint64_t> filled{0};
    };
    DBlock* dblocks = nullptr;
    static const size_t NDBLOCKS = (size_t)1 << 16;  // 4 TiB of output
    size_t ncopiers = 8;
    // state (guarded by mu)
    std::mutex mu;
    NCondVar cv_ready;  // copiers/writer wait for ready chunks
    NCondVar cv_done;   // finish() waits for completion
    std::vector<Chunk> chunks;  // indexed by seq
    uint64_t frontier = 0;      // chunks [0, frontier) have offsets
    uint64_t next_off = 0;      // offset (relative to `start`) of chunk `frontier`
    std::vector<uint64_t> ready;  // seqs with offsets, not yet taken by a copier (FIFO via ready_head)
    size_t ready_head = 0;
    uint64_t taken = 0, written = 0;  // number of chunks taken by / completed by copiers
    bool finishing = false;
    // file
    int fd = 1;            // MAP: the read-write reopened descriptor
    uint64_t start = 0;    // file offset of chunk 0
    uint64_t orig_size = 0;  // MAP: file length at start (never truncated below it, like write())
    char* map = nullptr;
    uint64_t map_len = 0;
    bool use_fallocate = true;   // ensure_size: grow by fallocate (see there); LEAN4EXPORT_FALLOCATE=0 disables
    bool falloc_started = false;
    std::mutex size_mu;
    std::atomic<uint64_t> fsize{0};  // current file length (MAP)
    std::vector<NThread*> threads;
    // pre-population (MAP): background threads fault in the page cache of the estimated output range ahead of the
    // copiers (page-cache insertion, ~5 GB/s for one file, is what bounds the copy otherwise)
    std::vector<NThread*> pop_threads;
    std::atomic<bool> pop_stop{false};
    std::atomic<uint64_t> pop_next{0};
    uint64_t pop_end = 0;
    std::string err;
    double write_s = 0;  // statistics (WRITE: time inside write())

    static const uint64_t GROW = 1ull << 30;
    static const uint64_t RESERVE = 1ull << 42;  // 4 TiB of address space for the shared mapping

    [[noreturn]] static void fatal(const std::string& m) {
        fprintf(stderr, "lean4export (native): output: %s\n", m.c_str());
        fflush(stderr);
        _exit(1);
    }

    // mode: 0 = automatic, 1 = force WRITE
    void start_sink(size_t copiers, int mode = 0) {
        if (const char* fa = getenv("LEAN4EXPORT_FALLOCATE")) use_fallocate = !(fa[0] == '0' && fa[1] == 0);
        ncopiers = copiers < 1 ? 1 : copiers;
        off_t cur = lseek(1, 0, SEEK_CUR);
        struct stat s1, s2;
        bool reg = fstat(1, &s1) == 0 && S_ISREG(s1.st_mode) && cur >= 0;
        if (reg && mode == 0) {
            int fl = fcntl(1, F_GETFL);
            bool shared_with_stderr = fstat(2, &s2) == 0 && s2.st_dev == s1.st_dev && s2.st_ino == s1.st_ino;
            const char* od = getenv("LEAN4EXPORT_ODIRECT");
            if (od && od[0] == '1' && fl >= 0 && !(fl & O_APPEND) && !shared_with_stderr) {
                int f3 = open("/proc/self/fd/1", O_WRONLY | O_DIRECT | O_CLOEXEC);
                struct stat s3;
                if (f3 >= 0 && fstat(f3, &s3) == 0 && s3.st_dev == s1.st_dev && s3.st_ino == s1.st_ino) {
                    dfd = f3;
                    start = (uint64_t)cur;
                    orig_size = (uint64_t)s1.st_size;
                    dio_a = (start + 4095) & ~(uint64_t)4095;
                    dblocks = new DBlock[NDBLOCKS];
                    use_dio = true;
                } else if (f3 >= 0) {
                    close(f3);
                }
            }
            if (!use_dio && fl >= 0 && !(fl & O_APPEND) && !shared_with_stderr) {
                int f2 = open("/proc/self/fd/1", O_RDWR | O_CLOEXEC);
                struct stat s3;
                if (f2 >= 0 && fstat(f2, &s3) == 0 && s3.st_dev == s1.st_dev && s3.st_ino == s1.st_ino) {
                    void* m = mmap(nullptr, RESERVE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_NORESERVE, f2, 0);
                    if (m != MAP_FAILED) {
                        fd = f2;
                        map = (char*)m;
                        map_len = RESERVE;
                        start = (uint64_t)cur;
                        fsize.store((uint64_t)s1.st_size);
                        orig_size = (uint64_t)s1.st_size;
                        use_map = true;
                    } else {
                        close(f2);
                    }
                } else if (f2 >= 0) {
                    close(f2);
                }
            }
        }
        size_t n = (use_map || use_dio) ? ncopiers : 1;
        for (size_t i = 0; i < n; i++) {
            NThread* t = new NThread();
            t->start([this] { worker(); }, (size_t)1 << 20);
            threads.push_back(t);
        }
    }

    // Buffers: anonymous mappings, 2 MB aligned and MADV_HUGEPAGE (renderers write them front to back, so the first
    // touch of every 2 MB is a write -> one huge-page fault instead of 512 small ones), recycled through `freel`.
    static const size_t HUGE = (size_t)2 << 20;
    static size_t round_huge(size_t n) { return (n + HUGE - 1) & ~(HUGE - 1); }
    static char* map_huge(size_t bytes) {  // bytes: multiple of HUGE
        size_t len = bytes + HUGE;
        char* m = (char*)mmap(nullptr, len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
        if (m == (char*)MAP_FAILED) fatal("out of memory (output buffer)");
        uintptr_t a = ((uintptr_t)m + HUGE - 1) & ~(uintptr_t)(HUGE - 1);
        size_t head = (size_t)(a - (uintptr_t)m), tail = len - head - bytes;
        if (head) munmap(m, head);
        if (tail) munmap((char*)a + bytes, tail);
        madvise((void*)a, bytes, MADV_HUGEPAGE);
        return (char*)a;
    }
    // a buffer of at least `want` bytes (recycled if possible); its capacity is returned in `cap`
    char* get_buffer(size_t want, size_t& cap) {
        size_t need = round_huge(want < 1 ? 1 : want);
        {
            std::lock_guard<std::mutex> l(mu);
            size_t best = (size_t)-1;
            for (size_t i = 0; i < freel.size(); i++)
                if (freel[i].second >= need && (best == (size_t)-1 || freel[i].second < freel[best].second)) best = i;
            if (best != (size_t)-1) {
                char* b = freel[best].first;
                cap = freel[best].second;
                freel[best] = freel.back();
                freel.pop_back();
                return b;
            }
        }
        cap = need;
        return map_huge(need);
    }
    // enlarge a get_buffer() buffer to at least `need` bytes (contents kept, may move)
    char* grow(char* buf, size_t& cap, size_t need) {
        size_t nc = round_huge(need > cap * 2 ? need : cap * 2);
        void* m = mremap(buf, cap, nc, MREMAP_MAYMOVE);
        if (m == MAP_FAILED) fatal(std::string("mremap: ") + strerror(errno));
        cap = nc;
        return (char*)m;
    }
    // give back an unused get_buffer() buffer
    void release(char* buf, size_t cap) {
        {
            std::lock_guard<std::mutex> l(mu);
            if (freel.size() < max_free) {
                freel.push_back({buf, cap});
                return;
            }
        }
        munmap(buf, cap);
    }

    // hand over chunk `seq`: a get_buffer() buffer with capacity `cap` (recycled after writing), or a malloc'ed buffer
    // with cap = 0 (free()d after writing); `len` bytes are used
    void put(uint64_t seq, char* buf, size_t len, size_t cap = 0) {
        std::unique_lock<std::mutex> l(mu);
        if (seq < frontier || (seq < chunks.size() && chunks[seq].present)) fatal("duplicate chunk " + std::to_string(seq));
        if (seq >= chunks.size()) chunks.resize(seq + 1 + (seq >> 3));
        Chunk& c = chunks[seq];
        c.buf = buf;
        c.len = len;
        c.cap = cap;
        c.present = true;
        bool any = false;
        while (frontier < chunks.size() && chunks[frontier].present) {
            Chunk& f = chunks[frontier];
            f.off = next_off;
            next_off += f.len;
            ready.push_back(frontier);
            frontier++;
            any = true;
        }
        if (any) cv_ready.notify_all();
    }

    void ensure_size(uint64_t end) {  // MAP: file length >= end (absolute file offset)
        if (end <= fsize.load(std::memory_order_acquire)) return;
        std::lock_guard<std::mutex> g(size_mu);
        uint64_t cur = fsize.load(std::memory_order_relaxed);
        if (end <= cur) return;
        uint64_t ns = end + GROW;
        if (ns > map_len) ns = end;
        if (end > map_len) fatal("output larger than the mapping reserve");
        // Grow with fallocate (real, unwritten extents) instead of ftruncate: with ftruncate the pages written through
        // the mapping are delayed-allocation blocks, and since finish() trims the file (a truncate DOWN), XFS then
        // flushes ALL dirty pages of the file synchronously in the last close (xfs_release: XFS_ITRUNCATED and
        // i_delayed_blks > 0), i.e. in the exiting child: ~3 s for 11.7 GB on local XFS.  Without delalloc blocks
        // that flush does not happen.  The first call starts at offset 0 so that the block of the metadata line
        // (written before by Main.lean) is allocated as well.  Falls back to ftruncate if fallocate is unsupported.
        bool grown = false;
        if (use_fallocate) {
            off_t from = falloc_started ? (off_t)cur : 0;
            if (fallocate(fd, 0, from, (off_t)ns - from) == 0) {
                grown = true;
                falloc_started = true;
            } else {
                use_fallocate = false;
            }
        }
        if (!grown && ftruncate(fd, (off_t)ns) != 0) fatal(std::string("ftruncate: ") + strerror(errno));
        fsize.store(ns, std::memory_order_release);
    }

    static void pwrite_all(int f, const char* p, size_t n, uint64_t off) {
        size_t d = 0;
        while (d < n) {
            ssize_t w = pwrite(f, p + d, n - d, (off_t)(off + d));
            if (w < 0) {
                if (errno == EINTR) continue;
                fatal(std::string("pwrite to stdout failed: ") + strerror(errno));
            }
            if (w == 0) fatal("pwrite to stdout wrote nothing");
            d += (size_t)w;
        }
    }
    // n and off multiples of 4096, p 4096-aligned
    void dio_write(const char* p, size_t n, uint64_t off) {
        if (dio_ok.load(std::memory_order_relaxed)) {
            ssize_t w;
            do {
                w = pwrite(dfd, p, n, (off_t)off);
            } while (w < 0 && errno == EINTR);
            if (w == (ssize_t)n) return;
            if (w > 0) {  // short O_DIRECT write: the rest buffered
                pwrite_all(1, p + w, n - (size_t)w, off + (uint64_t)w);
                return;
            }
            if (errno != EINVAL && errno != EOPNOTSUPP && errno != ENOTSUP)
                fatal(std::string("O_DIRECT pwrite failed: ") + strerror(errno));
            dio_ok.store(false);
        }
        pwrite_all(1, p, n, off);
    }
    char* dblock_buf(uint64_t k) {
        if (k >= NDBLOCKS) fatal("output larger than the staging block table");
        char* b = dblocks[k].buf.load(std::memory_order_acquire);
        if (b) return b;
        size_t cap;
        char* nb = get_buffer(DB, cap);
        char* expected = nullptr;
        if (dblocks[k].buf.compare_exchange_strong(expected, nb, std::memory_order_acq_rel)) return nb;
        release(nb, cap);
        return expected;
    }
    // copy [abs, abs+len) of the output (absolute file offsets) into the head / staging blocks; whoever completes a
    // block writes it (the acq_rel fill counters order every copier's bytes before the completing writer's pwrite)
    void dio_place(const char* src, uint64_t abs, size_t len) {
        if (abs < dio_a) {
            uint64_t n = (abs + len < dio_a ? abs + len : dio_a) - abs;
            memcpy(dio_head + (abs - start), src, n);
            if (head_filled.fetch_add(n, std::memory_order_acq_rel) + n == dio_a - start)
                pwrite_all(1, dio_head, dio_a - start, start);
            src += n;
            abs += n;
            len -= n;
        }
        while (len) {
            uint64_t k = (abs - dio_a) / DB, boff = (abs - dio_a) % DB;
            uint64_t n = len < DB - boff ? len : DB - boff;
            char* b = dblock_buf(k);
            memcpy(b + boff, src, n);
            if (dblocks[k].filled.fetch_add(n, std::memory_order_acq_rel) + n == DB) {
                dio_write(b, DB, dio_a + k * DB);
                dblocks[k].buf.store(nullptr, std::memory_order_relaxed);
                release(b, DB);
            }
            src += n;
            abs += n;
            len -= n;
        }
    }

    void worker() {
        while (true) {
            uint64_t seq;
            Chunk c;
            {
                std::unique_lock<std::mutex> l(mu);
                // WRITE: ready is in sequence order and there is a single writer, so FIFO keeps the order
                cv_ready.wait(l, [this] { return ready_head < ready.size() || finishing; });
                if (ready_head >= ready.size()) return;  // finishing and nothing left
                seq = ready[ready_head++];
                c = chunks[seq];
                chunks[seq].buf = nullptr;
                taken++;
            }
            if (c.len) {
                if (use_dio) {
                    dio_place(c.buf, start + c.off, c.len);
                } else if (use_map) {
                    uint64_t o = start + c.off;
                    ensure_size(o + c.len);
                    memcpy(map + o, c.buf, c.len);
                } else {
                    size_t d = 0;
                    while (d < c.len) {
                        ssize_t w = ::write(1, c.buf + d, c.len - d);
                        if (w < 0) {
                            if (errno == EINTR) continue;
                            fatal(std::string("write to stdout failed: ") + strerror(errno));
                        }
                        d += (size_t)w;
                    }
                }
            }
            bool unmap = false;
            {
                std::lock_guard<std::mutex> l(mu);
                written++;
                if (c.buf && c.cap) {
                    if (freel.size() < max_free)
                        freel.push_back({c.buf, c.cap});
                    else
                        unmap = true;
                } else {
                    free(c.buf);
                }
            }
            if (unmap) munmap(c.buf, c.cap);
            cv_done.notify_all();
        }
    }

    // blocks while more than `max_unwritten` chunks with known offsets are not written yet (back-pressure for a
    // sequential producer that puts chunks in order)
    void wait_backlog(uint64_t max_unwritten) {
        std::unique_lock<std::mutex> l(mu);
        cv_done.wait(l, [&] { return frontier - written <= max_unwritten; });
    }

    // MAP back end: start `k` threads (SCHED_IDLE if `idle`) that MADV_POPULATE_WRITE the file range of the next `est`
    // bytes in 64 MB pieces, front to back.  Purely a performance hint: an over-estimate is trimmed by finish(), an
    // under-estimate leaves the tail to ordinary faults, errors are ignored.
    void prepopulate(uint64_t est, size_t k, bool idle) {
#ifndef MADV_POPULATE_WRITE
#define MADV_POPULATE_WRITE 23
#endif
        if (!use_map || est == 0 || k == 0) return;
        uint64_t end = start + est;
        if (end > map_len) return;
        ensure_size(end);
        pop_end = end;
        pop_next.store(start & ~(uint64_t)4095);
        for (size_t i = 0; i < k; i++) {
            NThread* t = new NThread();
            t->start(
                [this, idle] {
                    if (idle) {
                        struct sched_param sp;
                        memset(&sp, 0, sizeof sp);
                        pthread_setschedparam(pthread_self(), SCHED_IDLE, &sp);
                    }
                    const uint64_t PIECE = (uint64_t)64 << 20;
                    while (!pop_stop.load(std::memory_order_relaxed)) {
                        uint64_t o = pop_next.fetch_add(PIECE);
                        if (o >= pop_end) break;
                        uint64_t n = pop_end - o < PIECE ? pop_end - o : PIECE;
                        madvise(map + o, (size_t)n, MADV_POPULATE_WRITE);
                    }
                },
                (size_t)1 << 20);
            pop_threads.push_back(t);
        }
    }

    // all chunks have been put; returns the number of bytes written
    uint64_t finish() {
        uint64_t total;
        {
            std::unique_lock<std::mutex> l(mu);
            if (frontier != chunks.size()) {
                // trailing slack from resize() is fine, a gap is not
                for (uint64_t i = frontier; i < chunks.size(); i++)
                    if (chunks[i].present) fatal("missing chunk " + std::to_string(frontier));
            }
            cv_done.wait(l, [this] { return written == frontier; });
            finishing = true;
            total = next_off;
        }
        cv_ready.notify_all();
        for (NThread* t : threads) {
            t->join();
            delete t;
        }
        threads.clear();
        pop_stop.store(true);
        for (NThread* t : pop_threads) {
            t->join();
            delete t;
        }
        pop_threads.clear();
        if (use_dio) {
            uint64_t end = start + total;
            if (end <= dio_a) {
                if (end < dio_a && end > start) pwrite_all(1, dio_head, end - start, start);  // (== : written by a copier)
            } else {
                uint64_t k = (end - dio_a) / DB, rem = (end - dio_a) % DB;
                if (rem) {  // the last, partial block: O_DIRECT up to its last 4K boundary, the rest buffered
                    char* b = dblocks[k].buf.load(std::memory_order_acquire);
                    if (!b || dblocks[k].filled.load() != rem) fatal("internal: incomplete last staging block");
                    uint64_t dpart = rem & ~(uint64_t)4095;
                    if (dpart) dio_write(b, dpart, dio_a + k * DB);
                    if (rem > dpart) pwrite_all(1, b + dpart, rem - dpart, dio_a + k * DB + dpart);
                }
            }
            if (lseek(1, (off_t)end, SEEK_SET) < 0) fatal(std::string("lseek: ") + strerror(errno));
        }
        if (use_map) {
            uint64_t end = start + total;
            uint64_t len = end > orig_size ? end : orig_size;  // write() would leave bytes beyond `end` in place
            if (ftruncate(fd, (off_t)len) != 0) fatal(std::string("ftruncate: ") + strerror(errno));
            if (lseek(1, (off_t)end, SEEK_SET) < 0) fatal(std::string("lseek: ") + strerror(errno));
        }
        return total;
    }
};

}  // namespace lean4export_native
