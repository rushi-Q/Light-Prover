// warm-delta-extract.cpp — Fast C++ streaming delta & manifest extractor for lean4export 3.1.0 NDJSON.
// Completely UNTRUSTED helper for testing/benchmarking (e.g. extracting RH 61.6 GB M1-M4 minimal deltas or base_consts.txt).
//
// Usage:
//   warm-delta-extract manifest EXPORT.ndjson OUT_NAMES.txt
//   warm-delta-extract decls    EXPORT.ndjson MAX_OFFSET DECLS.jsonl OUT_DELTA.ndjson
//
// In `decls` mode:
//   - Reads one or more raw declaration JSON lines from DECLS.jsonl (using EXPORT's original in/il/ie IDs).
//   - Streams EXPORT.ndjson BACKWARDS from MAX_OFFSET to 0 in 64 MiB chunks (~3-4 GB/s!), collecting ONLY
//     the transitively referenced `ie`, `il`, `in` records in O(|delta|) RAM.
//   - Emits a dense, self-contained, standard lean4export 3.1.0 NDJSON file to OUT_DELTA.ndjson!
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <sys/stat.h>
#include <unistd.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>

static inline bool parse_u64_after(const char* s, size_t len, const char* key, uint64_t& out) {
    size_t klen = strlen(key);
    const char* p = (const char*)memmem(s, len, key, klen);
    if (!p) return false;
    p += klen;
    const char* end = s + len;
    if (p >= end || *p < '0' || *p > '9') return false;
    uint64_t v = 0;
    while (p < end && *p >= '0' && *p <= '9') {
        v = v * 10 + (uint64_t)(*p - '0');
        p++;
    }
    out = v;
    return true;
}

// Extract all integers in a JSON array after key `key`, e.g. `"us":[1,2,3]`
static inline void parse_u64_array_after(const char* s, size_t len, const char* key, std::unordered_set<uint64_t>& dst) {
    size_t klen = strlen(key);
    const char* p = (const char*)memmem(s, len, key, klen);
    if (!p) return;
    p += klen;
    const char* end = s + len;
    while (p < end && *p != ']') {
        if (*p >= '0' && *p <= '9') {
            uint64_t v = 0;
            while (p < end && *p >= '0' && *p <= '9') {
                v = v * 10 + (uint64_t)(*p - '0');
                p++;
            }
            if (v > 0) dst.insert(v);
        } else {
            p++;
        }
    }
}

// Parse ALL occurrences of `"field":NUM` in a line (handles inductive arrays cleanly!)
static inline void parse_all_u64_after(const char* s, size_t len, const char* key, std::unordered_set<uint64_t>& dst, bool keep_zero) {
    size_t klen = strlen(key);
    const char* cur = s;
    const char* end = s + len;
    while (cur < end) {
        const char* p = (const char*)memmem(cur, (size_t)(end - cur), key, klen);
        if (!p) break;
        p += klen;
        if (p < end && *p >= '0' && *p <= '9') {
            uint64_t v = 0;
            while (p < end && *p >= '0' && *p <= '9') {
                v = v * 10 + (uint64_t)(*p - '0');
                p++;
            }
            if (keep_zero || v > 0) dst.insert(v);
        }
        cur = p;
    }
}

static inline void parse_all_u64_arrays_after(const char* s, size_t len, const char* key, std::unordered_set<uint64_t>& dst) {
    size_t klen = strlen(key);
    const char* cur = s;
    const char* end = s + len;
    while (cur < end) {
        const char* p = (const char*)memmem(cur, (size_t)(end - cur), key, klen);
        if (!p) break;
        p += klen;
        while (p < end && *p != ']') {
            if (*p >= '0' && *p <= '9') {
                uint64_t v = 0;
                while (p < end && *p >= '0' && *p <= '9') {
                    v = v * 10 + (uint64_t)(*p - '0');
                    p++;
                }
                if (v > 0) dst.insert(v);
            } else {
                p++;
            }
        }
        cur = p;
    }
}

static void collect_decl_refs(const std::string& ln,
                              std::unordered_set<uint64_t>& need_n,
                              std::unordered_set<uint64_t>& need_l,
                              std::unordered_set<uint64_t>& need_e) {
    const char* s = ln.data();
    size_t n = ln.size();
    // Names
    parse_all_u64_after(s, n, "\"name\":", need_n, false);
    parse_all_u64_after(s, n, "\"induct\":", need_n, false);
    parse_all_u64_after(s, n, "\"ctor\":", need_n, false);
    parse_all_u64_arrays_after(s, n, "\"levelParams\":[", need_n);
    parse_all_u64_arrays_after(s, n, "\"all\":[", need_n);
    parse_all_u64_arrays_after(s, n, "\"ctors\":[", need_n);
    // Exprs (keep_zero = true because ie=0 is valid!)
    parse_all_u64_after(s, n, "\"type\":", need_e, true);
    parse_all_u64_after(s, n, "\"value\":", need_e, true);
    parse_all_u64_after(s, n, "\"rhs\":", need_e, true);
    (void)need_l;
}

static void collect_expr_refs(const char* s, size_t n,
                              std::unordered_set<uint64_t>& need_n,
                              std::unordered_set<uint64_t>& need_l,
                              std::unordered_set<uint64_t>& need_e) {
    uint64_t v;
    if (memmem(s, n, "\"sort\":", 7)) {
        if (parse_u64_after(s, n, "\"sort\":", v) && v > 0) need_l.insert(v);
    } else if (memmem(s, n, "\"const\":", 8)) {
        if (parse_u64_after(s, n, "\"name\":", v) && v > 0) need_n.insert(v);
        parse_u64_array_after(s, n, "\"us\":[", need_l);
    } else if (memmem(s, n, "\"app\":", 6)) {
        if (parse_u64_after(s, n, "\"fn\":", v)) need_e.insert(v);
        if (parse_u64_after(s, n, "\"arg\":", v)) need_e.insert(v);
    } else if (memmem(s, n, "\"lam\":", 6) || memmem(s, n, "\"forallE\":", 10)) {
        if (parse_u64_after(s, n, "\"name\":", v) && v > 0) need_n.insert(v);
        if (parse_u64_after(s, n, "\"type\":", v)) need_e.insert(v);
        if (parse_u64_after(s, n, "\"body\":", v)) need_e.insert(v);
    } else if (memmem(s, n, "\"letE\":", 7)) {
        if (parse_u64_after(s, n, "\"name\":", v) && v > 0) need_n.insert(v);
        if (parse_u64_after(s, n, "\"type\":", v)) need_e.insert(v);
        if (parse_u64_after(s, n, "\"value\":", v)) need_e.insert(v);
        if (parse_u64_after(s, n, "\"body\":", v)) need_e.insert(v);
    } else if (memmem(s, n, "\"proj\":", 7)) {
        if (parse_u64_after(s, n, "\"typeName\":", v) && v > 0) need_n.insert(v);
        if (parse_u64_after(s, n, "\"struct\":", v)) need_e.insert(v);
    } else if (memmem(s, n, "\"mdata\":", 8)) {
        if (parse_u64_after(s, n, "\"expr\":", v)) need_e.insert(v);
    }
}

static void collect_level_refs(const char* s, size_t n,
                               std::unordered_set<uint64_t>& need_n,
                               std::unordered_set<uint64_t>& need_l) {
    uint64_t v;
    if (parse_u64_after(s, n, "\"succ\":", v)) {
        if (v > 0) need_l.insert(v);
    } else if (memmem(s, n, "\"max\":[", 7)) {
        parse_u64_array_after(s, n, "\"max\":[", need_l);
    } else if (memmem(s, n, "\"imax\":[", 8)) {
        parse_u64_array_after(s, n, "\"imax\":[", need_l);
    } else if (parse_u64_after(s, n, "\"param\":", v)) {
        if (v > 0) need_n.insert(v);
    }
}

// In `manifest` mode: stream EXPORT.ndjson once, build name table, emit all declared constant names (1 per line)
static int run_manifest(const char* exp_path, const char* out_path) {
    FILE* f = fopen(exp_path, "rb");
    if (!f) { perror("fopen export"); return 1; }
    static char rbuf[4 << 20];
    setvbuf(f, rbuf, _IOFBF, sizeof(rbuf));
    std::vector<std::string> names;
    names.push_back(""); // 0 = anonymous
    FILE* out = fopen(out_path, "wb");
    if (!out) { perror("fopen out"); return 1; }

    char* line = nullptr;
    size_t cap = 0;
    ssize_t len;
    size_t n_consts = 0;
    while ((len = getline(&line, &cap, f)) > 0) {
        if (len > 0 && line[len - 1] == '\n') len--;
        if (len > 0 && line[len - 1] == '\r') len--;
        if (len == 0) continue;
        if (memmem(line, (size_t)len, "\"in\":", 5)) {
            uint64_t idx = 0, pre = 0;
            if (!parse_u64_after(line, (size_t)len, "\"in\":", idx)) continue;
            if (idx >= names.size()) names.resize(idx + 1);
            if (parse_u64_after(line, (size_t)len, "\"pre\":", pre)) {
                const std::string& p = (pre < names.size()) ? names[pre] : std::string();
                const char* sp = (const char*)memmem(line, (size_t)len, "\"str\":\"", 7);
                if (sp) {
                    sp += 7;
                    std::string comp;
                    const char* end = line + len;
                    while (sp < end && *sp != '"') {
                        if (*sp == '\\' && sp + 1 < end) {
                            sp++;
                            if (*sp == '"' || *sp == '\\' || *sp == '/') comp.push_back(*sp);
                            else if (*sp == 'n') comp.push_back('\n');
                            else if (*sp == 't') comp.push_back('\t');
                            else comp.push_back(*sp);
                        } else {
                            comp.push_back(*sp);
                        }
                        sp++;
                    }
                    names[idx] = p.empty() ? comp : (p + "." + comp);
                } else {
                    uint64_t num = 0;
                    if (parse_u64_after(line, (size_t)len, "\"i\":", num)) {
                        std::string comp = std::to_string(num);
                        names[idx] = p.empty() ? comp : (p + "." + comp);
                    }
                }
            }
        } else if (strncmp(line, "{\"axiom\":", 9) == 0 || strncmp(line, "{\"def\":", 7) == 0 ||
                   strncmp(line, "{\"thm\":", 7) == 0 || strncmp(line, "{\"opaque\":", 10) == 0 ||
                   strncmp(line, "{\"quot\":", 8) == 0) {
            uint64_t nid = 0;
            if (parse_u64_after(line, (size_t)len, "\"name\":", nid) && nid < names.size() && !names[nid].empty()) {
                fwrite(names[nid].data(), 1, names[nid].size(), out);
                fputc('\n', out);
                n_consts++;
            }
        } else if (strncmp(line, "{\"inductive\":", 13) == 0) {
            std::unordered_set<uint64_t> nids;
            parse_all_u64_after(line, (size_t)len, "\"name\":", nids, false);
            for (uint64_t nid : nids) {
                if (nid < names.size() && !names[nid].empty()) {
                    fwrite(names[nid].data(), 1, names[nid].size(), out);
                    fputc('\n', out);
                    n_consts++;
                }
            }
        }
    }
    free(line);
    fclose(f);
    fclose(out);
    fprintf(stderr, "manifest: %zu names, %zu constants written to %s\n", names.size() - 1, n_consts, out_path);
    return 0;
}

// In `decls` mode: extract raw kept in/il/ie lines + decls into OUT_RAW.jsonl (small file, then Python densely re-indexes!)
static int run_decls(const char* exp_path, uint64_t max_off, const char* decls_path, const char* out_raw_path) {
    std::vector<std::string> decl_lines;
    {
        std::ifstream df(decls_path);
        if (!df) { perror("open decls"); return 1; }
        std::string ln;
        while (std::getline(df, ln)) {
            if (!ln.empty() && ln.back() == '\r') ln.pop_back();
            if (!ln.empty()) decl_lines.push_back(ln);
        }
    }
    std::unordered_set<uint64_t> need_n, need_l, need_e;
    for (const auto& ln : decl_lines) {
        // Also support inline `in`/`ie` lines in decls_path (like M3's new fakeAx lines!)
        if (memmem(ln.data(), ln.size(), "\"ie\":", 5)) {
            collect_expr_refs(ln.data(), ln.size(), need_n, need_l, need_e);
        } else if (memmem(ln.data(), ln.size(), "\"in\":", 5)) {
            uint64_t pre = 0;
            if (parse_u64_after(ln.data(), ln.size(), "\"pre\":", pre) && pre > 0) need_n.insert(pre);
        } else {
            collect_decl_refs(ln, need_n, need_l, need_e);
        }
    }
    // Remove IDs already defined inside decls_path (e.g., M3's injected fakeAx name/exprs)
    for (const auto& ln : decl_lines) {
        uint64_t id = 0;
        if (parse_u64_after(ln.data(), ln.size(), "\"in\":", id)) need_n.erase(id);
        if (parse_u64_after(ln.data(), ln.size(), "\"ie\":", id)) need_e.erase(id);
    }
    need_n.erase(0);
    need_l.erase(0);

    int fd = open(exp_path, O_RDONLY);
    if (fd < 0) { perror("open export"); return 1; }
    struct stat st;
    if (fstat(fd, &st) != 0) { perror("fstat"); return 1; }
    uint64_t fsize = (uint64_t)st.st_size;
    if (max_off == 0 || max_off > fsize) max_off = fsize;

    // Read meta line
    char mhead[4096];
    ssize_t mr = pread(fd, mhead, sizeof(mhead), 0);
    std::string meta_line;
    if (mr > 0) {
        const char* nl = (const char*)memchr(mhead, '\n', (size_t)mr);
        meta_line.assign(mhead, nl ? (size_t)(nl - mhead) : (size_t)mr);
    }

    std::vector<std::pair<uint64_t, std::string>> kept_n, kept_l, kept_e;
    const size_t CHUNK = 64 << 20;
    std::vector<char> buf(CHUNK);
    std::string carry;
    uint64_t pos = max_off;

    while (pos > 0 && (!need_e.empty() || !need_l.empty() || !need_n.empty())) {
        uint64_t rd_start = (pos > CHUNK) ? (pos - CHUNK) : 0;
        size_t to_read = (size_t)(pos - rd_start);
        size_t got = 0;
        while (got < to_read) {
            ssize_t r = pread(fd, buf.data() + got, to_read - got, (off_t)(rd_start + got));
            if (r <= 0) break;
            got += (size_t)r;
        }
        pos = rd_start;

        // Combine buf[0..got) + carry, iterate lines in reverse without copying every line!
        // First handle the boundary line (last line of buf + carry)
        const char* data = buf.data();
        const char* cur = data + got;
        bool first_piece = true;
        while (cur > data) {
            const char* nl = (const char*)memrchr(data, '\n', (size_t)(cur - data));
            const char* lstart = nl ? (nl + 1) : data;
            size_t llen = (size_t)(cur - lstart);
            if (!nl && pos > 0) {
                // Partial line at start of chunk -> save as carry for next (earlier) chunk
                if (first_piece && !carry.empty()) {
                    std::string tmp(lstart, llen);
                    tmp += carry;
                    carry = std::move(tmp);
                } else {
                    carry.assign(lstart, llen);
                }
                break;
            }
            const char* ls = lstart;
            size_t ll = llen;
            std::string joined;
            if (first_piece && !carry.empty()) {
                joined.assign(lstart, llen);
                joined += carry;
                carry.clear();
                ls = joined.data();
                ll = joined.size();
            }
            first_piece = false;
            if (ll > 0 && ls[ll - 1] == '\r') ll--;
            if (ll > 0) {
                if (!need_e.empty() && memmem(ls, ll, "\"ie\":", 5)) {
                    uint64_t eid = 0;
                    if (parse_u64_after(ls, ll, "\"ie\":", eid)) {
                        auto it = need_e.find(eid);
                        if (it != need_e.end()) {
                            need_e.erase(it);
                            kept_e.emplace_back(eid, std::string(ls, ll));
                            collect_expr_refs(ls, ll, need_n, need_l, need_e);
                        }
                    }
                } else if (!need_l.empty() && memmem(ls, ll, "\"il\":", 5)) {
                    uint64_t lid = 0;
                    if (parse_u64_after(ls, ll, "\"il\":", lid)) {
                        auto it = need_l.find(lid);
                        if (it != need_l.end()) {
                            need_l.erase(it);
                            kept_l.emplace_back(lid, std::string(ls, ll));
                            collect_level_refs(ls, ll, need_n, need_l);
                        }
                    }
                } else if (!need_n.empty() && memmem(ls, ll, "\"in\":", 5)) {
                    uint64_t nid = 0;
                    if (parse_u64_after(ls, ll, "\"in\":", nid)) {
                        auto it = need_n.find(nid);
                        if (it != need_n.end()) {
                            need_n.erase(it);
                            kept_n.emplace_back(nid, std::string(ls, ll));
                            uint64_t pre = 0;
                            if (parse_u64_after(ls, ll, "\"pre\":", pre) && pre > 0) need_n.insert(pre);
                        }
                    }
                }
            }
            cur = nl ? nl : data;
        }
    }
    close(fd);

    std::sort(kept_n.begin(), kept_n.end(), [](const auto& a, const auto& b) { return a.first < b.first; });
    std::sort(kept_l.begin(), kept_l.end(), [](const auto& a, const auto& b) { return a.first < b.first; });
    std::sort(kept_e.begin(), kept_e.end(), [](const auto& a, const auto& b) { return a.first < b.first; });

    FILE* out = fopen(out_raw_path, "wb");
    if (!out) { perror("fopen out"); return 1; }
    fprintf(out, "%s\n", meta_line.c_str());
    for (const auto& kv : kept_n) fprintf(out, "%s\n", kv.second.c_str());
    for (const auto& kv : kept_l) fprintf(out, "%s\n", kv.second.c_str());
    for (const auto& kv : kept_e) fprintf(out, "%s\n", kv.second.c_str());
    for (const auto& ln : decl_lines) fprintf(out, "%s\n", ln.c_str());
    fclose(out);
    fprintf(stderr, "decls: extracted %zu names, %zu levels, %zu exprs, %zu decls (unresolved: n=%zu l=%zu e=%zu)\n",
            kept_n.size(), kept_l.size(), kept_e.size(), decl_lines.size(), need_n.size(), need_l.size(), need_e.size());
    return (need_n.empty() && need_l.empty() && need_e.empty()) ? 0 : 2;
}

int main(int argc, char** argv) {
    if (argc == 4 && strcmp(argv[1], "manifest") == 0) {
        return run_manifest(argv[2], argv[3]);
    }
    if (argc == 6 && strcmp(argv[1], "decls") == 0) {
        uint64_t max_off = strtoull(argv[3], nullptr, 10);
        return run_decls(argv[2], max_off, argv[4], argv[5]);
    }
    fprintf(stderr, "usage:\n  %s manifest EXPORT OUT_NAMES\n  %s decls EXPORT MAX_OFF DECLS_JSONL OUT_RAW_JSONL\n", argv[0], argv[0]);
    return 2;
}
