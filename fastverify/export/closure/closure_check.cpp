// closure_check EXPORT TARGETS_NL [THREADS]  — independent fail-closed guard behind option E1.
//
// The official lean4export output is CLOSED by construction: names/levels/expressions are numbered 0,1,2,... in file
// order and every reference points to an already defined id; dumpConstant recurses into every constant a declaration
// uses (getUsedConstants = the `const` nodes of its type and value), inductive blocks are dumped whole (types, ctors,
// recursors), and every requested (safe, existing) target is declared. (proj type names and def/thm `all` lists are
// written as names only and are NOT required to be declared.)
// This tool checks exactly these properties on a produced export, independently of the exporter that wrote it:
//   * every line is one JSON object of a known shape (meta, name, level, expr, axiom/def/thm/opaque/quot/inductive)
//   * name ids are 1..N, level ids 1..L, expr ids 0..E-1, each sequential in file order (no gaps, no repeats)
//   * name.pre / level / expr children refer to smaller ids of their own kind; cross-kind references (expr -> name,
//     level; level -> name; declaration -> name, level, expr) refer to ids defined somewhere in the file
//   * every constant referenced by a `const` expression, and every inductive-block member reference (types' all/ctors,
//     ctor induct, recursor all / rule ctor) is declared; every target is declared
// Exit 0 = all properties hold; 3 = a property is violated (the caller declines the export); 2 = usage/IO error.
// It cannot prove byte-identity with the official exporter; it catches truncation and missing content (e.g. the
// >256-thread exporter bug, which wrote a well-formed but incomplete 533 MB export with exit 0).
#include <atomic>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

[[noreturn]] static void fail(const std::string& m) { fprintf(stderr, "closure_check: VIOLATION: %s\n", m.c_str()); fflush(stderr); _exit(3); }
[[noreturn]] static void usage_err(const std::string& m) { fprintf(stderr, "closure_check: %s\n", m.c_str()); fflush(stderr); _exit(2); }

// ---- atomic bitset over ids (lazily committed anonymous mapping)
struct Bits {
    std::atomic<uint64_t>* w = nullptr; uint64_t nbits = 0;
    void init(uint64_t n) {
        nbits = n; size_t bytes = ((n + 63) / 64) * 8 + 8;
        void* m = mmap(nullptr, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
        if (m == MAP_FAILED) usage_err("out of memory (bitset)");
        w = (std::atomic<uint64_t>*)m;
    }
    void set(uint64_t i) { if (i >= nbits) fail("id beyond any possible bound"); w[i >> 6].fetch_or(1ull << (i & 63), std::memory_order_relaxed); }
    bool get(uint64_t i) const { return i < nbits && ((w[i >> 6].load(std::memory_order_relaxed) >> (i & 63)) & 1); }
};

// ---- minimal strict JSON parser (one line = one object)
struct Val {
    enum K { OBJ, ARR, NUM, BIGNUM, STR, TRUE_, FALSE_, NUL } k = NUL;
    uint64_t n = 0;
    std::string s;                                     // STR (decoded), BIGNUM digits
    std::vector<std::pair<std::string, Val>> o;        // OBJ
    std::vector<Val> a;                                // ARR
    const Val* get(const char* key) const {
        for (auto& kv : o) if (kv.first == key) return &kv.second;
        return nullptr;
    }
};
struct Parser {
    const char* p; const char* e; uint64_t line;
    [[noreturn]] void bad(const char* why) { fail("line " + std::to_string(line) + ": malformed JSON (" + why + ")"); }
    void ws() { while (p < e && (*p == ' ' || *p == '\t' || *p == '\r')) p++; }
    static void utf8(std::string& out, uint32_t c) {
        if (c < 0x80) out += (char)c;
        else if (c < 0x800) { out += (char)(0xC0 | (c >> 6)); out += (char)(0x80 | (c & 0x3F)); }
        else if (c < 0x10000) { out += (char)(0xE0 | (c >> 12)); out += (char)(0x80 | ((c >> 6) & 0x3F)); out += (char)(0x80 | (c & 0x3F)); }
        else { out += (char)(0xF0 | (c >> 18)); out += (char)(0x80 | ((c >> 12) & 0x3F)); out += (char)(0x80 | ((c >> 6) & 0x3F)); out += (char)(0x80 | (c & 0x3F)); }
    }
    void str(std::string& out) {
        if (p >= e || *p != '"') bad("string expected");
        p++;
        while (true) {
            if (p >= e) bad("unterminated string");
            char c = *p++;
            if (c == '"') return;
            if ((unsigned char)c < 0x20) bad("control character in string");
            if (c != '\\') { out += c; continue; }
            if (p >= e) bad("bad escape");
            char d = *p++;
            switch (d) {
                case '"': out += '"'; break; case '\\': out += '\\'; break; case '/': out += '/'; break;
                case 'b': out += '\b'; break; case 'f': out += '\f'; break; case 'n': out += '\n'; break;
                case 'r': out += '\r'; break; case 't': out += '\t'; break;
                case 'u': {
                    if (e - p < 4) bad("bad \\u");
                    uint32_t c2 = 0;
                    for (int i = 0; i < 4; i++) {
                        char h = *p++; c2 <<= 4;
                        if (h >= '0' && h <= '9') c2 |= h - '0'; else if (h >= 'a' && h <= 'f') c2 |= h - 'a' + 10;
                        else if (h >= 'A' && h <= 'F') c2 |= h - 'A' + 10; else bad("bad hex");
                    }
                    utf8(out, c2); break;
                }
                default: bad("bad escape");
            }
        }
    }
    void val(Val& v, int depth) {
        if (depth > 64) bad("nesting too deep");
        ws();
        if (p >= e) bad("value expected");
        char c = *p;
        if (c == '{') {
            v.k = Val::OBJ; p++; ws();
            if (p < e && *p == '}') { p++; return; }
            while (true) {
                ws(); v.o.emplace_back(); str(v.o.back().first); ws();
                if (p >= e || *p != ':') bad("':' expected");
                p++; val(v.o.back().second, depth + 1); ws();
                if (p < e && *p == ',') { p++; continue; }
                if (p < e && *p == '}') { p++; return; }
                bad("',' or '}' expected");
            }
        } else if (c == '[') {
            v.k = Val::ARR; p++; ws();
            if (p < e && *p == ']') { p++; return; }
            while (true) {
                v.a.emplace_back(); val(v.a.back(), depth + 1); ws();
                if (p < e && *p == ',') { p++; continue; }
                if (p < e && *p == ']') { p++; return; }
                bad("',' or ']' expected");
            }
        } else if (c == '"') { v.k = Val::STR; str(v.s); }
        else if (c >= '0' && c <= '9') {
            const char* q = p; while (p < e && *p >= '0' && *p <= '9') p++;
            if (p < e && (*p == '.' || *p == 'e' || *p == 'E')) bad("non-integer number");
            size_t len = p - q;
            if (len > 1 && *q == '0') bad("leading zero");
            if (len <= 18) { uint64_t n = 0; for (const char* r = q; r < p; r++) n = n * 10 + (*r - '0'); v.k = Val::NUM; v.n = n; }
            else { v.k = Val::BIGNUM; v.s.assign(q, len); }
        } else if (e - p >= 4 && !memcmp(p, "true", 4)) { v.k = Val::TRUE_; p += 4; }
        else if (e - p >= 5 && !memcmp(p, "false", 5)) { v.k = Val::FALSE_; p += 5; }
        else if (e - p >= 4 && !memcmp(p, "null", 4)) { v.k = Val::NUL; p += 4; }
        else bad("unexpected character");
    }
};

struct TargetComp { std::vector<std::string> comps; };  // string components only (numeric -> not supported -> fail)

struct Chunk {  // per-chunk results (chunks are contiguous byte ranges cut at line starts)
    uint64_t first_name = 0, last_name = 0, n_names = 0;
    uint64_t first_level = 0, last_level = 0, n_levels = 0;
    uint64_t first_expr = 0, last_expr = 0, n_exprs = 0;
    uint64_t max_ref_name = 0, max_ref_level = 0, max_ref_expr = 0;
    bool any_ref_name = false, any_ref_level = false, any_ref_expr = false;
    uint64_t lines = 0, decls = 0, meta = 0;
    std::vector<std::tuple<uint64_t, uint64_t, std::string>> cand;  // (id, pre, comp) of names whose comp is a target comp
};

int main(int argc, char** argv) {
    if (argc < 3) usage_err("usage: closure_check EXPORT TARGETS_NL [THREADS]");
    unsigned nt = argc > 3 ? (unsigned)atoi(argv[3]) : std::thread::hardware_concurrency();
    if (nt == 0) nt = 1;
    if (nt > 4096) nt = 4096;
    // targets: one name per line; components split at '.' outside «»; «» stripped; numeric components unsupported
    std::vector<TargetComp> targets;
    std::unordered_set<std::string> tcomp;
    {
        FILE* f = fopen(argv[2], "r");
        if (!f) usage_err("cannot open targets");
        char* buf = nullptr; size_t cap = 0; ssize_t r;
        while ((r = getline(&buf, &cap, f)) >= 0) {
            std::string t(buf, r);
            while (!t.empty() && (t.back() == '\n' || t.back() == '\r')) t.pop_back();
            if (t.empty()) continue;
            TargetComp tc; std::string cur; bool esc = false;
            for (size_t i = 0; i < t.size();) {
                if (!esc && t.compare(i, 2, "\xC2\xAB") == 0) { esc = true; i += 2; continue; }
                if (esc && t.compare(i, 2, "\xC2\xBB") == 0) { esc = false; i += 2; continue; }
                if (!esc && t[i] == '.') { tc.comps.push_back(cur); cur.clear(); i++; continue; }
                cur += t[i++];
            }
            tc.comps.push_back(cur);
            for (auto& c : tc.comps) {
                if (c.empty()) fail("target '" + t + "': empty component");
                bool digits = true; for (char ch : c) if (ch < '0' || ch > '9') digits = false;
                if (digits) fail("target '" + t + "': numeric component not supported by the guard");
                tcomp.insert(c);
            }
            targets.push_back(tc);
        }
        free(buf); fclose(f);
    }
    int fd = open(argv[1], O_RDONLY);
    if (fd < 0) usage_err("cannot open export");
    struct stat st; if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) usage_err("export is not a regular file");
    size_t len = (size_t)st.st_size;
    if (len == 0) fail("empty export");
    const char* base = (const char*)mmap(nullptr, len, PROT_READ, MAP_PRIVATE, fd, 0);
    if (base == MAP_FAILED) usage_err("mmap failed");
    madvise((void*)base, len, MADV_SEQUENTIAL);
    if (base[len - 1] != '\n') fail("export does not end with a newline");
    uint64_t bound = len / 8 + 16;  // every line is longer than 8 bytes: no id can reach this
    Bits declared, referenced;
    declared.init(bound); referenced.init(bound);
    // chunks
    size_t nch = (size_t)nt * 8; if (nch > len / 4096 + 1) nch = len / 4096 + 1;
    std::vector<size_t> cut(nch + 1);
    cut[0] = 0; cut[nch] = len;
    for (size_t k = 1; k < nch; k++) {
        size_t q = len * k / nch;
        while (q < len && base[q - 1] != '\n') q++;
        cut[k] = q < cut[k - 1] ? cut[k - 1] : q;
    }
    std::vector<Chunk> res(nch);
    std::atomic<size_t> next{0};
    auto work = [&]() {
        while (true) {
            size_t k = next.fetch_add(1);
            if (k >= nch) return;
            Chunk& C = res[k];
            const char* p = base + cut[k]; const char* end = base + cut[k + 1];
            while (p < end) {
                const char* nl = (const char*)memchr(p, '\n', end - p);
                if (!nl) fail("line without newline");
                Parser ps{p, nl, 0};
                p = nl + 1;  // next line (the body below may `continue`)
                // line numbers are only for messages: chunk index + local line
                ps.line = (uint64_t)k * 1000000000000ull + C.lines + 1;
                Val v; ps.val(v, 0); ps.ws();
                if (ps.p != nl) ps.bad("trailing characters");
                if (v.k != Val::OBJ) ps.bad("not an object");
                C.lines++;
                auto num = [&](const Val* x, const char* what) -> uint64_t {
                    if (!x || x->k != Val::NUM) fail("line " + std::to_string(ps.line) + ": integer field '" + what + "' missing");
                    return x->n;
                };
                auto refN = [&](uint64_t i) { if (i > 0) { C.any_ref_name = true; if (i > C.max_ref_name) C.max_ref_name = i; } };
                auto refL = [&](uint64_t i) { if (i > 0) { C.any_ref_level = true; if (i > C.max_ref_level) C.max_ref_level = i; } };
                auto refE = [&](uint64_t i) { C.any_ref_expr = true; if (i > C.max_ref_expr) C.max_ref_expr = i; };
                auto arrN = [&](const Val* x, const char* what, bool constRef) {
                    if (!x || x->k != Val::ARR) fail("line " + std::to_string(ps.line) + ": array '" + what + "' missing");
                    for (auto& y : x->a) {
                        if (y.k != Val::NUM) fail("line " + std::to_string(ps.line) + ": non-integer in '" + what + "'");
                        refN(y.n); if (constRef) referenced.set(y.n);
                    }
                };
                auto arrL = [&](const Val* x, const char* what) {
                    if (!x || x->k != Val::ARR) fail("line " + std::to_string(ps.line) + ": array '" + what + "' missing");
                    for (auto& y : x->a) { if (y.k != Val::NUM) fail("bad level list"); refL(y.n); }
                };
                const Val* vin = v.get("in"); const Val* vil = v.get("il"); const Val* vie = v.get("ie");
                if (v.get("meta")) { C.meta++; continue; }
                if (vin) {  // name
                    uint64_t id = num(vin, "in");
                    if (v.o.size() != 2) fail("name line with extra fields");
                    if (C.n_names == 0) C.first_name = id; else if (id != C.last_name + 1) fail("name ids not sequential at " + std::to_string(id));
                    C.last_name = id; C.n_names++;
                    if (id == 0) fail("name id 0 (anonymous) redefined");
                    if (const Val* s = v.get("str")) {
                        uint64_t pre = num(s->get("pre"), "pre");
                        const Val* cs = s->get("str");
                        if (!cs || cs->k != Val::STR) fail("name str component missing");
                        if (pre >= id) fail("name pre not smaller than id");
                        if (tcomp.count(cs->s)) C.cand.emplace_back(id, pre, cs->s);
                    } else if (const Val* n = v.get("num")) {
                        uint64_t pre = num(n->get("pre"), "pre");
                        const Val* ci = n->get("i");
                        if (!ci || (ci->k != Val::NUM && ci->k != Val::BIGNUM)) fail("name num component missing");
                        if (pre >= id) fail("name pre not smaller than id");
                    } else fail("name line of unknown shape");
                    continue;
                }
                if (vil) {  // level
                    uint64_t id = num(vil, "il");
                    if (v.o.size() != 2) fail("level line with extra fields");
                    if (C.n_levels == 0) C.first_level = id; else if (id != C.last_level + 1) fail("level ids not sequential");
                    C.last_level = id; C.n_levels++;
                    if (id == 0) fail("level id 0 (zero) redefined");
                    if (const Val* s = v.get("succ")) { uint64_t a = num(s, "succ"); if (a >= id) fail("level ref not smaller"); }
                    else if (const Val* m = v.get("max") ? v.get("max") : v.get("imax")) {
                        if (m->k != Val::ARR || m->a.size() != 2 || m->a[0].k != Val::NUM || m->a[1].k != Val::NUM) fail("bad max/imax");
                        if (m->a[0].n >= id || m->a[1].n >= id) fail("level ref not smaller");
                    } else if (const Val* q = v.get("param")) refN(num(q, "param"));
                    else fail("level line of unknown shape");
                    continue;
                }
                if (vie) {  // expression
                    uint64_t id = num(vie, "ie");
                    if (v.o.size() != 2) fail("expr line with extra fields");
                    if (C.n_exprs == 0) C.first_expr = id; else if (id != C.last_expr + 1) fail("expr ids not sequential at " + std::to_string(id));
                    C.last_expr = id; C.n_exprs++;
                    auto sub = [&](uint64_t c) { if (c >= id) fail("expr child not smaller than its id"); };
                    const std::string& key = v.o[0].first == "ie" ? v.o[1].first : v.o[0].first;
                    const Val& b = v.o[0].first == "ie" ? v.o[1].second : v.o[0].second;
                    if (key == "bvar") { if (b.k != Val::NUM) fail("bad bvar"); }
                    else if (key == "sort") refL(num(&b, "sort"));
                    else if (key == "const") { uint64_t n = num(b.get("name"), "name"); refN(n); referenced.set(n); arrL(b.get("us"), "us"); }
                    else if (key == "app") { sub(num(b.get("fn"), "fn")); sub(num(b.get("arg"), "arg")); }
                    else if (key == "lam" || key == "forallE") {
                        refN(num(b.get("name"), "name")); sub(num(b.get("type"), "type")); sub(num(b.get("body"), "body"));
                        const Val* bi = b.get("binderInfo"); if (!bi || bi->k != Val::STR) fail("binderInfo missing");
                    } else if (key == "letE") {
                        refN(num(b.get("name"), "name")); sub(num(b.get("type"), "type")); sub(num(b.get("value"), "value"));
                        sub(num(b.get("body"), "body"));
                    } else if (key == "proj") {
                        uint64_t n = num(b.get("typeName"), "typeName"); refN(n); sub(num(b.get("struct"), "struct"));  // not required to be declared: getUsedConstants ignores proj type names
                        const Val* ix = b.get("idx"); if (!ix || (ix->k != Val::NUM && ix->k != Val::BIGNUM)) fail("proj idx missing");
                    } else if (key == "natVal" || key == "strVal") { if (b.k != Val::STR) fail("literal is not a string"); }
                    else if (key == "mdata") { sub(num(b.get("expr"), "expr")); }
                    else fail("expr line of unknown kind '" + key + "'");
                    // keep the max expr reference too (all children are < id, so they are defined)
                    continue;
                }
                // declarations
                if (v.o.size() != 1) fail("declaration line with several keys");
                const std::string& dk = v.o[0].first; const Val& d = v.o[0].second;
                C.decls++;
                auto cval = [&](const Val& x) {
                    uint64_t n = num(x.get("name"), "name"); refN(n); declared.set(n);
                    arrN(x.get("levelParams"), "levelParams", false);
                    refE(num(x.get("type"), "type"));
                };
                if (dk == "axiom" || dk == "quot") cval(d);
                else if (dk == "def" || dk == "thm" || dk == "opaque") {
                    cval(d); refE(num(d.get("value"), "value")); arrN(d.get("all"), "all", false);  // `all` members are dumped as names only
                } else if (dk == "inductive") {
                    const Val* ts = d.get("types"); const Val* cs = d.get("ctors"); const Val* rs = d.get("recs");
                    if (!ts || ts->k != Val::ARR || !cs || cs->k != Val::ARR || !rs || rs->k != Val::ARR) fail("bad inductive block");
                    for (auto& t : ts->a) { cval(t); arrN(t.get("all"), "all", true); arrN(t.get("ctors"), "ctors", true); }
                    for (auto& c : cs->a) { cval(c); uint64_t ind = num(c.get("induct"), "induct"); refN(ind); referenced.set(ind); }
                    for (auto& r : rs->a) {
                        cval(r); arrN(r.get("all"), "all", true);
                        const Val* rules = r.get("rules"); if (!rules || rules->k != Val::ARR) fail("rules missing");
                        for (auto& ru : rules->a) {
                            uint64_t c = num(ru.get("ctor"), "ctor"); refN(c); referenced.set(c);
                            refE(num(ru.get("rhs"), "rhs"));
                        }
                    }
                } else fail("unknown line kind '" + dk + "'");
            }
        }
    };
    std::vector<std::thread> th;
    for (unsigned i = 0; i < nt; i++) th.emplace_back(work);
    for (auto& t : th) t.join();
    // stitch: sequential numbering across chunks
    uint64_t nn = 0, nl = 0, ne = 0, metas = 0, decls = 0, lines = 0;
    uint64_t mrn = 0, mrl = 0, mre = 0; bool arn = false, arl = false, are = false;
    for (auto& C : res) {
        if (C.n_names) { if (C.first_name != nn + 1) fail("name ids not sequential across chunks"); nn = C.last_name; }
        if (C.n_levels) { if (C.first_level != nl + 1) fail("level ids not sequential across chunks"); nl = C.last_level; }
        if (C.n_exprs) { if (C.first_expr != ne) fail("expr ids not sequential across chunks"); ne = C.last_expr + 1; }
        metas += C.meta; decls += C.decls; lines += C.lines;
        if (C.any_ref_name) { arn = true; if (C.max_ref_name > mrn) mrn = C.max_ref_name; }
        if (C.any_ref_level) { arl = true; if (C.max_ref_level > mrl) mrl = C.max_ref_level; }
        if (C.any_ref_expr) { are = true; if (C.max_ref_expr > mre) mre = C.max_ref_expr; }
    }
    if (metas != 1 || res[0].meta != 1) fail("exactly one meta line (the first) expected");
    if (arn && mrn > nn) fail("reference to undefined name id " + std::to_string(mrn));
    if (arl && mrl > nl) fail("reference to undefined level id " + std::to_string(mrl));
    if (are && mre >= ne) fail("reference to undefined expr id " + std::to_string(mre));
    // closure over constants
    for (uint64_t i = 0; i <= nn; i++)
        if (referenced.get(i) && !declared.get(i)) fail("constant (name id " + std::to_string(i) + ") referenced but not declared");
    // targets
    std::unordered_map<uint64_t, std::vector<std::pair<std::string, uint64_t>>> bypre;  // pre -> (comp, id)
    for (auto& C : res) for (auto& t : C.cand) bypre[std::get<1>(t)].emplace_back(std::get<2>(t), std::get<0>(t));
    for (auto& t : targets) {
        uint64_t cur = 0; bool ok = true;
        for (auto& c : t.comps) {
            bool found = false;
            auto it = bypre.find(cur);
            if (it != bypre.end()) for (auto& pr : it->second) if (pr.first == c) { cur = pr.second; found = true; break; }
            if (!found) { ok = false; break; }
        }
        std::string nm; for (size_t i = 0; i < t.comps.size(); i++) nm += (i ? "." : "") + t.comps[i];
        if (!ok) fail("target " + nm + " has no name record");
        if (!declared.get(cur)) fail("target " + nm + " is not declared");
    }
    printf("closure_check: OK lines=%llu names=%llu levels=%llu exprs=%llu declarations=%llu targets=%zu\n",
           (unsigned long long)lines, (unsigned long long)nn, (unsigned long long)nl, (unsigned long long)ne,
           (unsigned long long)decls, targets.size());
    return 0;
}
