// prechk — official-limits pre-check for Lean 4 NDJSON exports (lean4export format 3.1.x)
//
// Purpose: a fast checker that wants to reproduce the OFFICIAL `lake comparator` verdict (Lean 4.36: official export
// parser + `leanchecker --from-export` replay + optionally official nanoda 4c544ed) must DECLINE whenever the export has a
// feature on which the official tools fail for reasons of their own (resource / format limits, replay order, panics).
// prechk reads the export ONCE (mmap, multi-threaded) and reports every such feature. Exit status:
//   0 = clean (no counted hazard)      3 = hazard(s) found -> the fast check must DECLINE (run the official path)
//   4 = malformed / non-canonical export (also DECLINE)     2 = usage / IO error (DECLINE)
// Anything other than 0 means "decline". prechk never says "accept": it only says "no known official-limit hazard".
//
// Hazard classes (see check/checkB/README.md for the exact source references):
//   malformed       line not in the canonical lean4export form, dangling/forward reference, duplicate constant ...
//   parser_abort    official parser internal-panics (Expr.mkData: bvar idx+1 > 1048575; Level.mkData: depth > 16777215)
//   official_quirk  official parser semantics differ from the literal value (hints regular >= 2^32 is truncated)
//   nanoda_parse    official nanoda 4c544ed parser/structural failure (u16/u32 fields, mdata, unsafe/partial,
//                   duplicate nodes, non-contiguous indices, format version, missing isUnsafe)
//   nanoda_proj     Expr.proj on an inductive with indices or != 1 constructor (nanoda infer_proj panics, finding 056)
//   nanoda_depth    expression depth > --nanoda-depth (16 MiB nanoda worker stacks, finding 047) or binder nesting >= 65535
//   kernel_depth    expression depth > --kernel-depth (official Lean kernel / comparator recursion)
//   walk_depth      upper bound of the official replay walk depth >= --walk-limit (finding 051)
//   order_quot      a declaration uses Quot.mk/lift/ind but does not depend on Quot (official replay may add it first)
//   order_strlit    a declaration has a string literal but does not depend on String.ofList and Char.ofNat (finding 012)
//   order_natlit    a declaration has a Nat literal but does not depend on Nat
//   budget          analysis budget exceeded (cannot exclude hazards)
//
// No dependencies beyond the C++17 standard library and POSIX.

#include <algorithm>
#include <atomic>
#include <cerrno>
#include <chrono>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <mutex>
#include <string>
#include <sys/mman.h>
#include <sys/stat.h>
#include <thread>
#include <unistd.h>
#include <vector>

static const uint32_t NONE = 0xFFFFFFFFu;
// vectors whose resize() does not zero-fill (filled in parallel right after allocation)
template <class T> struct DIAlloc : std::allocator<T> {
  template <class U> struct rebind { using other = DIAlloc<U>; };
  DIAlloc() = default; template <class U> DIAlloc(const DIAlloc<U>&) {}
  template <class U> void construct(U* p) noexcept { ::new ((void*)p) U; }
  template <class U, class... A> void construct(U* p, A&&... a) { ::new ((void*)p) U(std::forward<A>(a)...); }
};
using V8 = std::vector<uint8_t, DIAlloc<uint8_t>>;
using V32 = std::vector<uint32_t, DIAlloc<uint32_t>>;
static const char* VERSION = "prechk 1.6";

enum HazClass {
  HZ_MALFORMED = 0, HZ_PARSER_ABORT, HZ_OFFICIAL_QUIRK, HZ_NANODA_PARSE, HZ_NANODA_PROJ, HZ_NANODA_DEPTH,
  HZ_KERNEL_DEPTH, HZ_WALK_DEPTH, HZ_ORDER_QUOT, HZ_ORDER_STRLIT, HZ_ORDER_NATLIT, HZ_BUDGET, HZ_CLOSURE, NHZ
};
static const char* HZ_NAME[NHZ] = {"malformed", "parser_abort", "official_quirk", "nanoda_parse", "nanoda_proj",
                                   "nanoda_depth", "kernel_depth", "walk_depth", "order_quot", "order_strlit",
                                   "order_natlit", "budget", "closure"};

// ------------------------------------------------------------------------------------------------ options
struct Opts {
  int threads = 0;
  const char* json = nullptr;
  bool nanoda = true;           // count nanoda_* classes
  bool counted[NHZ];
  uint64_t nanoda_depth = 32768;
  uint64_t kernel_depth = 50000;
  uint64_t walk_limit = 100000;
  bool replay = true;
  const char* closure = nullptr;   // --closure TARGETS: export-completeness guard mode
  double visit_budget = 256.0;  // total DFS visits allowed, as a multiple of the number of expr records (+1e8)
  int max_examples = 8;
};
static Opts O;

// ------------------------------------------------------------------------------------------------ hazards
struct Example { uint64_t off; uint64_t lline; int chunk; std::string msg; };
struct HazSink {
  uint64_t count[NHZ] = {0};
  std::vector<Example> ex[NHZ];
  void add(int cls, int chunk, uint64_t off, uint64_t lline, std::string msg) {
    count[cls]++;
    if ((int)ex[cls].size() < O.max_examples) ex[cls].push_back({off, lline, chunk, std::move(msg)});
  }
};

// ------------------------------------------------------------------------------------------------ hashing
static inline uint64_t mix64(uint64_t x) {
  x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL; x ^= x >> 27; x *= 0x94d049bb133111ebULL; x ^= x >> 31; return x;
}
static inline uint64_t hcomb(uint64_t h, uint64_t v) { return mix64(h ^ (v + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2))); }
static uint64_t hbytes(const char* p, size_t n, uint64_t seed) {
  uint64_t h = mix64(seed ^ n);
  while (n >= 8) { uint64_t w; memcpy(&w, p, 8); h = hcomb(h, w); p += 8; n -= 8; }
  uint64_t w = 0; memcpy(&w, p, n); return hcomb(h, w ^ ((uint64_t)n << 56));
}

// Lean 4.36 runtime hashes (src/runtime/hash.cpp MurmurHash64A, lean.h lean_uint64_mix_hash): Name.hash / NameSet order
static uint64_t lean_murmur64a(const void* key, size_t len, uint64_t seed) {
  const uint64_t m = 0xc6a4a7935bd1e995ULL; const int r = 47;
  uint64_t h = seed ^ (len * m);
  const unsigned char* data = (const unsigned char*)key; const unsigned char* end = data + (len / 8) * 8;
  while (data != end) { uint64_t k; memcpy(&k, data, 8); data += 8; k *= m; k ^= k >> r; k *= m; h ^= k; h *= m; }
  switch (len & 7) {
    case 7: h ^= uint64_t(data[6]) << 48; [[fallthrough]];
    case 6: h ^= uint64_t(data[5]) << 40; [[fallthrough]];
    case 5: h ^= uint64_t(data[4]) << 32; [[fallthrough]];
    case 4: h ^= uint64_t(data[3]) << 24; [[fallthrough]];
    case 3: h ^= uint64_t(data[2]) << 16; [[fallthrough]];
    case 2: h ^= uint64_t(data[1]) << 8; [[fallthrough]];
    case 1: h ^= uint64_t(data[0]); h *= m;
  }
  h ^= h >> r; h *= m; h ^= h >> r;
  return h;
}
static inline uint64_t lean_mix_hash(uint64_t h, uint64_t k) {
  const uint64_t m = 0xc6a4a7935bd1e995ULL; const uint64_t r = 47;
  k *= m; k ^= k >> r; k ^= m; h ^= k; h *= m; return h;
}

// ------------------------------------------------------------------------------------------------ strict JSON
// Canonical compact JSON only (what lean4export / Lean's Json.compress emits): no whitespace, non-negative integers in
// canonical decimal form, standard escapes, valid UTF-8, no raw control characters. Everything else -> malformed.
enum JT : uint8_t { J_OBJ, J_ARR, J_STR, J_NUM, J_TRUE, J_FALSE, J_NULL };
struct JNode {
  uint8_t t; bool esc = false; bool big = false;
  uint32_t a = 0, b = 0;          // OBJ/ARR: first kid, count (OBJ kids = key,value pairs => 2*count entries)
  const char* p = nullptr; uint32_t len = 0;   // STR: raw contents between quotes; NUM: digits
  uint64_t num = 0;
};
struct JParser {
  const char* p; const char* e;
  std::vector<JNode> nodes; std::vector<uint32_t> kids; std::vector<uint32_t> stk;
  const char* err = nullptr;
  int depth = 0;
  bool fail(const char* m) { if (!err) err = m; return false; }
  bool parse(const char* b, const char* end, uint32_t& root) {
    p = b; e = end; nodes.clear(); kids.clear(); stk.clear(); err = nullptr; depth = 0;
    if (!value(root)) return false;
    if (p != e) return fail("trailing characters");
    return true;
  }
  bool str(uint32_t& out) {
    // p at opening quote
    ++p; const char* s = p; bool esc = false;
    while (true) {
      if (p >= e) return fail("unterminated string");
      unsigned char c = (unsigned char)*p;
      if (c == '"') break;
      if (c < 0x20) return fail("raw control character in string");
      if (c == '\\') {
        esc = true; ++p; if (p >= e) return fail("bad escape");
        char x = *p;
        if (x == 'u') {
          auto hex4 = [&](const char* q, unsigned& v) -> bool {
            if (e - q < 4) return false; v = 0;
            for (int i = 0; i < 4; i++) { char h = q[i]; v <<= 4;
              if (h >= '0' && h <= '9') v |= h - '0'; else if (h >= 'a' && h <= 'f') v |= h - 'a' + 10;
              else if (h >= 'A' && h <= 'F') v |= h - 'A' + 10; else return false; }
            return true; };
          unsigned v; if (!hex4(p + 1, v)) return fail("bad \\u escape");
          p += 5;
          if (v >= 0xDC00 && v <= 0xDFFF) return fail("lone low surrogate");
          if (v >= 0xD800 && v <= 0xDBFF) {
            unsigned w; if (e - p < 6 || p[0] != '\\' || p[1] != 'u' || !hex4(p + 2, w) || w < 0xDC00 || w > 0xDFFF)
              return fail("lone high surrogate");
            p += 6;
          }
          continue;
        }
        if (!strchr("\"\\/bfnrt", x) || x == 0) return fail("bad escape");
        ++p; continue;
      }
      if (c < 0x80) { ++p; continue; }
      // UTF-8 validation (no overlongs, no surrogates, <= U+10FFFF)
      int n; unsigned cp;
      if ((c & 0xE0) == 0xC0) { n = 1; cp = c & 0x1F; }
      else if ((c & 0xF0) == 0xE0) { n = 2; cp = c & 0x0F; }
      else if ((c & 0xF8) == 0xF0) { n = 3; cp = c & 0x07; }
      else return fail("invalid UTF-8");
      if (e - p <= n) return fail("invalid UTF-8");
      for (int i = 1; i <= n; i++) { unsigned char d = (unsigned char)p[i]; if ((d & 0xC0) != 0x80) return fail("invalid UTF-8"); cp = (cp << 6) | (d & 0x3F); }
      if ((n == 1 && cp < 0x80) || (n == 2 && cp < 0x800) || (n == 3 && cp < 0x10000) || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF))
        return fail("invalid UTF-8");
      p += n + 1;
    }
    JNode nd; nd.t = J_STR; nd.p = s; nd.len = (uint32_t)(p - s); nd.esc = esc; ++p;
    out = (uint32_t)nodes.size(); nodes.push_back(nd); return true;
  }
  bool value(uint32_t& out) {
    if (p >= e) return fail("unexpected end");
    char c = *p;
    if (c == '"') return str(out);
    if (c == '{' || c == '[') {
      if (++depth > 64) return fail("nesting too deep");
      bool obj = c == '{'; ++p;
      size_t base = stk.size();
      if (p < e && *p == (obj ? '}' : ']')) { ++p; }
      else {
        while (true) {
          if (obj) {
            if (p >= e || *p != '"') return fail("expected key");
            uint32_t k; if (!str(k)) return false; stk.push_back(k);
            if (p >= e || *p != ':') return fail("expected ':'");
            ++p;
          }
          uint32_t v; if (!value(v)) return false; stk.push_back(v);
          if (p >= e) return fail("unexpected end");
          if (*p == ',') { ++p; continue; }
          if (*p == (obj ? '}' : ']')) { ++p; break; }
          return fail("expected ',' or close");
        }
      }
      JNode nd; nd.t = obj ? J_OBJ : J_ARR; nd.a = (uint32_t)kids.size();
      size_t cnt = stk.size() - base; nd.b = (uint32_t)(obj ? cnt / 2 : cnt);
      kids.insert(kids.end(), stk.begin() + base, stk.end()); stk.resize(base);
      --depth; out = (uint32_t)nodes.size(); nodes.push_back(nd); return true;
    }
    if (c >= '0' && c <= '9') {
      const char* s = p;
      if (c == '0') { ++p; }
      else { while (p < e && *p >= '0' && *p <= '9') ++p; }
      if (p < e && (*p == '.' || *p == 'e' || *p == 'E' || (*p >= '0' && *p <= '9'))) return fail("non-canonical number");
      JNode nd; nd.t = J_NUM; nd.p = s; nd.len = (uint32_t)(p - s);
      uint64_t v = 0; bool big = false;
      for (const char* q = s; q < p; q++) { unsigned d = *q - '0'; if (v > (UINT64_MAX - d) / 10) { big = true; break; } v = v * 10 + d; }
      nd.num = big ? UINT64_MAX : v; nd.big = big;
      out = (uint32_t)nodes.size(); nodes.push_back(nd); return true;
    }
    if (c == '-') return fail("negative number");
    if (e - p >= 4 && !memcmp(p, "true", 4)) { p += 4; JNode nd; nd.t = J_TRUE; out = (uint32_t)nodes.size(); nodes.push_back(nd); return true; }
    if (e - p >= 5 && !memcmp(p, "false", 5)) { p += 5; JNode nd; nd.t = J_FALSE; out = (uint32_t)nodes.size(); nodes.push_back(nd); return true; }
    if (e - p >= 4 && !memcmp(p, "null", 4)) { p += 4; JNode nd; nd.t = J_NULL; out = (uint32_t)nodes.size(); nodes.push_back(nd); return true; }
    return fail("unexpected character");
  }
  // helpers
  const JNode& N(uint32_t i) const { return nodes[i]; }
  bool keyeq(uint32_t k, const char* s) const { const JNode& n = nodes[k]; size_t l = strlen(s); return !n.esc && n.len == l && !memcmp(n.p, s, l); }
  // object field lookup; returns NONE if missing
  uint32_t get(uint32_t obj, const char* key) const {
    const JNode& o = nodes[obj];
    for (uint32_t i = 0; i < o.b; i++) if (keyeq(kids[o.a + 2 * i], key)) return kids[o.a + 2 * i + 1];
    return NONE;
  }
  // checks that the object has exactly the given keys (each once) -- canonical form
  bool exact_keys(uint32_t obj, std::initializer_list<const char*> ks, const char* optional = nullptr) const {
    const JNode& o = nodes[obj];
    if (o.t != J_OBJ) return false;
    size_t need = ks.size();
    uint32_t seen = 0; bool opt_seen = false;
    for (uint32_t i = 0; i < o.b; i++) {
      uint32_t k = kids[o.a + 2 * i]; bool found = false; int j = 0;
      for (const char* s : ks) { if (keyeq(k, s)) { if (seen & (1u << j)) return false; seen |= 1u << j; found = true; break; } j++; }
      if (!found) { if (optional && keyeq(k, optional) && !opt_seen) { opt_seen = true; continue; } return false; }
    }
    return seen == ((need == 32) ? 0xFFFFFFFFu : ((1u << need) - 1));
  }
};
static std::string jdecode(const JNode& n) {
  std::string out; if (!n.esc) { out.assign(n.p, n.len); return out; }
  const char* p = n.p; const char* e = n.p + n.len;
  auto put = [&](unsigned cp) {
    if (cp < 0x80) out += (char)cp;
    else if (cp < 0x800) { out += (char)(0xC0 | (cp >> 6)); out += (char)(0x80 | (cp & 0x3F)); }
    else if (cp < 0x10000) { out += (char)(0xE0 | (cp >> 12)); out += (char)(0x80 | ((cp >> 6) & 0x3F)); out += (char)(0x80 | (cp & 0x3F)); }
    else { out += (char)(0xF0 | (cp >> 18)); out += (char)(0x80 | ((cp >> 12) & 0x3F)); out += (char)(0x80 | ((cp >> 6) & 0x3F)); out += (char)(0x80 | (cp & 0x3F)); }
  };
  auto hex4 = [](const char* q) { unsigned v = 0; for (int i = 0; i < 4; i++) { char h = q[i]; v <<= 4; v |= (h <= '9') ? h - '0' : ((h | 0x20) - 'a' + 10); } return v; };
  while (p < e) {
    if (*p != '\\') { out += *p++; continue; }
    ++p; char x = *p++;
    switch (x) {
      case '"': out += '"'; break; case '\\': out += '\\'; break; case '/': out += '/'; break;
      case 'b': out += '\b'; break; case 'f': out += '\f'; break; case 'n': out += '\n'; break;
      case 'r': out += '\r'; break; case 't': out += '\t'; break;
      case 'u': { unsigned v = hex4(p); p += 4;
        if (v >= 0xD800 && v <= 0xDBFF) { unsigned w = hex4(p + 2); p += 6; v = 0x10000 + ((v - 0xD800) << 10) + (w - 0xDC00); }
        put(v); break; }
    }
  }
  return out;
}

// ------------------------------------------------------------------------------------------------ records
enum EK : uint8_t { EK_BVAR = 1, EK_SORT, EK_CONST, EK_APP, EK_LAM, EK_PI, EK_LET, EK_PROJ, EK_NAT, EK_STR, EK_MDATA };
enum LK : uint8_t { LK_SUCC = 1, LK_MAX, LK_IMAX, LK_PARAM };
enum DK : uint8_t { DK_AXIOM = 1, DK_DEF, DK_THM, DK_OPAQUE, DK_QUOT, DK_IND, DK_CTOR, DK_REC };
static const char* DK_NAME[] = {"?", "axiom", "def", "thm", "opaque", "quot", "inductive", "ctor", "rec"};
struct DeclRec {
  uint8_t kind; uint8_t skip;   // skip: unsafe/partial (not replayed by Lean.Replay)
  uint32_t name, type, value;   // value NONE if none
  uint64_t off;
  uint32_t xbeg, xcnt;          // extra used names (ind: ctors; ctor: self; rec: all)
  uint32_t aux;                 // ind: numIndices>0||nctors!=1 flag ; ctor: induct name
  uint32_t xall;                // ind: number of `all` names stored after the ctors in xnames (walk-bound extras only)
};
enum SpecialComp : uint8_t { SC_NONE = 0, SC_Quot, SC_mk, SC_lift, SC_ind, SC_String, SC_ofList, SC_Char, SC_ofNat, SC_Nat, SC_Eq };
struct SpecialName { uint32_t idx, pre; uint8_t comp; };
struct DupRec { uint64_t h; uint64_t off; };

struct Chunk {
  int id; uint64_t beg, end;
  uint64_t nlines = 0;
  // per-kind counts and contiguity
  uint64_t n_names = 0, n_levels = 0, n_exprs = 0;
  int64_t first_name = -1, first_level = -1, first_expr = -1;
  bool contig_name = true, contig_level = true, contig_expr = true;
  int64_t def_name = INT64_MIN, def_level = INT64_MIN, def_expr = INT64_MIN;
  // records
  std::vector<uint8_t> lk; std::vector<uint32_t> la, lb;
  std::vector<uint8_t> ek; std::vector<uint32_t> ea, eb;
  std::vector<std::pair<uint32_t, uint32_t>> letb;   // (local expr index, body)
  std::vector<DeclRec> decls; std::vector<uint32_t> xnames;
  std::vector<std::pair<uint32_t, uint64_t>> projs;  // (typeName, offset)
  std::vector<SpecialName> specials;
  std::vector<uint8_t> nk; std::vector<uint32_t> npre; std::vector<uint64_t> ncomp, noff;   // name records (exact replay order)
  std::vector<DupRec> dn, dl, de;
  // stats
  uint64_t max_height = 0, max_name_num = 0, max_bvar = 0, max_proj_idx = 0, max_u16_field = 0, n_nat = 0, n_str = 0, n_proj = 0;
  HazSink hz;
};

static inline bool isnum(const JParser& J, uint32_t v) { return v != NONE && J.N(v).t == J_NUM; }
static inline bool isbool(const JParser& J, uint32_t v) { return v != NONE && (J.N(v).t == J_TRUE || J.N(v).t == J_FALSE); }

// ------------------------------------------------------------------------------------------------ canonical key
// Content of a name/level/expr record without its own index; used to verify duplicate candidates exactly.
// Returns false if the line cannot be parsed (should not happen for lines that passed the first pass).
static bool canon_key(const char* b, const char* e, std::string& out) {
  JParser J; uint32_t r;
  if (!J.parse(b, e, r) || J.N(r).t != J_OBJ) return false;
  const JNode& o = J.N(r);
  out.clear();
  for (uint32_t i = 0; i < o.b; i++) {
    uint32_t k = J.kids[o.a + 2 * i], v = J.kids[o.a + 2 * i + 1];
    if (J.keyeq(k, "in") || J.keyeq(k, "il") || J.keyeq(k, "ie")) { out += J.keyeq(k, "in") ? "N|" : J.keyeq(k, "il") ? "L|" : "E|"; continue; }
    out += std::string(J.N(k).p, J.N(k).len); out += '|';
    // serialize value canonically (decoded strings)
    std::vector<uint32_t> st{v};
    while (!st.empty()) {
      uint32_t x = st.back(); st.pop_back();
      const JNode& n = J.N(x);
      switch (n.t) {
        case J_STR: { std::string s = jdecode(n); out += 'S'; out += std::to_string(s.size()); out += ':'; out += s; break; }
        case J_NUM: out += 'n'; out.append(n.p, n.len); out += ';'; break;
        case J_TRUE: out += 'T'; break; case J_FALSE: out += 'F'; break; case J_NULL: out += 'Z'; break;
        case J_ARR: out += '['; out += std::to_string(n.b); for (uint32_t j = n.b; j-- > 0;) st.push_back(J.kids[n.a + j]); break;
        case J_OBJ: {
          // keys sorted for canonicity
          std::vector<std::pair<std::string, uint32_t>> kv;
          for (uint32_t j = 0; j < n.b; j++) kv.push_back({std::string(J.N(J.kids[n.a + 2 * j]).p, J.N(J.kids[n.a + 2 * j]).len), J.kids[n.a + 2 * j + 1]});
          std::sort(kv.begin(), kv.end());
          out += '{'; out += std::to_string(n.b);
          // push in reverse so they serialize in order; keys emitted inline via a marker is complex -> emit keys now
          for (auto& p : kv) { out += p.first; out += ','; }
          for (size_t j = kv.size(); j-- > 0;) st.push_back(kv[j].second);
          break;
        }
      }
    }
    out += '#';
  }
  return true;
}

// ------------------------------------------------------------------------------------------------ pass 1 (parallel)
static const char* G_BASE = nullptr;  // mmap base

static void process_chunk(Chunk& C) {
  JParser J;
  const char* base = G_BASE;
  uint64_t pos = C.beg;
  std::string tmp;
  auto H = [&](int cls, uint64_t off, const std::string& m) { C.hz.add(cls, C.id, off, C.nlines, m); };
  while (pos < C.end) {
    const char* ls = base + pos;
    const char* nl = (const char*)memchr(ls, '\n', C.end - pos);
    const char* le = nl ? nl : base + C.end;
    uint64_t off = pos;
    pos = (le - base) + (nl ? 1 : 0);
    C.nlines++;
    uint32_t r;
    if (le == ls) { H(HZ_MALFORMED, off, "empty line (official parser: invalid JSON)"); continue; }
    if (!J.parse(ls, le, r)) { H(HZ_MALFORMED, off, std::string("JSON: ") + J.err); continue; }
    const JNode& o = J.N(r);
    if (o.t != J_OBJ) { H(HZ_MALFORMED, off, "not a JSON object"); continue; }
    // record kind by keys
    uint32_t vin = J.get(r, "in"), vil = J.get(r, "il"), vie = J.get(r, "ie");
    auto ref_name = [&](uint64_t v, bool big) { int64_t d = big || v > (uint64_t)INT64_MAX / 2 ? INT64_MAX : (int64_t)v - (int64_t)C.n_names; if (d > C.def_name) C.def_name = d; if (big || v > 0xFFFFFFFFull) H(HZ_NANODA_PARSE, off, "name index > u32"); };
    auto ref_level = [&](uint64_t v, bool big) { int64_t d = big || v > (uint64_t)INT64_MAX / 2 ? INT64_MAX : (int64_t)v - (int64_t)C.n_levels; if (d > C.def_level) C.def_level = d; if (big || v > 0xFFFFFFFFull) H(HZ_NANODA_PARSE, off, "level index > u32"); };
    auto ref_expr = [&](uint64_t v, bool big) { int64_t d = big || v > (uint64_t)INT64_MAX / 2 ? INT64_MAX : (int64_t)v - (int64_t)C.n_exprs; if (d > C.def_expr) C.def_expr = d; if (big || v > 0xFFFFFFFFull) H(HZ_NANODA_PARSE, off, "expr index > u32"); };
    auto numv = [&](uint32_t v) -> uint64_t { return J.N(v).num; };
    auto u16chk = [&](uint32_t v, const char* what) {
      uint64_t x = J.N(v).num; if (x > C.max_u16_field) C.max_u16_field = x;
      if (J.N(v).big || x > 65535) H(HZ_NANODA_PARSE, off, std::string(what) + " = " + std::string(J.N(v).p, J.N(v).len) + " > u16 (nanoda)");
    };
    auto namelist = [&](uint32_t arr, std::vector<uint32_t>* sink) -> bool {
      if (arr == NONE || J.N(arr).t != J_ARR) return false;
      const JNode& a = J.N(arr);
      for (uint32_t i = 0; i < a.b; i++) { uint32_t x = J.kids[a.a + i]; if (!isnum(J, x)) return false; ref_name(numv(x), J.N(x).big); if (sink) sink->push_back((uint32_t)std::min<uint64_t>(numv(x), NONE)); }
      return true;
    };
    if (o.b == 2 && (vin != NONE || vil != NONE || vie != NONE)) {
      uint32_t vidx = vin != NONE ? vin : vil != NONE ? vil : vie;
      if (!isnum(J, vidx)) { H(HZ_MALFORMED, off, "index not a number"); continue; }
      uint64_t idx = numv(vidx); bool bigidx = J.N(vidx).big;
      if (bigidx || idx > 0xFFFFFFFFull) H(HZ_NANODA_PARSE, off, "record index > u32");
      // the other key (exactly one index key allowed)
      auto isidx = [&](uint32_t k) { return J.keyeq(k, "in") || J.keyeq(k, "il") || J.keyeq(k, "ie"); };
      uint32_t k0 = J.kids[o.a], k1 = J.kids[o.a + 2];
      if (isidx(k0) == isidx(k1)) { H(HZ_MALFORMED, off, "record with two index keys"); continue; }
      uint32_t kk = isidx(k0) ? k1 : k0;
      uint32_t vv = isidx(k0) ? J.kids[o.a + 3] : J.kids[o.a + 1];
      if (J.N(kk).esc) { H(HZ_MALFORMED, off, "escaped key"); continue; }
      const JNode& K = J.N(kk);
      std::string key(K.p, K.len);
      if (vin != NONE) {
        // ---------------- name
        int64_t expect = C.first_name < 0 ? -1 : C.first_name + (int64_t)C.n_names;
        if (C.first_name < 0) C.first_name = bigidx ? INT64_MAX : (int64_t)idx; else if ((int64_t)idx != expect || bigidx) C.contig_name = false;
        uint64_t h;
        if (key == "str") {
          if (!J.exact_keys(vv, {"pre", "str"})) { H(HZ_MALFORMED, off, "Name.str fields"); C.n_names++; continue; }
          uint32_t pre = J.get(vv, "pre"), s = J.get(vv, "str");
          if (!isnum(J, pre) || J.N(s).t != J_STR) { H(HZ_MALFORMED, off, "Name.str field types"); C.n_names++; continue; }
          ref_name(numv(pre), J.N(pre).big);
          std::string ds = jdecode(J.N(s));
          h = hcomb(hcomb(1, numv(pre)), hbytes(ds.data(), ds.size(), 7));
          uint8_t sc = SC_NONE;
          if (ds == "Quot") sc = SC_Quot; else if (ds == "mk") sc = SC_mk; else if (ds == "lift") sc = SC_lift; else if (ds == "ind") sc = SC_ind;
          else if (ds == "String") sc = SC_String; else if (ds == "ofList") sc = SC_ofList; else if (ds == "Char") sc = SC_Char;
          else if (ds == "ofNat") sc = SC_ofNat; else if (ds == "Nat") sc = SC_Nat; else if (ds == "Eq") sc = SC_Eq;
          if (sc) C.specials.push_back({(uint32_t)std::min<uint64_t>(idx, NONE), (uint32_t)std::min<uint64_t>(numv(pre), NONE), sc});
          C.nk.push_back(1); C.npre.push_back((uint32_t)std::min<uint64_t>(numv(pre), NONE)); C.ncomp.push_back(lean_murmur64a(ds.data(), ds.size(), 11)); C.noff.push_back(off);
        } else if (key == "num") {
          if (!J.exact_keys(vv, {"i", "pre"})) { H(HZ_MALFORMED, off, "Name.num fields"); C.n_names++; continue; }
          uint32_t pre = J.get(vv, "pre"), iv = J.get(vv, "i");
          if (!isnum(J, pre) || !isnum(J, iv)) { H(HZ_MALFORMED, off, "Name.num field types"); C.n_names++; continue; }
          ref_name(numv(pre), J.N(pre).big);
          if (J.N(iv).big) { H(HZ_NANODA_PARSE, off, "name number > u32 (nanoda, finding 032)"); }
          else {
            if (numv(iv) > C.max_name_num) C.max_name_num = numv(iv);
            if (numv(iv) > 0xFFFFFFFFull) H(HZ_NANODA_PARSE, off, "name number " + std::to_string(numv(iv)) + " > u32 (nanoda, finding 032)");
          }
          h = hcomb(hcomb(2, numv(pre)), hbytes(J.N(iv).p, J.N(iv).len, 9));
          C.nk.push_back(2); C.npre.push_back((uint32_t)std::min<uint64_t>(numv(pre), NONE)); C.ncomp.push_back(J.N(iv).big ? 17 : numv(iv)); C.noff.push_back(off);
        } else { H(HZ_MALFORMED, off, "unknown name record " + key); C.n_names++; continue; }
        C.dn.push_back({h, off});
        C.n_names++;
        continue;
      }
      if (vil != NONE) {
        // ---------------- level
        int64_t expect = C.first_level < 0 ? -1 : C.first_level + (int64_t)C.n_levels;
        if (C.first_level < 0) C.first_level = bigidx ? INT64_MAX : (int64_t)idx; else if ((int64_t)idx != expect || bigidx) C.contig_level = false;
        uint8_t k = 0; uint32_t a = NONE, b = NONE; uint64_t h = 0;
        if (key == "succ" && isnum(J, vv)) { k = LK_SUCC; ref_level(numv(vv), J.N(vv).big); a = (uint32_t)std::min<uint64_t>(numv(vv), NONE); h = hcomb(11, numv(vv)); }
        else if ((key == "max" || key == "imax") && J.N(vv).t == J_ARR && J.N(vv).b == 2 && isnum(J, J.kids[J.N(vv).a]) && isnum(J, J.kids[J.N(vv).a + 1])) {
          k = key == "max" ? LK_MAX : LK_IMAX;
          uint32_t x = J.kids[J.N(vv).a], y = J.kids[J.N(vv).a + 1];
          ref_level(numv(x), J.N(x).big); ref_level(numv(y), J.N(y).big);
          a = (uint32_t)std::min<uint64_t>(numv(x), NONE); b = (uint32_t)std::min<uint64_t>(numv(y), NONE);
          h = hcomb(hcomb(k == LK_MAX ? 12 : 13, numv(x)), numv(y));
        } else if (key == "param" && isnum(J, vv)) { k = LK_PARAM; ref_name(numv(vv), J.N(vv).big); a = (uint32_t)std::min<uint64_t>(numv(vv), NONE); h = hcomb(14, numv(vv)); }
        else { H(HZ_MALFORMED, off, "level record " + key); }
        C.lk.push_back(k); C.la.push_back(a); C.lb.push_back(b);
        C.dl.push_back({h, off});
        C.n_levels++;
        continue;
      }
      // ---------------- expr
      int64_t expect = C.first_expr < 0 ? -1 : C.first_expr + (int64_t)C.n_exprs;
      if (C.first_expr < 0) C.first_expr = bigidx ? INT64_MAX : (int64_t)idx; else if ((int64_t)idx != expect || bigidx) C.contig_expr = false;
      uint8_t k = 0; uint32_t a = NONE, b = NONE; uint64_t h = 0;
      auto cl = [](uint64_t v) { return (uint32_t)std::min<uint64_t>(v, NONE); };
      if (key == "bvar" && isnum(J, vv)) {
        k = EK_BVAR; uint64_t v = numv(vv); bool big = J.N(vv).big; a = cl(v); h = hcomb(21, v);
        if (!big && v > C.max_bvar) C.max_bvar = v;
        if (big || v >= 1048575) H(HZ_PARSER_ABORT, off, "bvar " + std::string(J.N(vv).p, J.N(vv).len) + ": idx+1 > 1048575 -> official Expr.mkData internal panic (finding 044)");
        if (big || v >= 65535) H(HZ_NANODA_PARSE, off, "bvar " + std::string(J.N(vv).p, J.N(vv).len) + " >= 65535 (nanoda u16 index / loose-bvar count)");
      } else if (key == "sort" && isnum(J, vv)) {
        k = EK_SORT; ref_level(numv(vv), J.N(vv).big); a = cl(numv(vv)); h = hcomb(22, numv(vv));
      } else if (key == "const") {
        if (!J.exact_keys(vv, {"name", "us"})) { H(HZ_MALFORMED, off, "const fields"); }
        else {
          uint32_t nm = J.get(vv, "name"), us = J.get(vv, "us");
          if (!isnum(J, nm) || J.N(us).t != J_ARR) H(HZ_MALFORMED, off, "const field types");
          else {
            k = EK_CONST; ref_name(numv(nm), J.N(nm).big); a = cl(numv(nm)); h = hcomb(23, numv(nm));
            const JNode& A = J.N(us);
            for (uint32_t i = 0; i < A.b; i++) { uint32_t x = J.kids[A.a + i]; if (!isnum(J, x)) { H(HZ_MALFORMED, off, "const level"); k = 0; break; } ref_level(numv(x), J.N(x).big); h = hcomb(h, numv(x)); }
            h = hcomb(h, A.b);
          }
        }
      } else if (key == "app") {
        uint32_t f = J.get(vv, "fn"), g = J.get(vv, "arg");
        if (!J.exact_keys(vv, {"arg", "fn"}) || !isnum(J, f) || !isnum(J, g)) H(HZ_MALFORMED, off, "app fields");
        else { k = EK_APP; ref_expr(numv(f), J.N(f).big); ref_expr(numv(g), J.N(g).big); a = cl(numv(f)); b = cl(numv(g)); h = hcomb(hcomb(24, numv(f)), numv(g)); }
      } else if (key == "lam" || key == "forallE") {
        uint32_t nm = J.get(vv, "name"), ty = J.get(vv, "type"), bd = J.get(vv, "body"), bi = J.get(vv, "binderInfo");
        if (!J.exact_keys(vv, {"binderInfo", "body", "name", "type"}) || !isnum(J, nm) || !isnum(J, ty) || !isnum(J, bd) || J.N(bi).t != J_STR)
          H(HZ_MALFORMED, off, key + " fields");
        else {
          int bic = J.keyeq(bi, "default") ? 0 : J.keyeq(bi, "implicit") ? 1 : J.keyeq(bi, "strictImplicit") ? 2 : J.keyeq(bi, "instImplicit") ? 3 : -1;
          if (bic < 0) H(HZ_MALFORMED, off, "binderInfo");
          else {
            k = key == "lam" ? EK_LAM : EK_PI;
            ref_name(numv(nm), J.N(nm).big); ref_expr(numv(ty), J.N(ty).big); ref_expr(numv(bd), J.N(bd).big);
            a = cl(numv(ty)); b = cl(numv(bd));
            h = hcomb(hcomb(hcomb(hcomb(k == EK_LAM ? 25 : 26, numv(nm)), numv(ty)), numv(bd)), bic);
          }
        }
      } else if (key == "letE") {
        uint32_t nm = J.get(vv, "name"), ty = J.get(vv, "type"), va = J.get(vv, "value"), bd = J.get(vv, "body"), nd = J.get(vv, "nondep");
        if (!J.exact_keys(vv, {"body", "name", "nondep", "type", "value"}) || !isnum(J, nm) || !isnum(J, ty) || !isnum(J, va) || !isnum(J, bd) || !isbool(J, nd))
          H(HZ_MALFORMED, off, "letE fields");
        else {
          k = EK_LET; ref_name(numv(nm), J.N(nm).big); ref_expr(numv(ty), J.N(ty).big); ref_expr(numv(va), J.N(va).big); ref_expr(numv(bd), J.N(bd).big);
          a = cl(numv(ty)); b = cl(numv(va)); C.letb.push_back({(uint32_t)C.n_exprs, cl(numv(bd))});
          h = hcomb(hcomb(hcomb(hcomb(hcomb(27, numv(nm)), numv(ty)), numv(va)), numv(bd)), J.N(nd).t == J_TRUE);
        }
      } else if (key == "proj") {
        uint32_t tn = J.get(vv, "typeName"), ix = J.get(vv, "idx"), st = J.get(vv, "struct");
        if (!J.exact_keys(vv, {"idx", "struct", "typeName"}) || !isnum(J, tn) || !isnum(J, ix) || !isnum(J, st)) H(HZ_MALFORMED, off, "proj fields");
        else {
          k = EK_PROJ; ref_name(numv(tn), J.N(tn).big); ref_expr(numv(st), J.N(st).big); a = cl(numv(st)); b = cl(numv(tn));
          C.n_proj++;
          if (!J.N(ix).big && numv(ix) > C.max_proj_idx) C.max_proj_idx = numv(ix);
          if (J.N(ix).big) H(HZ_NANODA_PARSE, off, "proj idx > usize (nanoda)");
          if (J.N(ix).big || numv(ix) > 65535) H(HZ_NANODA_PARSE, off, "proj idx " + std::string(J.N(ix).p, J.N(ix).len) + " > 65535: structure would need > u16 fields (nanoda numFields u16; findings 003/008 class)");
          h = hcomb(hcomb(hcomb(28, numv(tn)), hbytes(J.N(ix).p, J.N(ix).len, 3)), numv(st));
          C.projs.push_back({cl(numv(tn)), off});
        }
      } else if (key == "natVal") {
        if (J.N(vv).t != J_STR || J.N(vv).esc || J.N(vv).len == 0) H(HZ_MALFORMED, off, "natVal not a digit string");
        else {
          const JNode& s = J.N(vv); bool ok = true;
          for (uint32_t i = 0; i < s.len; i++) if (s.p[i] < '0' || s.p[i] > '9') ok = false;
          if (s.len > 1 && s.p[0] == '0') ok = false;   // canonical: no leading zeros
          if (!ok) H(HZ_MALFORMED, off, "natVal not canonical decimal");
          else { k = EK_NAT; C.n_nat++; h = hcomb(29, hbytes(s.p, s.len, 5)); }
        }
      } else if (key == "strVal") {
        if (J.N(vv).t != J_STR) H(HZ_MALFORMED, off, "strVal not a string");
        else { k = EK_STR; C.n_str++; std::string ds = jdecode(J.N(vv)); h = hcomb(30, hbytes(ds.data(), ds.size(), 6)); }
      } else if (key == "mdata") {
        uint32_t ex = J.get(vv, "expr"), dt = J.get(vv, "data");
        if (!J.exact_keys(vv, {"data", "expr"}) || !isnum(J, ex) || J.N(dt).t != J_OBJ) H(HZ_MALFORMED, off, "mdata fields");
        else { k = EK_MDATA; ref_expr(numv(ex), J.N(ex).big); a = cl(numv(ex)); h = hcomb(31, numv(ex)); }
        H(HZ_NANODA_PARSE, off, "Expr.mdata record (official nanoda: panic \"Expr.mdata not supported\")");
      } else {
        H(HZ_MALFORMED, off, "unknown expr record " + key);
      }
      C.ek.push_back(k); C.ea.push_back(a); C.eb.push_back(b);
      C.de.push_back({h, off});
      C.n_exprs++;
      continue;
    }
    // ---------------- declarations
    if (o.b != 1) { H(HZ_MALFORMED, off, "unknown export object"); continue; }
    uint32_t kk = J.kids[o.a], d = J.kids[o.a + 1];
    std::string key(J.N(kk).p, J.N(kk).len);
    if (J.N(d).t != J_OBJ) { H(HZ_MALFORMED, off, "declaration payload not an object"); continue; }
    auto basic = [&](uint32_t obj, DeclRec& R, bool hasValue) -> bool {
      uint32_t nm = J.get(obj, "name"), ty = J.get(obj, "type"), lp = J.get(obj, "levelParams");
      if (!isnum(J, nm) || !isnum(J, ty)) return false;
      if (!namelist(lp, nullptr)) return false;
      ref_name(numv(nm), J.N(nm).big); ref_expr(numv(ty), J.N(ty).big);
      R.name = (uint32_t)std::min<uint64_t>(numv(nm), NONE); R.type = (uint32_t)std::min<uint64_t>(numv(ty), NONE); R.value = NONE;
      if (hasValue) { uint32_t va = J.get(obj, "value"); if (!isnum(J, va)) return false; ref_expr(numv(va), J.N(va).big); R.value = (uint32_t)std::min<uint64_t>(numv(va), NONE); }
      R.off = off; R.xbeg = (uint32_t)C.xnames.size(); R.xcnt = 0; R.skip = 0; R.aux = 0;
      return true;
    };
    DeclRec R{};
    if (key == "axiom") {
      if (!J.exact_keys(d, {"isUnsafe", "levelParams", "name", "type"}) || !isbool(J, J.get(d, "isUnsafe")) || !basic(d, R, false)) { H(HZ_MALFORMED, off, "axiom fields"); continue; }
      R.kind = DK_AXIOM;
      if (J.N(J.get(d, "isUnsafe")).t == J_TRUE) { R.skip = 1; H(HZ_NANODA_PARSE, off, "unsafe axiom (nanoda assert)"); }
      C.decls.push_back(R);
    } else if (key == "def") {
      if (!J.exact_keys(d, {"all", "hints", "levelParams", "name", "safety", "type", "value"}) || !basic(d, R, true) || !namelist(J.get(d, "all"), nullptr)) { H(HZ_MALFORMED, off, "def fields"); continue; }
      uint32_t hi = J.get(d, "hints"), sf = J.get(d, "safety");
      R.kind = DK_DEF;
      if (J.N(hi).t == J_STR && (J.keyeq(hi, "opaque") || J.keyeq(hi, "abbrev"))) {}
      else if (J.N(hi).t == J_OBJ && J.exact_keys(hi, {"regular"}) && isnum(J, J.get(hi, "regular"))) {
        uint32_t hv = J.get(hi, "regular"); uint64_t x = numv(hv); bool big = J.N(hv).big;
        if (!big && x > C.max_height) C.max_height = x;
        if (big || x > 65535) H(HZ_NANODA_PARSE, off, "reducibility height " + std::string(J.N(hv).p, J.N(hv).len) + " > u16 (nanoda, finding 045)");
        if (big || x > 0xFFFFFFFFull) H(HZ_OFFICIAL_QUIRK, off, "reducibility height >= 2^32 (official parser truncates with toUInt32)");
      } else { H(HZ_MALFORMED, off, "def hints"); continue; }
      if (J.N(sf).t != J_STR) { H(HZ_MALFORMED, off, "def safety"); continue; }
      if (J.keyeq(sf, "safe")) {}
      else if (J.keyeq(sf, "unsafe") || J.keyeq(sf, "partial")) { R.skip = 1; H(HZ_NANODA_PARSE, off, "unsafe/partial definition (nanoda assert)"); }
      else { H(HZ_MALFORMED, off, "def safety value"); continue; }
      C.decls.push_back(R);
    } else if (key == "thm") {
      if (!J.exact_keys(d, {"all", "levelParams", "name", "type", "value"}) || !basic(d, R, true) || !namelist(J.get(d, "all"), nullptr)) { H(HZ_MALFORMED, off, "thm fields"); continue; }
      R.kind = DK_THM; C.decls.push_back(R);
    } else if (key == "opaque") {
      bool hasU = J.get(d, "isUnsafe") != NONE;
      if (!J.exact_keys(d, {"all", "levelParams", "name", "type", "value"}, "isUnsafe") || !basic(d, R, true) || !namelist(J.get(d, "all"), nullptr) || (hasU && !isbool(J, J.get(d, "isUnsafe")))) { H(HZ_MALFORMED, off, "opaque fields"); continue; }
      R.kind = DK_OPAQUE;
      if (!hasU) H(HZ_NANODA_PARSE, off, "opaque without isUnsafe (official defaults to false; nanoda requires the field)");
      else if (J.N(J.get(d, "isUnsafe")).t == J_TRUE) { R.skip = 1; H(HZ_NANODA_PARSE, off, "unsafe opaque (nanoda assert)"); }
      C.decls.push_back(R);
    } else if (key == "quot") {
      uint32_t kd = J.get(d, "kind");
      if (!J.exact_keys(d, {"kind", "levelParams", "name", "type"}) || !basic(d, R, false) || J.N(kd).t != J_STR ||
          !(J.keyeq(kd, "type") || J.keyeq(kd, "ctor") || J.keyeq(kd, "lift") || J.keyeq(kd, "ind"))) { H(HZ_MALFORMED, off, "quot fields"); continue; }
      R.kind = DK_QUOT; C.decls.push_back(R);
    } else if (key == "inductive") {
      if (!J.exact_keys(d, {"ctors", "recs", "types"})) { H(HZ_MALFORMED, off, "inductive fields"); continue; }
      uint32_t ts = J.get(d, "types"), cs = J.get(d, "ctors"), rs = J.get(d, "recs");
      if (J.N(ts).t != J_ARR || J.N(cs).t != J_ARR || J.N(rs).t != J_ARR) { H(HZ_MALFORMED, off, "inductive arrays"); continue; }
      bool bad = false;
      for (uint32_t i = 0; i < J.N(ts).b && !bad; i++) {
        uint32_t t = J.kids[J.N(ts).a + i];
        if (!J.exact_keys(t, {"all", "ctors", "isRec", "isReflexive", "isUnsafe", "levelParams", "name", "numIndices", "numNested", "numParams", "type"})) { bad = true; break; }
        DeclRec T{};
        if (!basic(t, T, false)) { bad = true; break; }
        uint32_t ni = J.get(t, "numIndices"), nn = J.get(t, "numNested"), np = J.get(t, "numParams"), ct = J.get(t, "ctors");
        if (!isnum(J, ni) || !isnum(J, nn) || !isnum(J, np) || !isbool(J, J.get(t, "isRec")) || !isbool(J, J.get(t, "isReflexive")) || !isbool(J, J.get(t, "isUnsafe"))) { bad = true; break; }
        u16chk(ni, "numIndices"); u16chk(nn, "numNested"); u16chk(np, "numParams");
        T.kind = DK_IND;
        T.xbeg = (uint32_t)C.xnames.size();
        if (!namelist(ct, &C.xnames)) { bad = true; break; }
        T.xcnt = (uint32_t)C.xnames.size() - T.xbeg;
        { size_t b0 = C.xnames.size(); if (!namelist(J.get(t, "all"), &C.xnames)) { bad = true; break; } T.xall = (uint32_t)(C.xnames.size() - b0); }
        T.aux = (numv(ni) > 0 || J.N(ni).big || T.xcnt != 1) ? 1 : 0;
        if (J.N(J.get(t, "isUnsafe")).t == J_TRUE) { T.skip = 1; H(HZ_NANODA_PARSE, off, "unsafe inductive (nanoda assert)"); }
        C.decls.push_back(T);
      }
      for (uint32_t i = 0; i < J.N(cs).b && !bad; i++) {
        uint32_t c = J.kids[J.N(cs).a + i];
        if (!J.exact_keys(c, {"cidx", "induct", "isUnsafe", "levelParams", "name", "numFields", "numParams", "type"})) { bad = true; break; }
        DeclRec T{};
        if (!basic(c, T, false)) { bad = true; break; }
        uint32_t ci = J.get(c, "cidx"), in = J.get(c, "induct"), nf = J.get(c, "numFields"), np = J.get(c, "numParams");
        if (!isnum(J, ci) || !isnum(J, in) || !isnum(J, nf) || !isnum(J, np) || !isbool(J, J.get(c, "isUnsafe"))) { bad = true; break; }
        ref_name(numv(in), J.N(in).big);
        u16chk(ci, "cidx"); u16chk(nf, "numFields"); u16chk(np, "numParams");
        T.kind = DK_CTOR; T.aux = (uint32_t)std::min<uint64_t>(numv(in), NONE);
        T.xbeg = (uint32_t)C.xnames.size(); C.xnames.push_back(T.name); T.xcnt = 1;   // getUsedConstantsAsSet: ctor -> its own name
        if (J.N(J.get(c, "isUnsafe")).t == J_TRUE) { T.skip = 1; H(HZ_NANODA_PARSE, off, "unsafe constructor (nanoda assert)"); }
        C.decls.push_back(T);
      }
      for (uint32_t i = 0; i < J.N(rs).b && !bad; i++) {
        uint32_t c = J.kids[J.N(rs).a + i];
        if (!J.exact_keys(c, {"all", "isUnsafe", "k", "levelParams", "name", "numIndices", "numMinors", "numMotives", "numParams", "rules", "type"})) { bad = true; break; }
        DeclRec T{};
        if (!basic(c, T, false)) { bad = true; break; }
        uint32_t ni = J.get(c, "numIndices"), nmi = J.get(c, "numMinors"), nmo = J.get(c, "numMotives"), np = J.get(c, "numParams"), ru = J.get(c, "rules");
        if (!isnum(J, ni) || !isnum(J, nmi) || !isnum(J, nmo) || !isnum(J, np) || !isbool(J, J.get(c, "k")) || !isbool(J, J.get(c, "isUnsafe")) || J.N(ru).t != J_ARR) { bad = true; break; }
        u16chk(ni, "numIndices"); u16chk(nmi, "numMinors"); u16chk(nmo, "numMotives"); u16chk(np, "numParams");
        for (uint32_t j = 0; j < J.N(ru).b; j++) {
          uint32_t rr = J.kids[J.N(ru).a + j];
          if (!J.exact_keys(rr, {"ctor", "nfields", "rhs"})) { bad = true; break; }
          uint32_t rc = J.get(rr, "ctor"), rn = J.get(rr, "nfields"), rh = J.get(rr, "rhs");
          if (!isnum(J, rc) || !isnum(J, rn) || !isnum(J, rh)) { bad = true; break; }
          ref_name(numv(rc), J.N(rc).big); ref_expr(numv(rh), J.N(rh).big); u16chk(rn, "rule nfields");
        }
        if (bad) break;
        T.kind = DK_REC;
        T.xbeg = (uint32_t)C.xnames.size();
        if (!namelist(J.get(c, "all"), &C.xnames)) { bad = true; break; }
        T.xcnt = (uint32_t)C.xnames.size() - T.xbeg;
        if (J.N(J.get(c, "isUnsafe")).t == J_TRUE) { T.skip = 1; H(HZ_NANODA_PARSE, off, "unsafe recursor (nanoda assert)"); }
        C.decls.push_back(T);
      }
      if (bad) { H(HZ_MALFORMED, off, "inductive member fields"); continue; }
    } else {
      H(HZ_MALFORMED, off, "unknown declaration kind " + key);
    }
  }
}

// ------------------------------------------------------------------------------------------------ small hash set
struct U32Set {
  std::vector<uint32_t> tab; std::vector<uint32_t> used; uint32_t mask = 0; size_t n = 0;
  void init(size_t cap) { size_t c = 1; while (c < cap * 2) c <<= 1; tab.assign(c, NONE); mask = (uint32_t)(c - 1); used.clear(); n = 0; }
  void clear() { if (used.size() > tab.size() / 4) std::fill(tab.begin(), tab.end(), NONE); else for (uint32_t s : used) tab[s] = NONE; used.clear(); n = 0; }
  bool insert(uint32_t k) {
    if ((n + 1) * 2 > tab.size()) grow();
    uint32_t s = (uint32_t)(mix64(k) & mask);
    while (true) { uint32_t v = tab[s]; if (v == k) return false; if (v == NONE) { tab[s] = k; used.push_back(s); n++; return true; } s = (s + 1) & mask; }
  }
  void grow() {
    std::vector<uint32_t> keys; keys.reserve(n); for (uint32_t s : used) keys.push_back(tab[s]);
    size_t c = tab.size() * 2; tab.assign(c, NONE); mask = (uint32_t)(c - 1); used.clear(); n = 0;
    for (uint32_t k : keys) insert(k);
  }
};

// ------------------------------------------------------------------------------------------------ main
static double now_s() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

static void usage() {
  fprintf(stderr,
    "usage: prechk [options] EXPORT.ndjson\n"
    "  --threads N          worker threads (default: all online CPUs)\n"
    "  --json FILE          write a machine-readable report\n"
    "  --no-nanoda          the project's comparator config runs no nanoda kernel: report nanoda_* hazards but do not count them\n"
    "  --ignore C1,C2       report but do not count these hazard classes\n"
    "  --nanoda-depth D     expression depth limit attributed to nanoda's 16 MiB stacks (default 32768)\n"
    "  --kernel-depth D     expression depth limit for the official Lean kernel / comparator (default 50000)\n"
    "  --walk-limit W       limit for the bound on the official replay walk depth (default 100000)\n"
    "  --no-replay          skip the dependency analysis (walk_depth/order_* then reported as budget)\n"
    "  --closure TARGETS    export guard: count only 'closure' (a target or a referenced constant is not declared:\n"
    "                       an official lean4export output is closed) and 'malformed'; TARGETS = names, whitespace-separated\n"
    "exit: 0 clean, 3 hazard(s) -> DECLINE, 4 malformed -> DECLINE, 2 usage/IO error -> DECLINE\n");
}

int main(int argc, char** argv) {
  for (int i = 0; i < NHZ; i++) O.counted[i] = true;
  const char* path = nullptr;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto need = [&]() -> const char* { if (i + 1 >= argc) { usage(); exit(2); } return argv[++i]; };
    if (a == "--threads") O.threads = atoi(need());
    else if (a == "--json") O.json = need();
    else if (a == "--no-nanoda") O.nanoda = false;
    else if (a == "--nanoda-depth") O.nanoda_depth = strtoull(need(), nullptr, 10);
    else if (a == "--kernel-depth") O.kernel_depth = strtoull(need(), nullptr, 10);
    else if (a == "--walk-limit") O.walk_limit = strtoull(need(), nullptr, 10);
    else if (a == "--no-replay") O.replay = false;
    else if (a == "--closure") O.closure = need();
    else if (a == "--ignore") {
      std::string s = need(); size_t p = 0;
      while (p <= s.size()) { size_t q = s.find(',', p); if (q == std::string::npos) q = s.size(); std::string c = s.substr(p, q - p);
        bool ok = false; for (int k = 0; k < NHZ; k++) if (c == HZ_NAME[k]) { O.counted[k] = false; ok = true; }
        if (!ok && !c.empty()) { fprintf(stderr, "prechk: unknown hazard class %s\n", c.c_str()); return 2; }
        p = q + 1; }
    }
    else if (a == "--version") { printf("%s\n", VERSION); return 0; }
    else if (a == "-h" || a == "--help") { usage(); return 2; }
    else if (!a.empty() && a[0] == '-') { fprintf(stderr, "prechk: unknown option %s\n", a.c_str()); usage(); return 2; }
    else if (!path) path = argv[i];
    else { usage(); return 2; }
  }
  if (!path) { usage(); return 2; }
  if (!O.nanoda) { O.counted[HZ_NANODA_PARSE] = O.counted[HZ_NANODA_PROJ] = O.counted[HZ_NANODA_DEPTH] = false; }
  if (O.closure) { for (int k = 0; k < NHZ; k++) O.counted[k] = (k == HZ_CLOSURE || k == HZ_MALFORMED); }
  else O.counted[HZ_CLOSURE] = false;
  if (O.threads <= 0) O.threads = (int)std::max(1u, std::thread::hardware_concurrency());
  double t0 = now_s();

  // ---- open + mmap (regular file only)
  int fd = open(path, O_RDONLY);
  if (fd < 0) { fprintf(stderr, "prechk: cannot open %s: %s\n", path, strerror(errno)); return 2; }
  struct stat st; if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) { fprintf(stderr, "prechk: %s is not a regular file\n", path); return 2; }
  uint64_t size = (uint64_t)st.st_size;
  if (size == 0) { fprintf(stderr, "prechk: empty export\n"); return 4; }
  const char* base = (const char*)mmap(nullptr, size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (base == MAP_FAILED) { fprintf(stderr, "prechk: mmap failed: %s\n", strerror(errno)); return 2; }
  madvise((void*)base, size, MADV_SEQUENTIAL);
  G_BASE = base;
  HazSink G;   // global (non-chunk) hazards

  // ---- meta line (official parser skips line 1 entirely; nanoda checks format version 3.1.0 <= v < 3.2.0)
  const char* nl0 = (const char*)memchr(base, '\n', size);
  uint64_t body = nl0 ? (uint64_t)(nl0 - base) + 1 : size;
  std::string meta_version;
  {
    JParser J; uint32_t r; const char* le = nl0 ? nl0 : base + size;
    bool ok = J.parse(base, le, r) && J.N(r).t == J_OBJ && J.N(r).b == 1 && J.get(r, "meta") != NONE;
    if (ok) {
      uint32_t m = J.get(r, "meta"); uint32_t f = J.N(m).t == J_OBJ ? J.get(m, "format") : NONE;
      uint32_t v = (f != NONE && J.N(f).t == J_OBJ) ? J.get(f, "version") : NONE;
      if (v != NONE && J.N(v).t == J_STR) meta_version = jdecode(J.N(v));
      else ok = false;
    }
    if (!ok) G.add(HZ_MALFORMED, -1, 0, 0, "line 1 is not a lean4export meta record (the official parser skips line 1 unread)");
    else {
      unsigned a = 0, b = 0, c = 0; char tail;
      if (sscanf(meta_version.c_str(), "%u.%u.%u%c", &a, &b, &c, &tail) != 3 || !(a == 3 && b == 1))
        G.add(HZ_NANODA_PARSE, -1, 0, 0, "export format version " + meta_version + " outside nanoda's [3.1.0, 3.2.0)");
    }
  }

  // ---- chunking
  int nch = std::max(1, O.threads * 8);
  uint64_t bodylen = size - body;
  if (bodylen < (uint64_t)nch * 4096) nch = std::max<uint64_t>(1, bodylen / 4096 + 1);
  std::vector<Chunk> ch(nch);
  {
    uint64_t prev = body;
    for (int i = 0; i < nch; i++) {
      uint64_t e = (i == nch - 1) ? size : body + bodylen * (uint64_t)(i + 1) / nch;
      if (e < prev) e = prev;
      if (i != nch - 1) { const char* q = (const char*)memchr(base + e, '\n', size - e); e = q ? (uint64_t)(q - base) + 1 : size; }
      ch[i].id = i; ch[i].beg = prev; ch[i].end = e; prev = e;
    }
  }
  {
    std::atomic<int> next{0};
    std::vector<std::thread> th;
    for (int t = 0; t < O.threads; t++) th.emplace_back([&]() { int i; while ((i = next.fetch_add(1)) < nch) { process_chunk(ch[i]);
      // drop the consumed file pages from this process (clean, file-backed: a later read faults them in from the page cache)
      uint64_t pb = (ch[i].beg + 4095) & ~4095ull, pe = ch[i].end & ~4095ull; if (pe > pb) madvise((void*)(base + pb), pe - pb, MADV_DONTNEED); } });
    for (auto& x : th) x.join();
  }
  double t1 = now_s();
  madvise((void*)base, size, MADV_DONTNEED);

  // ---- line numbers
  std::vector<uint64_t> line_base(nch);
  { uint64_t lb = 2; for (int i = 0; i < nch; i++) { line_base[i] = lb; lb += ch[i].nlines; } }
  uint64_t nlines = 1; for (auto& c : ch) nlines += c.nlines;

  // ---- contiguity + reference validity (skipped when a line is already malformed: the counts are then shifted and
  //      every later reference would be reported; the export is declined anyway)
  bool lineMalformed = G.count[HZ_MALFORMED] > 0; for (auto& c : ch) if (c.hz.count[HZ_MALFORMED]) lineMalformed = true;
  bool contiguous = !lineMalformed, refsOk = true;
  uint64_t NN = 1, NL = 1, NE = 0;   // anonymous name 0 and level zero 0 are implicit
  for (int i = 0; i < nch; i++) {
    Chunk& c = ch[i];
    if (c.n_names) { if (!c.contig_name || c.first_name != (int64_t)NN) contiguous = false; }
    if (c.n_levels) { if (!c.contig_level || c.first_level != (int64_t)NL) contiguous = false; }
    if (c.n_exprs) { if (!c.contig_expr || c.first_expr != (int64_t)NE) contiguous = false; }
    if (lineMalformed) { NN += c.n_names; NL += c.n_levels; NE += c.n_exprs; continue; }
    if ((c.def_name != INT64_MIN && c.def_name >= (int64_t)NN) || (c.def_level != INT64_MIN && c.def_level >= (int64_t)NL) || (c.def_expr != INT64_MIN && c.def_expr >= (int64_t)NE)) refsOk = false;
    if (c.def_name != INT64_MIN && c.def_name >= (int64_t)NN) G.add(HZ_MALFORMED, i, c.beg, 0, "name reference to an index not defined before its use (chunk " + std::to_string(i) + ")");
    if (c.def_level != INT64_MIN && c.def_level >= (int64_t)NL) G.add(HZ_MALFORMED, i, c.beg, 0, "level reference to an index not defined before its use (chunk " + std::to_string(i) + ")");
    if (c.def_expr != INT64_MIN && c.def_expr >= (int64_t)NE) G.add(HZ_MALFORMED, i, c.beg, 0, "expr reference to an index not defined before its use (chunk " + std::to_string(i) + ")");
    NN += c.n_names; NL += c.n_levels; NE += c.n_exprs;
  }
  if (!contiguous && !lineMalformed) G.add(HZ_NANODA_PARSE, -1, 0, 0, "name/level/expr indices are not the contiguous sequence 1.. / 1.. / 0.. (nanoda: 'Back-refs must be continuous', exit 2); prechk analyses that need dense indices skipped");
  if (NE > 0xFFFFFFF0ull || NN > 0xFFFFFFF0ull) { G.add(HZ_NANODA_PARSE, -1, 0, 0, "more than 2^32 records of one kind (nanoda u32 indices)"); contiguous = false; }

  // stats
  uint64_t max_height = 0, max_name_num = 0, max_bvar = 0, max_proj_idx = 0, max_u16 = 0, n_nat = 0, n_str = 0, n_proj = 0, ndecl = 0;
  for (auto& c : ch) { max_height = std::max(max_height, c.max_height); max_name_num = std::max(max_name_num, c.max_name_num); max_bvar = std::max(max_bvar, c.max_bvar);
    max_proj_idx = std::max(max_proj_idx, c.max_proj_idx); max_u16 = std::max(max_u16, c.max_u16_field); n_nat += c.n_nat; n_str += c.n_str; n_proj += c.n_proj; ndecl += c.decls.size(); }

  uint64_t max_ldepth = 0, max_edepth = 0, max_bdepth = 0, walk_bound = 0, n_consts = 0, n_nodes = 0, n_edges = 0, visits = 0;
  uint64_t n_dup_checked = 0, n_order_conservative = 0, n_order_exact = 0, walk_exact = 0; bool replay_exact = false; std::string sim_error; uint64_t n_closure_targets = 0;
  double t_dup = 0, t_depth = 0, t_replay = 0;
  bool replay_done = false;

  if (contiguous && refsOk) {
    // ---- duplicates (exact: hash candidates verified by canonical content)
    double td = now_s();
    auto dupcheck = [&](std::vector<DupRec> Chunk::*field, const char* what) {
      // radix partition by the top 12 hash bits (parallel count + scatter, chunk vectors freed as they are consumed),
      // then every bucket is sorted and scanned independently. Equal-hash candidates are verified on the decoded content.
      const int BB = 12, NB = 1 << BB; int T = O.threads;
      std::vector<std::vector<uint64_t>> cnt(nch, std::vector<uint64_t>(NB, 0));
      { std::atomic<int> nx{0}; std::vector<std::thread> th;
        for (int t = 0; t < T; t++) th.emplace_back([&]() { int c; while ((c = nx.fetch_add(1)) < nch) for (auto& r : ch[c].*field) cnt[c][r.h >> (64 - BB)]++; });
        for (auto& x : th) x.join(); }
      std::vector<uint64_t> bstart(NB + 1, 0);
      std::vector<std::vector<uint64_t>> pos(nch, std::vector<uint64_t>(NB, 0));
      { uint64_t acc = 0; for (int b = 0; b < NB; b++) { bstart[b] = acc; for (int c = 0; c < nch; c++) { pos[c][b] = acc; acc += cnt[c][b]; } } bstart[NB] = acc; }
      std::vector<DupRec> all(bstart[NB]);
      { std::atomic<int> nx{0}; std::vector<std::thread> th;
        for (int t = 0; t < T; t++) th.emplace_back([&]() { int c; while ((c = nx.fetch_add(1)) < nch) {
          auto& v = ch[c].*field; auto& P = pos[c]; for (auto& r : v) all[P[r.h >> (64 - BB)]++] = r; std::vector<DupRec>().swap(v); } });
        for (auto& x : th) x.join(); }
      std::mutex mu; std::vector<std::pair<uint64_t, uint64_t>> dups; std::atomic<uint64_t> checked{0}; std::atomic<bool> toomany{false};
      { std::atomic<int> nx{0}; std::vector<std::thread> th;
        for (int t = 0; t < T; t++) th.emplace_back([&]() {
          std::string k1, k2; int b;
          auto line = [&](uint64_t off, const char*& lb, const char*& le) { lb = base + off; const char* q = (const char*)memchr(lb, '\n', size - off); le = q ? q : base + size; };
          while ((b = nx.fetch_add(1)) < NB) {
            DupRec* B0 = all.data() + bstart[b]; DupRec* B1 = all.data() + bstart[b + 1];
            std::sort(B0, B1, [](const DupRec& x, const DupRec& y) { return x.h < y.h || (x.h == y.h && x.off < y.off); });
            for (DupRec* i = B0; i < B1; ) {
              DupRec* j = i + 1; while (j < B1 && j->h == i->h) j++;
              if (j - i > 1) {
                if (j - i > 16) toomany = true;          // bounded work: a long equal-hash run is declined (budget)
                DupRec* lim = std::min(j, i + 16);
                bool found = false;
                for (DupRec* x = i; x < lim && !found; x++) for (DupRec* y = x + 1; y < lim && !found; y++) {
                  checked++;
                  const char *b1, *e1, *b2, *e2; line(x->off, b1, e1); line(y->off, b2, e2);
                  if (canon_key(b1, e1, k1) && canon_key(b2, e2, k2) && k1 == k2) { std::lock_guard<std::mutex> g(mu); dups.push_back({x->off, y->off}); found = true; }
                }
              }
              i = j;
            }
          }
        });
        for (auto& x : th) x.join(); }
      n_dup_checked += checked.load();
      std::sort(dups.begin(), dups.end());
      for (auto& d : dups) G.add(HZ_NANODA_PARSE, -1, d.second, 0, std::string("duplicate ") + what + " record (same content at byte offsets " + std::to_string(d.first) + " and " + std::to_string(d.second) + "): nanoda 'Attempted to insert duplicate' panic (finding 024)");
      if (toomany) G.add(HZ_BUDGET, -1, 0, 0, std::string("more than 16 ") + what + " records share one 64-bit content hash: duplicate analysis bounded, cannot exclude duplicates");
    };
    dupcheck(&Chunk::dn, "name"); dupcheck(&Chunk::dl, "level"); dupcheck(&Chunk::de, "expr");
    t_dup = now_s() - td;

    // ---- global arrays
    double tdep = now_s();
    std::vector<uint8_t> lk; std::vector<uint32_t> la, lb;
    lk.reserve(NL); la.reserve(NL); lb.reserve(NL); lk.push_back(0); la.push_back(NONE); lb.push_back(NONE);
    for (auto& c : ch) { lk.insert(lk.end(), c.lk.begin(), c.lk.end()); la.insert(la.end(), c.la.begin(), c.la.end()); lb.insert(lb.end(), c.lb.begin(), c.lb.end());
      std::vector<uint8_t>().swap(c.lk); std::vector<uint32_t>().swap(c.la); std::vector<uint32_t>().swap(c.lb); }
    // level depth (official: zero/param 0, succ +1, max/imax max+1; > 16777215 -> internal panic)
    {
      std::vector<uint32_t> ld(NL, 0);
      for (uint64_t i = 1; i < NL; i++) {
        uint64_t d = 0;
        switch (lk[i]) {
          case LK_SUCC: d = (uint64_t)ld[la[i]] + 1; break;
          case LK_MAX: case LK_IMAX: d = (uint64_t)std::max(ld[la[i]], ld[lb[i]]) + 1; break;
          default: d = 0;
        }
        if (d > 0xFFFFFFF0ull) d = 0xFFFFFFF0ull;
        ld[i] = (uint32_t)d; if (d > max_ldepth) max_ldepth = d;
        if (d > 16777215 && G.count[HZ_PARSER_ABORT] < 1000000) G.add(HZ_PARSER_ABORT, -1, 0, 0, "level index " + std::to_string(i) + " has depth " + std::to_string(d) + " > 16777215 -> official Level.mkData internal panic (finding 044)");
      }
    }
    // exprs: global arrays filled in parallel from the chunk vectors
    std::vector<uint64_t> ebase(nch + 1, 0); for (int i = 0; i < nch; i++) ebase[i + 1] = ebase[i] + ch[i].n_exprs;
    V8 ek(NE); V32 ea(NE), eb(NE);
    std::vector<std::pair<uint32_t, uint32_t>> letb;
    for (int i = 0; i < nch; i++) for (auto& p : ch[i].letb) letb.push_back({(uint32_t)(ebase[i] + p.first), p.second});   // already sorted
    { std::atomic<int> nx{0}; std::vector<std::thread> th;
      for (int t = 0; t < O.threads; t++) th.emplace_back([&]() { int i; while ((i = nx.fetch_add(1)) < nch) { Chunk& c = ch[i];
        if (c.n_exprs) { memcpy(&ek[ebase[i]], c.ek.data(), c.n_exprs); memcpy(&ea[ebase[i]], c.ea.data(), 4 * c.n_exprs); memcpy(&eb[ebase[i]], c.eb.data(), 4 * c.n_exprs); }
        std::vector<uint8_t>().swap(c.ek); std::vector<uint32_t>().swap(c.ea); std::vector<uint32_t>().swap(c.eb); std::vector<std::pair<uint32_t, uint32_t>>().swap(c.letb); } });
      for (auto& x : th) x.join(); }
    // special names
    uint32_t nQuot = NONE, nQmk = NONE, nQlift = NONE, nQind = NONE, nString = NONE, nSofList = NONE, nChar = NONE, nCofNat = NONE, nNat = NONE, nEq = NONE;
    {
      std::vector<SpecialName> sp; for (auto& c : ch) sp.insert(sp.end(), c.specials.begin(), c.specials.end());
      for (auto& s : sp) if (s.pre == 0) { if (s.comp == SC_Quot) nQuot = s.idx; if (s.comp == SC_String) nString = s.idx; if (s.comp == SC_Char) nChar = s.idx; if (s.comp == SC_Nat) nNat = s.idx; if (s.comp == SC_Eq) nEq = s.idx; }
      for (auto& s : sp) {
        if (nQuot != NONE && s.pre == nQuot) { if (s.comp == SC_mk) nQmk = s.idx; if (s.comp == SC_lift) nQlift = s.idx; if (s.comp == SC_ind) nQind = s.idx; }
        if (nString != NONE && s.pre == nString && s.comp == SC_ofList) nSofList = s.idx;
        if (nChar != NONE && s.pre == nChar && s.comp == SC_ofNat) nCofNat = s.idx;
      }
    }
    // bottom-up pass: depth, binder depth, flags (bit0 strlit, bit1 natlit, bit2 uses Quot.mk/lift/ind).
    // Parallel over chunks in file order; dep[x] != 0 marks x as computed (depth >= 1), a child in an earlier chunk that
    // is not computed yet is awaited (the lowest unfinished chunk never waits, so this always progresses).
    V32 dep(NE), bdep(NE); V8 fl(NE);
    {
      { std::atomic<int> nx{0}; std::vector<std::thread> th;
        for (int t = 0; t < O.threads; t++) th.emplace_back([&]() { int i; while ((i = nx.fetch_add(1)) < nch) if (ch[i].n_exprs) memset(&dep[ebase[i]], 0, 4 * ch[i].n_exprs); });
        for (auto& x : th) x.join(); }
      std::atomic<int> nx{0}; std::mutex mu; std::vector<std::thread> th;
      for (int t = 0; t < O.threads; t++) th.emplace_back([&]() {
        uint64_t mx = 0, mb = 0; int c;
        auto get = [&](uint32_t x) -> uint32_t { uint32_t d; unsigned spins = 0;
          while ((d = __atomic_load_n(&dep[x], __ATOMIC_ACQUIRE)) == 0) { if (++spins > 64) { std::this_thread::yield(); spins = 0; } else __builtin_ia32_pause(); }
          return d; };
        while ((c = nx.fetch_add(1)) < nch) {
          size_t li = std::lower_bound(letb.begin(), letb.end(), std::make_pair((uint32_t)ebase[c], 0u)) - letb.begin();
          for (uint64_t i = ebase[c]; i < ebase[c + 1]; i++) {
            uint64_t d = 1, bd = 0; uint8_t f = 0;
            uint32_t a = ea[i], b = eb[i];
            switch (ek[i]) {
              case EK_APP: { uint32_t da = get(a), db = get(b); d = 1 + (uint64_t)std::max(da, db); bd = std::max(bdep[a], bdep[b]); f = fl[a] | fl[b]; break; }
              case EK_LAM: case EK_PI: { uint32_t da = get(a), db = get(b); d = 1 + (uint64_t)std::max(da, db); bd = std::max<uint64_t>(bdep[a], (uint64_t)bdep[b] + 1); f = fl[a] | fl[b]; break; }
              case EK_LET: { while (li < letb.size() && letb[li].first < i) li++; uint32_t cc = (li < letb.size() && letb[li].first == i) ? letb[li].second : 0;
                uint32_t da = get(a), db = get(b), dc = get(cc);
                d = 1 + (uint64_t)std::max(std::max(da, db), dc); bd = std::max<uint64_t>(std::max(bdep[a], bdep[b]), (uint64_t)bdep[cc] + 1); f = fl[a] | fl[b] | fl[cc]; break; }
              case EK_PROJ: case EK_MDATA: { uint32_t da = get(a); d = 1 + (uint64_t)da; bd = bdep[a]; f = fl[a]; break; }
              case EK_STR: f = 1; break;
              case EK_NAT: f = 2; break;
              case EK_CONST: if (a != NONE && (a == nQmk || a == nQlift || a == nQind)) f = 4; break;
              default: break;
            }
            if (d > 0xFFFFFFF0ull) d = 0xFFFFFFF0ull;
            if (bd > 0xFFFFFFF0ull) bd = 0xFFFFFFF0ull;
            bdep[i] = (uint32_t)bd; fl[i] = f; __atomic_store_n(&dep[i], (uint32_t)d, __ATOMIC_RELEASE);
            if (d > mx) mx = d;
            if (bd > mb) mb = bd;
          }
        }
        std::lock_guard<std::mutex> g(mu); if (mx > max_edepth) max_edepth = mx; if (mb > max_bdepth) max_bdepth = mb;
      });
      for (auto& x : th) x.join();
    }
    if (max_edepth > O.nanoda_depth) G.add(HZ_NANODA_DEPTH, -1, 0, 0, "max expression depth " + std::to_string(max_edepth) + " > " + std::to_string(O.nanoda_depth) + " (official nanoda 16 MiB worker stacks may overflow, finding 047)");
    if (max_bdepth > 65535) G.add(HZ_NANODA_DEPTH, -1, 0, 0, "binder nesting " + std::to_string(max_bdepth) + " > 65535 (nanoda u16 de Bruijn level counter)");
    if (max_edepth > O.kernel_depth) G.add(HZ_KERNEL_DEPTH, -1, 0, 0, "max expression depth " + std::to_string(max_edepth) + " > " + std::to_string(O.kernel_depth) + " (official Lean kernel / comparator recursion)");
    t_depth = now_s() - tdep;

    // ---- constants
    double tr = now_s();
    std::vector<DeclRec> D; std::vector<uint32_t> X;
    for (auto& c : ch) { uint32_t xb = (uint32_t)X.size(); for (auto r : c.decls) { r.xbeg += xb; D.push_back(r); } X.insert(X.end(), c.xnames.begin(), c.xnames.end());
      std::vector<DeclRec>().swap(c.decls); std::vector<uint32_t>().swap(c.xnames); }
    n_consts = D.size();
    std::vector<uint32_t> n2c(NN, NONE);
    for (uint32_t i = 0; i < D.size(); i++) {
      if (D[i].name >= NN) continue;
      if (n2c[D[i].name] != NONE) G.add(HZ_MALFORMED, -1, D[i].off, 0, std::string("duplicate declaration of a ") + DK_NAME[D[i].kind] + " name (official parser: 'Duplicate declaration')");
      else n2c[D[i].name] = i;
    }
    // nanoda 056: Expr.proj whose typeName is an inductive with indices or != 1 ctor
    for (auto& c : ch) for (auto& p : c.projs) {
      uint32_t ci = p.first < NN ? n2c[p.first] : NONE;
      if (ci != NONE && D[ci].kind == DK_IND && D[ci].aux) c.hz.add(HZ_NANODA_PROJ, c.id, p.second, 0, "Expr.proj on an inductive with indices or != 1 constructor: nanoda infer_proj get_structure().unwrap() panics (finding 056)");
    }
    // ---- closure guard (--closure): every target and every constant referenced by an exported record is declared
    if (O.closure) {
      uint64_t dangling = 0;
      auto need = [&](uint32_t n, uint64_t off, const std::string& what) {
        if (n < NN && n2c[n] != NONE) return;
        if (dangling++ < 100000) G.add(HZ_CLOSURE, -1, off, 0, what + " refers to a constant that is not declared in the export (official lean4export output is closed)");
      };
      for (uint64_t i = 0; i < NE; i++) { if (ek[i] == EK_CONST) need(ea[i], 0, "expr " + std::to_string(i) + " (const)"); else if (ek[i] == EK_PROJ) need(eb[i], 0, "expr " + std::to_string(i) + " (proj typeName)"); }
      for (auto& d : D) {
        for (uint32_t k = 0; k < d.xcnt + d.xall; k++) need(X[d.xbeg + k], d.off, std::string(DK_NAME[d.kind]) + " (ctors/all)");
        if (d.kind == DK_CTOR) need(d.aux, d.off, "constructor (induct)");
      }
      // targets: Lean name syntax (components split at '.', «» escapes, all-digit components are numbers), matched via Lean's Name.hash
      std::vector<uint8_t> nkg(NN, 0); std::vector<uint32_t> npg(NN, 0); std::vector<uint64_t> ncg(NN, 0), nog(NN, 0), NH(NN, 1723);
      bool namesOk = true;
      { uint64_t k = 1; for (auto& c : ch) { if (c.nk.size() != c.n_names) { namesOk = false; break; }
          for (size_t i = 0; i < c.nk.size(); i++, k++) { nkg[k] = c.nk[i]; npg[k] = c.npre[i]; ncg[k] = c.ncomp[i]; nog[k] = c.noff[i]; } }
        if (k != NN) namesOk = false; }
      for (uint64_t i = 1; i < NN && namesOk; i++) { if (npg[i] >= i) { namesOk = false; break; } NH[i] = lean_mix_hash(NH[npg[i]], ncg[i]); }
      std::string tf; { FILE* f = fopen(O.closure, "rb"); if (!f) { fprintf(stderr, "prechk: cannot read targets %s\n", O.closure); return 2; }
        char buf[65536]; size_t r; while ((r = fread(buf, 1, sizeof buf, f)) > 0) tf.append(buf, r); fclose(f); }
      std::vector<std::vector<std::pair<int, std::string>>> targets;   // components: (1 str | 2 num, text)
      { size_t i = 0; while (i < tf.size()) {
          while (i < tf.size() && isspace((unsigned char)tf[i])) i++;
          if (i >= tf.size()) break;
          std::vector<std::pair<int, std::string>> comps; std::string cur; bool esc = false, wasEsc = false;
          while (i < tf.size() && (esc || !isspace((unsigned char)tf[i]))) {
            if (!esc && tf.compare(i, 2, "\xc2\xab") == 0) { esc = true; wasEsc = true; i += 2; continue; }      // «
            if (esc && tf.compare(i, 2, "\xc2\xbb") == 0) { esc = false; i += 2; continue; }                    // »
            if (!esc && tf[i] == '.') { bool num = !wasEsc && !cur.empty() && cur.find_first_not_of("0123456789") == std::string::npos; comps.push_back({num ? 2 : 1, cur}); cur.clear(); wasEsc = false; i++; continue; }
            cur += tf[i++];
          }
          bool num = !wasEsc && !cur.empty() && cur.find_first_not_of("0123456789") == std::string::npos; comps.push_back({num ? 2 : 1, cur});
          targets.push_back(comps);
        } }
      auto comp_of = [&](uint32_t n, std::string& out) {
        const char* b = base + nog[n]; const char* q = (const char*)memchr(b, '\n', size - nog[n]); const char* e = q ? q : base + size;
        JParser J; uint32_t r; out.clear(); if (!J.parse(b, e, r)) return;
        uint32_t v = J.get(r, nkg[n] == 1 ? "str" : "num"); if (v == NONE) return;
        uint32_t x = J.get(v, nkg[n] == 1 ? "str" : "i"); if (x == NONE) return;
        if (nkg[n] == 1) out = jdecode(J.N(x)); else out.assign(J.N(x).p, J.N(x).len);
      };
      for (auto& t : targets) {
        uint64_t h = 1723; bool hashable = true;
        for (auto& c : t) {
          if (c.first == 1) h = lean_mix_hash(h, lean_murmur64a(c.second.data(), c.second.size(), 11));
          else { if (c.second.size() > 19) hashable = false; uint64_t v = 0; for (char ch2 : c.second) v = v * 10 + (ch2 - '0'); h = lean_mix_hash(h, (c.second.size() > 20) ? 17 : v); }
        }
        std::string tname; for (auto& c : t) { if (!tname.empty()) tname += '.'; tname += c.second; }
        bool found = false;
        if (namesOk && hashable) for (uint32_t n = 1; n < NN && !found; n++) {
          if (NH[n] != h) continue;
          // verify the component chain exactly
          uint32_t m = n; bool ok = true; std::string cs;
          for (size_t k = t.size(); k-- > 0;) { if (m == 0 || nkg[m] != t[k].first) { ok = false; break; } comp_of(m, cs); if (cs != t[k].second) { ok = false; break; } m = npg[m]; }
          if (ok && m == 0 && n2c[n] != NONE) found = true;
        }
        if (!found) G.add(HZ_CLOSURE, -1, 0, 0, "target " + tname + " is not declared in the export");
      }
      n_closure_targets = targets.size();
    }
    // ---- replay graph (Lean/Replay.lean 4.36 order semantics, conservative)
    if (O.replay) {
      // node set = constants replayed: not unsafe/partial, not Quot.mk/lift/ind (erased by checkExport)
      std::vector<uint8_t> isnode(D.size(), 0);
      for (uint32_t i = 0; i < D.size(); i++) isnode[i] = !D[i].skip && D[i].name != nQmk && D[i].name != nQlift && D[i].name != nQind;
      std::vector<std::vector<uint32_t>> adjT(O.threads); std::vector<std::vector<uint64_t>> adjOffT(O.threads);
      std::vector<uint32_t> deg(D.size() + 1, 0);
      std::vector<uint32_t> adjAll; std::vector<uint64_t> start(D.size() + 1, 0);
      // per-thread DFS; results stored per decl as (thread, offset, count)
      std::vector<uint32_t> owner(D.size(), 0); std::vector<uint64_t> offs(D.size(), 0);
      std::vector<uint32_t> simdeg(D.size(), 0);   // length of getUsedConstantsAsSet within the list (quot's extra Eq edge excluded)
      std::atomic<uint32_t> next{0}; std::atomic<uint64_t> totvis{0}; std::atomic<bool> over{false};
      uint64_t budget = (uint64_t)(O.visit_budget * (double)NE) + 100000000ull;
      {
        std::vector<std::thread> th;
        for (int t = 0; t < O.threads; t++) th.emplace_back([&, t]() {
          U32Set vis; vis.init(1024); std::vector<uint32_t> stk; std::vector<uint32_t> found; U32Set fset; fset.init(64);
          uint64_t myvis = 0;
          while (true) {
            uint32_t i0 = next.fetch_add(64); if (i0 >= D.size() || over.load(std::memory_order_relaxed)) break;
            for (uint32_t i = i0; i < std::min<uint32_t>(i0 + 64, (uint32_t)D.size()); i++) {
              if (!isnode[i]) continue;
              vis.clear(); fset.clear(); found.clear(); stk.clear();
              stk.push_back(D[i].type); if (D[i].value != NONE) stk.push_back(D[i].value);
              while (!stk.empty()) {
                uint32_t e = stk.back(); stk.pop_back();
                if (e >= NE || !vis.insert(e)) continue;
                myvis++;
                switch (ek[e]) {
                  case EK_APP: case EK_LAM: case EK_PI: stk.push_back(ea[e]); stk.push_back(eb[e]); break;
                  case EK_LET: { stk.push_back(ea[e]); stk.push_back(eb[e]);
                    auto it = std::lower_bound(letb.begin(), letb.end(), std::make_pair(e, 0u)); if (it != letb.end() && it->first == e) stk.push_back(it->second); break; }
                  case EK_MDATA: stk.push_back(ea[e]); break;
                  case EK_PROJ: {   // Lean's foldConsts counts a projection's typeName as a used constant (FoldConsts.lean)
                    stk.push_back(ea[e]); uint32_t n = eb[e]; if (n < NN) { uint32_t c = n2c[n]; if (c != NONE && isnode[c] && fset.insert(c)) found.push_back(c); } break; }
                  case EK_CONST: { uint32_t n = ea[e]; if (n < NN) { uint32_t c = n2c[n]; if (c != NONE && isnode[c] && fset.insert(c)) found.push_back(c); } break; }
                  default: break;
                }
              }
              for (uint32_t k = 0; k < D[i].xcnt; k++) { uint32_t n = X[D[i].xbeg + k]; if (n < NN) { uint32_t c = n2c[n]; if (c != NONE && isnode[c] && fset.insert(c)) found.push_back(c); } }
              simdeg[i] = (uint32_t)found.size();
              if (D[i].kind == DK_QUOT && nEq != NONE && n2c[nEq] != NONE && isnode[n2c[nEq]] && fset.insert(n2c[nEq])) found.push_back(n2c[nEq]);
              owner[i] = t; offs[i] = adjT[t].size(); deg[i] = (uint32_t)found.size();
              adjT[t].insert(adjT[t].end(), found.begin(), found.end());
              if (myvis > 1000000) { if (totvis.fetch_add(myvis) + myvis > budget) over = true; myvis = 0; }
            }
          }
          totvis.fetch_add(myvis);
        });
        for (auto& x : th) x.join();
      }
      visits = totvis.load();
      if (over) {
        G.add(HZ_BUDGET, -1, 0, 0, "dependency analysis exceeded its visit budget (" + std::to_string(budget) + " expr visits); walk_depth/order hazards cannot be excluded");
      } else {
        replay_done = true;
        // CSR
        for (uint32_t i = 0; i < D.size(); i++) start[i + 1] = start[i] + (isnode[i] ? deg[i] : 0);
        n_edges = start[D.size()];
        adjAll.resize(n_edges);
        for (uint32_t i = 0; i < D.size(); i++) if (isnode[i] && deg[i]) memcpy(&adjAll[start[i]], &adjT[owner[i]][offs[i]], deg[i] * sizeof(uint32_t));
        for (auto& v : adjT) std::vector<uint32_t>().swap(v);
        for (uint32_t i = 0; i < D.size(); i++) n_nodes += isnode[i];
        // walk graph = dependency graph + (inductive -> constructors of every member of its mutual block): Lean.Replay's
        // inductive branch replays the used constants of the constructors of ALL block members before addDecl.
        std::vector<uint64_t> wstart(D.size() + 1, 0); std::vector<uint32_t> wadj;
        {
          std::vector<uint32_t> extra;
          for (uint32_t i = 0; i < D.size(); i++) {
            for (uint64_t e = start[i]; e < start[i + 1]; e++) wadj.push_back(adjAll[e]);
            if (isnode[i] && D[i].kind == DK_IND) {
              for (uint32_t k = 0; k < D[i].xall; k++) {
                uint32_t m = X[D[i].xbeg + D[i].xcnt + k]; uint32_t mc = m < NN ? n2c[m] : NONE;
                if (mc == NONE || D[mc].kind != DK_IND) continue;
                for (uint32_t q = 0; q < D[mc].xcnt; q++) { uint32_t cn = X[D[mc].xbeg + q]; uint32_t c = cn < NN ? n2c[cn] : NONE; if (c != NONE && isnode[c]) wadj.push_back(c); }
              }
            }
            wstart[i + 1] = wadj.size();
          }
        }
        // ---- walk depth bound: longest path in the SCC condensation, SCCs weighted by size (iterative Tarjan)
        {
          uint32_t V = (uint32_t)D.size();
          std::vector<uint32_t> idx(V, NONE), low(V, 0), comp(V, NONE), lp_comp; std::vector<uint8_t> onst(V, 0);
          std::vector<uint32_t> S; std::vector<std::pair<uint32_t, uint64_t>> cs;
          uint32_t counter = 0, ncomp = 0;
          for (uint32_t r = 0; r < V; r++) {
            if (!isnode[r] || idx[r] != NONE) continue;
            cs.push_back({r, wstart[r]}); idx[r] = low[r] = counter++; S.push_back(r); onst[r] = 1;
            while (!cs.empty()) {
              uint32_t v = cs.back().first; uint64_t& it = cs.back().second;
              if (it < wstart[v + 1]) {
                uint32_t w = wadj[it++];
                if (idx[w] == NONE) { idx[w] = low[w] = counter++; S.push_back(w); onst[w] = 1; cs.push_back({w, wstart[w]}); }
                else if (onst[w]) low[v] = std::min(low[v], idx[w]);
              } else {
                if (low[v] == idx[v]) {
                  // pop SCC; its longest path = size + max over outgoing edges to finished SCCs
                  uint64_t sz = 0, best = 0; size_t k = S.size();
                  while (true) { uint32_t w = S[--k]; comp[w] = ncomp; onst[w] = 0; sz++; if (w == v) break; }
                  for (size_t q = k; q < S.size(); q++) { uint32_t w = S[q];
                    for (uint64_t e = wstart[w]; e < wstart[w + 1]; e++) { uint32_t u = wadj[e]; if (comp[u] != ncomp && comp[u] != NONE) best = std::max<uint64_t>(best, lp_comp[comp[u]]); } }
                  S.resize(k);
                  uint64_t lp = sz + best; lp_comp.push_back((uint32_t)std::min<uint64_t>(lp, 0xFFFFFFF0ull)); ncomp++;
                  if (lp > walk_bound) walk_bound = lp;
                }
                cs.pop_back();
                if (!cs.empty()) { uint32_t u = cs.back().first; low[u] = std::min(low[u], low[v]); }
              }
            }
          }
          if (walk_bound >= O.walk_limit) G.add(HZ_WALK_DEPTH, -1, 0, 0, "upper bound of the official replay walk depth " + std::to_string(walk_bound) + " >= " + std::to_string(O.walk_limit) + " (finding 051; measured official capacity ~3.7M levels with the default stack)");
        }
        // ---- order hazards: reverse reachability from Quot / String.ofList / Char.ofNat / Nat
        {
          uint32_t V = (uint32_t)D.size();
          std::vector<uint64_t> rstart(V + 1, 0); std::vector<uint32_t> radj(n_edges);
          for (uint32_t v = 0; v < V; v++) for (uint64_t e = start[v]; e < start[v + 1]; e++) rstart[adjAll[e] + 1]++;
          for (uint32_t v = 0; v < V; v++) rstart[v + 1] += rstart[v];
          { std::vector<uint64_t> pos(rstart.begin(), rstart.end() - 1);
            for (uint32_t v = 0; v < V; v++) for (uint64_t e = start[v]; e < start[v + 1]; e++) radj[pos[adjAll[e]]++] = v; }
          std::vector<uint8_t> reach(V, 0);   // bit0 Quot, bit1 String.ofList, bit2 Char.ofNat, bit3 Nat
          auto bfs = [&](uint32_t nameidx, uint8_t bit) {
            if (nameidx == NONE || nameidx >= NN) return; uint32_t s = n2c[nameidx]; if (s == NONE || !isnode[s]) return;
            std::vector<uint32_t> q{s}; reach[s] |= bit;
            while (!q.empty()) { uint32_t v = q.back(); q.pop_back(); for (uint64_t e = rstart[v]; e < rstart[v + 1]; e++) { uint32_t u = radj[e]; if (!(reach[u] & bit)) { reach[u] |= bit; q.push_back(u); } } }
          };
          bfs(nQuot, 1); bfs(nSofList, 2); bfs(nCofNat, 4); bfs(nNat, 8);
          struct OH { int cls; uint64_t off; std::string msg; };
          std::vector<OH> cons;   // conservative, order-independent (used if the exact simulation cannot run)
          for (uint32_t v = 0; v < V; v++) {
            if (!isnode[v] || D[v].kind == DK_REC) continue;   // recursors are generated by the kernel, not checked
            uint8_t f = fl[D[v].type < NE ? D[v].type : 0] | (D[v].value != NONE && D[v].value < NE ? fl[D[v].value] : 0);
            if ((f & 4) && !(reach[v] & 1)) cons.push_back({HZ_ORDER_QUOT, D[v].off, std::string(DK_NAME[D[v].kind]) + " uses Quot.mk/lift/ind but does not depend on Quot: the official replay may add it before Quot ('unknown constant')"});
            if ((f & 1) && (reach[v] & 6) != 6) cons.push_back({HZ_ORDER_STRLIT, D[v].off, std::string(DK_NAME[D[v].kind]) + " has a string literal but does not depend on String.ofList and Char.ofNat: the official replay may check it before them (finding 012)"});
            if ((f & 2) && !(reach[v] & 8)) cons.push_back({HZ_ORDER_NATLIT, D[v].off, std::string(DK_NAME[D[v].kind]) + " has a Nat literal but does not depend on Nat: the official replay may check it before Nat"});
          }
          n_order_conservative = cons.size();

          // ---- EXACT simulation of Lean 4.36 Lean.Replay (as run by leanchecker --from-export): NameSet order =
          //      Name.quickCmp (Name.hash, then quickCmpAux), deps = getUsedConstantsAsSet, inductive/quot branches,
          //      Quot.mk/lift/ind erased. A declaration is an order hazard iff it is checked while a constant the kernel
          //      needs implicitly is not yet added (Quot.* => definite; String.ofList/Char.ofNat for string literals,
          //      Nat for Nat literals => potential). Zero hazards here = the official replay order cannot matter.
          std::string simerr;
          std::vector<OH> exact;
          {
            // names: global arrays + Lean Name.hash
            std::vector<uint8_t> nkg(NN, 0); std::vector<uint32_t> npg(NN, 0); std::vector<uint64_t> ncg(NN, 0), nog(NN, 0), NH(NN, 1723);
            { uint64_t k = 1; bool ok = true;
              for (auto& c : ch) { if (c.nk.size() != c.n_names) { ok = false; break; }
                for (size_t i = 0; i < c.nk.size(); i++, k++) { nkg[k] = c.nk[i]; npg[k] = c.npre[i]; ncg[k] = c.ncomp[i]; nog[k] = c.noff[i]; } }
              if (!ok || k != NN) simerr = "name records incomplete"; }
            for (uint64_t i = 1; i < NN && simerr.empty(); i++) { if (npg[i] >= i) { simerr = "name prefix order"; break; } NH[i] = lean_mix_hash(NH[npg[i]], ncg[i]); }
            auto comp_of = [&](uint32_t n, std::string& out) {   // decoded component (string bytes, or decimal digits)
              const char* b = base + nog[n]; const char* q = (const char*)memchr(b, '\n', size - nog[n]); const char* e = q ? q : base + size;
              JParser J; uint32_t r; out.clear(); if (!J.parse(b, e, r)) return;
              uint32_t v = J.get(r, nkg[n] == 1 ? "str" : "num"); if (v == NONE) return;
              uint32_t x = J.get(v, nkg[n] == 1 ? "str" : "i"); if (x == NONE) return;
              if (nkg[n] == 1) out = jdecode(J.N(x)); else out.assign(J.N(x).p, J.N(x).len);
            };
            auto qcmp = [&](uint32_t a, uint32_t b) -> int {   // Name.quickCmp
              if (a == b) return 0;
              if (NH[a] != NH[b]) return NH[a] < NH[b] ? -1 : 1;
              std::string sa, sb;
              while (true) {   // quickCmpAux: last component first, then the prefixes
                if (a == 0 && b == 0) return 0;
                if (a == 0) return -1;
                if (b == 0) return 1;
                if (nkg[a] != nkg[b]) return nkg[a] == 2 ? -1 : 1;    // num < str
                comp_of(a, sa); comp_of(b, sb);
                int c;
                if (nkg[a] == 2) c = sa.size() != sb.size() ? (sa.size() < sb.size() ? -1 : 1) : sa.compare(sb);  // Nat compare (canonical digits)
                else c = sa.compare(sb);                                                                              // String compare = UTF-8 byte order
                if (c != 0) return c < 0 ? -1 : 1;
                a = npg[a]; b = npg[b];
              }
            };
            uint32_t V2 = (uint32_t)D.size();
            // used lists in NameSet order (in place: the reach analysis above does not depend on the order)
            if (simerr.empty()) {
              std::atomic<uint32_t> nx{0}; std::vector<std::thread> th;
              for (int t = 0; t < O.threads; t++) th.emplace_back([&]() { uint32_t i;
                while ((i = nx.fetch_add(256)) < V2) for (uint32_t v = i; v < std::min(V2, i + 256); v++) {
                  if (!isnode[v] || simdeg[v] < 2) continue;
                  std::sort(adjAll.begin() + start[v], adjAll.begin() + start[v] + simdeg[v], [&](uint32_t x, uint32_t y) { return qcmp(D[x].name, D[y].name) < 0; });
                } });
              for (auto& x : th) x.join();
            }
            std::vector<uint32_t> roots; for (uint32_t v = 0; v < V2; v++) if (isnode[v]) roots.push_back(v);
            if (simerr.empty()) std::sort(roots.begin(), roots.end(), [&](uint32_t x, uint32_t y) { return qcmp(D[x].name, D[y].name) < 0; });
            uint32_t cSof = (nSofList != NONE && nSofList < NN) ? n2c[nSofList] : NONE, cCof = (nCofNat != NONE && nCofNat < NN) ? n2c[nCofNat] : NONE;
            uint32_t cNat = (nNat != NONE && nNat < NN) ? n2c[nNat] : NONE, cEq = (nEq != NONE && nEq < NN) ? n2c[nEq] : NONE;
            std::vector<uint8_t> remaining(V2, 0), pending(V2, 0), added(V2, 0);
            for (uint32_t v = 0; v < V2; v++) remaining[v] = isnode[v];
            bool quotAdded = false;
            auto isAdded = [&](uint32_t c) { return c != NONE && added[c]; };
            auto check = [&](uint32_t v, uint8_t f) {
              if ((f & 4) && !quotAdded) exact.push_back({HZ_ORDER_QUOT, D[v].off, std::string(DK_NAME[D[v].kind]) + " uses Quot.mk/lift/ind and is checked before Quot is added in the official replay order: 'unknown constant' (definite)"});
              if ((f & 1) && !(isAdded(cSof) && isAdded(cCof))) exact.push_back({HZ_ORDER_STRLIT, D[v].off, std::string(DK_NAME[D[v].kind]) + " has a string literal and is checked before String.ofList/Char.ofNat are added in the official replay order (finding 012: rejected if the kernel expands the literal)"});
              if ((f & 2) && !isAdded(cNat)) exact.push_back({HZ_ORDER_NATLIT, D[v].off, std::string(DK_NAME[D[v].kind]) + " has a Nat literal and is checked before Nat is added in the official replay order"});
            };
            auto flagsOf = [&](uint32_t v) -> uint8_t { return fl[D[v].type] | (D[v].value != NONE ? fl[D[v].value] : 0); };
            struct Frame { uint32_t v; uint8_t ph; uint32_t i, j; uint64_t k; };
            std::vector<Frame> st; uint64_t maxd = 0;
            auto memberOf = [&](uint32_t v, uint32_t k) -> uint32_t { uint32_t m = X[D[v].xbeg + D[v].xcnt + k]; return m < NN ? n2c[m] : NONE; };
            auto enter = [&](uint32_t c) -> bool {   // replayConstant c: isTodo moves it to pending and pushes a frame
              if (c == NONE || !remaining[c]) return false;
              remaining[c] = 0; pending[c] = 1; st.push_back({c, 0, 0, 0, 0}); if (st.size() > maxd) maxd = st.size(); return true;
            };
            for (uint32_t r : roots) {
              if (!simerr.empty()) break;
              enter(r);
              while (!st.empty() && simerr.empty()) {
                Frame& F = st.back(); uint32_t v = F.v;
                if (F.ph == 0) {   // replayConstants (getUsedConstantsAsSet v)
                  bool pushed = false;
                  while (F.k < simdeg[v]) { uint32_t c = adjAll[start[v] + F.k++]; if (enter(c)) { pushed = true; break; } }
                  if (pushed) continue;
                  F.ph = 1; continue;
                }
                if (F.ph == 1) {   // main dispatch
                  if (!pending[v]) { st.pop_back(); continue; }
                  uint8_t k = D[v].kind;
                  if (k == DK_DEF || k == DK_THM || k == DK_AXIOM || k == DK_OPAQUE) { check(v, flagsOf(v)); added[v] = 1; pending[v] = 0; st.pop_back(); continue; }
                  if (k == DK_CTOR || k == DK_REC) { pending[v] = 0; st.pop_back(); continue; }
                  if (k == DK_QUOT) { F.ph = 3; enter(cEq); continue; }
                  if (k == DK_IND) {
                    for (uint32_t q = 0; q < D[v].xall; q++) { uint32_t m = memberOf(v, q); if (m == NONE || D[m].kind != DK_IND) { simerr = "inductive block member missing"; break; } remaining[m] = 0; pending[m] = 0; }
                    if (!simerr.empty()) break;
                    F.ph = 2; F.i = 0; F.j = 0; F.k = 0; continue;
                  }
                  simerr = "unknown kind"; break;
                }
                if (F.ph == 2) {   // inductive: replay the used constants of every constructor of every block member
                  bool pushed = false;
                  while (!pushed && F.i < D[v].xall) {
                    uint32_t m = memberOf(v, F.i);
                    if (F.j >= D[m].xcnt) { F.i++; F.j = 0; F.k = 0; continue; }
                    uint32_t cn = X[D[m].xbeg + F.j]; uint32_t c = cn < NN ? n2c[cn] : NONE;
                    if (c == NONE) { simerr = "constructor missing"; break; }
                    if (!isnode[c] || F.k >= simdeg[c]) { F.j++; F.k = 0; continue; }
                    uint32_t u = adjAll[start[c] + F.k++];
                    if (enter(u)) pushed = true;
                  }
                  if (pushed || !simerr.empty()) continue;
                  // addDecl (inductDecl): check the block, then types + constructors are in the environment
                  uint8_t f = 0;
                  for (uint32_t q = 0; q < D[v].xall; q++) { uint32_t m = memberOf(v, q); f |= fl[D[m].type];
                    for (uint32_t j = 0; j < D[m].xcnt; j++) { uint32_t cn = X[D[m].xbeg + j]; uint32_t c = cn < NN ? n2c[cn] : NONE; if (c != NONE) f |= fl[D[c].type]; } }
                  check(v, f);
                  for (uint32_t q = 0; q < D[v].xall; q++) { uint32_t m = memberOf(v, q); added[m] = 1;
                    for (uint32_t j = 0; j < D[m].xcnt; j++) { uint32_t cn = X[D[m].xbeg + j]; uint32_t c = cn < NN ? n2c[cn] : NONE; if (c != NONE) added[c] = 1; } }
                  pending[v] = 0; st.pop_back(); continue;
                }
                if (F.ph == 3) { quotAdded = true; added[v] = 1; pending[v] = 0; st.pop_back(); continue; }   // after replayConstant Eq
              }
            }
            if (simerr.empty()) { replay_exact = true; walk_exact = maxd; }
          }
          n_order_exact = exact.size();
          for (auto& h : (replay_exact ? exact : cons)) G.add(h.cls, -1, h.off, 0, h.msg);
          sim_error = simerr;   // not a hazard by itself: the conservative order hazards above are reported instead
        }
      }
    } else {
      G.add(HZ_BUDGET, -1, 0, 0, "--no-replay: walk_depth/order hazards not analysed");
    }
    t_replay = now_s() - tr;
  } else {
    G.add(HZ_BUDGET, -1, 0, 0, lineMalformed ? "malformed export: depth/duplicate/replay analyses skipped" : !refsOk ? "dangling references: depth/duplicate/replay analyses skipped" : "indices not dense: depth/duplicate/replay analyses skipped");
  }

  // ---- aggregate
  uint64_t cnt[NHZ] = {0}; std::vector<Example> exs[NHZ];
  auto take = [&](HazSink& s, int chunk) {
    for (int k = 0; k < NHZ; k++) { cnt[k] += s.count[k]; for (auto& e : s.ex[k]) if ((int)exs[k].size() < O.max_examples) { Example x = e; x.chunk = chunk; exs[k].push_back(x); } }
  };
  take(G, -1); for (int i = 0; i < nch; i++) take(ch[i].hz, i);
  auto lineof = [&](const Example& e) -> uint64_t {
    if (e.chunk >= 0 && e.lline) return line_base[e.chunk] + e.lline - 1;
    if (e.off == 0) return 0;
    // find chunk containing offset and count lines (examples only)
    for (int i = 0; i < nch; i++) if (e.off >= ch[i].beg && e.off < ch[i].end) {
      uint64_t l = line_base[i]; const char* p = base + ch[i].beg; const char* q = base + e.off;
      while (p < q) { const char* n = (const char*)memchr(p, '\n', q - p); if (!n) break; l++; p = n + 1; }
      return l; }
    return 0;
  };
  bool counted_any = false, malformed_counted = false;
  for (int k = 0; k < NHZ; k++) if (cnt[k] && O.counted[k]) { counted_any = true; if (k == HZ_MALFORMED) malformed_counted = true; }
  int rc = malformed_counted ? 4 : counted_any ? 3 : 0;
  double t2 = now_s();

  // ---- report (stdout)
  printf("prechk: %s\n", path);
  printf("  %" PRIu64 " bytes, %" PRIu64 " lines, names %" PRIu64 ", levels %" PRIu64 ", exprs %" PRIu64 ", constants %" PRIu64 " (%d threads, %.1f s: parse %.1f, dup %.1f, depth %.1f, replay %.1f)\n",
         size, nlines, NN, NL, NE, ndecl, O.threads, t2 - t0, t1 - t0, t_dup, t_depth, t_replay);
  printf("  max: height %" PRIu64 ", name number %" PRIu64 ", u16 field %" PRIu64 ", bvar %" PRIu64 ", proj idx %" PRIu64 ", level depth %" PRIu64 ", expr depth %" PRIu64 ", binder nesting %" PRIu64 "; replay graph %" PRIu64 " nodes %" PRIu64 " edges, walk bound %" PRIu64 " (%" PRIu64 " visits)\n",
         max_height, max_name_num, max_u16, max_bvar, max_proj_idx, max_ldepth, max_edepth, max_bdepth, n_nodes, n_edges, walk_bound, visits);
  for (int k = 0; k < NHZ; k++) {
    if (!cnt[k]) continue;
    printf("  %s %-15s %" PRIu64 "\n", O.counted[k] ? "HAZARD " : "(info) ", HZ_NAME[k], cnt[k]);
    for (auto& e : exs[k]) printf("      line %" PRIu64 " (byte %" PRIu64 "): %s\n", lineof(e), e.off, e.msg.c_str());
  }
  if (replay_done) printf("  replay order: %s; order hazards exact %" PRIu64 " / conservative %" PRIu64 "; exact official walk depth %" PRIu64 "\n",
                         replay_exact ? "EXACT simulation of Lean.Replay (NameSet hash order)" : ("conservative (simulation not possible: " + sim_error + ")").c_str(),
                         n_order_exact, n_order_conservative, walk_exact);
  if (O.closure) printf("  closure guard: %" PRIu64 " targets checked; %" PRIu64 " closure violations\n", n_closure_targets, cnt[HZ_CLOSURE]);
  printf("  verdict: %s (exit %d)\n", rc == 0 ? "CLEAN - no known official-limit hazard" : rc == 4 ? "MALFORMED - decline" : "HAZARD - decline", rc);

  if (O.json) {
    FILE* f = fopen(O.json, "w");
    if (!f) { fprintf(stderr, "prechk: cannot write %s\n", O.json); return 2; }
    auto js = [](const std::string& s) { std::string o; for (char c : s) { if (c == '"' || c == '\\') { o += '\\'; o += c; } else if ((unsigned char)c < 0x20) { char b[8]; snprintf(b, 8, "\\u%04x", c); o += b; } else o += c; } return o; };
    fprintf(f, "{\"tool\":\"%s\",\"export\":\"%s\",\"bytes\":%" PRIu64 ",\"lines\":%" PRIu64 ",\"threads\":%d,\"elapsed_s\":%.3f,\n", VERSION, js(path).c_str(), size, nlines, O.threads, t2 - t0);
    fprintf(f, " \"options\":{\"nanoda_counted\":%s,\"nanoda_depth\":%" PRIu64 ",\"kernel_depth\":%" PRIu64 ",\"walk_limit\":%" PRIu64 ",\"replay\":%s},\n", O.nanoda ? "true" : "false", O.nanoda_depth, O.kernel_depth, O.walk_limit, O.replay ? "true" : "false");
    fprintf(f, " \"stats\":{\"names\":%" PRIu64 ",\"levels\":%" PRIu64 ",\"exprs\":%" PRIu64 ",\"constants\":%" PRIu64 ",\"max_height\":%" PRIu64 ",\"max_name_number\":%" PRIu64 ",\"max_u16_field\":%" PRIu64 ",\"max_bvar\":%" PRIu64 ",\"max_proj_idx\":%" PRIu64 ",\"max_level_depth\":%" PRIu64 ",\"max_expr_depth\":%" PRIu64 ",\"max_binder_nesting\":%" PRIu64 ",\"nat_literals\":%" PRIu64 ",\"str_literals\":%" PRIu64 ",\"projs\":%" PRIu64 ",\"replay_nodes\":%" PRIu64 ",\"replay_edges\":%" PRIu64 ",\"walk_bound\":%" PRIu64 ",\"replay_analysed\":%s,\"dup_candidates_checked\":%" PRIu64 ",\"replay_order_exact\":%s,\"order_hazards_exact\":%" PRIu64 ",\"order_hazards_conservative\":%" PRIu64 ",\"walk_depth_exact\":%" PRIu64 "},\n",
            NN, NL, NE, ndecl, max_height, max_name_num, max_u16, max_bvar, max_proj_idx, max_ldepth, max_edepth, max_bdepth, n_nat, n_str, n_proj, n_nodes, n_edges, walk_bound, replay_done ? "true" : "false", n_dup_checked, replay_exact ? "true" : "false", n_order_exact, n_order_conservative, walk_exact);
    fprintf(f, " \"hazards\":{");
    bool first = true;
    for (int k = 0; k < NHZ; k++) {
      if (!cnt[k]) continue;
      fprintf(f, "%s\n  \"%s\":{\"count\":%" PRIu64 ",\"counted\":%s,\"examples\":[", first ? "" : ",", HZ_NAME[k], cnt[k], O.counted[k] ? "true" : "false"); first = false;
      for (size_t i = 0; i < exs[k].size(); i++) fprintf(f, "%s{\"line\":%" PRIu64 ",\"byte\":%" PRIu64 ",\"msg\":\"%s\"}", i ? "," : "", lineof(exs[k][i]), exs[k][i].off, js(exs[k][i].msg).c_str());
      fprintf(f, "]}");
    }
    fprintf(f, "},\n \"verdict\":\"%s\",\"exit\":%d}\n", rc == 0 ? "clean" : rc == 4 ? "malformed" : "hazard", rc);
    fclose(f);
  }
  return rc;
}
