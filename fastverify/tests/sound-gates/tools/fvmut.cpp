// fvmut — apply a small, exactly specified edit to a (huge) lean4export NDJSON file, writing a full-size copy.
// Analysis tool for the RH mutant validation; not a fastverify component.
//
//   fvmut SRC DST SPEC [--threads N]
//
// SPEC (text, one directive per line):
//   E <byte offset>      start of an edit: the line of SRC that starts at this offset is replaced
//   O <line>             the exact current content of that line (verified byte for byte; the edit is refused otherwise)
//   N <line>             a replacement line (zero or more, written in this order in place of the old line)
//   S <name_k> <name_d> <expr_k> <expr_d>
//                        renumber every line of SRC AFTER the first edited line: every name index >= name_k is
//                        increased by name_d and every expr index >= expr_k by expr_d (used when new name/expr records
//                        are inserted by an edit, so that the indices stay the contiguous sequences nanoda requires and
//                        every reference still points to the record it pointed to). Level indices are never changed.
// Edits must be given in increasing offset order. Bytes outside the edited lines are copied with copy_file_range
// (no renumbering) or rewritten by a strict scanner (renumbering): the scanner knows which JSON key holds which kind of
// index (lean4export format 3.1.0) and refuses any numeric field it does not know, and any mdata record.
// Exit 0 = written, 1 = refused (spec does not match SRC, unknown field, I/O error).
#include <algorithm>
#include <atomic>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <string>
#include <sys/mman.h>
#include <sys/stat.h>
#include <thread>
#include <unistd.h>
#include <vector>

[[noreturn]] static void die(const std::string& m) { fprintf(stderr, "fvmut: %s\n", m.c_str()); exit(1); }

struct Edit { uint64_t off; std::string old; std::vector<std::string> neu; };
static uint64_t NK = UINT64_MAX, ND = 0, EK = UINT64_MAX, ED = 0;
static bool SHIFT = false;

enum Cat { C_UNKNOWN = -1, C_OTHER = 0, C_NAME = 1, C_LEVEL = 2, C_EXPR = 3 };
static int keycat(const char* k, size_t n) {
  struct KC { const char* k; int c; };
  static const KC T[] = {
    {"in", C_NAME}, {"pre", C_NAME}, {"name", C_NAME}, {"param", C_NAME}, {"levelParams", C_NAME}, {"all", C_NAME},
    {"ctors", C_NAME}, {"induct", C_NAME}, {"ctor", C_NAME}, {"typeName", C_NAME},
    {"il", C_LEVEL}, {"succ", C_LEVEL}, {"max", C_LEVEL}, {"imax", C_LEVEL}, {"sort", C_LEVEL}, {"us", C_LEVEL},
    {"ie", C_EXPR}, {"fn", C_EXPR}, {"arg", C_EXPR}, {"type", C_EXPR}, {"body", C_EXPR}, {"value", C_EXPR},
    {"struct", C_EXPR}, {"expr", C_EXPR}, {"rhs", C_EXPR},
    {"i", C_OTHER}, {"idx", C_OTHER}, {"bvar", C_OTHER}, {"numParams", C_OTHER}, {"numIndices", C_OTHER},
    {"numNested", C_OTHER}, {"cidx", C_OTHER}, {"numFields", C_OTHER}, {"numMotives", C_OTHER},
    {"numMinors", C_OTHER}, {"nfields", C_OTHER}, {"regular", C_OTHER}};
  for (auto& t : T) if (strlen(t.k) == n && memcmp(t.k, k, n) == 0) return t.c;
  return C_UNKNOWN;
}

static inline void put_u64(std::string& out, uint64_t v) {
  char b[24]; int n = 0; do { b[n++] = char('0' + v % 10); v /= 10; } while (v);
  while (n) out.push_back(b[--n]);
}

// rewrite one line [b, e) (without '\n') into out; returns false + msg on anything unexpected
static bool rewrite_line(const char* b, const char* e, std::string& out, std::string& err) {
  struct Ctx { char t; int cat; };
  Ctx st[64]; int sp = 0;
  const char* key = nullptr; size_t keyn = 0; bool afterColon = false;
  const char* p = b;
  while (p < e) {
    char c = *p;
    if (c == '"') {
      const char* q = p + 1;
      while (q < e && *q != '"') { if (*q == '\\') q += 2; else q++; }
      if (q >= e) { err = "unterminated string"; return false; }
      out.append(p, q + 1);
      const char* s = p + 1; size_t sn = (size_t)(q - s);
      p = q + 1;
      if (p < e && *p == ':') {   // a key
        key = s; keyn = sn;
        if (keyn == 5 && memcmp(key, "mdata", 5) == 0) { err = "mdata record (not supported)"; return false; }
      }
      afterColon = false;
      continue;
    }
    if (c == ':') { out.push_back(c); afterColon = true; p++; continue; }
    if (c == '{') { if (sp >= 63) { err = "nesting"; return false; } st[sp++] = {'{', 0}; out.push_back(c); p++; afterColon = false; continue; }
    if (c == '[') {
      if (sp >= 63) { err = "nesting"; return false; }
      int cat = key ? keycat(key, keyn) : C_UNKNOWN;
      st[sp++] = {'[', cat}; out.push_back(c); p++; afterColon = false; continue;
    }
    if (c == '}' || c == ']') { if (sp == 0) { err = "unbalanced"; return false; } sp--; out.push_back(c); p++; afterColon = false; continue; }
    if (c >= '0' && c <= '9') {
      uint64_t v = 0; const char* q = p;
      while (q < e && *q >= '0' && *q <= '9') { if (v > (UINT64_MAX - 9) / 10) { err = "number overflow"; return false; } v = v * 10 + (uint64_t)(*q - '0'); q++; }
      int cat;
      if (sp > 0 && st[sp - 1].t == '[' && !afterColon) cat = st[sp - 1].cat;
      else cat = key ? keycat(key, keyn) : C_UNKNOWN;
      if (cat == C_UNKNOWN) { err = "numeric field with unknown key '" + std::string(key ? key : "", key ? keyn : 0) + "'"; return false; }
      if (cat == C_NAME && v >= NK) v += ND;
      else if (cat == C_EXPR && v >= EK) v += ED;
      put_u64(out, v);
      p = q; afterColon = false; continue;
    }
    if (c == '-' || c == '.' || c == 'e' || c == 'E') {
      // only legal inside true/false (handled by the letter branch below) -- a signed/fractional number is refused
      if (c == '-' || c == '.') { err = "non-canonical number"; return false; }
    }
    out.push_back(c); p++;
    if (c != ' ') {} // (canonical exports contain no whitespace; it would simply be copied)
  }
  if (sp != 0) { err = "unbalanced at end of line"; return false; }
  return true;
}

static int g_threads = 64;
static const char* g_base = nullptr;

static void write_all(int fd, uint64_t& woff, const char* p, size_t n) {
  while (n) { ssize_t w = pwrite(fd, p, n, (off_t)woff); if (w <= 0) die(std::string("write: ") + strerror(errno)); p += w; n -= (size_t)w; woff += (uint64_t)w; }
}
static void copy_range(int fin, int fout, uint64_t from, uint64_t to, uint64_t& woff) {
  loff_t in = (loff_t)from, out = (loff_t)woff; uint64_t left = to - from;
  while (left) {
    ssize_t r = copy_file_range(fin, &in, fout, &out, std::min<uint64_t>(left, 1ull << 30), 0);
    if (r < 0) { if (errno == EXDEV || errno == ENOSYS || errno == EOPNOTSUPP) { // fallback
        write_all(fout, woff, g_base + in, left); return; }
      die(std::string("copy_file_range: ") + strerror(errno)); }
    if (r == 0) die("copy_file_range: unexpected EOF");
    left -= (uint64_t)r; woff += (uint64_t)r;
  }
}
// renumber [from, to) (must start at a line start and end at a line end or EOF) in parallel batches
static void shift_range(int fout, uint64_t from, uint64_t to, uint64_t& woff) {
  const uint64_t BATCH = 8ull << 30;
  uint64_t pos = from, lines = 0;
  while (pos < to) {
    uint64_t bend = std::min(to, pos + BATCH);
    if (bend < to) { const char* q = (const char*)memchr(g_base + bend, '\n', to - bend); bend = q ? (uint64_t)(q - g_base) + 1 : to; }
    int nch = g_threads * 4;
    std::vector<uint64_t> cut(nch + 1); cut[0] = pos; cut[nch] = bend;
    for (int i = 1; i < nch; i++) {
      uint64_t c = pos + (bend - pos) * (uint64_t)i / nch; if (c < cut[i - 1]) c = cut[i - 1];
      const char* q = (const char*)memchr(g_base + c, '\n', bend - c); cut[i] = q ? std::min<uint64_t>((uint64_t)(q - g_base) + 1, bend) : bend;
    }
    std::vector<std::string> outb(nch); std::vector<std::string> errs(nch); std::vector<uint64_t> nl(nch, 0);
    std::atomic<int> nx{0}; std::vector<std::thread> th;
    for (int t = 0; t < g_threads; t++) th.emplace_back([&]() { int i;
      while ((i = nx.fetch_add(1)) < nch) {
        std::string& o = outb[i]; o.reserve((size_t)(cut[i + 1] - cut[i]) + ((cut[i + 1] - cut[i]) >> 6) + 64);
        const char* p = g_base + cut[i]; const char* E = g_base + cut[i + 1];
        while (p < E) {
          const char* q = (const char*)memchr(p, '\n', (size_t)(E - p)); const char* le = q ? q : E;
          std::string err;
          if (!rewrite_line(p, le, o, err)) { errs[i] = err + " at byte " + std::to_string((uint64_t)(p - g_base)); break; }
          nl[i]++;
          if (q) { o.push_back('\n'); p = q + 1; } else p = E;
        }
      } });
    for (auto& x : th) x.join();
    for (int i = 0; i < nch; i++) if (!errs[i].empty()) die("renumbering refused: " + errs[i]);
    for (int i = 0; i < nch; i++) { write_all(fout, woff, outb[i].data(), outb[i].size()); lines += nl[i]; std::string().swap(outb[i]); }
    fprintf(stderr, "fvmut: renumbered up to byte %llu of %llu\n", (unsigned long long)bend, (unsigned long long)to);
    pos = bend;
  }
  fprintf(stderr, "fvmut: renumbered %llu lines\n", (unsigned long long)lines);
}

int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: fvmut SRC DST SPEC [--threads N]\n"); return 1; }
  const char *src = argv[1], *dst = argv[2], *spec = argv[3];
  for (int i = 4; i < argc; i++) { if (!strcmp(argv[i], "--threads") && i + 1 < argc) g_threads = atoi(argv[++i]); else die("bad argument"); }
  if (g_threads < 1) g_threads = 1;
  // ---- spec
  std::vector<Edit> ed;
  { FILE* f = fopen(spec, "r"); if (!f) die("cannot read spec");
    char* line = nullptr; size_t cap = 0; ssize_t n;
    while ((n = getline(&line, &cap, f)) >= 0) {
      std::string s(line, (size_t)n); if (!s.empty() && s.back() == '\n') s.pop_back();
      if (s.empty() || s[0] == '#') continue;
      if (s.size() < 2 || s[1] != ' ') die("bad spec line: " + s);
      std::string a = s.substr(2);
      if (s[0] == 'E') { ed.push_back({strtoull(a.c_str(), nullptr, 10), "", {}}); }
      else if (s[0] == 'O') { if (ed.empty()) die("O before E"); ed.back().old = a; }
      else if (s[0] == 'N') { if (ed.empty()) die("N before E"); ed.back().neu.push_back(a); }
      else if (s[0] == 'S') { unsigned long long a1, a2, a3, a4; if (sscanf(a.c_str(), "%llu %llu %llu %llu", &a1, &a2, &a3, &a4) != 4) die("bad S line");
        NK = a1; ND = a2; EK = a3; ED = a4; SHIFT = (ND != 0 || ED != 0); }
      else die("bad spec directive: " + s);
    }
    free(line); fclose(f); }
  if (ed.empty()) die("no edit in spec");
  for (size_t i = 1; i < ed.size(); i++) if (ed[i].off <= ed[i - 1].off) die("edits not in increasing offset order");
  // ---- input
  int fin = open(src, O_RDONLY); if (fin < 0) die(std::string("open src: ") + strerror(errno));
  struct stat st; if (fstat(fin, &st) || !S_ISREG(st.st_mode)) die("src not a regular file");
  uint64_t size = (uint64_t)st.st_size;
  g_base = (const char*)mmap(nullptr, size, PROT_READ, MAP_SHARED, fin, 0); if (g_base == MAP_FAILED) die("mmap");
  for (auto& x : ed) {
    if (x.off >= size || (x.off > 0 && g_base[x.off - 1] != '\n')) die("edit offset " + std::to_string(x.off) + " is not a line start");
    const char* q = (const char*)memchr(g_base + x.off, '\n', size - x.off); uint64_t le = q ? (uint64_t)(q - g_base) : size;
    if (std::string(g_base + x.off, le - x.off) != x.old) die("line at offset " + std::to_string(x.off) + " differs from the spec's O line:\n  have " + std::string(g_base + x.off, std::min<uint64_t>(le - x.off, 400)));
  }
  int fout = open(dst, O_WRONLY | O_CREAT | O_EXCL, 0644); if (fout < 0) die(std::string("create dst (must not exist): ") + strerror(errno));
  uint64_t woff = 0, cur = 0; bool shifting = false;
  for (size_t k = 0; k < ed.size(); k++) {
    auto& x = ed[k];
    if (shifting) shift_range(fout, cur, x.off, woff); else copy_range(fin, fout, cur, x.off, woff);
    for (auto& l : x.neu) { std::string o = l + "\n"; write_all(fout, woff, o.data(), o.size()); }
    cur = x.off + x.old.size() + 1; if (cur > size) cur = size;
    if (k == 0 && SHIFT) shifting = true;
    fprintf(stderr, "fvmut: edit at byte %llu: 1 line -> %zu line(s)\n", (unsigned long long)x.off, x.neu.size());
  }
  if (cur < size) { if (shifting) shift_range(fout, cur, size, woff); else copy_range(fin, fout, cur, size, woff); }
  if (fsync(fout) != 0) die("fsync");
  close(fout);
  fprintf(stderr, "fvmut: wrote %s: %llu bytes (source %llu bytes)\n", dst, (unsigned long long)woff, (unsigned long long)size);
  return 0;
}
