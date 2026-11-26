// Exact check that two import graphs give every root module the same ORDERED imported-module list under
// Lean 4.33's `importModulesCore` (`Lean/Environment.lean:2177-2229`), supporting BOTH:
//   (1) traditional projects (plain post-order DFS over imports), and
//   (2) `module`-system / mixed projects (when `@mod` or `pub:`/`priv:`/`meta:`/`all:` tags appear in the graph file),
//       simulating the exact `(importAll, isExported, hasData, needsIRTrans, irPhases)` lattice + `moduleNames` array!
// Usage: dfsverify OLD.txt NEW.txt ROOTS.txt [THREADS]
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>
#include <unordered_map>
#include <fstream>
#include <sstream>
#include <iostream>
#include <thread>
#include <atomic>
using namespace std;

struct Edge {
  int mod;
  bool isExported;
  bool isMeta;
  bool importAll;
};

struct Graph {
  vector<bool> isModule;
  vector<vector<Edge>> adj;
  bool anyModSys = false;
};

unordered_map<string,int> id_map;
vector<string> names;

int getid(const string& s) {
  auto it = id_map.find(s);
  if (it != id_map.end()) return it->second;
  int n = (int)names.size();
  id_map[s] = n;
  names.push_back(s);
  return n;
}

Graph load(const char* f) {
  Graph g;
  ifstream in(f);
  string line;
  struct Row { int m; bool isMod; vector<Edge> es; };
  vector<Row> rows;
  while (getline(in, line)) {
    istringstream ss(line);
    string mraw;
    if (!(ss >> mraw)) continue;
    bool isMod = false;
    if (mraw.size() > 4 && mraw.substr(mraw.size() - 4) == "@mod") {
      isMod = true;
      g.anyModSys = true;
      mraw = mraw.substr(0, mraw.size() - 4);
    }
    int a = getid(mraw);
    vector<Edge> es;
    string x;
    while (ss >> x) {
      bool pub = false, priv = false, meta = false, all = false;
      bool changed = true;
      while (changed) {
        changed = false;
        if (x.rfind("pub:", 0) == 0) { pub = true; g.anyModSys = true; x = x.substr(4); changed = true; }
        else if (x.rfind("priv:", 0) == 0) { priv = true; g.anyModSys = true; x = x.substr(5); changed = true; }
        else if (x.rfind("meta:", 0) == 0) { meta = true; g.anyModSys = true; x = x.substr(5); changed = true; }
        else if (x.rfind("all:", 0) == 0) { all = true; g.anyModSys = true; x = x.substr(4); changed = true; }
      }
      // In Lean 4 syntax: inside a `module` file, plain `import` has isExported=false unless `public` is given;
      // inside a non-`module` file, plain `import` has isExported=true unless `private` is given.
      bool isExp = isMod ? pub : (!priv);
      es.push_back({getid(x), isExp, meta, all});
    }
    rows.push_back({a, isMod, move(es)});
  }
  g.isModule.assign(names.size(), false);
  g.adj.resize(names.size());
  for (auto& r : rows) {
    if ((int)g.adj.size() <= r.m) {
      g.adj.resize(r.m + 1);
      g.isModule.resize(r.m + 1, false);
    }
    g.isModule[r.m] = r.isMod;
    g.adj[r.m] = move(r.es);
  }
  return g;
}

static void dfs_plain(const Graph& g, int root, vector<int>& stamp, int st, vector<int>& out) {
  vector<pair<int,size_t>> stack;
  stack.push_back({root, 0});
  while (!stack.empty()) {
    auto& top = stack.back();
    int n = top.first;
    const vector<Edge>* ch = n < (int)g.adj.size() ? &g.adj[n] : nullptr;
    if (ch && top.second < ch->size()) {
      int c = (*ch)[top.second++].mod;
      if (stamp[c] == st) continue;
      stamp[c] = st;
      stack.push_back({c, 0});
    } else {
      if (n != root) out.push_back(n);
      stack.pop_back();
    }
  }
}

struct ModState {
  bool present = false;
  bool importAll = false;
  bool isExported = false;
  bool hasData = false;
  bool needsIRTrans = false;
  int irPhases = 0; // 0=runtime, 1=comptime, 2=all
  bool operator==(const ModState& o) const {
    return present == o.present && importAll == o.importAll && isExported == o.isExported &&
           hasData == o.hasData && needsIRTrans == o.needsIRTrans && irPhases == o.irPhases;
  }
};

struct ModSysResult {
  vector<int> moduleNames;
  vector<pair<int, ModState>> states;
  bool operator==(const ModSysResult& o) const {
    return moduleNames == o.moduleNames && states == o.states;
  }
};

static void go_modsys(const Graph& g, bool globalPrivate, const vector<Edge>& imports,
                      bool importAll, bool isExported, bool needsData, bool needsIRTrans,
                      vector<ModState>& map, vector<int>& moduleNames) {
  for (const auto& i : imports) {
    bool nd = needsData && (i.isExported || importAll);
    bool ia = globalPrivate || (importAll && i.importAll);
    bool ie = isExported && i.isExported;
    bool nirt = needsIRTrans || (nd && i.isMeta);
    bool nir = nirt || ia || globalPrivate;
    if (!nd && !nir) continue;
    int irp = ia ? 2 : (nirt ? 1 : 0);
    int m = i.mod;
    if (map[m].present) {
      ModState cur = map[m];
      bool ia2 = ia || cur.importAll;
      bool ie2 = ie || cur.isExported;
      bool nd2 = nd || cur.hasData;
      bool nirt2 = nirt || cur.needsIRTrans;
      int irp2 = (irp == cur.irPhases) ? irp : 2;
      if (ia2 != cur.importAll || ie2 != cur.isExported || nirt2 != cur.needsIRTrans ||
          nd2 != cur.hasData || irp2 != cur.irPhases) {
        map[m] = {true, ia2, ie2, nd2, nirt2, irp2};
        if (nd2 && m < (int)g.adj.size()) {
          go_modsys(g, globalPrivate, g.adj[m], ia2, ie2, nd2, nirt2, map, moduleNames);
        }
      }
      continue;
    }
    map[m] = {true, ia, ie, nd, nirt, irp};
    if (nd && m < (int)g.adj.size()) {
      go_modsys(g, globalPrivate, g.adj[m], ia, ie, nd, nirt, map, moduleNames);
    }
    moduleNames.push_back(m);
  }
}

static ModSysResult run_modsys(const Graph& g, int root, size_t N) {
  bool rootIsMod = root < (int)g.isModule.size() ? g.isModule[root] : false;
  bool globalPrivate = !rootIsMod;
  bool initExported = !globalPrivate; // globalLevel < .private
  vector<ModState> map(N);
  vector<int> moduleNames;
  if (root < (int)g.adj.size()) {
    go_modsys(g, globalPrivate, g.adj[root], true, initExported, true, false, map, moduleNames);
  }
  vector<pair<int, ModState>> st;
  st.reserve(moduleNames.size());
  for (int m : moduleNames) st.push_back({m, map[m]});
  return {move(moduleNames), move(st)};
}

int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: dfsverify OLD.txt NEW.txt ROOTS.txt [THREADS]\n"); return 2; }
  auto g1 = load(argv[1]);
  auto g2 = load(argv[2]);
  vector<int> roots;
  { ifstream in(argv[3]); string s; while (in >> s) roots.push_back(getid(s)); }
  size_t N = names.size();
  g1.adj.resize(N); g1.isModule.resize(N, false);
  g2.adj.resize(N); g2.isModule.resize(N, false);
  bool modsys = g1.anyModSys || g2.anyModSys;
  int T = argc > 4 ? atoi(argv[4]) : 8;
  atomic<long> idx(0), bad(0), total(0);
  atomic<long> firstbad(-1);
  vector<thread> th;
  for (int t = 0; t < T; t++) th.emplace_back([&]() {
    vector<int> s1(N, -1), s2(N, -1);
    vector<int> o1, o2;
    o1.reserve(65536); o2.reserve(65536);
    long i;
    while ((i = idx++) < (long)roots.size()) {
      int r = roots[i];
      if (!modsys) {
        o1.clear(); o2.clear();
        s1[r] = (int)i; s2[r] = (int)i;
        dfs_plain(g1, r, s1, (int)i, o1);
        dfs_plain(g2, r, s2, (int)i, o2);
        total += (long)o1.size();
        if (o1 != o2) {
          bad++;
          long exp = -1;
          firstbad.compare_exchange_strong(exp, i);
        }
      } else {
        auto r1 = run_modsys(g1, r, N);
        auto r2 = run_modsys(g2, r, N);
        total += (long)r1.moduleNames.size();
        if (!(r1 == r2)) {
          bad++;
          long exp = -1;
          firstbad.compare_exchange_strong(exp, i);
        }
      }
    }
  });
  for (auto& x : th) x.join();
  printf("mode %s roots %zu identical %ld different %ld total_list_entries %ld\n",
         modsys ? "module-system" : "plain", roots.size(), (long)roots.size() - bad.load(), bad.load(), total.load());
  if (firstbad >= 0) printf("first different root: %s\n", names[roots[firstbad]].c_str());
  return bad ? 1 : 0;
}
