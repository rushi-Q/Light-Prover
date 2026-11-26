#!/usr/bin/env python3
"""cpath.py PLAN_JSONL THREADS [--sched SCHED_OUT | --lakelog BUILD_LOG] : build-shape statistics of one build:
modules, sum of per-module walls, work bound (sum/threads), critical path (longest import chain weighted by the measured
per-module walls), its length in modules and the top contributors, import depth (unweighted). Walls from the fastverify
scheduler's sched.out (B1/B2/B3) or from an official `lake build` log (B0: '✔ [i/N] Built M (1.3s)')."""
import json, re, sys
plan, threads = sys.argv[1], int(sys.argv[2])
deps = {}
with open(plan) as f:
    f.readline()
    for ln in f:
        r = json.loads(ln)
        if "name" in r: deps[r["name"]] = r.get("deps") or []
wall = {}
if "--sched" in sys.argv:
    for ln in open(sys.argv[sys.argv.index("--sched") + 1]):
        try: r = json.loads(ln)
        except Exception: continue
        if r.get("event") == "module": wall[r["module"]] = wall.get(r["module"], 0) + r.get("wall", 0)
if "--lakelog" in sys.argv:
    def secs(t):
        s = 0.0
        for v, u in re.findall(r'([\d.]+)(ms|s|m|h)', t):
            s += float(v) * {"ms": 0.001, "s": 1, "m": 60, "h": 3600}[u]
        return s
    for ln in open(sys.argv[sys.argv.index("--lakelog") + 1], encoding="utf-8", errors="replace"):
        m = re.search(r'Built (\S+)(?: \(([^)]*)\))?\s*$', ln)
        if m and m.group(1) in deps: wall[m.group(1)] = secs(m.group(2) or "0s")
mods = [m for m in deps if m in wall]
memo = {}; best = {}; dep = {}
sys.setrecursionlimit(1000000)
order = []
seen = set()
def topo(m):
    st = [(m, 0)]
    while st:
        x, i = st.pop()
        if i == 0:
            if x in seen: continue
            seen.add(x)
        ds = [d for d in deps.get(x, []) if d in deps]
        if i < len(ds):
            st.append((x, i + 1)); 
            if ds[i] not in seen: st.append((ds[i], 0))
        else: order.append(x)
for m in deps: topo(m)
for m in order:
    ds = [d for d in deps.get(m, []) if d in deps]
    p = max(ds, key=lambda d: memo[d], default=None)
    memo[m] = wall.get(m, 0) + (memo[p] if p else 0); best[m] = p
    dep[m] = 1 + max((dep[d] for d in ds), default=0)
end = max(memo, key=memo.get)
chain = []; x = end
while x: chain.append(x); x = best[x]
tot = sum(wall.values())
out = {"modules_planned": len(deps), "modules_timed": len(mods), "sum_wall_s": round(tot, 1), "threads": threads,
       "work_bound_s": round(tot / threads, 1), "critical_path_s": round(memo[end], 1), "cp_modules": len(chain),
       "import_depth": max(dep.values()), "cp_share_top5": [(c, round(wall.get(c, 0), 1)) for c in sorted(chain, key=lambda c: -wall.get(c, 0))[:5]],
       "max_wall": round(max(wall.values()), 1), "mean_wall": round(tot / max(1, len(mods)), 2)}
print(json.dumps(out))
