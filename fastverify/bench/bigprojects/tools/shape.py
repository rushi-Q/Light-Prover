#!/usr/bin/python3 -I
"""shape.py RUNDIR [THREADS] -> import-graph shape + schedule bounds of a B1-B3 build (plan.jsonl + sched.out):
modules, edges, depth (longest import chain in modules), critical path by measured walls (CP), work = sum of walls,
work/threads, achieved scheduler wall, the heaviest modules and the CP chain head."""
import json, os, sys
d = sys.argv[1]
for sub in ("build-fast", "build-fast-b1"):
    lp = os.path.join(d, "log", sub)
    if os.path.exists(os.path.join(lp, "sched.out")):
        break
plan = {}
for ln in open(os.path.join(lp, "plan.jsonl")):
    try:
        e = json.loads(ln)
    except Exception:
        continue
    if "name" in e:
        plan[e["name"]] = e.get("deps", [])
walls, wall_sched, threads = {}, None, None
for ln in open(os.path.join(lp, "sched.out")):
    try:
        e = json.loads(ln)
    except Exception:
        continue
    if e.get("event") == "module" and e.get("rc") == 0:
        walls[e["module"]] = e["wall"]
    if e.get("event") == "summary":
        wall_sched = e.get("wall")
    if e.get("event") == "start":
        threads = e.get("jobs")
# merged groups: members missing from walls -> 0
memo, depth, best = {}, {}, {}
sys.setrecursionlimit(100000)
def cp(m):
    if m in memo:
        return memo[m]
    ds = [x for x in plan.get(m, []) if x in plan]
    sub = max(ds, key=cp) if ds else None
    memo[m] = walls.get(m, 0.0) + (cp(sub) if sub else 0.0)
    depth[m] = 1 + (max(depth_of(x) for x in ds) if ds else 0)
    best[m] = sub
    return memo[m]
def depth_of(m):
    cp(m); return depth[m]
top = max(plan, key=cp)
chain, m = [], top
while m:
    chain.append(m); m = best.get(m)
W = sum(walls.values()); T = int(sys.argv[2]) if len(sys.argv) > 2 else (threads or 1)
heavy = sorted(walls.items(), key=lambda kv: -kv[1])[:5]
print(json.dumps({"run": os.path.basename(d.rstrip("/")), "modules": len(plan), "built": len(walls),
                  "edges": sum(len([x for x in v if x in plan]) for v in plan.values()),
                  "depth": max(depth_of(x) for x in plan), "cp_s": round(cp(top), 1), "cp_len": len(chain),
                  "work_s": round(W, 1), "threads": T, "work_over_T": round(W / T, 1), "sched_wall": wall_sched,
                  "heaviest": [(k.split(".")[-1], round(v, 1)) for k, v in heavy],
                  "cp_head": [c.split(".")[-1] for c in chain[:4]]}))
