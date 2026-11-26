#!/usr/bin/python3 -I
"""sched_stats.py LOGDIR [JOBS]  -> statistics of a finished build.sh run (LOGDIR = the stage's --log dir):
modules, failures, sum of per-module walls, makespan, average parallelism, and the critical path through the import
graph weighted by the measured walls (= the lower bound of the makespan for ANY schedule with unlimited workers).
Usage example: python3 -I build/test/sched_stats.py OUT/log/build-fast 384"""
import json, sys


def main():
    log = sys.argv[1]
    jobs = int(sys.argv[2]) if len(sys.argv) > 2 else None
    deps = {}
    with open(f"{log}/plan.jsonl") as f:
        f.readline()
        for line in f:
            r = json.loads(line)
            if "end" in r:
                break
            deps[r["name"]] = r["deps"]
    wall = {}; fails = 0; summary = None
    with open(f"{log}/sched.out") as f:
        for line in f:
            if not line.startswith("{"):
                continue
            r = json.loads(line)
            if r.get("event") == "module":
                wall[r["module"]] = r["wall"]
                fails += r["rc"] != 0
            elif r.get("event") == "summary":
                summary = r
    # critical path (longest weighted path) over the import DAG
    order = []; seen = set()
    for m in deps:
        stack = [(m, 0)]
        while stack:
            n, i = stack.pop()
            if i == 0:
                if n in seen:
                    continue
                seen.add(n)
            ds = deps.get(n, [])
            if i < len(ds):
                stack.append((n, i + 1))
                if ds[i] not in seen:
                    stack.append((ds[i], 0))
            else:
                order.append(n)
    cp = {}; prev = {}
    for n in order:
        best = max(deps.get(n, []), key=lambda d: cp.get(d, 0.0), default=None)
        cp[n] = wall.get(n, 0.0) + (cp[best] if best else 0.0); prev[n] = best
    end = max(cp, key=cp.get)
    chain = []
    n = end
    while n:
        chain.append(n); n = prev[n]
    tot = sum(wall.values())
    mk = summary["wall"] if summary else None
    print(f"modules built {len(wall)} of {len(deps)}, failures {fails}")
    print(f"sum of module walls {tot:,.0f} s; makespan {mk} s; average parallelism {tot / mk:.1f}" if mk else
          f"sum of module walls {tot:,.0f} s")
    if jobs and mk:
        print(f"work bound with {jobs} jobs: {tot / jobs:,.0f} s ({100 * tot / jobs / mk:.1f}% of makespan)")
    print(f"critical path (measured walls): {cp[end]:,.0f} s over {len(chain)} modules, ends at {end}")
    top = sorted(wall.items(), key=lambda kv: -kv[1])[:5]
    print("longest modules:", ", ".join(f"{m} {w:.0f} s" for m, w in top))


if __name__ == "__main__":
    main()
