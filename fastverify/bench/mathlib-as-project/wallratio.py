#!/usr/bin/env python3
"""wallratio.py LAKE_BUILD_LOG SCHED_OUT... : per-module wall ratio (fast scheduler / official lake build) for the same modules."""
import json, re, statistics, sys
def secs(t):
    s = 0.0
    for v, u in re.findall(r"([\d.]+)(ms|s|m|h)", t): s += float(v) * {"ms": 0.001, "s": 1, "m": 60, "h": 3600}[u]
    return s
b0 = {}
for ln in open(sys.argv[1], errors="replace"):
    m = re.search(r"Built (\S+) \(([^)]*)\)\s*$", ln)
    if m: b0[m.group(1)] = secs(m.group(2))
for p in sys.argv[2:]:
    b2 = {}
    for ln in open(p):
        try: r = json.loads(ln)
        except Exception: continue
        if r.get("event") == "module": b2[r["module"]] = r["wall"]
    big = [b2[m] / b0[m] for m in b2 if m in b0 and b0[m] >= 5]
    mid = [b2[m] / b0[m] for m in b2 if m in b0 and 1 <= b0[m] < 5]
    print(p, "modules>=5s:", len(big), "median ratio", round(statistics.median(big), 3) if big else None,
          "| 1-5s:", len(mid), "median", round(statistics.median(mid), 3) if mid else None)
