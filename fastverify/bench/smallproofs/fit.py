#!/usr/bin/python3 -I
"""fit.py ANATOMY.tsv TABLE.tsv : least-squares fit T = a + b * closure_MB per preset configuration and import class
(Mathlib / core), excluding kernel-heavy cases (styles kscale*, decide-heavy, decide-kernel, rfl-gmp, neg*) and batches;
plus a binned 'plot as table' of totals vs closure size. Total = run wall - prepare (challenge build)."""
import csv, statistics as S, sys
from collections import defaultdict
an = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
tb = list(csv.DictReader(open(sys.argv[2]), delimiter="\t"))
def f(x):
    try: return float(x)
    except Exception: return None
# map (case, preset, build_opt) -> total from table.tsv (collect.py rows)
tot = defaultdict(list)
for r in tb:
    if r["verdict"] not in ("ACCEPTED", "REJECTED"): continue
    tot[(r["case"], r["preset"], r["build_opt"])].append(f(r["wall"]) - (f(r["prepare"]) or 0))
pts = defaultdict(list)
heavy = ("kscale", "decide-heavy", "decide-kernel", "rfl-gmp", "neg", "batch")
for r in an:
    if r["verdict"] != "ACCEPTED" or (r["style"] or "").startswith(heavy): continue
    cfg = r["preset"] + ("-" + r["tag"] if r["tag"] else "")
    t = tot.get((r["case"], r["preset"], r["build_opt"]))
    if not t: continue
    pts[(cfg, r["imports"] == "Mathlib")].append((f(r["export_MB"]), S.median(t)))
def lsq(P):
    n = len(P); mx = sum(x for x, _ in P) / n; my = sum(y for _, y in P) / n
    sxx = sum((x - mx) ** 2 for x, _ in P)
    b = sum((x - mx) * (y - my) for x, y in P) / sxx if sxx else 0.0
    return my - b * mx, b
print("| configuration | imports | n | fit: total = a + b x MB | median total |")
print("|---|---|---|---|---|")
for (cfg, ml), P in sorted(pts.items()):
    a, b = lsq(P)
    print(f"| {cfg} | {'Mathlib' if ml else 'core'} | {len(P)} | {a:.1f} s + {b:.3f} s/MB | {S.median(y for _, y in P):.1f} s |")
print()
bins = [(0, 2), (2, 10), (10, 25), (25, 50), (50, 1e9)]
cfgs = sorted({c for c, ml in pts if ml})
print("| closure MB (Mathlib proofs) | n | " + " | ".join(cfgs) + " |")
print("|---|---|" + "---|" * len(cfgs))
for lo, hi in bins:
    row = []
    n = 0
    for c in cfgs:
        ys = [y for x, y in pts[(c, True)] if lo <= x < hi]
        n = max(n, len(ys))
        row.append(f"{S.median(ys):.1f}" if ys else "-")
    print(f"| {lo}-{'' if hi > 1e8 else hi} | {n} | " + " | ".join(row) + " |")
