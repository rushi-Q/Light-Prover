#!/usr/bin/env python3
"""extrapolate.py TRY_WD APPLY_OUT POP_LINES POP_MODULES [--policy-tsv FINAL.tsv] — project a random-module run to the
whole population: per module (finished, random order) the search wall time, the lines of the module, and the VERIFIED
saved lines (apply.py; optionally only the edits kept in FINAL.tsv, e.g. after liveedits/policy); ratio estimator
saved/lines with a bootstrap 95 % interval, scaled to POP_LINES; search cost scaled to POP_MODULES."""
import json, os, sys, random, glob, collections

wd, ap, pop_lines, pop_mods = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
keep = None
if "--policy-tsv" in sys.argv:
    keep = collections.Counter()
    for l in open(sys.argv[sys.argv.index("--policy-tsv") + 1]):
        f = l.split("\t", 5)
        keep[f[0]] += (int(f[2]) - int(f[1]) + 1) - (f[5].count("\\n") + 1)
idx = dict(l.split() for l in open(os.path.join(wd, "index.txt")))
rows = []
for f in glob.glob(os.path.join(wd, "res", "*.done")):
    n = os.path.basename(f)[:-5]
    rc, sec, rel = open(f).read().split()
    src = os.path.join(wd, "in", n + ".lean")
    if not os.path.exists(src):
        continue
    lines = open(src, "rb").read().count(b"\n")
    aj = os.path.join(ap, "apply.d", n + ".json")
    if not os.path.exists(aj):
        continue          # not applied yet: skip (keeps the estimator unbiased as long as apply order is random)
    r = json.loads(open(aj).read().strip().splitlines()[-1])
    if keep is not None:
        saved = keep.get(rel, 0)
    else:
        saved = (r.get("lines0", 0) - r.get("lines1", 0)) if r.get("status") == "ok" else 0
    rows.append((float(sec), lines, saved))
if not rows:
    print("no rows"); sys.exit(0)
S = sum(r[2] for r in rows); L = sum(r[1] for r in rows); T = sum(r[0] for r in rows)
ratio = S / L
random.seed(1)
bs = []
for _ in range(2000):
    smp = [rows[random.randrange(len(rows))] for _ in rows]
    bs.append(sum(r[2] for r in smp) / max(sum(r[1] for r in smp), 1))
bs.sort()
lo, hi = bs[int(0.025 * len(bs))], bs[int(0.975 * len(bs))]
print(f"modules {len(rows)}, lines {L:,}, verified saved lines {S:,} = {100*ratio:.2f}% (95% CI {100*lo:.2f}-{100*hi:.2f}%)")
print(f"projected to {pop_lines:,} lines: {ratio*pop_lines:,.0f} lines ({lo*pop_lines:,.0f}-{hi*pop_lines:,.0f})")
print(f"search wall per module {T/len(rows):.1f} s (one core each, loaded node) -> {pop_mods:,} modules: {T/len(rows)*pop_mods/3600:,.0f} core-hours")
