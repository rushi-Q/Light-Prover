#!/usr/bin/env python3
"""exclude_decls.py INDEX.pkl MY.tsv OUT.tsv OTHER.tsv... — drop every edit of MY.tsv whose enclosing declaration (the pruning index's
rh-index.pkl ranges) also receives an edit in one of the OTHER edit lists (team TSV format, original line numbers).
Why: an automated closer may use a hypothesis that another owner deletes as dead in the original proof (dead-have
elimination), or need more heartbeats than another owner's lowered option (normalize) - interactions that line-overlap
conflict detection cannot see."""
import pickle, sys, collections, bisect
idx = pickle.load(open(sys.argv[1], "rb")); ranges = idx["ranges"]
other = collections.defaultdict(list)
for f in sys.argv[4:]:
    for l in open(f, encoding="utf-8"):
        p = l.split("\t", 5)
        if len(p) >= 4 and p[1].isdigit():
            other[p[0][:-5].replace("/", ".") if p[0].endswith(".lean") else p[0]].append((int(p[1]), int(p[2])))
kept = dropped = 0
with open(sys.argv[3], "w") as o:
    for l in open(sys.argv[2], encoding="utf-8"):
        p = l.split("\t", 5); a, b = int(p[1]), int(p[2])
        mod = p[0][:-5].replace("/", ".") if p[0].endswith(".lean") else p[0]
        enc = [r for r in ranges.get(mod, []) if r[1] <= a and b <= r[3]]
        lo, hi = (min(enc, key=lambda r: r[3] - r[1])[1], min(enc, key=lambda r: r[3] - r[1])[3]) if enc else (a, b)
        if any(not (y < lo or hi < x) for x, y in other.get(mod, [])):
            dropped += 1; continue
        o.write(l); kept += 1
print(f"exclude_decls: kept {kept}, dropped {dropped} (declaration also edited by another owner)")
