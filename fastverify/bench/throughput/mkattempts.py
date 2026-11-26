#!/usr/bin/python3 -I
"""mkattempts.py CORPUS OUT MODE : attempts dir for batchverify: OUT/<theorem>.lean = the solution module of each problem.
MODE pos = every positive solution; mix = the positive ones, except that each problem with negative variants gets its
(first) negative variant instead; neg = only the negative variants."""
import json, os, shutil, sys
corpus, out, mode = sys.argv[1:4]
cases = json.load(open(os.path.join(corpus, "cases.json")))
os.makedirs(out, exist_ok=False)
neg = {}
for c, v in sorted(cases.items()):
    if v["kind"] != "positive":
        neg.setdefault(v["challenge"], c)
n = 0
for c, v in sorted(cases.items()):
    if v["kind"] != "positive" or c == "BATCH":
        continue
    src = c
    if mode == "mix" and c in neg:
        src = neg[c]
    if mode == "neg":
        if c not in neg:
            continue
        src = neg[c]
    shutil.copyfile(os.path.join(corpus, "projects", src, "Solution.lean"), os.path.join(out, c + ".lean"))
    n += 1
json.dump({c: (neg[c] if (mode in ("mix", "neg") and c in neg) else c) for c in
           [f[:-5] for f in os.listdir(out)]}, open(out + ".map.json", "w"), indent=1)
print(n, "attempts")
