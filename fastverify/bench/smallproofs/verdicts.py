#!/usr/bin/python3 -I
"""verdicts.py CORPUS RUNSDIR... : differential tally: per case the verdict of every preset run vs the official
(reference) verdict and the expected one; prints disagreements and counts."""
import glob, json, os, sys
from collections import Counter, defaultdict
cases = json.load(open(os.path.join(sys.argv[1], "cases.json")))
V = defaultdict(dict)
for runs in sys.argv[2:]:
    for d in glob.glob(os.path.join(runs, "*")):
        if not os.path.isdir(d): continue
        p = os.path.basename(d).split(".")
        try: r = json.load(open(os.path.join(d, "result.json")))
        except Exception: continue
        if r.get("verdict_basis") == "not finished": continue
        V[p[0]][".".join(p[1:])] = (r.get("verdict"), r.get("trust"), (r.get("export") or {}).get("sha256"))
cnt = Counter(); bad = []
for c, d in sorted(V.items()):
    exp = cases.get(c, {}).get("expected", "ACCEPTED")
    off = d.get("reference", (None,))[0]
    for cfg, (v, t, sha) in d.items():
        cnt[(cfg.split(".")[0], v)] += 1
        if v in ("ACCEPTED", "REJECTED") and off in ("ACCEPTED", "REJECTED") and v != off:
            bad.append((c, cfg, v, off, exp))
        if v == "ACCEPTED" and exp == "REJECTED":
            bad.append((c, cfg, v, off, exp, "CRITICAL"))
    # export identity (exact presets must equal the official export when both accept)
    if "fast-exact" in d and "reference" in d and d["fast-exact"][0] == d["reference"][0] == "ACCEPTED":
        cnt[("export-identical(fast-exact)", d["fast-exact"][2] == d["reference"][2])] += 1
    if "sound" in d and "reference" in d and d["sound"][0] == d["reference"][0] == "ACCEPTED":
        cnt[("export-identical(sound)", d["sound"][2] == d["reference"][2])] += 1
print("cases with results:", len(V))
for k, n in sorted(cnt.items(), key=str): print(" ", k, n)
print("disagreements:", len(bad))
for b in bad: print("  ", b)
