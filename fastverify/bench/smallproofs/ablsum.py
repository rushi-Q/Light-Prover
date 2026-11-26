#!/usr/bin/python3 -I
"""ablsum.py RUNSDIR : median (over repeats) wall and stage seconds per case x configuration of ablate.sh runs."""
import glob, json, os, statistics as S, sys
from collections import defaultdict
g = defaultdict(list)
for d in glob.glob(os.path.join(sys.argv[1], "*")):
    if not os.path.isdir(d): continue
    p = os.path.basename(d).split(".")
    case, preset, tag = p[0], p[1], ".".join(p[2:])
    cfg = preset + ("-" + tag.rsplit(".", 1)[0] if "." in tag else "")
    try: r = json.load(open(os.path.join(d, "result.json")))
    except Exception: continue
    if r.get("verdict") not in ("ACCEPTED", "REJECTED"): continue
    ss = r.get("stage_seconds", {})
    w = (__import__("datetime").datetime.fromisoformat(r["finished"].replace("Z", "+00:00")) -
         __import__("datetime").datetime.fromisoformat(r["started"].replace("Z", "+00:00"))).total_seconds() \
        if r.get("finished") and r.get("started") else None
    chk = sum(v for k, v in ss.items() if k.startswith("check_"))
    bo = (r.get("build") or {}).get("option"); eo = (r.get("export") or {}).get("option")
    g[(case, cfg)].append((w, ss.get("preflight"), ss.get("build"), ss.get("export"), chk, bo, eo, r.get("verdict")))
print("case\tconfig\tn\twall_med\tpreflight\tbuild\texport\tcheck\tother(=wall-stages)\tbuild_opt\texport_opt\tverdict")
for (case, cfg), L in sorted(g.items()):
    med = lambda i: round(S.median([x[i] for x in L if x[i] is not None]), 1) if any(x[i] is not None for x in L) else 0.0
    wm = med(0); st = [med(i) for i in (1, 2, 3, 4)]
    print("\t".join(map(str, [case, cfg, len(L), wm] + st + [round(wm - sum(st), 1), L[0][5], L[0][6], L[0][7]])))
