#!/usr/bin/python3 -I
"""collect.py CORPUS OUT.tsv SUMMARY_TSV:RUNSDIR ... : one row per run with per-stage seconds (from result.json)."""
import json, os, sys
corpus, out = sys.argv[1], sys.argv[2]
cases = json.load(open(os.path.join(corpus, "cases.json")))
rows = []
for spec in sys.argv[3:]:
    summ, runs = spec.split(":")
    for ln in open(summ):
        f = ln.rstrip("\n").split("\t")
        if len(f) < 8: continue
        tag, case, preset, kind, rc, wall, host, when = f[:8]
        d = os.path.join(runs, tag)
        try:
            r = json.load(open(os.path.join(d, "result.json")))
        except Exception:
            r = {}
        ss = r.get("stage_seconds") or {}
        ce = (r.get("inputs") or {}).get("challenge_export") or {}
        b = r.get("build") or {}
        st = ((b.get("attempts") or [{}])[-1].get("stage") or {})
        t1 = [u for u in (st.get("unsafe") or []) if str(u).startswith("toolchain-T1")]
        chk = sum(v for k, v in ss.items() if k.startswith("check_") and isinstance(v, (int, float)))
        c = cases.get(case, {})
        rows.append({"case": case, "style": c.get("style"), "imports": c.get("imports"), "n_thm": c.get("n_theorems"),
                     "preset": preset, "challenge": kind, "rc": rc, "verdict": r.get("verdict"), "trust": r.get("trust"),
                     "wall": float(wall), "preflight": ss.get("preflight"), "prepare": ss.get("prepare"),
                     "build": ss.get("build"), "export": ss.get("export"), "check": round(chk, 3),
                     "build_opt": b.get("option"), "export_opt": (r.get("export") or {}).get("option"),
                     "export_bytes": (r.get("export") or {}).get("size"), "challenge_s": ce.get("seconds"),
                     "export_sha": (r.get("export") or {}).get("sha256"), "t1": t1[0] if t1 else "", "host": host,
                     "when": when})
keys = list(rows[0].keys()) if rows else []
with open(out, "w") as fo:
    fo.write("\t".join(keys) + "\n")
    for x in rows:
        fo.write("\t".join("" if x[k] is None else str(x[k]) for k in keys) + "\n")
print(len(rows), "rows ->", out)
