#!/usr/bin/env python3
"""mktable.py SUMM.jsonl... : markdown rows (case | preset | build attempts | build / export / check | total | export sha) from
summ.py output lines; total = preflight + prepare + build + export + checks_total (+ confirm_reject)."""
import json, sys
rows = []
for p in sys.argv[1:]:
    for ln in open(p):
        ln = ln.strip()
        if not ln.startswith("{"): continue
        r = json.loads(ln); s = r.get("stage") or {}
        chk = s.get("checks_total") or 0
        tot = sum(s.get(k) or 0 for k in ("preflight", "prepare", "build", "export", "sha256_export")) + chk + (s.get("confirm_reject") or 0)
        rows.append((r["run"], r.get("verdict"), r.get("build_attempts"), s.get("build"), s.get("export"), chk, round(tot, 1),
                     (r.get("export") or [None, None, ""])[2], (r.get("export") or [None, None])[1]))
print("| run | verdict | build attempts | build s | export s | check s | total s | export sha (size) |")
print("|---|---|---|---|---|---|---|---|")
for x in rows:
    print(f"| {x[0]} | {x[1]} | {x[2]} | {x[3]} | {x[4]} | {x[5]} | {x[6]} | {x[7]} ({x[8]}) |")
