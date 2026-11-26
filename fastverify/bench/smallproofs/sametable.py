#!/usr/bin/python3 -I
"""sametable.py ANATOMY.tsv TABLE.tsv PROFILE.tsv : markdown table of the 'same statement, different proof style' cases
(ids s<k>_<style>): per statement and style the closure size, the official stage times and total, the sound totals, and
Lean's profiler (elaboration / kernel ms)."""
import csv, sys
from collections import defaultdict
an = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
tb = list(csv.DictReader(open(sys.argv[2]), delimiter="\t"))
pf = {r["case"]: r for r in csv.DictReader(open(sys.argv[3]), delimiter="\t")}
def f(x):
    try: return float(x)
    except Exception: return None
tot = defaultdict(list)
for r in tb:
    if r["verdict"] in ("ACCEPTED", "REJECTED"):
        tot[(r["case"], r["preset"], r["build_opt"])].append(f(r["wall"]) - (f(r["prepare"]) or 0))
rows = defaultdict(dict)
for r in an:
    if not r["case"][:1] == "s" or "_" not in r["case"]: continue
    cfg = r["preset"] + ("-" + r["tag"] if r["tag"] else "")
    rows[r["case"]][cfg] = r
STMT = {}
import os, importlib.util
spec = importlib.util.spec_from_file_location("problems", os.path.join(os.path.dirname(os.path.abspath(__file__)), "problems.py"))
P = importlib.util.module_from_spec(spec); spec.loader.exec_module(P)
for x in P.P:
    if x[1] == "same": STMT[x[0].split("_")[0]] = x[3].lstrip(": ")
print("| statement | style | closure MB | elab / kernel ms (profiler) | official build / export / check / total | sound total | sound --build B0 total | fast-exact total |")
print("|---|---|---|---|---|---|---|---|")
last = None
for case in sorted(rows, key=lambda c: (c.split("_")[0], f(rows[c].get("reference", {}).get("export_MB")) or 0)):
    st, style = case.split("_", 1)
    R = rows[case].get("reference")
    if not R: continue
    def T(cfg, preset, bo):
        v = tot.get((case, preset, bo)); return f"{min(v):.1f}" if v else "-"
    p = pf.get(case, {})
    el = f"{1000*f(p['elab']):.0f} / {1000*f(p['kernel']):.0f}" if p.get("elab") else "-"
    stmt = f"`{STMT.get(st, st)}`" if st != last else ""
    last = st
    print(f"| {stmt} | {style} | {R['export_MB']} | {el} | {f(R['build']):.1f} / {f(R['export']):.1f} / {f(R['check']):.1f} / "
          f"**{T('reference','reference','B0')}** | {T('sound','sound','B3')} | {T('sound-B0','sound','B0')} | {T('fast-exact','fast-exact','B2')} |")
