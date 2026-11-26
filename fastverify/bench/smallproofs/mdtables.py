#!/usr/bin/python3 -I
"""mdtables.py ANATOMY.tsv TABLE.tsv [--per-case] : markdown tables of the small-proof study.
Total = wall of the run minus the one-time challenge build ('prepare'), i.e. what a verifier pays per proof when the
official challenge export is given. Columns per preset: preflight, build, export, check, other (= end-of-run re-verify etc.)."""
import csv, statistics as S, sys
from collections import defaultdict
an = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
tb = list(csv.DictReader(open(sys.argv[2]), delimiter="\t"))
per_case = "--per-case" in sys.argv
wall = {}
for r in tb:
    key = (r["case"], r["preset"] + ("" if not r.get("tag") else ""))
    wall[(r["case"], r["preset"], r.get("run_tag", ""))] = r
def f(x):
    try: return float(x)
    except Exception: return None
def g(x):
    return "-" if x is None else f"{x:.1f}"
W = {}
for r in tb:
    # table.tsv (collect.py) has wall and prepare; the tag is encoded in nothing -> use (case, preset, challenge kind, wall)
    W.setdefault((r["case"], r["preset"]), []).append(r)
rows = defaultdict(dict)
for r in an:
    tag = r["tag"] or ""
    cfg = r["preset"] + ("-" + tag if tag else "")
    rows[r["case"]][cfg] = r
def tot(case, cfg):
    r = rows[case].get(cfg)
    if not r: return None
    # find the matching collect row by preset + build option
    cands = [x for x in W.get((case, r["preset"]), []) if x["build_opt"] == r["build_opt"] and x["verdict"] == r["verdict"]
             and x["verdict"] in ("ACCEPTED", "REJECTED")]
    if not cands: return None
    x = cands[-1]
    return round(f(x["wall"]) - (f(x["prepare"]) or 0), 1)
cfgs = ["reference", "sound", "sound-B0", "fast-exact"]
styles = defaultdict(list)
out = []
hdr = "| case | style | imports | export MB | official: build / export / check / total | sound: build / export / check / total | sound --build B0 total | fast-exact total | official / sound |"
out.append(hdr); out.append("|" + "---|" * 9)
for case in sorted(rows, key=lambda c: (rows[c].get("reference", {}).get("style") or "", c)):
    R = rows[case].get("reference"); Sd = rows[case].get("sound")
    if not R or not Sd: continue
    to, ts, tb0, tfe = tot(case, "reference"), tot(case, "sound"), tot(case, "sound-B0"), tot(case, "fast-exact")
    if to is None or ts is None: continue
    styles[(R["style"], R["imports"])].append((to, ts, tb0, f(R["export_MB"]), f(R["build"]), f(R["export"]), f(R["check"]),
                                               f(Sd["build"]), f(Sd["export"]), f(Sd["check"]), tfe))
    if per_case:
        out.append(f"| {case} | {R['style']} | {R['imports']} | {R['export_MB']} | {g(f(R['build']))} / {g(f(R['export']))} / "
                   f"{g(f(R['check']))} / **{to}** | {g(f(Sd['build']))} / {g(f(Sd['export']))} / {g(f(Sd['check']))} / **{ts}** | "
                   f"{tb0 if tb0 is not None else '-'} | {tfe if tfe is not None else '-'} | {to / ts:.2f} |")
print("\n".join(out) if per_case else "")
print()
print("| style | imports | n | export MB (median) | official total | sound total | sound --build B0 total | fast-exact total | official build / export / check | sound build / export / check | official / sound |")
print("|" + "---|" * 11)
for (st, imp), L in sorted(styles.items()):
    m = lambda i: S.median([x[i] for x in L if x[i] is not None]) if any(x[i] is not None for x in L) else float("nan")
    print(f"| {st} | {imp} | {len(L)} | {m(3):.1f} | {m(0):.1f} | {m(1):.1f} | {m(2):.1f} | {m(10):.1f} | {m(4):.1f} / {m(5):.1f} / {m(6):.1f} | "
          f"{m(7):.1f} / {m(8):.1f} / {m(9):.1f} | {m(0) / m(1):.2f} |")
