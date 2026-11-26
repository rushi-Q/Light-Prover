#!/usr/bin/python3 -I
"""styles.py RESULTS.jsonl... [--md] -> per-module verification cost of each CONTENT kind (wide cases only):
build CPU per module (B2 = official lean, from sched.out), export bytes per module, official check (C0: nanoda + Lean
kernel, single-threaded) and sound check (CS) seconds per module above the 1-module case (fixed part removed)."""
import json, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from table import load  # noqa: E402


def main():
    a = sys.argv[1:]; md = "--md" in a; a = [x for x in a if x != "--md"]
    recs = load(a)
    base_chk = {}
    for (c, p), r in recs.items():
        if c.endswith("-wide-1-tiny") and r.get("verdict") == "ACCEPTED":
            base_chk[(c.split("-")[0], p)] = (r.get("stage_seconds") or {}).get("checks_total", 0)
    rows = []
    for (c, p), r in recs.items():
        parts = c.split("-")
        if len(parts) != 4 or parts[1] != "wide" or parts[2] in ("1",) or p != "fast-exact":
            continue
        n = int(parts[2]); base, kind = parts[0], parts[3]
        ref, snd = recs.get((c, "reference")), recs.get((c, "sound"))
        sc = r.get("sched") or {}
        size = (r.get("export") or {}).get("size") or 0
        def chk(x, p):
            return ((x.get("stage_seconds") or {}).get("checks_total", 0) - base_chk.get((base, p), 0)) if x else None
        c0, cs = chk(ref, "reference"), chk(snd, "sound")
        rows.append([c, kind, base, str(n), f"{sc.get('sum_cpu', 0) / (n + 1):.2f}", f"{size / (n + 1) / 1e3:.0f}",
                     f"{c0 / n * 1000:.0f}" if c0 is not None else "", f"{cs / n * 1000:.0f}" if cs is not None else ""])
    hdr = ["case", "content", "base", "N", "build CPU-s/module (official lean)", "export KB/module",
           "official check ms/module", "sound check ms/module"]
    if md:
        print("| " + " | ".join(hdr) + " |"); print("|" + "---|" * len(hdr))
        for r in rows: print("| " + " | ".join(r) + " |")
    else:
        for r in [hdr] + rows: print("  ".join(r))


if __name__ == "__main__":
    main()
