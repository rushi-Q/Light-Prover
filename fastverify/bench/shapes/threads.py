#!/usr/bin/python3 -I
"""threads.py LABEL=RESULTS.jsonl ... [--md]  -> thread-scaling table: one row per (case, preset), one column per
(label, threads): total seconds (build seconds). LABEL distinguishes machines (e.g. dev6=..., amd=...); the thread count
of every run is taken from its record."""
import json, sys
from collections import OrderedDict


def main():
    a = sys.argv[1:]; md = "--md" in a; a = [x for x in a if x != "--md"]
    cells, cols = OrderedDict(), []
    for spec in a:
        label, path = spec.split("=", 1)
        if not __import__("os").path.exists(path):
            continue
        for line in open(path):
            r = json.loads(line)
            p = r["preset"] + ((" " + r["tag"]) if r.get("tag") and not r["tag"].startswith("t") else "")
            col = (label, r["threads"])
            if col not in cols:
                cols.append(col)
            s = r.get("stage_seconds") or {}
            cells.setdefault((r["case"], p), {})[col] = f"{r['wall']:.1f} ({s.get('build', 0):.1f})" + \
                ("" if r.get("verdict") == "ACCEPTED" else f" {r.get('verdict')}")
    cols.sort(key=lambda c: (c[0], c[1]))
    hdr = ["case", "preset"] + [f"{l} {t} thr" for l, t in cols]
    rows = [[c, p] + [v.get(col, "") for col in cols] for (c, p), v in sorted(cells.items())]
    if md:
        print("| " + " | ".join(hdr) + " |"); print("|" + "---|" * len(hdr))
        for r in rows:
            print("| " + " | ".join(r) + " |")
    else:
        for r in [hdr] + rows:
            print("  ".join(r))


if __name__ == "__main__":
    main()
