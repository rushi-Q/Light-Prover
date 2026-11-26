#!/usr/bin/python3 -I
"""tools/ci/ci-summary.py TSV... : per-flow summary of tools/ci/ci-chain.sh result tables (one TSV per flow).
Prints per TSV: commits, verdicts, wall per commit (median / mean / max / sum) and the stage medians
(official: build / export / comparator; sound: build / export / check / warm-up), and a per-commit verdict matrix when
several TSVs are given (same commit index -> verdicts side by side; 'DIFF' marks a disagreement)."""
import json, statistics, sys, os


def load(p):
    rows = []
    for l in open(p):
        f = l.rstrip("\n").split("\t")
        if len(f) < 5:
            continue
        try:
            j = json.loads(f[4])
        except Exception:  # noqa: BLE001
            j = {}
        rows.append({"i": int(f[0]), "commit": f[1], "rc": int(f[2]), "wall": float(f[3]), "j": j})
    return rows


def stages(r):
    j = r["j"]
    if "flow" in j:   # official-incr
        return {"build": j.get("build_s"), "export": j.get("export_s"), "check": j.get("check_s"), "verdict": j.get("verdict")}
    a = (j.get("attempts") or [{}])[-1]
    return {"build": sum(x.get("build_s", 0) for x in j.get("attempts", [])), "export": sum(x.get("export_s", 0) for x in j.get("attempts", [])),
            "check": sum(x.get("check_s", 0) for x in j.get("attempts", [])), "warmup": j.get("warmup_s"),
            "verdict": j.get("verdict"), "dirty": a.get("dirty"), "attempts": len(j.get("attempts", []))}


def med(xs):
    xs = [x for x in xs if isinstance(x, (int, float))]
    return round(statistics.median(xs), 1) if xs else None


tabs = {os.path.basename(p): load(p) for p in sys.argv[1:]}
for name, rows in tabs.items():
    if not rows:
        print(name, "empty"); continue
    st = [stages(r) for r in rows]
    w = [r["wall"] for r in rows]
    vs = {}
    for s in st:
        vs[s["verdict"]] = vs.get(s["verdict"], 0) + 1
    print(f"{name}: {len(rows)} commits {rows[0]['i']}..{rows[-1]['i']} verdicts {vs} | wall/commit median {med(w)} mean "
          f"{round(sum(w)/len(w), 1)} max {round(max(w), 1)} sum {round(sum(w))} | stage medians build {med([s['build'] for s in st])}"
          f" export {med([s['export'] for s in st])} check {med([s['check'] for s in st])}"
          + (f" warmup {med([s.get('warmup') for s in st])}" if any(s.get('warmup') for s in st) else ""))
if len(tabs) > 1:
    idx = sorted({r["i"] for rows in tabs.values() for r in rows})
    print("\ncommit  " + "  ".join(n[:22].ljust(22) for n in tabs))
    for i in idx:
        cells, verd = [], set()
        for rows in tabs.values():
            r = next((r for r in rows if r["i"] == i), None)
            if r is None:
                cells.append("-".ljust(22)); continue
            s = stages(r); verd.add(s["verdict"])
            cells.append(f"{s['verdict'] or r['rc']} {r['wall']:.0f}s".ljust(22))
        print(f"{i:5d}   " + "  ".join(cells) + ("  DIFF" if len(verd) > 1 else ""))
