#!/usr/bin/python3 -I
"""model.py RESULTS.jsonl... [--md]  -> split every run into a FIXED part and a SCALING part, per preset and base.

T(preset, project) = F(preset, base) + S(preset, project)
F = the total of the 1-module case of the same base (`core-wide-1-tiny`, `mathlib-wide-1-tiny`) with the same preset in
the same result file(s): preflight, planner/plugin/zygote start, Lake workspace load, exporter/checker start-up, pins.
S = T - F: what grows with the project (lean processes, critical path, export size, kernel work of the closure).
Prints per case: F and S of `reference` and `sound`, the speed-up of the scaling part S_ref / S_sound (the asymptotic
speed-up for large projects of that shape) and the break-even scale factor k* (the project scaled k times in S would
make both presets equally fast: F_snd + k S_snd = F_ref + k S_ref -> k* = (F_snd - F_ref) / (S_ref - S_snd))."""
import json, sys
from collections import OrderedDict

sys.path.insert(0, __import__("os").path.dirname(__file__))
from table import load  # noqa: E402


def main():
    a = sys.argv[1:]
    md = "--md" in a
    a = [x for x in a if x != "--md"]
    recs = load(a)
    tot = OrderedDict()
    for (c, p), r in recs.items():
        if r.get("verdict") in ("ACCEPTED", "REJECTED"):
            tot[(c, p)] = r["wall"]
    fixed = {}
    for base in ("core", "mathlib"):
        for p in ("reference", "fast-exact", "sound", "sound-nozy"):
            # median over the plain run and its repeats (tags r2, r3, ...): the fixed part is load-sensitive
            vs = sorted(v for (c, pp), v in tot.items() if c == f"{base}-wide-1-tiny" and
                        (pp == p or (pp.startswith(p + "-r") and pp[len(p) + 2:].isdigit())))
            if vs:
                fixed[(base, p)] = vs[len(vs) // 2]
    hdr = ["case", "F ref", "S ref", "F sound", "S sound", "S_ref/S_sound", "total ref/sound", "break-even k*"]
    rows = []
    cases = []
    for (c, p) in tot:
        if c not in cases:
            cases.append(c)
    for c in cases:
        base = c.split("-")[0]
        tr, ts = tot.get((c, "reference")), tot.get((c, "sound"))
        fr, fs = fixed.get((base, "reference")), fixed.get((base, "sound"))
        if None in (tr, ts, fr, fs) or c.endswith("-1-tiny"):
            continue
        sr, ss = tr - fr, ts - fs
        ratio = f"{sr / ss:.2f}x" if ss > 0.5 else "(S_sound ~ 0)"
        if sr > ss and ss >= 0:
            k = (fs - fr) / (sr - ss)
            ke = f"{k:.2f}" if k > 0 else "always faster"
        else:
            ke = "never (S_sound >= S_ref)"
        rows.append([c, f"{fr:.1f}", f"{sr:.1f}", f"{fs:.1f}", f"{ss:.1f}", ratio, f"{tr / ts:.2f}x", ke])
    if md:
        print("| " + " | ".join(hdr) + " |"); print("|" + "---|" * len(hdr))
        for r in rows:
            print("| " + " | ".join(r) + " |")
    else:
        w = [max(len(h), *(len(r[i]) for r in rows)) for i, h in enumerate(hdr)] if rows else [len(h) for h in hdr]
        print("  ".join(h.ljust(w[i]) for i, h in enumerate(hdr)))
        for r in rows:
            print("  ".join(x.ljust(w[i]) for i, x in enumerate(r)))
    print("fixed parts:", {f"{b}/{p}": v for (b, p), v in fixed.items()})


if __name__ == "__main__":
    main()
