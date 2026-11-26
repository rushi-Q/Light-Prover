#!/usr/bin/python3 -I
"""build/closureplan.py PLAN_IN PLAN_OUT MODULE [MODULE...] — restrict a Lake plan (plan.jsonl of build/planner) to the
import closure of MODULE(s) (B3 item `closure-only`, sound preset only, opt-in).

Why: the official Lean 4.36 `lake comparator` builds only the solution module (Lake/CLI/Check.lean: safeLakeBuild
#[module] = `lake build <solution_module>`), while B0-B3 build the project's DEFAULT targets. On libraries whose default
targets are much larger than the solution's closure (formal-conjectures: ~1,400 problem files vs 162 modules of the
challenge's library; per-claim checks of a big library) the rest is wasted work. Sound mode: UNTRUSTED (the build only
produces .olean files; the exporter reads only the closure of the solution module; a module missing from the closure can
only fail the build or the export -> no accept).
Records keep their exact argv/setup; deps outside the closure cannot occur (the closure is import-closed).
Exit 0 = written (stdout: one JSON line), 2 = MODULE not in the plan / malformed plan (caller: build unfiltered or decline).
"""
import json, sys


def main():
    if len(sys.argv) < 4:
        print(__doc__.split("\n")[0]); return 2
    src, dst, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
    with open(src) as f:
        lines = f.read().splitlines()
    header = json.loads(lines[0]); recs = []; end = None
    for l in lines[1:]:
        if not l.strip():
            continue
        r = json.loads(l)
        if "end" in r:
            end = r["end"]; break
        recs.append(r)
    if end != len(recs) or header.get("nmods") != len(recs):
        print(json.dumps({"closure": "error", "detail": "truncated or inconsistent plan"})); return 2
    by = {r["name"]: r for r in recs}
    missing = [m for m in roots if m not in by]
    if missing:
        print(json.dumps({"closure": "error", "detail": f"not in the plan: {missing[:5]}"})); return 2
    keep, stack = set(roots), list(roots)
    while stack:
        for d in by[stack.pop()]["deps"]:
            if d in by and d not in keep:
                keep.add(d); stack.append(d)
    hd = dict(header); hd["nmods"] = len(keep); hd["closure_of"] = roots; hd["closure_from"] = len(recs)
    with open(dst + ".tmp", "w") as f:
        f.write(json.dumps(hd) + "\n")
        for r in recs:                     # original (topological) order
            if r["name"] in keep:
                f.write(json.dumps(r) + "\n")
        f.write(json.dumps({"end": len(keep)}) + "\n")
    import os
    os.replace(dst + ".tmp", dst)
    print(json.dumps({"closure": "ok", "roots": roots, "modules": len(keep), "of": len(recs)}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
