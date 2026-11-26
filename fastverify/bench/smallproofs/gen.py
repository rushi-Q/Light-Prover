#!/usr/bin/python3 -I
"""gen.py OUTDIR [TOOLCHAIN] : small-proof corpus generator (with TOOLCHAIN, e.g. leanprover/lean4:v4.36.0: only the
core-only problems + bC, for the other-Lean-version test).
Writes OUTDIR/challenges/<id> (Challenge.lean with `sorry`, comparator.json, lakefile.toml, lean-toolchain,
lake-manifest.json) and OUTDIR/projects/<id> (Solution.lean with the proof) for every problem of problems.py, plus
batch cases: bM (all Mathlib problems in one module), bC (all core-only problems), bM10a.. (10-problem slices).
Challenge and solution statements are textually identical. Toolchain v4.33.1, Mathlib 0df444a (trusted workspace
manifest with only `name` changed); core-only problems have no dependencies (manifest packages = [])."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import problems

TOOLCHAIN = "leanprover/lean4:v4.33.1\n"
WS = os.environ.get("FV_PACKAGES") or os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))), "verify", "challenge")   # trusted workspace (its lake-manifest.json)
REQ = ('[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\n'
       'rev = "0df444a360eaa60ab8c11dca51a86af692955474"\n\n')
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def manifest(pkg, deps):
    if deps:
        m = json.load(open(os.path.join(WS, "lake-manifest.json"), encoding="utf-8"))
    else:
        m = {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [], "lakeDir": ".lake",
             "fixedToolchain": False}
    m["name"] = pkg
    return json.dumps(m, indent=1) + "\n"


def write(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(s)


def emit(out, cid, items, imports, preamble=""):
    """items: [(name, statement, proof)]; imports: list of module names ([] = core only); preamble: definitions shared by
    challenge and solution (placed before the theorems)."""
    deps = any(i.startswith("Mathlib") for i in imports)
    hdr = "".join(f"import {i}\n" for i in imports) + ("\n" if imports else "") + (preamble + "\n\n" if preamble else "")
    ch = hdr + "".join(f"theorem {n} {s} := by sorry\n\n" for n, s, _ in items)
    so = hdr + "".join(f"theorem {n} {s} := {p}\n\n" for n, s, p in items)
    cfg = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": [n for n, _, _ in items],
           "definition_names": [], "permitted_axioms": AXIOMS}
    pk = "sp_" + cid.replace("-", "_")
    for kind, mod, src in (("challenges", "Challenge", ch), ("projects", "Solution", so)):
        d = os.path.join(out, kind, cid)
        name = pk + ("challenge" if kind == "challenges" else "")
        write(os.path.join(d, f"{mod}.lean"), src)
        write(os.path.join(d, "lean-toolchain"), TOOLCHAIN)
        write(os.path.join(d, "lakefile.toml"), f'name = "{name}"\ndefaultTargets = ["{mod}"]\n\n' + (REQ if deps else "")
              + f'[[lean_lib]]\nname = "{mod}"\n')
        write(os.path.join(d, "lake-manifest.json"), manifest(name, deps))
        if kind == "challenges":
            write(os.path.join(d, "comparator.json"), json.dumps(cfg, indent=1) + "\n")


def main():
    global TOOLCHAIN
    out = sys.argv[1]
    core_only = len(sys.argv) > 2   # gen.py OUTDIR TOOLCHAIN: core-only problems on another toolchain
    if core_only:
        TOOLCHAIN = sys.argv[2].strip() + "\n"
    cases = {}
    for (i, style, imp, st, pr, *pre) in problems.P:
        if core_only and imp:
            continue
        emit(out, i, [(i, st, pr)], [imp] if imp else [], pre[0] if pre else "")
        cases[i] = {"style": style, "imports": imp or "(core)", "n_theorems": 1,
                    "expected": "REJECTED" if style.startswith("neg") else "ACCEPTED"}
    mp = [] if core_only else [x for x in problems.P if x[2] == "Mathlib" and not x[1].startswith(("neg", "same")) and len(x) == 5]
    cp = [x for x in problems.P if x[2] == "" and not x[1].startswith(("kscale", "neg")) and len(x) == 5]   # bC: the 24 core problems (series excluded)
    if mp:
        emit(out, "bM", [(x[0], x[3], x[4]) for x in mp], ["Mathlib"])
        cases["bM"] = {"style": "batch", "imports": "Mathlib", "n_theorems": len(mp)}
    emit(out, "bC", [(x[0], x[3], x[4]) for x in cp], [])
    cases["bC"] = {"style": "batch", "imports": "(core)", "n_theorems": len(cp)}
    for k in range(0, len(mp), 10):
        cid = f"bM10{chr(ord('a') + k // 10)}"
        sl = mp[k:k + 10]
        emit(out, cid, [(x[0], x[3], x[4]) for x in sl], ["Mathlib"])
        cases[cid] = {"style": "batch10", "imports": "Mathlib", "n_theorems": len(sl)}
    write(os.path.join(out, "cases.json"), json.dumps(cases, indent=1) + "\n")
    print(f"{len(cases)} cases -> {out}")


if __name__ == "__main__":
    main()
