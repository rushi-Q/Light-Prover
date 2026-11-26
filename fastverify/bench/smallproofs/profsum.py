#!/usr/bin/python3 -I
"""profsum.py CORPUS PROFDIR OUT.tsv : parse Lean's '-Dprofiler=true' cumulative times per case (seconds) and group them:
import | elab = elaboration + tactic execution + typeclass inference + instantiate metavars + ... | interp (IR interpreter:
tactic code of Mathlib run interpreted) | kernel = type checking | lint = linting* | other."""
import glob, json, os, re, sys
corpus, pd, out = sys.argv[1:4]
cases = json.load(open(os.path.join(corpus, "cases.json")))
U = {"s": 1.0, "ms": 1e-3, "us": 1e-6, "μs": 1e-6, "ns": 1e-9}
rows = []; cats = set()
for f in sorted(glob.glob(os.path.join(pd, "*.prof"))):
    c = os.path.basename(f)[:-5]
    txt = open(f, errors="replace").read()
    d = {}
    if "cumulative profiling times:" in txt:
        for ln in txt.split("cumulative profiling times:")[1].splitlines():
            m = re.match(r"^\s+(.+?)\s+([0-9.]+)(s|ms|us|μs|ns)$", ln)
            if m:
                d[m.group(1)] = float(m.group(2)) * U[m.group(3)]
    w = re.search(r"WALL ([0-9.]+)", txt); rc = re.search(r"RC (\d+)", txt)
    cats |= set(d)
    rows.append((c, d, float(w.group(1)) if w else None, int(rc.group(1)) if rc else None))
def grp(d):
    imp = d.get("import", 0); kern = d.get("type checking", 0); interp = d.get("interpretation", 0)
    lint = sum(v for k, v in d.items() if "lint" in k.lower())
    init = d.get("initialization", 0)
    elab = sum(v for k, v in d.items() if k not in ("import", "type checking", "interpretation", "initialization")
               and "lint" not in k.lower())
    return imp, init, elab, interp, kern, lint
with open(out, "w") as fo:
    fo.write("case\tstyle\timports\trc\twall\timport\tinit\telab\tinterp\tkernel\tlint\ttop_elab_categories\n")
    for c, d, w, rc in rows:
        imp, init, elab, interp, kern, lint = grp(d)
        top = sorted(((v, k) for k, v in d.items() if k not in ("import", "type checking", "interpretation", "initialization")
                      and "lint" not in k.lower()), reverse=True)[:4]
        fo.write("\t".join(map(str, [c, cases.get(c, {}).get("style"), cases.get(c, {}).get("imports"), rc, w,
                                     round(imp, 3), round(init, 3), round(elab, 3), round(interp, 3), round(kern, 3),
                                     round(lint, 3), "; ".join(f"{k} {v:.3f}" for v, k in top)])) + "\n")
print(len(rows), "rows ->", out)
