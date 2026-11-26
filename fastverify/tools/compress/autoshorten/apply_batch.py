#!/usr/bin/env python3
"""apply_batch.py TRY_WD SRC PROJ OUT [--jobs J] [--leaf-only | --leaf-or-hinted] [--prefer ..] [--exclude ..] [--lean-opts '-Dk=v ...']
Resumable apply step for a (possibly still running) tryat_batch.sh work dir: every FINISHED module (.done) with at least
one successful try is applied and re-verified by apply.py (once; OUT/apply.d/<n>.json marks it). Outputs:
OUT/tree (edited modules), OUT/edits.d/<n>.tsv (edit-list lines), OUT/apply.d/<n>.json (apply.py summary).
`cat OUT/edits.d/*.tsv` = the module-verified edit list."""
import json, os, subprocess, sys, concurrent.futures as cf

T = os.path.dirname(os.path.realpath(__file__))
a = sys.argv[1:]
wd, src, proj, out = [os.path.abspath(x) for x in a[:4]]
opt = lambda k, d=None: a[a.index(k) + 1] if k in a else d
jobs = int(opt("--jobs", "8"))
extra = (["--leaf-only"] if "--leaf-only" in a else []) + (["--leaf-or-hinted"] if "--leaf-or-hinted" in a else []) + (["--prefer", opt("--prefer")] if opt("--prefer") else []) \
    + (["--exclude", opt("--exclude")] if opt("--exclude") else []) \
    + (["--lean-opts", opt("--lean-opts")] if opt("--lean-opts") else [])
for d in ("tree", "edits.d", "apply.d"):
    os.makedirs(os.path.join(out, d), exist_ok=True)
todo = []
for ln in open(os.path.join(wd, "index.txt")):
    n, rel = ln.split()
    if not os.path.exists(os.path.join(wd, "res", n + ".done")) or os.path.exists(os.path.join(out, "apply.d", n + ".json")):
        continue
    rf = os.path.join(wd, "res", n + ".jsonl")
    if not os.path.exists(rf):
        continue
    ok = False
    for l in open(rf):
        if '"ok":true' in l:
            ok = True; break
    if ok:
        todo.append((n, rel, rf))
    else:
        json.dump({"module": rel, "status": "no-candidate"}, open(os.path.join(out, "apply.d", n + ".json"), "w"))


def one(t):
    n, rel, rf = t
    et = os.path.join(out, "edits.d", n + ".tsv")
    if os.path.exists(et):
        os.unlink(et)
    p = subprocess.run([sys.executable, os.path.join(T, "apply.py"), proj, rel, src, rf, os.path.join(out, "tree"),
                        "--edits", et] + extra, capture_output=True, text=True)
    line = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else json.dumps(
        {"module": rel, "status": "apply-failed", "stderr": p.stderr[-300:]})
    tp = os.path.join(out, "tree", rel)
    if os.path.exists(tp) and open(tp, "rb").read() == open(os.path.join(src, rel), "rb").read():
        os.unlink(tp)
    open(os.path.join(out, "apply.d", n + ".json"), "w").write(line + "\n")
    return line


with cf.ThreadPoolExecutor(jobs) as ex:
    for line in ex.map(one, todo):
        pass
print(f"applied {len(todo)} modules")
