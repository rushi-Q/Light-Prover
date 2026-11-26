#!/usr/bin/env python3
"""autoshorten.py — G2 proof shortening by automated closers. Untrusted tool: it only proposes edits;
an edited tree is claimed correct only when the trusted check ACCEPTS it against the official challenge.

  autoshorten.py --proj PROJ --src SRC --modules LIST --out OUT [--ladder FILE] [--hb N] [--mode greedy|all|top]
                 [--min-lines N] [--jobs J] [--timeout SEC] [--leaf-only] [--prefer t1,t2,..] [--exclude t,..]
                 [--skip-try]

  PROJ     a built tree of the project (its .lake/build/lib/lean and .lake/packages/*/.lake/build/lib/lean give
           LEAN_PATH; read-only), e.g. a B1 build tree of RH
  SRC      the project's source root (module files relative to it), LIST = module files (relative paths), one per line
  OUT      results: OUT/try (TryAt results per module), OUT/tree (edited modules only, same relative paths),
           OUT/edits.tsv (the shared edit-list format against SRC: module, first line, last line, replace, P06, text),
           OUT/apply.jsonl (one summary per module), OUT/summary.txt (stats.py)
Steps: (1) tryat_batch.sh: TryAt.lean in bwrap per module (tries the ladder on the goals before every suffix of every
tactic sequence of theorem/lemma proofs); (2) apply.py per module with a candidate: apply the non-overlapping successful
replacements (preferred tactic per position), re-elaborate the module with the official lean in bwrap, revert edits
that break it; (3) stats.py.
"""
import argparse, json, os, subprocess, sys, concurrent.futures as cf

T = os.path.dirname(os.path.realpath(__file__))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proj", required=True); ap.add_argument("--src", required=True)
    ap.add_argument("--modules", required=True); ap.add_argument("--out", required=True)
    ap.add_argument("--ladder", default=os.path.join(T, "ladder-default.txt"))
    ap.add_argument("--hb", default="20000"); ap.add_argument("--mode", default="greedy")
    ap.add_argument("--min-lines", default="2"); ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("--timeout", default="1800"); ap.add_argument("--leaf-only", action="store_true")
    ap.add_argument("--prefer", default=None); ap.add_argument("--exclude", default=None)
    ap.add_argument("--skip-try", action="store_true")
    a = ap.parse_args()
    out = os.path.abspath(a.out); src = os.path.abspath(a.src); proj = os.path.abspath(a.proj)
    os.makedirs(out, exist_ok=True)
    tw = os.path.join(out, "try")
    if not a.skip_try:
        subprocess.run([os.path.join(T, "tryat_batch.sh"), proj, src, os.path.abspath(a.modules), tw,
                        os.path.abspath(a.ladder), a.hb, a.mode, a.min_lines, str(a.jobs), a.timeout], check=False)
    idx = [l.split() for l in open(os.path.join(tw, "index.txt"))]
    todo = []
    for n, rel in idx:
        rf = os.path.join(tw, "res", n + ".jsonl")
        if os.path.exists(rf) and any(json.loads(l).get("ok") for l in open(rf) if l.strip()):
            todo.append((n, rel, rf))
    tree = os.path.join(out, "tree")
    edits = os.path.join(out, "edits.tsv")
    if os.path.exists(edits):
        os.unlink(edits)
    os.makedirs(os.path.join(out, "edits.d"), exist_ok=True)

    def one(t):
        n, rel, rf = t
        cmd = [sys.executable, os.path.join(T, "apply.py"), proj, rel, src, rf, tree,
               "--edits", os.path.join(out, "edits.d", n + ".tsv")]
        if a.leaf_only: cmd.append("--leaf-only")
        if a.prefer: cmd += ["--prefer", a.prefer]
        if a.exclude: cmd += ["--exclude", a.exclude]
        p = subprocess.run(cmd, capture_output=True, text=True)
        line = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else json.dumps({"module": rel, "status": "apply-failed", "stderr": p.stderr[-300:]})
        return line

    with cf.ThreadPoolExecutor(a.jobs) as ex, open(os.path.join(out, "apply.jsonl"), "w") as o:
        for line in ex.map(one, todo):
            o.write(line + "\n")
    with open(edits, "w") as e:
        for n, rel, rf in todo:
            f = os.path.join(out, "edits.d", n + ".tsv")
            if os.path.exists(f):
                e.write(open(f).read())
    # modules whose edits did not verify keep no file in tree (apply.py writes the original back: remove unchanged ones)
    for n, rel, rf in todo:
        p = os.path.join(tree, rel)
        if os.path.exists(p) and open(p, "rb").read() == open(os.path.join(src, rel), "rb").read():
            os.unlink(p)
    s = subprocess.run([sys.executable, os.path.join(T, "stats.py"), tw] + (["--prefer", a.prefer] if a.prefer else []),
                       capture_output=True, text=True).stdout
    tot = dict(modules=len(idx), with_candidates=len(todo), applied=0, reverted=0, lines0=0, lines1=0, chars0=0, chars1=0,
               orig_wall=0.0, new_wall=0.0)
    for l in open(os.path.join(out, "apply.jsonl")):
        r = json.loads(l)
        if r.get("status") != "ok": continue
        for k in ("applied", "reverted", "lines0", "lines1", "chars0", "chars1"):
            tot[k] += r.get(k, 0)
        if "new" in r:
            tot["orig_wall"] += r["orig"]["wall"]; tot["new_wall"] += r["new"]["wall"]
    open(os.path.join(out, "summary.txt"), "w").write(s + "\napply totals: " + json.dumps(tot) + "\n")
    print(s); print("apply totals:", json.dumps(tot))


if __name__ == "__main__":
    main()
