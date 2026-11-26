#!/usr/bin/env python3
"""verifiers.py CORPUS WORKDIR [CASE_PREFIXES] -> WORKDIR/verifiers.tsv : how NAIVE verifier configurations judge every cheat case.

Every project is elaborated only inside bwrap (tools/lsand.sh: no network, / read-only, home hidden). Configurations:
  V1 compiles   : `lake build` exits 0 (the weakest check an evaluation harness can do)
  V2 no-sorry   : V1 and no "declaration uses 'sorry'" warning in the build output
  V3 axioms+text: V2, `#print axioms` of every target lists only permitted axioms (passes if EITHER common harness pattern
                  passes: appended to a copy of Solution.lean, or a separate `import Solution` file), and every challenge statement line
                  (`theorem NAME ... :=` prefix up to ':=') occurs verbatim in the solution sources (a common harness)
  V4 kernel     : the official lean4export of the targets' closure is accepted by the official Lean 4.36
                  `leanchecker --from-export` (a kernel replay WITHOUT the statement / axiom comparison)
The full verifiers (official lake comparator = preset reference, fastverify --preset sound / fast-exact / default) come
from RUNS/summary.tsv (run.sh).
"""
import json, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LSAND = os.path.join(HERE, "tools", "lsand.sh")
T36 = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0")
T33 = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1")
EXP = "$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export"   # official lean4export v4.33.0
EXPDIR = "$LIGHT_LEAN/env/tools/lean4export"
WS = "$LIGHT_LEAN/verify/challenge"
PERMITTED = {"propext", "Quot.sound", "Classical.choice"}

corpus, work = sys.argv[1], sys.argv[2]
cases = json.load(open(os.path.join(corpus, "cases.json")))
os.makedirs(work, exist_ok=True)

def sh(d, *cmd, timeout=900, ro=""):
    try:
        p = subprocess.run([LSAND, d] + list(cmd), capture_output=True, text=True, timeout=timeout,
                           env=dict(os.environ, LSAND_RO=ro))
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        return 124, "TIMEOUT"

def challenge_info(ch):
    cfg = json.load(open(os.path.join(corpus, "challenges", ch, "comparator.json")))
    src = open(os.path.join(corpus, "challenges", ch, "Challenge.lean"), encoding="utf-8").read()
    stmts = []
    for line in src.splitlines():
        m = re.match(r"theorem (\S+)(.*?):=", line)
        if m:
            stmts.append(line.split(":=")[0].strip())
    return cfg["theorem_names"], stmts

def one(cid):
    meta = cases[cid]
    names, stmts = challenge_info(meta["challenge"])
    d = os.path.join(work, cid)
    if os.path.exists(d):
        shutil.rmtree(d)
    shutil.copytree(os.path.join(corpus, "cases", cid), d)
    ro = ""
    if meta.get("mathlib"):   # trusted dependency workspace, read-only, at the project's Lake package path
        os.makedirs(os.path.join(d, ".lake"), exist_ok=True)
        os.symlink(os.path.join(WS, ".lake", "packages"), os.path.join(d, ".lake", "packages"))
        ro = WS
    rc, log = sh(d, "lake", "build", ro=ro)
    open(os.path.join(d, ".v-build.log"), "w").write(log)
    v1 = rc == 0
    v2 = v1 and "declaration uses 'sorry'" not in log and "declaration uses `sorry`" not in log
    def axioms_check(fname, text):
        with open(os.path.join(d, fname), "w", encoding="utf-8") as f:
            f.write(text)
        rc2, out = sh(d, "lake", "env", "lean", fname, ro=ro)
        open(os.path.join(d, ".v-%s.log" % fname), "w").write(out)
        found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
        none = re.findall(r"'([^']+)' does not depend on any axioms", out)
        seen = {n for n, _ in found} | set(none)
        bad = sorted({a.strip() for _, axs in found for a in axs.split(",") if a.strip() and a.strip() not in PERMITTED})
        ok = rc2 == 0 and seen >= set(names) and not bad
        det = ("bad axioms: " + ",".join(bad)) if bad else ("missing: " + ",".join(sorted(set(names) - seen)) if not seen >= set(names) else "")
        return ok, det
    axioms_ok, ax_detail, ok_app, ok_imp = False, "", False, False
    if v1:
        # two common harness patterns: (a) `#print axioms` appended to (a copy of) the solution file, re-elaborated with
        # `lake env lean`; (b) a separate file `import Solution` + `#print axioms` (reads the built .olean files)
        prints = "".join("#print axioms %s\n" % n for n in names)
        base = open(os.path.join(d, "Solution.lean"), encoding="utf-8").read()
        ok_app, det_app = axioms_check("VCheckA.lean", base + "\n" + prints)
        ok_imp, det_imp = axioms_check("VCheckB.lean", "import Solution\n" + prints)
        axioms_ok = ok_app or ok_imp
        ax_detail = "append:%s import:%s" % (det_app or "ok", det_imp or "ok")
    srcs = ""
    for root, _, files in os.walk(d):
        if ".lake" in root:
            continue
        for fn in files:
            if fn.endswith(".lean") and not fn.startswith("VCheck"):
                srcs += open(os.path.join(root, fn), encoding="utf-8", errors="replace").read() + "\n"
    text_ok = all(s in srcs for s in stmts)
    v3 = v2 and axioms_ok and text_ok
    # V4: kernel replay only: official lean4export (4.33) of the targets' closure + official leanchecker 4.36, both in bwrap
    v4, v4d = "no-build", ""
    if v1:
        env = dict(os.environ, LSAND_RO=":".join(x for x in (EXPDIR, T36, ro) if x))
        cmd = ("LP=$(lake env printenv LEAN_PATH); LEAN_ABORT_ON_PANIC=1 LEAN_PATH=$LP:%s %s Solution -- %s > .v-k.export 2> .v-k.err; echo EXPORT_RC=$?; "
               "%s --silent --from-export .v-k.export; echo CHECK_RC=$?") % (os.path.join(T33, "lib", "lean"), EXP, " ".join(names),
                                                                           os.path.join(T36, "bin", "leanchecker"))
        try:
            p = subprocess.run([LSAND, d, "sh", "-c", cmd], capture_output=True, text=True, timeout=1800, env=env)
            out = p.stdout + p.stderr
            erc = re.search(r"EXPORT_RC=(\d+)", out); crc = re.search(r"CHECK_RC=(\d+)", out)
            if not erc or erc.group(1) != "0":
                v4, v4d = "export-failed", open(os.path.join(d, ".v-k.err"), errors="replace").read().strip()[-150:]
            else:
                v4 = "ACCEPT" if crc and crc.group(1) == "0" else "REJECT"
                v4d = " ".join(l for l in out.splitlines() if "RC=" not in l)[-150:]
        except subprocess.TimeoutExpired:
            v4 = "TIMEOUT"
    return dict(case=cid, challenge=meta["challenge"], expected=meta["expected_official"],
                V1=v1, V2=v2, V3=v3, V3_axioms=axioms_ok, V3_append=ok_app, V3_import=ok_imp, V3_text=text_ok, V4=v4, detail=" ".join((ax_detail + " " + v4d).split())[:200])

if __name__ == "__main__":
    from concurrent.futures import ThreadPoolExecutor
    ids = sorted(cases)
    if len(sys.argv) > 3:
        ids = [i for i in ids if any(i.startswith(p) for p in sys.argv[3].split(","))]
    with ThreadPoolExecutor(int(os.environ.get("LANES", "8"))) as ex:
        res = list(ex.map(one, ids))
    cols = ["case", "challenge", "expected", "V1", "V2", "V3", "V3_axioms", "V3_append", "V3_import", "V3_text", "V4", "detail"]
    with open(os.path.join(work, "verifiers.tsv"), "w") as f:
        f.write("\t".join(cols) + "\n")
        for r in res:
            f.write("\t".join(str(r[c]) for c in cols) + "\n")
    for r in res:
        print("\t".join(str(r[c]) for c in cols))
