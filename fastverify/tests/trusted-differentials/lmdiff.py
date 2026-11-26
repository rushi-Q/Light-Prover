#!/usr/bin/python3 -I
"""lmdiff.py BASEDIR WORK [--per-op N] [--seed S] [--jobs J] [--sut SCRIPT] : differential of an alternative trusted
check (default: check/lowmem/check-sound-lowmem.sh) against the unchanged check/sound/check-sound.sh on the
structure-aware export mutants (tests/export-fuzz/xfuzz.py, 52 operators) of one base (BASEDIR/out/{solution,challenge}
.export + BASEDIR/challenge/comparator.json).
Rows: CRITICAL = SUT ACCEPTED, reference not; AVAIL = reference ACCEPTED, SUT not; DECLINE-DIFF = one gave no verdict;
AGREE otherwise."""
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

_here = os.path.dirname(os.path.realpath(__file__))
_pkg = os.path.dirname(os.path.dirname(_here))
LL = os.environ.get("LIGHT_LEAN", "$LIGHT_LEAN")
PKGROOT = _pkg if os.path.isfile(os.path.join(_pkg, "check", "sound", "check-sound.sh")) else os.path.join(LL, "fastverify")
XF = os.path.join(PKGROOT, "tests/export-fuzz/xfuzz.py")
REF = os.path.join(PKGROOT, "check/sound/check-sound.sh")
SUT = os.path.join(PKGROOT, "check/lowmem/check-sound-lowmem.sh")


def run(script, ex, ch, cfg, jf, threads):
    t = time.time()
    p = subprocess.run([script, ex, ch, cfg, "--threads", str(threads), "--json", jf], capture_output=True, text=True)
    try:
        j = json.load(open(jf))
    except Exception:
        j = {"verdict": "NOJSON"}
    return j.get("verdict"), p.returncode, str(j.get("reason"))[:200], round(time.time() - t, 2)


def main(argv):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("work")
    ap.add_argument("--per-op", type=int, default=4)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--sut", default=SUT)
    ap.add_argument("--ops", default="all")
    a = ap.parse_args(argv)
    os.makedirs(a.work, exist_ok=True)
    sol = os.path.join(a.base, "out", "solution.export")
    ch = os.path.join(a.base, "out", "challenge.export")
    cfg = os.path.join(a.base, "challenge", "comparator.json")
    tg = ",".join(json.load(open(cfg))["theorem_names"])
    md = os.path.join(a.work, "mut")
    subprocess.run([sys.executable, XF, "gen", sol, md, "--ops", a.ops, "--per-op", str(a.per_op), "--seed",
                    str(a.seed), "--targets", tg], check=True, capture_output=True)
    rows = [ln.rstrip("\n").split("\t") for ln in open(os.path.join(md, "manifest.tsv")) if ln.strip()]
    rows = [r for r in rows if r and os.path.exists(os.path.join(md, r[0] + ".ndjson"))]
    rows = [["base", "BASE", "-", "unmutated"]] + rows

    def one(r):
        mid = r[0]
        ex = sol if mid == "base" else os.path.join(md, mid + ".ndjson")
        ref = run(REF, ex, ch, cfg, os.path.join(a.work, mid + ".ref.json"), a.threads)
        sut = run(a.sut, ex, ch, cfg, os.path.join(a.work, mid + ".sut.json"), a.threads)
        return r, ref, sut

    with ThreadPoolExecutor(a.jobs) as pool:
        res = list(pool.map(one, rows))
    counts = {}
    out = []
    for r, ref, sut in res:
        rv, sv = ref[0], sut[0]
        if sv == "ACCEPTED" and rv != "ACCEPTED":
            cl = "CRITICAL"
        elif rv == "ACCEPTED" and sv != "ACCEPTED":
            cl = "AVAIL"
        elif rv != sv:
            cl = "DECLINE-DIFF"
        else:
            cl = "AGREE"
        counts[cl] = counts.get(cl, 0) + 1
        line = f"{cl}\t{r[0]}\t{r[1]}\tref={rv}\tsut={sv}\t{ref[3]}s/{sut[3]}s"
        if cl != "AGREE":
            line += f"\tref: {ref[2]}\tsut: {sut[2]}"
            print(line)
        out.append(line)
    open(os.path.join(a.work, "rows.tsv"), "w").write("\n".join(out) + "\n")
    print("RESULT", json.dumps(counts), len(res), "inputs")
    return 1 if counts.get("CRITICAL") else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
