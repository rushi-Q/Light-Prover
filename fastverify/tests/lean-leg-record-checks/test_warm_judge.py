#!/usr/bin/python3 -I
"""test_warm_judge.py FVCHECKD BINS_DIR [SELFTEST_DIR] : the crafted record-check warm-delta cases of
test_warm_record_checks.py through the WHOLE warm judge (fvcheckd: ccmp-warm + pleanchecker-warm + gruszka-warm), against the cold
reference = check/sound/check-sound.sh on the materialized effective export E_eff = (B \\ dirty) U D (built here: B's
lines + the delta's declarations re-serialized under B's tables is not needed - each case also has a full-export twin).
Rows: case, warm verdict, cold verdict of the full twin. A warm ACCEPTED where cold is not ACCEPTED = 'MISMATCH'."""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import os  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "kernel-cves"))
from craft_cves import ExportBuilder, load_export  # noqa: E402
import test_warm_record_checks as W  # noqa: E402

PKG = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", ".."))


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def run(args, timeout=600):
    p = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout)
    try:
        j = json.loads(p.stdout.strip().splitlines()[-1]) if p.stdout.strip() else {}
    except Exception:
        j = {"raw": p.stdout[-400:] + p.stderr[-400:]}
    return p.returncode, j


def main():
    fvd, bins = sys.argv[1], sys.argv[2]
    st = Path(sys.argv[3] if len(sys.argv) > 3 else "/scratch/fastverify-next/selftest")
    hdr, items = load_export(st / "good.export")
    chal, cfg = st / "challenge.export", st / "comparator.json"
    td = Path(tempfile.mkdtemp(prefix="h01wj.", dir="/tmp"))
    try:
        def mk(fn, *steps, prefix=True):
            b = ExportBuilder(hdr, items if prefix else [])
            for s in steps:
                s(b)
            p = td / fn
            b.write(p)
            return p
        cases = [  # (id, base steps, delta steps, full-twin steps)
            ("W1a", [W.add_atkx, lambda b: W.add_prop_ind(b, "T")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_unsafe_axiom(b, "T.rec")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_prop_ind(b, "T"), lambda b: W.add_unsafe_axiom(b, "T.rec")]),
            ("W1b", [W.add_atkx, lambda b: W.add_prop_ind(b, "T")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_id_def(b, "T.rec")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_prop_ind(b, "T"), lambda b: W.add_id_def(b, "T.rec")]),
            ("W2", [W.add_atkx, lambda b: W.add_id_def(b, "Foo.rec")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_prop_ind(b, "Foo")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_id_def(b, "Foo.rec"), lambda b: W.add_prop_ind(b, "Foo")]),
            ("W3", [W.add_atkx, lambda b: W.add_unsafe_axiom(b, "Foo.rec")],
             [lambda b: W.add_prop_ind(b, "Foo")],
             [W.add_atkx, lambda b: W.add_unsafe_axiom(b, "Foo.rec"), lambda b: W.add_prop_ind(b, "Foo")]),
            ("W6", [W.add_atkx], [lambda b: W.add_prop_ind_axiom_ctor(b, "Ax6")],
             [W.add_atkx, lambda b: W.add_prop_ind_axiom_ctor(b, "Ax6")]),
            ("C2", [W.add_atkx, lambda b: W.add_prop_ind(b, "T")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_prop_ind(b, "Good2")],
             [lambda b: W.add_atkx(b, True), lambda b: W.add_prop_ind(b, "T"), lambda b: W.add_prop_ind(b, "Good2")]),
        ]
        print("case\twarm_verdict\twarm_legs\tcold_verdict(full twin, check-sound.sh)\tclass")
        for cid, bsteps, dsteps, fsteps in cases:
            base = mk(f"{cid}-base.export", *bsteps)
            delta = mk(f"{cid}-delta.export", *dsteps, prefix=False)
            full = mk(f"{cid}-full.export", *fsteps)
            sd = str(td / f"s{cid}")
            lf = open(sd + ".log", "w")
            proc = subprocess.Popen(["/usr/bin/python3", "-I", fvd, "serve", "--state", sd, "--challenge", str(chal),
                                     "--challenge-sha256", sha(chal), "--config", str(cfg), "--base", str(base),
                                     "--threads", "4", "--bins-dir", bins, "--pkgroot", PKG],
                                    stdout=lf, stderr=subprocess.STDOUT)
            ok = False
            for _ in range(1200):
                if os.path.exists(os.path.join(sd, "sock")):
                    ok = True
                    break
                if proc.poll() is not None:
                    break
                time.sleep(0.1)
            if not ok:
                print(f"{cid}\tSERVER-NOT-READY\t-\t-\t{open(sd + '.log').read()[-300:]!r}")
                proc.kill()
                continue
            rc, j = run(["/usr/bin/python3", "-I", fvd, "check-delta", "--state", sd, "--delta", str(delta),
                         "--config", str(cfg)])
            legs = {k: (v.get("status") if isinstance(v, dict) else v) for k, v in (j.get("legs") or {}).items()}
            run(["/usr/bin/python3", "-I", fvd, "stop", "--state", sd])
            try:
                proc.wait(10)
            except Exception:
                proc.kill()
            lf.close()
            crc, cj = run([f"{PKG}/check/sound/check-sound.sh", str(full), str(chal), str(cfg), "--threads", "4",
                           "--json", str(td / f"{cid}-cold.json")])
            try:
                cv = json.load(open(td / f"{cid}-cold.json")).get("verdict")
            except Exception:
                cv = f"rc={crc}"
            wv = j.get("verdict")
            cls = "MISMATCH" if (wv == "ACCEPTED" and cv != "ACCEPTED") else "same-or-stricter"
            print(f"{cid}\t{wv} (rc {rc})\t{json.dumps(legs)}\t{cv}\t{cls}\t{str(j.get('reason', ''))[:160]}")
    finally:
        shutil.rmtree(td, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
