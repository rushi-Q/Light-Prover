#!/usr/bin/python3 -I
"""test_incr_avail.py PLEANCHECKER_INCR [SELFTEST_DIR] : AVAILABILITY of the full incremental path
(`--incremental`, `finalCheck`) after the finalCheck completion: legitimate edits must still be decided by the incremental
path (stderr '[incr] final: ... dirty re-checked', no 'incremental path not usable') and ACCEPTED.
  V1  snap S (inductive AtkInd : Prop | mk) -> final B = S with AtkInd edited (a second constructor mk2)   [inductive edit]
  V2  snap S (def AtkX : Type := Prop)      -> final B = S with AtkX := Prop -> Prop                      [definition edit]
  V3  snap S                                 -> final B = S + a fresh inductive Fresh : Prop | mk          [pure extension]
  V4  snap S (AtkInd)                        -> final B = S + a theorem using AtkInd.mk                    [extension using it]
Prints TSV rows and 'RESULT pass=N fail=M'."""
import subprocess
import sys
import tempfile
from pathlib import Path

import os  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "kernel-cves"))
from craft_cves import ExportBuilder, load_export  # noqa: E402

ENV = {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1", "LEAN_STACK_SIZE_KB": "917376"}


def ind(b, name, nctors=1):
    nT = b.name(name)
    s0 = b.sort(b.lvl_zero())
    eT = b.const(nT, [])
    ctors = [b.name(f"{name}.mk" if i == 0 else f"{name}.mk{i + 1}") for i in range(nctors)]
    b.items.append({"inductive": {
        "types": [{"name": nT, "levelParams": [], "type": s0, "numParams": 0, "numIndices": 0, "all": [nT],
                   "ctors": ctors, "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
        "ctors": [{"name": c, "levelParams": [], "type": eT, "induct": nT, "cidx": i, "numParams": 0, "numFields": 0,
                   "isUnsafe": False} for i, c in enumerate(ctors)],
        "recs": []}})


def atkx(b, p2p=False):
    s0 = b.sort(b.lvl_zero())
    s1 = b.sort(b.lvl_succ(b.lvl_zero()))
    n = b.name("AtkX")
    b.items.append({"def": {"name": n, "levelParams": [], "type": s1, "value": b.forallE(b.name("_"), s0, s0) if p2p else s0,
                            "hints": "abbrev", "safety": "safe", "all": [n]}})


def thm_uses(b):
    n = b.name("UsesMk")
    b.items.append({"thm": {"name": n, "levelParams": [], "type": b.const(b.name("AtkInd"), []),
                            "value": b.const(b.name("AtkInd.mk"), []), "all": [n]}})


def main():
    plc = sys.argv[1]
    st = Path(sys.argv[2] if len(sys.argv) > 2 else "/scratch/fastverify-next/selftest")
    hdr, items = load_export(st / "good.export")
    npass = nfail = 0
    with tempfile.TemporaryDirectory(prefix="leanleg-incr-avail.") as td:
        td = Path(td)

        def mk(fn, *steps):
            b = ExportBuilder(hdr, items)
            for s in steps:
                s(b)
            p = td / fn
            b.write(p)
            return p
        S = mk("S.export", lambda b: ind(b, "AtkInd"), atkx)
        cases = [("V1-inductive-edit", S, mk("V1.export", lambda b: ind(b, "AtkInd", 2), atkx)),
                 ("V2-definition-edit", S, mk("V2.export", lambda b: ind(b, "AtkInd"), lambda b: atkx(b, True))),
                 ("V3-fresh-inductive", S, mk("V3.export", lambda b: ind(b, "AtkInd"), atkx, lambda b: ind(b, "Fresh"))),
                 ("V4-theorem-using-ctor", S, mk("V4.export", lambda b: ind(b, "AtkInd"), atkx, thm_uses))]
        for cid, snap, final in cases:
            r = subprocess.run([plc, "--incremental", "-j2", "-v"], input=f"snap {snap}\nfinal {final}\n",
                               capture_output=True, text=True, env=ENV, timeout=120)
            incr_path = "[incr] final:" in r.stderr and "incremental path not usable" not in r.stderr
            ok = r.returncode == 0 and incr_path
            npass += int(ok)
            nfail += int(not ok)
            why = [ln for ln in r.stderr.splitlines() if ln.startswith("[incr] final") or "not usable" in ln][-1:]
            print(f"{'PASS' if ok else 'FAIL'}\t{cid}\trc={r.returncode}\tincremental_path={incr_path}\t{(why or [''])[0][:170]}")
    print(f"binary {plc}")
    print(f"RESULT pass={npass} fail={nfail}")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
