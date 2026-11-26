#!/usr/bin/python3 -I
"""test_incr_attacks.py — adversarial repro for PChk/Incr.lean finalCheck.

Tests 3 full-incremental-mode (--incremental) bypasses where a forged constant collides with a kernel-generated
recursor whose inductive block was NOT pulled into `dirty`:
  ATK3: snap S has valid safe inductive T; final B adds unsafe axiom T.rec (does not ref T -> dirty={T.rec}, envD empty)
  ATK4: snap S has valid safe inductive T; final B adds SAFE def T.rec (does not ref T -> dirty={T.rec}, envD empty)
  ATK5: snap S has def X : Prop := True; final B modifies X, adds fresh inductive I (h : X) | mk (dirty via X),
        and adds fresh unsafe axiom I.rec : Prop (does not ref X/I -> freshClean, env1 has no I.rec, dmap has no I.rec!)
Later additions (the kernel-implicit names' CLOSURE), inputs from
mk_implicit_closure.py (same directory):
  ATK6: snap's Char.ofNatAux returns '\0'; r9_d : "a".bytes = "b".bytes (no syntactic path to Char.ofNat) is checked in
        the snapshot environment through the string literal's Char.ofNat; final = honest prelude + r9_d + r9_boom : False
  ATK7: the same through String's closure (snap's String.utf8EncodeChar := fun _ => [])
"""
import subprocess
import sys
import tempfile
from pathlib import Path

import os  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "kernel-cves"))
from craft_cves import ExportBuilder, load_export  # noqa: E402
sys.path.insert(0, str(Path(__file__).resolve().parent))   # mk_implicit_closure.py
import mk_implicit_closure  # noqa: E402


def main():
    if len(sys.argv) < 2:
        print("usage: test_incr_attacks.py PLEANCHECKER_INCR [SELFTEST_DIR]")
        return 2
    plc = sys.argv[1]
    st = Path(sys.argv[2] if len(sys.argv) > 2 else "/scratch/fastverify-next/selftest")
    hdr, items = load_export(st / "good.export")
    env = {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1", "LEAN_STACK_SIZE_KB": "917376"}

    npass = nfail = 0
    with tempfile.TemporaryDirectory(prefix="h03-incr-atk.") as td:
        td = Path(td)

        # Base snap S1: valid safe inductive AtkInd (without exporting AtkInd.rec)
        bS1 = ExportBuilder(hdr, items)
        nT, nmk = bS1.name("AtkInd"), bS1.name("AtkInd.mk")
        e_prop = bS1.sort(bS1.lvl_zero())
        eT = bS1.const(nT, [])
        bS1.items.append({"inductive": {
            "types": [{"name": nT, "levelParams": [], "type": e_prop, "numParams": 0, "numIndices": 0,
                       "all": [nT], "ctors": [nmk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": nmk, "levelParams": [], "type": eT, "induct": nT, "cidx": 0,
                       "numParams": 0, "numFields": 0, "isUnsafe": False}],
            "recs": [],
        }})
        pS1 = td / "snap1.export"
        bS1.write(pS1)

        # ATK3: unsafe axiom AtkInd.rec
        b3 = ExportBuilder(hdr, list(bS1.items))
        b3.items.append({"axiom": {"name": b3.name("AtkInd.rec"), "levelParams": [], "type": b3.sort(b3.lvl_zero()), "isUnsafe": True}})
        pB3 = td / "atk3.export"
        b3.write(pB3)

        # ATK4: safe def AtkInd.rec
        b4 = ExportBuilder(hdr, list(bS1.items))
        np, nh = b4.name("p"), b4.name("h")
        e_ty = b4.forallE(np, b4.sort(b4.lvl_zero()), b4.forallE(nh, b4.bvar(0), b4.bvar(1)))
        e_val = b4.lam(np, b4.sort(b4.lvl_zero()), b4.lam(nh, b4.bvar(0), b4.bvar(0)))
        nrec = b4.name("AtkInd.rec")
        b4.items.append({"def": {"name": nrec, "levelParams": [], "type": e_ty, "value": e_val,
                                 "hints": "opaque", "safety": "safe", "all": [nrec]}})
        pB4 = td / "atk4.export"
        b4.write(pB4)

        # ATK5: snap S2 has def X : Prop := Prop->Prop (Wait: def X : Type := Prop); final B5 changes X, adds fresh ind I depending on X, and fresh unsafe axiom I.rec
        bS2 = ExportBuilder(hdr, items)
        nX = bS2.name("Atk5X")
        e_s0 = bS2.sort(bS2.lvl_zero())
        e_s1 = bS2.sort(bS2.lvl_succ(bS2.lvl_zero()))
        bS2.items.append({"def": {"name": nX, "levelParams": [], "type": e_s1, "value": e_s0,
                                  "hints": "abbrev", "safety": "safe", "all": [nX]}})
        pS2 = td / "snap2.export"
        bS2.write(pS2)

        b5 = ExportBuilder(hdr, items)
        nX5 = b5.name("Atk5X")
        e_s0 = b5.sort(b5.lvl_zero())
        e_s1 = b5.sort(b5.lvl_succ(b5.lvl_zero()))
        # Different safe value for Atk5X (still Type 0 = Sort 1 -> value = Prop -> Prop)
        e_p2p = b5.forallE(b5.name("_"), e_s0, e_s0)
        b5.items.append({"def": {"name": nX5, "levelParams": [], "type": e_s1, "value": e_p2p,
                                 "hints": "abbrev", "safety": "safe", "all": [nX5]}})
        nI, nImk, nIrec = b5.name("Atk5Ind"), b5.name("Atk5Ind.mk"), b5.name("Atk5Ind.rec")
        eX5 = b5.const(nX5, [])
        eI = b5.const(nI, [])
        i_ty = b5.forallE(b5.name("h"), eX5, e_s0)
        imk_ty = b5.forallE(b5.name("h"), eX5, b5.app(eI, b5.bvar(0)))
        b5.items.append({"inductive": {
            "types": [{"name": nI, "levelParams": [], "type": i_ty, "numParams": 1, "numIndices": 0,
                       "all": [nI], "ctors": [nImk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": nImk, "levelParams": [], "type": imk_ty, "induct": nI, "cidx": 0,
                       "numParams": 1, "numFields": 0, "isUnsafe": False}],
            "recs": [],
        }})
        b5.items.append({"axiom": {"name": nIrec, "levelParams": [], "type": e_s0, "isUnsafe": True}})
        pB5 = td / "atk5.export"
        b5.write(pB5)

        # ATK6 / ATK7: kernel-implicit closure
        ic = {}
        for v in ("charaux", "utf8"):
            for fin in (False, True):
                p = td / f"ic-{v}-{'final' if fin else 'snap'}.export"
                mk_implicit_closure.build(hdr, items, v, fin).write(p)
                ic[(v, fin)] = p

        # Control: snap S1 -> final S1 (must ACCEPT)
        cases = [
            ("ATK3_unsafe_axiom_as_rec", pS1, pB3, "attack"),
            ("ATK4_safe_def_as_rec", pS1, pB4, "attack"),
            ("ATK5_dirty_fresh_ind_vs_clean_unsafe_rec", pS2, pB5, "attack"),
            ("ATK6_implicit_closure_Char.ofNatAux", ic[("charaux", False)], ic[("charaux", True)], "attack"),
            ("ATK7_implicit_closure_String.utf8EncodeChar", ic[("utf8", False)], ic[("utf8", True)], "attack"),
            ("CTRL_snap1_final1", pS1, pS1, "control"),
        ]

        for cid, pS, pB, expect in cases:
            for mode in ("plain", "incr"):
                if mode == "plain":
                    r = subprocess.run([plc, "-j2", "--from-export", str(pB)], capture_output=True, text=True, env=env, timeout=60)
                else:
                    r = subprocess.run([plc, "--incremental", "-j2"], input=f"snap {pS}\nfinal {pB}\n",
                                       capture_output=True, text=True, env=env, timeout=60)
                ok = (r.returncode == 0) if expect == "control" else (r.returncode != 0)
                st_str = "PASS" if ok else "FAIL"
                npass += int(ok)
                nfail += int(not ok)
                msg = ((r.stdout.strip().splitlines() or [""])[-1] or (r.stderr.strip().splitlines() or [""])[-1])[:150]
                print(f"{st_str}\t{cid}\t{mode}\t{expect}\trc={r.returncode}\t{msg}")

    print(f"RESULT pass={npass} fail={nfail}")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
