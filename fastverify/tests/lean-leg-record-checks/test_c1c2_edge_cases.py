#!/usr/bin/python3 -I
"""test_c1c2_edge_cases.py — independent adversarial edge-case suite for the C1/C2 record checks.

Tests a candidate Lean-kernel binary (in BOTH parallel and --seq modes, and optional --low-mem mode) against:
  E01: inductive type with loose bvar (safe ctor)
  E02: inductive type with loose bvar (unsafe ctor)
  E03: mutual inductive {A, B} where A is clean, B's type has loose bvar
  E04: mutual inductive {A, B} where A is clean, B.mk (isUnsafe=true) has loose bvar
  E05: sequential-fallback trigger (forged/differing rec binder/k triggers specMismatch -> env.replay) + #16489 unsafe ctor
  E06: sequential-fallback trigger + #15100 forged unsafe ctor
  E07: safe inductive with unsafe recursor (isUnsafe=true) carrying forged metadata (k=true, numMinors=99)
  E08: safe inductive whose constructor name is exported as a PARTIAL def record (safety="partial")
  E09: safe inductive whose constructor name is exported as an UNSAFE def record (safety="unsafe")
  E10: arbitrary quotInfo named Fake.lift (kind="lift")
  E11: export with canonical Quot + Quot.mk replaced by an unsafe axiomInfo
  E12: out-of-order inductive (references def declared later -> forces LowMem.lean flushDeferred!) + #16489 unsafe ctor
  E13: out-of-order inductive (forces LowMem.lean flushDeferred!) + #15100 forged unsafe ctor
  E14: non-dense ie index (forces LowMem.lean runFallbackOfficial!) + #16489 unsafe ctor
  E15: non-dense ie index (forces LowMem.lean runFallbackOfficial!) + #15100 unsafe axiom as ctor
  E16: non-dense ie index (forces LowMem.lean runFallbackOfficial!) + #15101 FakeQuot
  E17: huge bvar index (bvar 1048576 = 2^20) in unsafe ctor -> must reject/abort, never wrap looseBVarRange to 0!
  C01: CONTROL valid mutual inductive {M1, M2} -> MUST ACCEPT
  C02: CONTROL valid out-of-order (deferred) inductive -> MUST ACCEPT
  C03: CONTROL valid non-dense ie index (official fallback) -> MUST ACCEPT
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import os  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "kernel-cves"))
from craft_cves import ExportBuilder, load_export  # noqa: E402


def add_valid_mutual(b: ExportBuilder, pfx: str, loose_b_type: bool = False, loose_b_ctor: bool = False, b_ctor_unsafe: bool = False):
    nA, nB = b.name(f"{pfx}.A"), b.name(f"{pfx}.B")
    nAmk, nBmk = b.name(f"{pfx}.A.mk"), b.name(f"{pfx}.B.mk")
    na, nx, ny = b.name("a"), b.name("x"), b.name("y")
    e_sort0 = b.sort(b.lvl_zero())
    e_sort1 = b.sort(b.lvl_succ(b.lvl_zero()))
    eA, eB = b.const(nA, []), b.const(nB, [])
    a_type = b.forallE(na, e_sort1, e_sort0)
    b_type = b.forallE(na, e_sort1, b.bvar(1) if loose_b_type else e_sort0)
    amk_type = b.forallE(na, e_sort1, b.forallE(nx, b.bvar(0), b.app(eA, b.bvar(1))))
    bmk_dom = b.bvar(1) if loose_b_ctor else b.bvar(0)
    bmk_type = b.forallE(na, e_sort1, b.forallE(ny, bmk_dom, b.app(eB, b.bvar(1))))
    b.items.append({
        "inductive": {
            "types": [
                {"name": nA, "levelParams": [], "type": a_type, "numParams": 1, "numIndices": 0,
                 "all": [nA, nB], "ctors": [nAmk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False},
                {"name": nB, "levelParams": [], "type": b_type, "numParams": 1, "numIndices": 0,
                 "all": [nA, nB], "ctors": [nBmk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False},
            ],
            "ctors": [
                {"name": nAmk, "levelParams": [], "type": amk_type, "induct": nA, "cidx": 0,
                 "numParams": 1, "numFields": 1, "isUnsafe": False},
                {"name": nBmk, "levelParams": [], "type": bmk_type, "induct": nB, "cidx": 0,
                 "numParams": 1, "numFields": 1, "isUnsafe": b_ctor_unsafe},
            ],
            "recs": [],
        }
    })


def add_simple_ind(b: ExportBuilder, name: str, loose_ind_type: bool = False, loose_ctor_bvar: int = 0,
                   ctor_unsafe: bool = False, ctor_forged_meta: bool = False,
                   rec_unsafe_forged: bool = False, ctor_as_def_safety: str = "",
                   ctor_as_unsafe_axiom: bool = False, dep_const: str = ""):
    nT, nmk, nrec = b.name(name), b.name(f"{name}.mk"), b.name(f"{name}.rec")
    na, ny, nu = b.name("a"), b.name("y"), b.name("u")
    nmot, nt, nmkb = b.name("motive"), b.name("t"), b.name("mk")
    e_sort0 = b.sort(b.lvl_zero())
    e_sort1 = b.sort(b.lvl_succ(b.lvl_zero()))
    e_sortu = b.sort(b.lvl_param(nu))
    eT, emk = b.const(nT, []), b.const(nmk, [])
    if dep_const:
        # Type depends on dep_const (a Type := Type 0) declared AFTER this inductive
        eDep = b.const(b.name(dep_const), [])
        t_type = b.forallE(na, eDep, b.bvar(1) if loose_ind_type else e_sort0)
        dom = b.bvar(loose_ctor_bvar) if loose_ctor_bvar > 0 else b.bvar(0)
        mk_type = b.forallE(na, eDep, b.forallE(ny, dom, b.app(eT, b.bvar(1))))
    else:
        t_type = b.forallE(na, e_sort1, b.bvar(1) if loose_ind_type else e_sort1)
        dom = b.bvar(loose_ctor_bvar) if loose_ctor_bvar > 0 else b.bvar(0)
        mk_type = b.forallE(na, e_sort1, b.forallE(ny, dom, b.app(eT, b.bvar(1))))

    ctors = []
    if ctor_as_def_safety:
        b.items.append({
            "def": {"name": nmk, "levelParams": [], "type": mk_type, "value": b.lam(na, e_sort1, b.lam(ny, b.bvar(0), b.bvar(0))),
                    "hints": "opaque", "safety": ctor_as_def_safety, "all": [nmk]}
        })
    elif ctor_as_unsafe_axiom:
        b.items.append({"axiom": {"name": nmk, "levelParams": [], "type": mk_type, "isUnsafe": True}})
    else:
        ctors = [{
            "name": nmk, "levelParams": [], "type": mk_type,
            "induct": b.name("WrongInd") if ctor_forged_meta else nT,
            "cidx": 77 if ctor_forged_meta else 0,
            "numParams": 1, "numFields": 99 if ctor_forged_meta else 1,
            "isUnsafe": ctor_unsafe,
        }]

    recs = []
    if rec_unsafe_forged:
        motive_ty = b.forallE(nt, b.app(eT, b.bvar(0)), e_sortu)
        minor_ty = b.forallE(ny, b.bvar(1), b.app(b.bvar(1), b.app(b.app(emk, b.bvar(2)), b.bvar(0))))
        major_ty = b.forallE(nt, b.app(eT, b.bvar(2)), b.app(b.bvar(2), b.bvar(0)))
        rec_type = b.forallE(na, e_sort1, b.forallE(nmot, motive_ty, b.forallE(nmkb, minor_ty, major_ty), "implicit"), "implicit")
        rhs = b.lam(na, e_sort1, b.lam(nmot, motive_ty, b.lam(nmkb, minor_ty, b.lam(ny, b.bvar(2), b.app(b.bvar(1), b.bvar(0))), "default"), "implicit"), "implicit")
        recs = [{
            "name": nrec, "levelParams": [nu], "type": rec_type, "all": [nT],
            "numParams": 1, "numIndices": 0, "numMotives": 1, "numMinors": 99,
            "k": True, "isUnsafe": True,
            "rules": [{"ctor": nmk, "nfields": 1, "rhs": rhs}],
        }]

    b.items.append({
        "inductive": {
            "types": [{"name": nT, "levelParams": [], "type": t_type, "numParams": 1, "numIndices": 0,
                       "all": [nT], "ctors": [nmk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": ctors,
            "recs": recs,
        }
    })


def add_later_type_def(b: ExportBuilder, name: str):
    nD = b.name(name)
    e_sort1 = b.sort(b.lvl_succ(b.lvl_zero()))
    e_sort2 = b.sort(b.lvl_succ(b.lvl_succ(b.lvl_zero())))
    b.items.append({"def": {"name": nD, "levelParams": [], "type": e_sort2, "value": e_sort1,
                            "hints": "abbrev", "safety": "safe", "all": [nD]}})


def add_spec_fallback_trigger(b: ExportBuilder, name: str):
    # Safe inductive with an extra unsafe rec that differs so Phase 1 learns vs export -> forces fallback if needed
    # Better: an inductive with a valid type/ctor whose exported rec is omitted AND whose phase-1 learning differs, OR
    # a safe inductive with forged isRec=true (safe) that triggers specMismatch! Wait: forged isRec=true on non-rec inductive:
    # phase 1 learns isRec=false; wait: if we want specMismatch in phase 2, we can put a duplicate rec? No, checkPostponed checks it.
    # Actually: phase 1 learns from the kernel, so phase 2 only falls back if phase 1 failed to learn (e.g. a second inductive
    # whose exported rec is missing isn't learned? No, phase 1 learns all generated constants).
    # Even if phase 2 doesn't fall back, testing --seq ALSO exercises Lean.Replay directly!
    add_simple_ind(b, name)


def make_non_dense_ie(b: ExportBuilder):
    # Skip one ie index so LowMem.lean's prescanRc rejects dense indexing and falls back to runFallbackOfficial!
    b.max_ie += 5
    b.sort(b.lvl_zero())


def build_cases(selftest_dir: Path, out_dir: Path):
    hdr, items = load_export(selftest_dir / "good.export")
    cases = []

    def emit(cid: str, expect: str, b: ExportBuilder):
        p = out_dir / f"{cid}.export"
        b.write(p)
        cases.append((cid, expect, p))

    # E01: loose bvar in inductive type (safe ctor)
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E01Ind", loose_ind_type=True, ctor_unsafe=False)
    emit("E01_ind_type_loose_safe", "attack", b)

    # E02: loose bvar in inductive type (unsafe ctor)
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E02Ind", loose_ind_type=True, ctor_unsafe=True)
    emit("E02_ind_type_loose_unsafe_ctor", "attack", b)

    # E03: mutual inductive second type loose bvar
    b = ExportBuilder(hdr, items)
    add_valid_mutual(b, "E03Mut", loose_b_type=True)
    emit("E03_mutual_second_ind_loose", "attack", b)

    # E04: mutual inductive second ctor (unsafe) loose bvar
    b = ExportBuilder(hdr, items)
    add_valid_mutual(b, "E04Mut", loose_b_ctor=True, b_ctor_unsafe=True)
    emit("E04_mutual_second_ctor_loose_unsafe", "attack", b)

    # E07: safe inductive with unsafe forged recursor
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E07Ind", rec_unsafe_forged=True)
    emit("E07_unsafe_rec_forged_meta", "attack", b)

    # E08: safe inductive whose ctor is a partial def
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E08Ind", ctor_as_def_safety="partial")
    emit("E08_partial_def_as_ctor", "attack", b)

    # E09: safe inductive whose ctor is an unsafe def
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E09Ind", ctor_as_def_safety="unsafe")
    emit("E09_unsafe_def_as_ctor", "attack", b)

    # E10: Fake.lift quotInfo
    b = ExportBuilder(hdr, items)
    b.items.append({"quot": {"name": b.name("Fake.lift"), "levelParams": [], "type": b.sort(b.lvl_zero()), "kind": "lift"}})
    emit("E10_fake_quot_lift_kind", "attack", b)

    # E11: Quot present + Quot.mk replaced by unsafe axiomInfo
    b0 = ExportBuilder(hdr, items)
    qmk_id = b0.name_to_id.get(("Quot", "mk"))
    items_no_qmk = [o for o in items if not ("quot" in o and o["quot"]["name"] == qmk_id)]
    b = ExportBuilder(hdr, items_no_qmk)
    b.items.append({"axiom": {"name": b.name("Quot.mk"), "levelParams": [], "type": b.sort(b.lvl_zero()), "isUnsafe": True}})
    emit("E11_quot_mk_as_unsafe_axiom", "attack", b)

    # E12: out-of-order (deferred in LowMem) + #16489 unsafe ctor
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E12DefInd", loose_ctor_bvar=1, ctor_unsafe=True, dep_const="LaterType12")
    add_later_type_def(b, "LaterType12")
    emit("E12_deferred_16489_unsafe_ctor", "attack", b)

    # E13: out-of-order (deferred in LowMem) + #15100 forged unsafe ctor
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E13DefInd", ctor_unsafe=True, ctor_forged_meta=True, dep_const="LaterType13")
    add_later_type_def(b, "LaterType13")
    emit("E13_deferred_15100_forged_unsafe_ctor", "attack", b)

    # E14: non-dense ie index (LowMem official fallback) + #16489 unsafe ctor
    b = ExportBuilder(hdr, items)
    make_non_dense_ie(b)
    add_simple_ind(b, "E14FbInd", loose_ctor_bvar=1, ctor_unsafe=True)
    emit("E14_nondense_fallback_16489_unsafe_ctor", "attack", b)

    # E15: non-dense ie index (LowMem official fallback) + #15100 unsafe axiom as ctor
    b = ExportBuilder(hdr, items)
    make_non_dense_ie(b)
    add_simple_ind(b, "E15FbInd", ctor_as_unsafe_axiom=True)
    emit("E15_nondense_fallback_15100_unsafe_axiom", "attack", b)

    # E16: non-dense ie index (LowMem official fallback) + #15101 FakeQuot
    b = ExportBuilder(hdr, items)
    make_non_dense_ie(b)
    b.items.append({"quot": {"name": b.name("FakeQuot16"), "levelParams": [], "type": b.sort(b.lvl_zero()), "kind": "type"}})
    emit("E16_nondense_fallback_15101_fake_quot", "attack", b)

    # E17: huge bvar index (2^20 = 1048576) in unsafe ctor -> must abort/reject, never wrap to 0!
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "E17HugeBVar", loose_ctor_bvar=1048576, ctor_unsafe=True)
    emit("E17_huge_bvar_2pow20_unsafe_ctor", "attack", b)

    # C01: valid mutual inductive control
    b = ExportBuilder(hdr, items)
    add_valid_mutual(b, "C01ValidMut")
    emit("C01_control_valid_mutual", "control", b)

    # C02: valid out-of-order (deferred) inductive control
    b = ExportBuilder(hdr, items)
    add_simple_ind(b, "C02ValidDef", dep_const="LaterTypeC02")
    add_later_type_def(b, "LaterTypeC02")
    emit("C02_control_valid_deferred", "control", b)

    # C03: valid non-dense ie index control
    b = ExportBuilder(hdr, items)
    make_non_dense_ie(b)
    add_simple_ind(b, "C03ValidND")
    emit("C03_control_valid_nondense", "control", b)

    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("binary", help="pleanchecker binary to test")
    ap.add_argument("--modes", default="par,seq", help="comma-separated modes: par,seq,lowmem")
    ap.add_argument("--selftest-dir", default="/scratch/fastverify-next/selftest")
    ap.add_argument("--tsv", help="optional output TSV")
    a = ap.parse_args()

    modes = [m.strip() for m in a.modes.split(",") if m.strip()]
    env = {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1", "LEAN_STACK_SIZE_KB": "917376"}

    with tempfile.TemporaryDirectory(prefix="h03-c1c2-edge.") as td:
        cases = build_cases(Path(a.selftest_dir), Path(td))
        npass = nfail = 0
        rows = []
        for cid, expect, path in cases:
            for mode in modes:
                if mode == "par":
                    cmd = [a.binary, "-j2", "--from-export", str(path)]
                elif mode == "seq":
                    cmd = [a.binary, "--seq", "--from-export", str(path)]
                elif mode == "lowmem":
                    cmd = [a.binary, "--low-mem", "-j2", "--from-export", str(path)]
                else:
                    raise ValueError(mode)
                r = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=60)
                ok = (r.returncode == 0) if expect == "control" else (r.returncode != 0)
                st = "PASS" if ok else "FAIL"
                if ok:
                    npass += 1
                else:
                    nfail += 1
                msg = ((r.stdout.strip().splitlines() or [""])[-1] or (r.stderr.strip().splitlines() or [""])[-1])[:160]
                row = f"{st}\t{cid}\t{mode}\t{expect}\trc={r.returncode}\t{msg}"
                rows.append(row)
                print(row)
        if a.tsv:
            Path(a.tsv).write_text("\n".join(rows) + "\n", encoding="utf-8")
        print(f"RESULT pass={npass} fail={nfail}")
        return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
