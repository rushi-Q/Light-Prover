#!/usr/bin/python3 -I
"""G1 crafted exports: a theorem whose NAME equals a kernel-generated constant of an earlier inductive block
(recursor QI.rec / constructor). ExportBuilder copied from fastverify/tests/kernel-cves/craft_cves.py."""
import sys, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from exportbuilder_src import ExportBuilder, load_export

def base(st):
    hdr, items = load_export(Path(st) / "good.export")
    return ExportBuilder(hdr, items)

def add_qi(b, with_rec_record):
    n_I, n_mk, n_rec = b.name("QI"), b.name("QI.mk"), b.name("QI.rec")
    e_prop = b.sort(b.lvl_zero())
    e_I, e_mk = b.const(n_I, []), b.const(n_mk, [])
    recs = []
    if with_rec_record:
        n_motive, n_t, n_mkb, n_u = b.name("motive"), b.name("t"), b.name("mk"), b.name("u")
        e_sortu = b.sort(b.lvl_param(n_u))
        motive_ty = b.forallE(n_t, e_I, e_sortu)
        minor_ty = b.app(b.bvar(0), e_mk)
        major_ty = b.forallE(n_t, e_I, b.app(b.bvar(2), b.bvar(0)))
        rec_type = b.forallE(n_motive, motive_ty, b.forallE(n_mkb, minor_ty, major_ty), "implicit")
        rhs = b.lam(n_motive, motive_ty, b.lam(n_mkb, minor_ty, b.bvar(0)), "implicit")
        recs = [{"name": n_rec, "levelParams": [n_u], "type": rec_type, "all": [n_I], "numParams": 0, "numIndices": 0,
                 "numMotives": 1, "numMinors": 1, "k": True, "isUnsafe": False,
                 "rules": [{"ctor": n_mk, "nfields": 0, "rhs": rhs}]}]
    b.items.append({"inductive": {
        "types": [{"name": n_I, "levelParams": [], "type": e_prop, "numParams": 0, "numIndices": 0, "all": [n_I],
                   "ctors": [n_mk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
        "ctors": [{"name": n_mk, "levelParams": [], "type": e_I, "induct": n_I, "cidx": 0, "numParams": 0,
                   "numFields": 0, "isUnsafe": False}],
        "recs": recs}})
    return n_I, n_mk, n_rec, e_I, e_mk

def main():
    st, out = sys.argv[1], Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
    # G1a: theorem QI.rec : QI := QI.mk (name of the kernel-generated recursor), no recursor record exported
    b = base(st); n_I, n_mk, n_rec, e_I, e_mk = add_qi(b, False)
    b.items.append({"thm": {"name": n_rec, "levelParams": [], "type": e_I, "value": e_mk, "all": [n_rec]}})
    b.write(out / "g1a_thm_named_rec.export")
    # control: theorem QI.thm : QI := QI.mk + recursor record exported (genuine shape)
    b = base(st); n_I, n_mk, n_rec, e_I, e_mk = add_qi(b, True)
    n_t = b.name("QI.thm")
    b.items.append({"thm": {"name": n_t, "levelParams": [], "type": e_I, "value": e_mk, "all": [n_t]}})
    b.write(out / "g1c_control.export")
    print("ok")

main()
