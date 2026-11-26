#!/usr/bin/python3 -I
"""mk_c1only.py SELFTEST_DIR OUT : exports that ONLY C1 rejects (C2 and the kernel pass).
An UNSAFE inductive block is never handed to the kernel by Lean.Replay / the walk (its records are not in `remaining`) and its
names are not in the final environment (so the veto-only record check compares nothing), but C1 checks every inductInfo record whatever its flags:
  c1only_unsafe_type_loose : unsafe inductive U1 : (a : Type) -> #1  (loose bound variable in the inductive TYPE)
  c1only_unsafe_ctor_loose : unsafe inductive U2 : Type, ctor U2.mk : (a : Type) -> #1 -> U2  (loose in the CONSTRUCTOR type)
  c1only_control_unsafe    : unsafe inductive U3 : Type, ctor U3.mk : U3 (closed; must be ACCEPTED, like the plain replay)
A genuine export never contains such a block; the official replay accepts these files."""
import sys
from pathlib import Path
import os  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "kernel-cves"))
from craft_cves import ExportBuilder, load_export  # noqa: E402


def block(b, name, ty, ctor_ty_fn):
    nT, nmk = b.name(name), b.name(name + ".mk")
    eT = b.const(nT, [])
    return {"inductive": {
        "types": [{"name": nT, "levelParams": [], "type": ty, "numParams": 0, "numIndices": 0, "all": [nT],
                   "ctors": [nmk], "numNested": 0, "isRec": False, "isUnsafe": True, "isReflexive": False}],
        "ctors": [{"name": nmk, "levelParams": [], "type": ctor_ty_fn(eT), "induct": nT, "cidx": 0, "numParams": 0,
                   "numFields": 1, "isUnsafe": True}],
        "recs": []}}


def main():
    st, out = Path(sys.argv[1]), Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    hdr, items = load_export(st / "good.export")
    # U1: loose bvar in the inductive TYPE
    b = ExportBuilder(hdr, items)
    s1 = b.sort(b.lvl_succ(b.lvl_zero()))
    b.items.append(block(b, "U1", b.forallE(b.name("a"), s1, b.bvar(1)), lambda eT: eT))
    b.write(out / "c1only_unsafe_type_loose.export")
    # U2: loose bvar in the CONSTRUCTOR type
    b = ExportBuilder(hdr, items)
    s1 = b.sort(b.lvl_succ(b.lvl_zero()))
    b.items.append(block(b, "U2", s1, lambda eT: b.forallE(b.name("a"), s1, b.forallE(b.name("y"), b.bvar(1), eT))))
    b.write(out / "c1only_unsafe_ctor_loose.export")
    # control
    b = ExportBuilder(hdr, items)
    s1 = b.sort(b.lvl_succ(b.lvl_zero()))
    b.items.append(block(b, "U3", s1, lambda eT: eT))
    b.write(out / "c1only_control_unsafe.export")
    print("ok")


if __name__ == "__main__":
    main()
