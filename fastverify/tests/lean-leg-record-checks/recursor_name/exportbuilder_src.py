#!/usr/bin/python3 -I
"""craft_cves.py — Deterministic NDJSON generator for Lean 4.36 kernel/replay CVE regressions.

Generates crafted NDJSON exports derived from the pinned selftest export:
  1. 00_honest_baseline            : unmodified selftest/good.export (control -> ACCEPTED)
  2. 16489_control_valid           : inductive Control16489Valid : Type -> Type | mk : (a : Type) -> (y : a) -> Control16489Valid a (control -> ACCEPTED)
  3. 16489_safe_ctor               : Lean #16489 (loose bvar #1 in ctor type, isUnsafe=false; v4.36 add_inductive accepts & rewrites -> caught by Replay postponed check + gruszka)
  4. 16489_unsafe_ctor             : Lean #16489 + Replay isUnsafe bypass (loose bvar #1 in ctor type, isUnsafe=true -> BYPASSES leanchecker/leanchecker-paranoid/pleanchecker/official-comparator! Vetoed by gruszka!)
  5. 16489_2param_unsafe           : Lean #16489 2-param variant (loose bvar #2 in ctor type, isUnsafe=true -> BYPASSES Lean legs! Vetoed by gruszka!)
  6. 15100_unsafe_axiom_as_ctor    : Lean #15100-class Replay bypass (safe inductive referencing an unsafe axiom in ctors -> BYPASSES Lean legs! Vetoed by gruszka!)
  7. 15100_unsafe_ctor_forged_meta : Lean #15100-class Replay bypass (safe inductive referencing an unsafe ctor with forged induct/cidx/numParams/numFields -> BYPASSES Lean legs! Vetoed by gruszka!)
  8. 15101_baseline_noquot         : selftest without Quot/Quot.sound (control for #15101 -> ACCEPTED)
  9. 15101_fake_quot_clean         : Lean #15101 (arbitrary quotInfo FakeQuot : ∀ p : Prop, p, kind=type -> BYPASSES Lean legs! Vetoed by gruszka!)
 10. 15101_fake_quot_plus_mk       : Lean #15101 (arbitrary FakeQuot replacing Quot while keeping Quot.{mk,lift,ind} -> BYPASSES Lean legs! Vetoed by gruszka!)
"""
import argparse, json, os, sys
from pathlib import Path

def load_export(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    return lines[0], [json.loads(l) for l in lines[1:] if l.strip()]

class ExportBuilder:
    def __init__(self, header, items):
        self.header = header
        self.items = list(items)
        self.names = {0: ()}
        self.name_to_id = {(): 0}
        self.levels = {0: ("zero",)}
        self.level_to_id = {("zero",): 0}
        self.max_in = 0
        self.max_il = 0
        self.max_ie = -1
        for obj in self.items:
            if "in" in obj:
                idx = obj["in"]
                self.max_in = max(self.max_in, idx)
                if "str" in obj:
                    tup = self.names[obj["str"]["pre"]] + (obj["str"]["str"],)
                else:
                    tup = self.names[obj["num"]["pre"]] + (obj["num"]["i"],)
                self.names[idx] = tup
                self.name_to_id[tup] = idx
            elif "il" in obj:
                idx = obj["il"]
                self.max_il = max(self.max_il, idx)
                if "succ" in obj: k = ("succ", obj["succ"])
                elif "param" in obj: k = ("param", obj["param"])
                elif "max" in obj: k = ("max", tuple(obj["max"]))
                elif "imax" in obj: k = ("imax", tuple(obj["imax"]))
                else: k = ("other", idx)
                self.levels[idx] = k
                self.level_to_id[k] = idx
            elif "ie" in obj:
                self.max_ie = max(self.max_ie, obj["ie"])

    def name(self, dotted: str) -> int:
        parts = tuple(dotted.split(".")) if dotted else ()
        if parts in self.name_to_id:
            return self.name_to_id[parts]
        cur, cur_id = (), 0
        for part in parts:
            nxt = cur + (part,)
            if nxt in self.name_to_id:
                cur_id = self.name_to_id[nxt]
            else:
                self.max_in += 1
                self.items.append({"in": self.max_in, "str": {"pre": cur_id, "str": part}})
                self.names[self.max_in] = nxt
                self.name_to_id[nxt] = self.max_in
                cur_id = self.max_in
            cur = nxt
        return cur_id

    def lvl_zero(self) -> int: return 0
    def lvl_succ(self, l: int) -> int:
        k = ("succ", l)
        if k in self.level_to_id: return self.level_to_id[k]
        self.max_il += 1
        self.items.append({"il": self.max_il, "succ": l})
        self.levels[self.max_il] = k; self.level_to_id[k] = self.max_il
        return self.max_il

    def lvl_param(self, n_id: int) -> int:
        k = ("param", n_id)
        if k in self.level_to_id: return self.level_to_id[k]
        self.max_il += 1
        self.items.append({"il": self.max_il, "param": n_id})
        self.levels[self.max_il] = k; self.level_to_id[k] = self.max_il
        return self.max_il

    def add_expr(self, body: dict) -> int:
        self.max_ie += 1
        d = {"ie": self.max_ie}; d.update(body)
        self.items.append(d)
        return self.max_ie

    def bvar(self, i: int) -> int: return self.add_expr({"bvar": i})
    def sort(self, l: int) -> int: return self.add_expr({"sort": l})
    def const(self, n: int, us=None) -> int: return self.add_expr({"const": {"name": n, "us": us or []}})
    def app(self, fn: int, arg: int) -> int: return self.add_expr({"app": {"fn": fn, "arg": arg}})
    def forallE(self, n: int, ty: int, body: int, bi="default") -> int:
        return self.add_expr({"forallE": {"name": n, "type": ty, "body": body, "binderInfo": bi}})
    def lam(self, n: int, ty: int, body: int, bi="default") -> int:
        return self.add_expr({"lam": {"name": n, "type": ty, "body": body, "binderInfo": bi}})

    def write(self, path: Path):
        with path.open("w", encoding="utf-8") as f:
            f.write(self.header + "\n")
            for obj in self.items:
                f.write(json.dumps(obj, separators=(",", ":"), sort_keys=True) + "\n")

def add_16489_ind(b: ExportBuilder, ctor_is_unsafe: bool, loose_bvar_idx: int, ind_name: str):
    n_T, n_mk, n_rec = b.name(ind_name), b.name(f"{ind_name}.mk"), b.name(f"{ind_name}.rec")
    n_a, n_y, n_u = b.name("a"), b.name("y"), b.name("u")
    n_motive, n_t, n_mk_b = b.name("motive"), b.name("t"), b.name("mk")
    e_sort1, e_sortu = b.sort(b.lvl_succ(b.lvl_zero())), b.sort(b.lvl_param(n_u))
    e_T, e_mk = b.const(n_T, []), b.const(n_mk, [])
    e_b0, e_b1, e_b2, e_bl = b.bvar(0), b.bvar(1), b.bvar(2), b.bvar(loose_bvar_idx)
    t_type = b.forallE(n_a, e_sort1, e_sort1)
    mk_type = b.forallE(n_a, e_sort1, b.forallE(n_y, e_bl, b.app(e_T, e_b1)))
    motive_ty = b.forallE(n_t, b.app(e_T, e_b0), e_sortu)
    minor_ty = b.forallE(n_y, e_b1, b.app(e_b1, b.app(b.app(e_mk, e_b2), e_b0)))
    major_ty = b.forallE(n_t, b.app(e_T, e_b2), b.app(e_b2, e_b0))
    rec_type = b.forallE(n_a, e_sort1, b.forallE(n_motive, motive_ty, b.forallE(n_mk_b, minor_ty, major_ty), "implicit"), "implicit")
    rhs = b.lam(n_a, e_sort1, b.lam(n_motive, motive_ty, b.lam(n_mk_b, minor_ty, b.lam(n_y, e_b2, b.app(e_b1, e_b0)), "default"), "implicit"), "implicit")
    b.items.append({
        "inductive": {
            "types": [{"name": n_T, "levelParams": [], "type": t_type, "numParams": 1, "numIndices": 0,
                       "all": [n_T], "ctors": [n_mk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": n_mk, "levelParams": [], "type": mk_type, "induct": n_T, "cidx": 0,
                       "numParams": 1, "numFields": 1, "isUnsafe": ctor_is_unsafe}],
            "recs": [{"name": n_rec, "levelParams": [n_u], "type": rec_type, "all": [n_T], "numParams": 1,
                      "numIndices": 0, "numMotives": 1, "numMinors": 1, "k": False, "isUnsafe": False,
                      "rules": [{"ctor": n_mk, "nfields": 1, "rhs": rhs}]}],
        }
    })

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest-dir", default="/scratch/fastverify-next/selftest")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    st = Path(args.selftest_dir)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    hdr, items = load_export(st / "good.export")
    comp = json.loads((st / "comparator.json").read_text(encoding="utf-8"))

    # Control: valid inductive
    b = ExportBuilder(hdr, items)
    add_16489_ind(b, ctor_is_unsafe=False, loose_bvar_idx=0, ind_name="Control16489Valid")
    b.write(out / "16489_control_valid.export")

    # #16489 safe ctor (isUnsafe=false)
    b = ExportBuilder(hdr, items)
    add_16489_ind(b, ctor_is_unsafe=False, loose_bvar_idx=1, ind_name="Bug16489Safe")
    b.write(out / "16489_safe_ctor.export")

    # #16489 unsafe ctor (isUnsafe=true -> bypasses Replay postponed check!)
    b = ExportBuilder(hdr, items)
    add_16489_ind(b, ctor_is_unsafe=True, loose_bvar_idx=1, ind_name="Bug16489Unsafe")
    b.write(out / "16489_unsafe_ctor.export")

    # #16489 2-param unsafe ctor
    b = ExportBuilder(hdr, items)
    n_T, n_mk = b.name("Bug16489_2P"), b.name("Bug16489_2P.mk")
    n_a, n_b, n_y = b.name("a"), b.name("b"), b.name("y")
    e_sort1 = b.sort(b.lvl_succ(b.lvl_zero()))
    e_T = b.const(n_T, [])
    t_type = b.forallE(n_a, e_sort1, b.forallE(n_b, e_sort1, e_sort1))
    mk_type = b.forallE(n_a, e_sort1, b.forallE(n_b, e_sort1, b.forallE(n_y, b.bvar(2), b.app(b.app(e_T, b.bvar(2)), b.bvar(1)))))
    b.items.append({
        "inductive": {
            "types": [{"name": n_T, "levelParams": [], "type": t_type, "numParams": 2, "numIndices": 0,
                       "all": [n_T], "ctors": [n_mk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": n_mk, "levelParams": [], "type": mk_type, "induct": n_T, "cidx": 0,
                       "numParams": 2, "numFields": 1, "isUnsafe": True}],
            "recs": [],
        }
    })
    b.write(out / "16489_2param_unsafe.export")

    # #15100-class: unsafe axiom referenced in safe inductive's ctors
    b = ExportBuilder(hdr, items)
    n_I, n_mk, n_rec = b.name("BadInd15100"), b.name("BadInd15100.mk"), b.name("BadInd15100.rec")
    n_motive, n_t, n_mk_b, n_u = b.name("motive"), b.name("t"), b.name("mk"), b.name("u")
    e_prop, e_sortu = b.sort(b.lvl_zero()), b.sort(b.lvl_param(n_u))
    e_I, e_mk = b.const(n_I, []), b.const(n_mk, [])
    b.items.append({"axiom": {"name": n_mk, "levelParams": [], "type": e_I, "isUnsafe": True}})
    motive_ty = b.forallE(n_t, e_I, e_sortu)
    minor_ty = b.app(b.bvar(0), e_mk)
    major_ty = b.forallE(n_t, e_I, b.app(b.bvar(2), b.bvar(0)))
    rec_type = b.forallE(n_motive, motive_ty, b.forallE(n_mk_b, minor_ty, major_ty), "implicit")
    rhs = b.lam(n_motive, motive_ty, b.lam(n_mk_b, minor_ty, b.bvar(0)), "implicit")
    b.items.append({
        "inductive": {
            "types": [{"name": n_I, "levelParams": [], "type": e_prop, "numParams": 0, "numIndices": 0,
                       "all": [n_I], "ctors": [n_mk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [],
            "recs": [{"name": n_rec, "levelParams": [n_u], "type": rec_type, "all": [n_I],
                      "numParams": 0, "numIndices": 0, "numMotives": 1, "numMinors": 1, "k": True, "isUnsafe": False,
                      "rules": [{"ctor": n_mk, "nfields": 0, "rhs": rhs}]}],
        }
    })
    b.write(out / "15100_unsafe_axiom_as_ctor.export")

    # #15100-class: unsafe ctor with forged induct/cidx/numParams/numFields
    b = ExportBuilder(hdr, items)
    n_I, n_mk, n_rec = b.name("BadCtorMeta"), b.name("BadCtorMeta.mk"), b.name("BadCtorMeta.rec")
    n_motive, n_t, n_mk_b, n_u = b.name("motive"), b.name("t"), b.name("mk"), b.name("u")
    e_prop, e_sortu = b.sort(b.lvl_zero()), b.sort(b.lvl_param(n_u))
    e_I, e_mk = b.const(n_I, []), b.const(n_mk, [])
    motive_ty = b.forallE(n_t, e_I, e_sortu)
    minor_ty = b.app(b.bvar(0), e_mk)
    major_ty = b.forallE(n_t, e_I, b.app(b.bvar(2), b.bvar(0)))
    rec_type = b.forallE(n_motive, motive_ty, b.forallE(n_mk_b, minor_ty, major_ty), "implicit")
    rhs = b.lam(n_motive, motive_ty, b.lam(n_mk_b, minor_ty, b.bvar(0)), "implicit")
    b.items.append({
        "inductive": {
            "types": [{"name": n_I, "levelParams": [], "type": e_prop, "numParams": 0, "numIndices": 0,
                       "all": [n_I], "ctors": [n_mk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": n_mk, "levelParams": [], "type": e_I, "induct": b.name("WrongInd"),
                       "cidx": 99, "numParams": 7, "numFields": 42, "isUnsafe": True}],
            "recs": [{"name": n_rec, "levelParams": [n_u], "type": rec_type, "all": [n_I],
                      "numParams": 0, "numIndices": 0, "numMotives": 1, "numMinors": 1, "k": True, "isUnsafe": False,
                      "rules": [{"ctor": n_mk, "nfields": 0, "rhs": rhs}]}],
        }
    })
    b.write(out / "15100_unsafe_ctor_forged_meta.export")

    # #15101 no-quot baseline + FakeQuot attacks
    b0 = ExportBuilder(hdr, items)
    drop_all_q = {b0.name_to_id[t] for t in (("Quot",), ("Quot", "mk"), ("Quot", "lift"), ("Quot", "ind"), ("Quot", "sound")) if t in b0.name_to_id}
    keep_nq = [o for o in items if not (("quot" in o and o["quot"]["name"] in drop_all_q) or ("axiom" in o and o["axiom"]["name"] in drop_all_q))]
    ExportBuilder(hdr, keep_nq).write(out / "15101_baseline_noquot.export")

    b = ExportBuilder(hdr, keep_nq)
    e_false = b.forallE(b.name("p"), b.sort(b.lvl_zero()), b.bvar(0))
    b.items.append({"quot": {"name": b.name("FakeQuot"), "levelParams": [], "type": e_false, "kind": "type"}})
    b.write(out / "15101_fake_quot_clean.export")

    drop_q_only = {b0.name_to_id[t] for t in (("Quot",), ("Quot", "sound")) if t in b0.name_to_id}
    keep_mk = [o for o in items if not (("quot" in o and o["quot"]["name"] in drop_q_only) or ("axiom" in o and o["axiom"]["name"] in drop_q_only))]
    b = ExportBuilder(hdr, keep_mk)
    e_false = b.forallE(b.name("p"), b.sort(b.lvl_zero()), b.bvar(0))
    b.items.append({"quot": {"name": b.name("FakeQuot"), "levelParams": [], "type": e_false, "kind": "type"}})
    b.write(out / "15101_fake_quot_plus_mk.export")

    comp_nq = dict(comp)
    comp_nq["permitted_axioms"] = ["propext", "Classical.choice"]
    (out / "comparator_noquot.json").write_text(json.dumps(comp_nq), encoding="utf-8")

if __name__ == "__main__":
    main()
