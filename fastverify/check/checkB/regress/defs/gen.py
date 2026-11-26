#!/usr/bin/python3 -I
"""definition_names corpus for kcompare / check B (official Lean 4.36 compareAt definition 'holes').
usage: gen.py OUTDIR  -> OUTDIR/chal/ + OUTDIR/<case>/ (Lean projects) + OUTDIR/cases.tsv (case, expected official
verdict: the values were confirmed by the official Lean 4.36 lake comparator); run.sh builds and judges them"""
import os, sys
out = sys.argv[1]
LAKE = 'name = "{n}"\ndefaultTargets = ["{m}"]\n\n[[lean_lib]]\nname = "{m}"\n'
TC = "leanprover/lean4:v4.33.1\n"
CHAL = """def myDef : Nat := 5
def myFun (n : Nat) : Nat := n + 1
def idU.{u} (α : Sort u) (a : α) : α := a
def spare : Nat := 0
def pf (n : Nat) : Nat := n
theorem foo : myDef + 1 = 6 := sorry
theorem bar (n : Nat) : myFun n = n + 1 := sorry
theorem baz : idU Nat 3 = 3 := sorry
"""
HONEST_THMS = """theorem foo : myDef + 1 = 6 := rfl
theorem bar (n : Nat) : myFun n = n + 1 := rfl
theorem baz : idU Nat 3 = 3 := rfl
"""
BASE_DEFS = {"myDef": "def myDef : Nat := 5", "myFun": "def myFun (n : Nat) : Nat := n + 1",
             "idU": "def idU.{u} (α : Sort u) (a : α) : α := a", "spare": "def spare : Nat := 0", "pf": "def pf (n : Nat) : Nat := n"}
def sol(over=None, pre="", thms=HONEST_THMS, post=""):
    d = dict(BASE_DEFS); d.update(over or {})
    return pre + "\n".join(v for v in d.values() if v) + "\n" + thms + post
CASES = {
    # case: (solution source, expected official verdict per the 4.36 source: 0 accept / 1 reject)
    "d-honest": (sol(), 0),
    "d-defbody": (sol({"myDef": "def myDef : Nat := 2 + 3", "myFun": "def myFun (n : Nat) : Nat := Nat.succ n",
                       "idU": "def idU.{u} (α : Sort u) (a : α) : α := (fun x => x) a", "spare": "def spare : Nat := 7"}), 0),
    "d-binder-name": (sol({"myFun": "def myFun (m : Nat) : Nat := m + 1"}), 0),
    "d-helper": (sol({"myDef": "def myDef : Nat := helperVal"}, pre="def helperVal : Nat := 5\n"), 0),
    "d-recursive": (sol({"myFun": "def myFun : Nat → Nat\n  | 0 => 1\n  | n + 1 => n + 2"},
                        thms="theorem foo : myDef + 1 = 6 := rfl\ntheorem bar (n : Nat) : myFun n = n + 1 := by cases n <;> rfl\n"
                             "theorem baz : idU Nat 3 = 3 := rfl\n"), 0),
    "d-abbrev": (sol({"spare": "abbrev spare : Nat := 0"}), 0),
    "d-noncomputable": (sol({"spare": "noncomputable def spare : Nat := 0"}), 0),
    "d-instance": (sol({"spare": "instance spare : Inhabited Nat := ⟨0⟩"}), 1),   # type differs (Inhabited Nat)
    "d-reducible": (sol({"spare": "@[reducible] def spare : Nat := 0"}), 0),
    "d-irreducible": (sol({"spare": "@[irreducible] def spare : Nat := 0"}), 0),
    "d-deftype": (sol({"spare": "def spare : Int := 0"}), 1),
    "d-unsafe": (sol({"spare": "unsafe def spare : Nat := 0"}), 1),
    "d-opaque": (sol({"spare": "opaque spare : Nat"}), 1),
    "d-partial": (sol({"spare": "partial def spare : Nat := 0"}), 0),   # not recursive: elaborated as a plain def
    "d-partial-rec": (sol({"pf": "partial def pf (n : Nat) : Nat := if n = 0 then 0 else pf (n - 1) + 1"}), 1),   # recursive: an opaque constant
    "d-theorem": (sol({"spare": "theorem spare : 0 = 0 := rfl"}), 1),
    "d-axiom": (sol({"spare": "axiom spare : Nat"}), 1),
    "d-sorry": (sol({"spare": "def spare : Nat := sorry"}), 1),
    "d-classical": (sol({"spare": "noncomputable def spare : Nat := Classical.choice ⟨0⟩"}), 1),
    "d-levels": (sol({"idU": "def idU.{v} (α : Sort v) (a : α) : α := a"}), 1),
    "d-levels-type": (sol({"idU": "def idU.{u} (α : Sort (u + 1)) (a : α) : α := a"}), 1),
    "d-helper-sorry": (sol({"myDef": "def myDef : Nat := helperVal"}, pre="def helperVal : Nat := sorry\n",
                           thms="theorem foo : myDef + 1 = 6 := sorry\ntheorem bar (n : Nat) : myFun n = n + 1 := rfl\n"
                                "theorem baz : idU Nat 3 = 3 := rfl\n"), 1),
    "d-helper-axiom": (sol({"spare": "noncomputable def spare : Nat := helperAx"}, pre="axiom helperAx : Nat\n"), 1),
    "d-thm-sorry": (sol(thms="theorem foo : myDef + 1 = 6 := rfl\ntheorem bar (n : Nat) : myFun n = n + 1 := sorry\n"
                             "theorem baz : idU Nat 3 = 3 := rfl\n"), 1),
    "d-stmt": (sol(thms="theorem foo : myDef + 2 = 7 := rfl\ntheorem bar (n : Nat) : myFun n = n + 1 := rfl\n"
                        "theorem baz : idU Nat 3 = 3 := rfl\n"), 1),
}
os.makedirs(os.path.join(out, "chal"), exist_ok=True)
open(os.path.join(out, "chal", "Challenge.lean"), "w").write(CHAL)
open(os.path.join(out, "chal", "lakefile.toml"), "w").write(LAKE.format(n="challenge", m="Challenge"))
open(os.path.join(out, "chal", "lean-toolchain"), "w").write(TC)
# names case: a theorem whose name needs «» (main-thm), named in the config WITHOUT escapes -> Lean's
# String.toName gives .anonymous -> the official comparator rejects; check B must never accept (it declines)
for d, src, mod in (("n-chal", "theorem «main-thm» : 1 + 1 = 2 := sorry\n", "Challenge"),
                    ("n-sol", "theorem «main-thm» : 1 + 1 = 2 := rfl\n", "Solution")):
    os.makedirs(os.path.join(out, d), exist_ok=True)
    open(os.path.join(out, d, mod + ".lean"), "w").write(src)
    open(os.path.join(out, d, "lakefile.toml"), "w").write(LAKE.format(n=d, m=mod))
    open(os.path.join(out, d, "lean-toolchain"), "w").write(TC)
with open(os.path.join(out, "cases.tsv"), "w") as f:
    for c, (src, exp) in CASES.items():
        d = os.path.join(out, c); os.makedirs(d, exist_ok=True)
        open(os.path.join(d, "Solution.lean"), "w").write(src)
        open(os.path.join(d, "lakefile.toml"), "w").write(LAKE.format(n="gen", m="Solution"))
        open(os.path.join(d, "lean-toolchain"), "w").write(TC)
        f.write(f"{c}\t{exp}\n")
