#!/usr/bin/python3 -I
"""challenge-variants: writes the challenge variants c-*/ and solution projects p-*/ of this test into the current directory.
Each challenge dir: Challenge source, lakefile.toml, lean-toolchain, comparator.json, export-targets.nl (one target per line,
in Lake 4.36 compareIt order: builtin Quot targets iff Quot.sound is permitted ++ theorems ++ permitted axioms ++ the 28
primitives ++ definitions, each as Name.toString prints it). cases.txt: '<project> <challenge>' per line."""
import json, os
TC = "leanprover/lean4:v4.33.1\n"
PRIM = ("Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft "
        "Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam "
        "semiOutParam outParam").split()
STD = ["propext", "Quot.sound", "Classical.choice"]

def lake(name, lib, default):
    return f'name = "{name}"\ndefaultTargets = ["{default}"]\n\n[[lean_lib]]\nname = "{lib}"\n'

def challenge(d, cfg, files, lib="Challenge"):
    os.makedirs(d, exist_ok=True)
    for rel, src in files.items():
        os.makedirs(os.path.dirname(os.path.join(d, rel)) or d, exist_ok=True)
        open(os.path.join(d, rel), "w").write(src)
    open(os.path.join(d, "lakefile.toml"), "w").write(lake("challenge", lib, lib))
    open(os.path.join(d, "lean-toolchain"), "w").write(TC)
    open(os.path.join(d, "comparator.json"), "w").write(json.dumps(cfg, ensure_ascii=False, indent=1) + "\n")
    axs = cfg["permitted_axioms"]
    t = (["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in axs else []) + cfg["theorem_names"] + axs + PRIM \
        + cfg.get("definition_names", [])
    open(os.path.join(d, "export-targets.nl"), "w").write("\n".join(t) + "\n")

def project(d, files, lib="Solution"):
    os.makedirs(d, exist_ok=True)
    for rel, src in files.items():
        os.makedirs(os.path.dirname(os.path.join(d, rel)) or d, exist_ok=True)
        open(os.path.join(d, rel), "w").write(src)
    open(os.path.join(d, "lakefile.toml"), "w").write(lake("gen4", lib, lib))
    open(os.path.join(d, "lean-toolchain"), "w").write(TC)

cases = []
def C(p, c): cases.append(f"{p} {c}")
base = {"challenge_module": "Challenge", "solution_module": "Solution"}
# 1. enable_nanoda (bundled-kernel switch) instead of external_kernels
challenge("c-enable-nanoda", dict(base, theorem_names=["foo"], permitted_axioms=STD, enable_nanoda=True),
          {"Challenge.lean": "theorem foo : 2 + 2 = 4 := sorry\n"})
project("p-en-honest", {"Solution.lean": "theorem foo : 2 + 2 = 4 := rfl\n"}); C("p-en-honest", "c-enable-nanoda")
project("p-en-sorry", {"Solution.lean": "theorem foo : 2 + 2 = 4 := sorry\n"}); C("p-en-sorry", "c-enable-nanoda")
# 2. definitions only (theorem_names = [])
challenge("c-defs-only", dict(base, theorem_names=[], definition_names=["myDef"], permitted_axioms=STD),
          {"Challenge.lean": "def myDef : Nat := 0\n"})
project("p-do-honest", {"Solution.lean": "def myDef : Nat := 42\n"}); C("p-do-honest", "c-defs-only")
project("p-do-type", {"Solution.lean": "def myDef : Int := 0\n"}); C("p-do-type", "c-defs-only")
project("p-do-sorry", {"Solution.lean": "def myDef : Nat := sorry\n"}); C("p-do-sorry", "c-defs-only")
# 3. nested module names (challenge Chal.Spec, solution Sol.Main)
challenge("c-nested-module", dict(challenge_module="Chal.Spec", solution_module="Sol.Main", theorem_names=["foo"],
          permitted_axioms=STD), {"Chal.lean": "import Chal.Spec\n", "Chal/Spec.lean": "theorem foo (n : Nat) : n + 0 = n := sorry\n"},
          lib="Chal")
project("p-nm-honest", {"Sol.lean": "import Sol.Main\n", "Sol/Main.lean": "theorem foo (n : Nat) : n + 0 = n := rfl\n"}, lib="Sol"); C("p-nm-honest", "c-nested-module")
project("p-nm-stmt", {"Sol.lean": "import Sol.Main\n", "Sol/Main.lean": "theorem foo (n : Nat) : 0 + n = n := Nat.zero_add n\n"}, lib="Sol"); C("p-nm-stmt", "c-nested-module")
# 4. names that need «» escapes (space, dot inside a component)
challenge("c-escaped", dict(base, theorem_names=["«my thm»", "Foo.«bar.baz»"], permitted_axioms=STD),
          {"Challenge.lean": "theorem «my thm» : 1 = 1 := sorry\ntheorem Foo.«bar.baz» : True := sorry\n"})
project("p-esc-honest", {"Solution.lean": "theorem «my thm» : 1 = 1 := rfl\ntheorem Foo.«bar.baz» : True := trivial\n"}); C("p-esc-honest", "c-escaped")
project("p-esc-sorry", {"Solution.lean": "theorem «my thm» : 1 = 1 := rfl\ntheorem Foo.«bar.baz» : True := sorry\n"}); C("p-esc-sorry", "c-escaped")
# 5. unicode identifiers
challenge("c-unicode", dict(base, theorem_names=["théorème_α", "Ω.β₁"], permitted_axioms=STD),
          {"Challenge.lean": "theorem théorème_α : 0 + 1 = 1 := sorry\ntheorem Ω.β₁ : True := sorry\n"})
project("p-uni-honest", {"Solution.lean": "theorem théorème_α : 0 + 1 = 1 := rfl\ntheorem Ω.β₁ : True := trivial\n"}); C("p-uni-honest", "c-unicode")
# 6. Quot.sound NOT permitted (no builtin Quot targets in the export)
challenge("c-no-quot", dict(base, theorem_names=["foo"], permitted_axioms=["propext"]),
          {"Challenge.lean": "theorem foo (p q : Prop) (h : p ↔ q) : p = q := sorry\n"})
project("p-nq-honest", {"Solution.lean": "theorem foo (p q : Prop) (h : p ↔ q) : p = q := propext h\n"}); C("p-nq-honest", "c-no-quot")
project("p-nq-funext", {"Solution.lean": "theorem helper : (fun x : Nat => x + 0) = (fun x => x) := funext fun x => rfl\n"
                        "theorem foo (p q : Prop) (h : p ↔ q) : p = q := by\n  have _ := helper\n  exact propext h\n"}); C("p-nq-funext", "c-no-quot")
# 7. sorryAx permitted by the challenge
challenge("c-sorryax", dict(base, theorem_names=["foo"], permitted_axioms=STD + ["sorryAx"]),
          {"Challenge.lean": "theorem foo : 1 + 1 = 2 := sorry\n"})
project("p-sa-sorry", {"Solution.lean": "theorem foo : 1 + 1 = 2 := sorry\n"}); C("p-sa-sorry", "c-sorryax")
open("cases.txt", "w").write("\n".join(cases) + "\n")
