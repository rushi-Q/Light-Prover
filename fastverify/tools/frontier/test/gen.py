#!/usr/bin/python3 -I
"""gen.py OUTDIR : core-only test projects for tools/frontier. Writes OUTDIR/ch (challenge, 2 targets) and
OUTDIR/cases/<id>/proj (+ OUTDIR/cases/<id>/expect: expected verdict, frontier, extra args) for every case below."""
import json, os, sys

CH = """def P (n : Nat) : Prop := n + 0 = n

structure Pt where
  x : Nat
  y : Nat

def Good (p : Pt) : Prop := p.x + p.y = p.y + p.x

theorem main : ∀ n, P n := by sorry

theorem main2 : ∀ p : Pt, Good p := by sorry
"""

BASE_DEFS = """def P (n : Nat) : Prop := n + 0 = n

structure Pt where
  x : Nat
  y : Nat

def Good (p : Pt) : Prop := p.x + p.y = p.y + p.x
"""

L2 = """theorem L2 (n : Nat) : P n ↔ Q n := by
  unfold P Q
  constructor
  · intro _; exact Nat.zero_add n
  · intro _; rfl
"""

# id -> (body after BASE_DEFS, expected verdict, expected frontier (sorted) or None, extra frontier.py args)
CASES = {
    # honest decomposition: one open lemma about a project definition
    "c01-one-open": ("""def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := sorry
""" + L2 + """theorem main : ∀ n, P n := fun n => (L2 n).2 (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "CONDITIONAL", ["L1"], []),
    # fully proved: plain sound acceptance
    "c02-proved": ("""def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := Nat.zero_add n
""" + L2 + """theorem main : ∀ n, P n := fun n => (L2 n).2 (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "ACCEPTED", [], []),
    # sorry inside a target's own proof: not a frontier -> REJECTED
    "c03-sorry-in-target": ("""theorem main : ∀ n, P n := fun n => sorry
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "REJECTED", [], []),
    # sorry in a definition used by a proof: data cannot be a frontier -> REJECTED
    "c04-sorry-in-def": ("""def k : Nat := sorry
theorem L0 : k + 0 = k := rfl
theorem main : ∀ n, P n := fun n => (fun _ => rfl) L0
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "REJECTED", [], []),
    # open lemma proving False: conditional acceptance is honest (frontier statement shown as False)
    "c05-false-frontier": ("""theorem Lbad : False := sorry
theorem main : ∀ n, P n := fun n => Lbad.elim
theorem main2 : ∀ p : Pt, Good p := fun p => Lbad.elim
""", "CONDITIONAL", ["Lbad"], []),
    # target statement changed in the project -> REJECTED
    "c06-statement-changed": ("""def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := sorry
theorem main : ∀ n, Q n := fun n => L1 n
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "REJECTED", None, []),
    # a project axiom (not sorry): REJECTED unless declared as a frontier hypothesis with --axioms
    "c07-axiom": ("""axiom myAx : ∀ n : Nat, n + 0 = n
theorem main : ∀ n, P n := fun n => myAx n
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "REJECTED", [], []),
    "c08-axiom-allowed": ("""axiom myAx : ∀ n : Nat, n + 0 = n
theorem main : ∀ n, P n := fun n => myAx n
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "CONDITIONAL", ["myAx"], ["--axioms", "myAx"]),
    # nested: L1 uses L3 (open) and is itself open; only L1 is on the minimal frontier
    "c09-nested": ("""def Q (n : Nat) : Prop := 0 + n = n
theorem L3 (n : Nat) : n = n := sorry
theorem L1 (n : Nat) : Q n := by have := L3 n; sorry
""" + L2 + """theorem main : ∀ n, P n := fun n => (L2 n).2 (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "CONDITIONAL", ["L1"], []),
    # universe-polymorphic open lemma + an inductive type and structure in its statement
    "c10-poly-inductive": ("""inductive Tree (α : Type u) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
def Tree.size {α : Type u} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size
theorem size_sym.{u} {α : Type u} (l r : Tree α) (a : α) : (Tree.node l a r).size = (Tree.node r a l).size := sorry
theorem main : ∀ n, P n := fun n => rfl
theorem main2 : ∀ p : Pt, Good p := fun p =>
  have h := size_sym (α := Nat) (Tree.node .leaf p.x .leaf) .leaf p.y
  Nat.add_comm _ _
""", "CONDITIONAL", ["size_sym"], []),
    # two open lemmas, one per target, names needing guillemets
    "c11-two-open-odd-names": ("""theorem «odd name».lemma (n : Nat) : n + 0 = n := sorry
namespace A.B
theorem «1x» (p : Pt) : p.x + p.y = p.y + p.x := sorry
end A.B
theorem main : ∀ n, P n := fun n => «odd name».lemma n
theorem main2 : ∀ p : Pt, Good p := fun p => A.B.«1x» p
""", "CONDITIONAL", ["A.B.«1x»", "«odd name».lemma"], []),
    # an explicit frontier list that omits an open lemma -> REJECTED (sorryAx outside the listed frontier)
    "c12-listed-incomplete": ("""theorem La (n : Nat) : n + 0 = n := sorry
theorem Lb (p : Pt) : p.x + p.y = p.y + p.x := sorry
theorem main : ∀ n, P n := fun n => La n
theorem main2 : ∀ p : Pt, Good p := fun p => Lb p
""", "REJECTED", None, ["--frontier", "La"]),
    # a frontier lemma whose statement uses a project definition with a sorry'd body -> REJECTED (data sorry)
    "c13-frontier-mentions-sorry-def": ("""def Q (n : Nat) : Prop := sorry
theorem L1 (n : Nat) : Q n := sorry
theorem main : ∀ n, P n := fun n => (fun _ => rfl) (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
""", "REJECTED", None, []),
    # native_decide-style axiom (Lean.ofReduceBool) -> REJECTED
    "c14-native-decide": ("""theorem main : ∀ n, P n := fun n => rfl
theorem t : 10 + 10 = 20 := by native_decide
theorem main2 : ∀ p : Pt, Good p := fun p => have := t; Nat.add_comm _ _
""", "REJECTED", None, []),
}


def write(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(s)


def proj(d, name, mod, src):
    write(os.path.join(d, mod + ".lean"), src)
    write(os.path.join(d, "lean-toolchain"), "leanprover/lean4:v4.33.1\n")
    write(os.path.join(d, "lakefile.toml"), 'name = "%s"\ndefaultTargets = ["%s"]\n\n[[lean_lib]]\nname = "%s"\n' % (name, mod, mod))
    write(os.path.join(d, "lake-manifest.json"), json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
                                                            "lakeDir": ".lake", "fixedToolchain": False, "name": name}) + "\n")


def main():
    out = sys.argv[1]
    proj(os.path.join(out, "chroot", "ch"), "frontier_ch", "Challenge", CH)
    write(os.path.join(out, "chroot", "ch", "comparator.json"), json.dumps({
        "challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["main", "main2"],
        "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, indent=1) + "\n")
    for cid, (body, verdict, front, args) in CASES.items():
        d = os.path.join(out, "cases", cid)
        proj(os.path.join(d, "proj"), "frontier_" + cid.replace("-", "_"), "Solution", BASE_DEFS + "\n" + body)
        write(os.path.join(d, "expect.json"), json.dumps({"verdict": verdict, "frontier": front, "args": args}) + "\n")
    print(" ".join(sorted(CASES)))


if __name__ == "__main__":
    main()
