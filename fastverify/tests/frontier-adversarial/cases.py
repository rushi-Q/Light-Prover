#!/usr/bin/python3 -I
"""gen.py OUTDIR : the frontier-mode test corpus. Core-only Lean 4.33.1 projects (no packages) with sorry
patterns. Writes OUTDIR/challenges/<id> (Challenge.lean with `sorry` proofs, comparator.json, lakefile.toml,
lean-toolchain, lake-manifest.json), OUTDIR/projects/<id> (Solution.lean) and OUTDIR/cases.json with the expected
outcome of the frontier flow:
  plain    = verdict of the normal sound check on the original export (ACCEPTED / REJECTED)
  frontier = verdict of check-frontier.sh on the rewritten export (ACCEPTED_MODULO_FRONTIER / REJECTED)
  names    = the frontier axioms the TRUSTED judge must report (sorted), for ACCEPTED_MODULO_FRONTIER
"""
import json
import os
import sys

TOOLCHAIN = "leanprover/lean4:v4.33.1\n"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
MAIN = "theorem main_thm (n : Nat) : n + 0 = n"

# id: (challenge body, solution body, expected plain, expected frontier, frontier names, note)
CASES = {
    "f01-basic": (
        f"{MAIN} := by sorry\n",
        "theorem helper (n : Nat) : n + 0 = n := by sorry\n\n" + f"{MAIN} := helper n\n",
        "REJECTED", "ACCEPTED_MODULO_FRONTIER", ["helper"], "one sorried lemma below the target"),
    "f02-closed": (
        f"{MAIN} := by sorry\n",
        "theorem helper (n : Nat) : n + 0 = n := rfl\n\n" + f"{MAIN} := helper n\n",
        "ACCEPTED", "ACCEPTED_MODULO_FRONTIER", [], "no sorry: the plain check accepts; empty frontier"),
    "f03-def-sorry": (
        "theorem main_thm : ∃ n : Nat, n = n := by sorry\n",
        "def k : Nat := sorry\n\ntheorem main_thm : ∃ n : Nat, n = n := ⟨k, rfl⟩\n",
        "REJECTED", "REJECTED", [], "sorry in a definition (data) is never a frontier assumption"),
    "f04-target-sorried": (
        f"{MAIN} := by sorry\n",
        f"{MAIN} := by sorry\n",
        "REJECTED", "REJECTED", [], "the target itself is sorried"),
    "f05-statement-sorry": (
        "theorem main_thm : True := by sorry\n",
        "theorem helper : (sorry : Prop) ∨ True := Or.inr trivial\n\n"
        "theorem main_thm : True := helper.elim (fun _ => trivial) id\n",
        "REJECTED", "REJECTED", [], "sorry inside a statement used by the proof"),
    "f06-nested-have": (
        f"{MAIN} := by sorry\n",
        "theorem helper (n : Nat) : n + 0 = n := by\n  have h : n = n + 0 := by sorry\n  exact h.symm\n\n"
        f"{MAIN} := helper n\n",
        "REJECTED", "ACCEPTED_MODULO_FRONTIER", ["helper"], "sorry inside a `have` of a lemma"),
    "f07-unused-sorry": (
        f"{MAIN} := by sorry\n",
        "theorem unused (n : Nat) : n * 0 = 1 := by sorry\n\n" + f"{MAIN} := rfl\n",
        "ACCEPTED", "ACCEPTED_MODULO_FRONTIER", [], "a sorried lemma the target does not use: empty frontier"),
    "f08-chain": (
        f"{MAIN} := by sorry\n",
        "theorem l1 (n : Nat) : 0 + n = n := by sorry\n\n"
        "theorem l2 (n : Nat) : n + 0 = n := by rw [Nat.add_comm]; exact l1 n\n\n" + f"{MAIN} := l2 n\n",
        "REJECTED", "ACCEPTED_MODULO_FRONTIER", ["l1"], "sorry two levels below the target"),
    "f09-user-axiom": (
        f"{MAIN} := by sorry\n",
        "axiom my_hyp : ∀ n : Nat, n + 0 = n\n\n" + f"{MAIN} := my_hyp n\n",
        "REJECTED", "REJECTED", [], "a project axiom is not a sorried lemma: rejected (oracle --allow-axioms: frontier [my_hyp])"),
    "f10-native-decide": (
        "theorem main_thm : 10 + 10 = 20 := by sorry\n",
        "theorem main_thm : 10 + 10 = 20 := by native_decide\n",
        "REJECTED", "REJECTED", [], "native_decide: Lean 4.33 adds an auxiliary AXIOM main_thm._native.native_decide.ax_1_1 (no Lean.ofReduceBool in the closure); never a frontier lemma"),
    "f11-statement-changed": (
        f"{MAIN} := by sorry\n",
        "theorem helper (n : Nat) : n = n := by sorry\n\ntheorem main_thm (n : Nat) : n = n := helper n\n",
        "REJECTED", "REJECTED", [], "the target statement differs from the challenge"),
    "f12-challenge-name": (
        "theorem aux_lemma (n : Nat) : n + 0 = n := by sorry\n\n" + f"{MAIN} := by sorry\n",
        "theorem aux_lemma (n : Nat) : n + 0 = n := by sorry\n\n" + f"{MAIN} := aux_lemma n\n",
        "REJECTED", "ACCEPTED_MODULO_FRONTIER", ["aux_lemma"], "a sorried lemma also declared in the challenge source but NOT in the challenge export (main_thm := sorry there): a legal frontier lemma"),
    "f12b-challenge-export-name": (
        "theorem aux_lemma (n : Nat) : n + 0 = n := by sorry\n\n" + f"{MAIN} := aux_lemma n\n",
        "theorem aux_lemma (n : Nat) : n + 0 = n := by sorry\n\n" + f"{MAIN} := aux_lemma n\n",
        "REJECTED", "?", [], "frontier lemma whose name is IN the challenge export (oracle: never a frontier axiom -> REJECTED; sound judge: conditional; both sound)"),
    "f13-universe": (
        "theorem main_thm (α : Type) (a : α) : a = a := by sorry\n",
        "theorem uhelper.{u} (α : Sort u) (a : α) : a = a := by sorry\n\n"
        "theorem main_thm (α : Type) (a : α) : a = a := uhelper α a\n",
        "REJECTED", "ACCEPTED_MODULO_FRONTIER", ["uhelper"], "universe-polymorphic frontier lemma"),
    "f14-proof-in-def": (
        "def f (n : Nat) : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩\n\n"
        "theorem main_thm (n : Nat) : (f n).val = 0 := by sorry\n",
        "def f (n : Nat) : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩\n\n"
        "theorem main_thm (n : Nat) : (f n).val = 0 := rfl\n",
        "ACCEPTED", "ACCEPTED_MODULO_FRONTIER", [], "control: statement definition, no sorry"),
    "f15-proof-obligation-sorry": (
        "theorem main_thm : (3 : Nat) = 3 := by sorry\n",
        "def g (n : Nat) : Fin (n + 1) := ⟨n, by sorry⟩\n\n"
        "theorem main_thm : (3 : Nat) = 3 := congrArg Fin.val (rfl : g 3 = g 3)\n",
        "REJECTED", "?", [], "sorried proof obligation inside a definition (lifted to an auxiliary theorem or kept in the def)"),
    "f16-two-frontier": (
        f"{MAIN} := by sorry\n\ntheorem second (n : Nat) : 0 + n = n := by sorry\n",
        "theorem a1 (n : Nat) : n + 0 = n := by sorry\n\ntheorem a2 (n : Nat) : 0 + n = n := by sorry\n\n"
        f"{MAIN} := a1 n\n\ntheorem second (n : Nat) : 0 + n = n := a2 n\n",
        "REJECTED", "ACCEPTED_MODULO_FRONTIER", ["a1", "a2"], "two targets, two frontier lemmas"),
    "f17-ill-typed-with-sorry": (
        f"{MAIN} := by sorry\n",
        "theorem helper (n : Nat) : n + 0 = n := by sorry\n\n"
        "set_option debug.skipKernelTC true in\ntheorem bad : 1 = 2 := by decide +kernel\n\n"
        f"{MAIN} := by have := bad; exact helper n\n",
        "REJECTED", "REJECTED", [], "a kernel-invalid lemma (skipKernelTC) next to a frontier lemma: kernels reject"),
    "f18-sorry-in-instance": (
        "class C (n : Nat) : Prop where\n  p : n = n\n\ntheorem main_thm (n : Nat) [C n] : n = n := by sorry\n",
        "class C (n : Nat) : Prop where\n  p : n = n\n\ninstance inst (n : Nat) : C n := ⟨by sorry⟩\n\n"
        "theorem main_thm (n : Nat) [C n] : n = n := (inst n).p\n",
        "REJECTED", "?", [], "sorried Prop-valued instance: elaborated as a THEOREM `inst` with a constructor around the sorry (partial proof: oracle frontier [inst]; canonical-only: REJECTED)"),
    "f19-dotted-name": (
        "theorem main_thm : (1 : Nat) = 2 := by sorry\n",
        "axiom Foo.bar : (1 : Nat) = 2\n\ntheorem «Foo.bar» : (0 : Nat) = 0 := by sorry\n\n"
        "theorem main_thm : (1 : Nat) = 2 := (fun (_ : (0 : Nat) = 0) => Foo.bar) «Foo.bar»\n",
        "REJECTED", "REJECTED", [], "a sorried one-component name «Foo.bar» next to a project axiom Foo.bar (two components) proving a FALSE target: name rendering / String.toName must not confuse them"),
    "f20-private-lemma": (
        f"{MAIN} := by sorry\n",
        "private theorem helper (n : Nat) : n + 0 = n := by sorry\n\n" + f"{MAIN} := helper n\n",
        "REJECTED", "ACCEPTED_MODULO_FRONTIER", ["_private.Solution.0.helper"], "a PRIVATE sorried lemma (numeric name component 0) on the frontier"),
    "f21-sketch-let": (
        "theorem main_thm (m : Nat) (hm : m = 5) : m + 0 = 5 := by sorry\n",
        "theorem main_thm (m : Nat) (hm : m = 5) : m + 0 = 5 := by\n  let n := m + 0\n  have h : n = 5 := by sorry\n  exact h\n",
        "REJECTED", "?", [], "sketch: a sorried `have` under a LET-bound variable; the abstracted open lemma must not quantify the let variable"),
    "f22-sketch-induction": (
        "theorem main_thm (n : Nat) : 0 + n = n := by sorry\n",
        "theorem main_thm (n : Nat) : 0 + n = n := by\n  induction n with\n  | zero => sorry\n  | succ k ih => sorry\n",
        "REJECTED", "?", [], "sketch: sorries in both minor premises of an induction (recursor motive in the context)"),
    "f23-sketch-cases-exists": (
        "theorem main_thm (h : ∃ x : Nat, x > 3) : ∃ y : Nat, y > 2 := by sorry\n",
        "theorem main_thm (h : ∃ x : Nat, x > 3) : ∃ y : Nat, y > 2 := by\n  obtain ⟨x, hx⟩ := h\n"
        "  have h2 : x > 2 := by sorry\n  exact ⟨x, h2⟩\n",
        "REJECTED", "?", [], "sketch: a sorried `have` after destructuring an existential (Exists.casesOn minor premise)"),
    "f24-sketch-universe": (
        "theorem main_thm.{u} (α : Sort u) (a b : α) (h : a = b) : b = a := by sorry\n",
        "theorem main_thm.{u} (α : Sort u) (a b : α) (h : a = b) : b = a := by\n  have h' : b = a := by sorry\n  exact h'\n",
        "REJECTED", "?", [], "sketch: universe-polymorphic context"),
    "f25-sketch-chain": (
        "theorem main_thm (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c + 1 := by sorry\n",
        "theorem main_thm (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c + 1 := by\n"
        "  have s1 : a ≤ c := by sorry\n  have s2 : c ≤ c + 1 := by sorry\n  exact Nat.le_trans s1 s2\n",
        "REJECTED", "?", [], "sketch: two sorried haves, the second after the first (earlier haves are context)"),
}


def write(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(s)


def manifest(pkg):
    return json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [], "lakeDir": ".lake",
                       "fixedToolchain": False, "name": pkg}, indent=1) + "\n"


def targets(src):
    out = []
    for ln in src.splitlines():
        if ln.startswith("theorem "):
            out.append(ln.split()[1].split(".{")[0])
    return out


def main(out):
    meta = {}
    for cid, (ch, so, plain, fr, names, note) in CASES.items():
        th = [t for t in targets(ch) if t in ("main_thm", "second")]
        cfg = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": th,
               "definition_names": [], "permitted_axioms": AXIOMS}
        pk = "fr_" + cid.replace("-", "_")
        for kind, mod, src in (("challenges", "Challenge", ch), ("projects", "Solution", so)):
            d = os.path.join(out, kind, cid)
            name = pk + ("challenge" if kind == "challenges" else "")
            write(os.path.join(d, f"{mod}.lean"), src)
            write(os.path.join(d, "lean-toolchain"), TOOLCHAIN)
            write(os.path.join(d, "lakefile.toml"), f'name = "{name}"\ndefaultTargets = ["{mod}"]\n\n'
                  f'[[lean_lib]]\nname = "{mod}"\n')
            write(os.path.join(d, "lake-manifest.json"), manifest(name))
            if kind == "challenges":
                write(os.path.join(d, "comparator.json"), json.dumps(cfg, indent=1) + "\n")
        meta[cid] = {"plain": plain, "frontier": fr, "names": sorted(names), "note": note}
    write(os.path.join(out, "cases.json"), json.dumps(meta, indent=1) + "\n")
    print(len(meta), "cases")


if __name__ == "__main__":
    main(sys.argv[1])
