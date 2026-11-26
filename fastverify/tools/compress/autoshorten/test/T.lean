import Mathlib

namespace P06Test

/-- closable as a whole: a three-line proof of a linear fact -/
theorem whole (a b : ℕ) (h : a ≤ b) : a < b + 1 := by
  have h1 : a ≤ b := h
  have h2 : b < b + 1 := Nat.lt_succ_self b
  exact lt_of_le_of_lt h1 h2

/-- only the nested block is closable -/
theorem nested (x : ℝ) (hx : 0 < x) : 0 < x * x + x := by
  have hsq : 0 < x * x := by
    have := mul_pos hx hx
    exact this
  exact add_pos hsq hx

/-- a definition with a tactic block: never touched -/
def dataDef (n : ℕ) : ℕ := by
  refine ?_
  exact n + 1

/-- two goals after constructor -/
theorem twoGoals (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

/-- a project lemma that the original proof below does not use, but `simp` does: TryAt reports it in `deps` -/
def P06Pred (n : ℕ) : Prop := n = n

@[simp] theorem p06pred_true (n : ℕ) : P06Pred n := rfl

theorem usesPred (n : ℕ) : P06Pred n ∧ True := by
  constructor
  · exact rfl
  · trivial

/-- regression (TryAt must try in the environment BEFORE the command): `simp` could only prove this `@[simp]` theorem
from itself; no closer of the test ladder proves it legitimately -/
def P06Opaque (n : ℕ) : Prop := ∀ m, m + n = n + m

@[simp] theorem selfSimp (n : ℕ) : P06Opaque n := by
  unfold P06Opaque
  intro m
  omega

end P06Test
