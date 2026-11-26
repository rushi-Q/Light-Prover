import Mathlib.Tactic.HigherOrder
import Mathlib.Tactic.Simps.Basic
@[higher_order hard_thm]
theorem easy_thm (f : Nat → Nat) (x : Nat) : (fun y => f y) x = f x := rfl
structure P where
  a : Nat
  b : Nat
@[simps!] def p : P := ⟨1, 2⟩
#print axioms hard_thm
#print axioms p_a
