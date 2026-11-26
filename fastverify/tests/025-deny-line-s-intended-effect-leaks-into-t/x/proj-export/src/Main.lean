import Lemmas
-- `grind +suggestions` asks Lean's default library-suggestion engine (Sine Qua Non) for premises.
theorem aux : X 5 ∨ True := by first | (left; grind +suggestions) | (right; trivial)
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by have _h := aux; rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
