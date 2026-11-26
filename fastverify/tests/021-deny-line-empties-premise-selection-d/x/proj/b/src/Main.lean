import Helpers
-- `grind +suggestions` needs `myFun_eq` from the premise-selection data in Helpers.olean (empty in the fast build).
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by
  have h : myFun (myFun 2) = 2 := by grind +suggestions
  rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
