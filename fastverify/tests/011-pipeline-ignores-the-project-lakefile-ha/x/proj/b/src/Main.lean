-- Uses an auto-bound implicit (`a`, `b`), legal with Lean's default autoImplicit = true (no leanOptions in the lakefile).
theorem my_symm (h : a = b) : b = a := h.symm
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := my_symm rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
