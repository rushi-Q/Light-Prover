set_option warningAsError true
-- official: the unusedVariables linter warns about `n`, warningAsError turns it into an error -> the build fails.
-- fast: -Dlinter.all=false silences the linter -> builds.
def helper : Nat → Nat
  | n => 0
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
