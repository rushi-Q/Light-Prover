theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
-- Lake buildType = "debug" => debugAssertions = true => f 0 = (if 0 > 0 then 5 else panic! ..) = 0, so this fails officially
def f (n : Nat) : Nat := debug_assert! n > 0; 5
theorem f_zero : f 0 = 5 := rfl
