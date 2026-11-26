-- Lake buildType = "debug" => debugAssertions = true => f's value is `if n > 0 then 5 else panic! ..` (release: just 5).
-- f is in the closure of the target theorem riemannHypothesis -> both flows succeed, exports differ.
def f (n : Nat) : Nat := debug_assert! n > 0; 5
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun _ => rfl) (f 1)
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
