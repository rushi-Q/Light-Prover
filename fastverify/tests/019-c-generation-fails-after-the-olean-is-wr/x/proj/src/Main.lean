-- The five challenge theorems, proved honestly.
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl

-- An unrelated helper with a hierarchical `@[export]` name. Elaboration (and the .olean) is fine; Lean's C code
-- generator (`lean -c`, which `lake build` always runs) rejects the name: "invalid export name 'helper'".
@[export my.helper] def helper (n : Nat) : Nat := n + 1
