import HB
-- PURE code: the interpreted tactics read the imported closed term `table` (HA.lean) three times
set_option maxHeartbeats 800 in
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by
  touch_table
  touch_table
  use_table
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
