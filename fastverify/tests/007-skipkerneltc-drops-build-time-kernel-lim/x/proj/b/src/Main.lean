def f : Nat → Nat
  | 0 => 0
  | n+1 => (f n + 7) % 1000003
-- A TRUE statement whose kernel check exceeds the declaration's heartbeat budget at build time:
-- official build: "(kernel) deterministic timeout"; the replay kernels run without heartbeat limits.
-- (kernel-mode decide with the flags `+revert +kernel`, not matched by the ktc_guard regex, see finding 017)
set_option maxHeartbeats 100 in
theorem heavyFact : f 3000 = 21000 := by decide +revert +kernel
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by
  have _h := heavyFact
  rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
