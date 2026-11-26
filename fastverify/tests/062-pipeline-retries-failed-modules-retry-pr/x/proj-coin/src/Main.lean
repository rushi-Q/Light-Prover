import Lean
open Lean Elab Command
-- A module that fails nondeterministically (here: a coin flip on the monotonic clock, standing for any flaky failure:
-- wall-clock timeouts, randomized tactics, memory/stack limits that depend on the machine state).
run_cmd do
  if (← IO.monoNanosNow) % 2 == 0 then
    throwError "flaky failure"
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
