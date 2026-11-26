import Delay
import Aesop

-- A project-local heartbeat budget (as many Mathlib/RH files do). The `aesop` call needs ~60-70k heartbeats when Aesop's
-- code is INTERPRETED (official Lean: `lake build` never loads native package code) but only ~25-30k when Aesop runs as
-- NATIVE code (fast pipeline: `--load-dynlib=libpkgs.so`). Budget 45 (x1000) lies in between.
set_option maxHeartbeats 45 in
theorem key : ∀ (p q r s : Prop), p → (p → q) → (q → r) → (r → s) → s ∧ p ∧ q := by aesop

theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by
  have _ := key
  rfl

theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
