import Mathlib

theorem Nat.iff_lt_exists_add_succ {n m : ℕ} : n < m ↔ ∃ k, m = n + (k + 1) := sorry

theorem Nat.sub_one_lt' {n : ℕ} [NeZero n] : n - 1 < n := sorry
