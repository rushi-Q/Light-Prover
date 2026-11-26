import Mathlib
set_option linter.all false
#count_heartbeats in
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x * y + x ^ 2 + 3 := by positivity
#count_heartbeats in
example : (123456789 : ℤ) * 987654321 - 1000 = 121932631112634269 := by norm_num
#count_heartbeats in
example (x : ℝ) (hx : x ≠ 0) : (x^2 + x) / x = x + 1 := by field_simp; ring
#count_heartbeats in
example (a b : ℕ) (h : a ≤ b) : a + 2 ≤ b + 2 := by gcongr
#count_heartbeats in
example (a b c : ℤ) (h1 : a < b) (h2 : b < c) : a < c + 1 := by omega
#count_heartbeats in
example (p q : Prop) (hp : p) (hq : q) : p ∧ (q ∨ False) := by aesop
#count_heartbeats in
example (G : Type) [AddCommGroup G] (a b c : G) : a + b - c + c - b = a := by abel
#count_heartbeats in
example (n : ℕ) (h : n < 4) : n * n < 16 := by interval_cases n <;> norm_num
#count_heartbeats in
example (a b : ℚ) (h : a = 2 * b) (hb : b = 3) : a = 6 := by subst hb; linarith
#count_heartbeats in
example (x : ℝ) : Real.sqrt (x^2) = |x| := by simp [Real.sqrt_sq_eq_abs]
#count_heartbeats in
example (n : ℕ) : ((n : ℤ) + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
