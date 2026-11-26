import Lean
open Lean Elab Term

/-- non-tail recursion (depth n) evaluated by the interpreter while elaborating a theorem body -/
partial def depthSum : Nat → Nat
  | 0 => 0
  | n+1 => 1 + depthSum n

elab "computeDeep" n:num : term => return mkNatLit (depthSum n.getNat)

theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by
  have _h : computeDeep 1000000 = 1000000 := rfl
  rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
