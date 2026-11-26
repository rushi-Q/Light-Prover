-- Cheat benchmark, challenge CHM (Mathlib 0df444a): TRUE targets, one deep (FLT for n = 3).
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Real.Basic

theorem m_flt3 : FermatLastTheoremFor 3 := sorry
theorem m_prime : Nat.Prime 1000003 := sorry
theorem m_real : (1 : ℝ) < 2 := sorry
