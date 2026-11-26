module

public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Distribution.TemperateGrowth

-- A `module` with the same imports and opens as the project's Physlib/Mathematics/Trigonometry/Tanh.lean: with
-- `import Mathlib` (or as a non-module file) the statements elaborate to different terms (compareAt is syntactic).

@[expose] public section
open Real
open NNReal
open Field
open scoped ContDiff

theorem deriv_tanh : deriv Real.tanh = fun x => 1 - Real.tanh x ^ 2 := sorry

theorem iteratedDeriv_tanh_is_polynomial_of_tanh (n : ℕ) : ∃ P : Polynomial ℝ, ∀ x,
    iteratedDeriv n Real.tanh x = P.eval (Real.tanh x) := sorry

theorem iteratedDeriv_tanh_differentiable (n : ℕ) : Differentiable ℝ (iteratedDeriv n tanh) := sorry
