import Mathlib
import SphereEversion.ToMathlib.Geometry.Manifold.Immersion

open Metric FiniteDimensional Set ModelWithCorners

open scoped Manifold Topology ContDiff

-- `import Mathlib` makes `TopCat.of.chartedSpace` available, which instance search would prefer over the project's
-- `chartedSpaceSelf` for `ChartedSpace ℝ³ ℝ³`; remove it locally so the statement elaborates like the project's.
attribute [-instance] TopCat.of.chartedSpace

section Smale

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

notation "𝕊²" => sphere (0 : ℝ³) 1

theorem Smale :
    ∃ f : ℝ → 𝕊² → ℝ³,
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ ↿f ∧
    (f 0 = fun x : 𝕊² ↦ (x : ℝ³)) ∧
    (f 1 = fun x : 𝕊² ↦ -(x : ℝ³)) ∧
    ∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) ∞ := sorry

end Smale
