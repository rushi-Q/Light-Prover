/- Challenge for ArkLib at 3f3f045dd295 (Lean v4.33.1, Mathlib 0df444a, VCVio 76071037, CompPoly a09455a2): algebraic
   correctness of the KZG polynomial commitment (ArkLib/Commitments/Functional/KZG/Correctness.lean, `KZG.correctness`),
   statement and its section context copied verbatim (proof: sorry). -/
import ArkLib.Commitments.Functional.KZG.Basic
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

open CompPoly CompPoly.CPolynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [Fact (0 < p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

variable {n : ℕ} -- the maximal degree of polynomials that can be committed to/opened.

omit [DecidableEq G₁] [Fact (0 < p)] in
/-- Algebraic correctness of one KZG opening for a coefficient vector. -/
theorem correctness (hpG1 : Nat.card G₁ = p) (n : ℕ) (a : ZMod p)
    (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) :
  let poly : CPolynomial (ZMod p) :=
    ⟨(Raw.mk (Array.ofFn coeffs)).trim, Raw.Trim.isCanonical_trim _⟩
  let v : ZMod p := eval z poly
  let srs : Vector G₁ (n + 1) × Vector G₂ 2 :=
    Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a
  let C : G₁ := commit srs.1 coeffs
  let opening : G₁ := generateOpening srs.1 coeffs z
  verifyOpening pairing (g₁ := g₁) (g₂ := g₂) srs.2 C opening z v := sorry

end KZG
