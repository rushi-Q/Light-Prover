import Mathlib

-- APAP 40a6a348 (Kelley-Meka bounds, YaelDillies/apap), APAP/FiniteField.lean `ff`: the finite-field case of the
-- Kelley-Meka theorem. The file's local notation `𝓛 x` (APAP/Prereqs/Chang.lean) is `1 + log x⁻¹`, written out here.
open Real Module
open Finset hiding card

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G] {A : Finset G} {q : ℕ} [Module (ZMod q) G]

theorem ff (hq₃ : 3 ≤ q) (hq : q.Prime) (hA₀ : A.Nonempty) (hA : ThreeAPFree (α := G) A) :
    finrank (ZMod q) G ≤ 2 ^ 148 * (1 + log (A.dens : ℝ)⁻¹) ^ 9 := sorry
