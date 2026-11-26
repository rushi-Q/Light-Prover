/- Challenge for SampCert at e85bd645ac21 (Lean v4.33.1, Mathlib 0df444a): zCDP of the discrete Gaussian mechanism
   (`SLang.privNoisedQuery_zCDP`), statement copied verbatim from
   SampCert/DifferentialPrivacy/ZeroConcentrated/Mechanism/Properties.lean (proof: sorry), under EXACTLY that file's imports
   and opens (a first version that also stated the pure-DP theorem of the Laplace mechanism under the union of both files'
   imports was rejected by the official comparator: `laplace_pureDP_noise_priv` elaborated differently with the extra
   imports - restate statements in their own elaboration context). The definition modules come from the project (copied
   into the challenge by tools/fetch.sh from the pinned commit). -/
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Code

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

theorem privNoisedQuery_zCDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDP (privNoisedQuery query Δ ε₁ ε₂) ((1/2) * ((ε₁ : NNReal) / ε₂) ^ 2) := sorry

end SLang
