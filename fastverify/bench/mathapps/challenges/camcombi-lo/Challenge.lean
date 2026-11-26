module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Order.Partition.Finpartition

-- LeanCamCombi d25aafaf, CamCombi/PlainCombi/LittlewoodOfford.lean (its auxiliary partition lemma is still `sorry` upstream:
-- the expected verdict is REJECTED, by the axiom check, in the official flow and in every preset).
public section

open scoped BigOperators

namespace Finset
variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝒜 : Finset (Finset ι)}
  {s : Finset ι} {f : ι → E} {r : ℝ}

/-- **Kleitman's lemma** (Littlewood-Offord). -/
lemma card_le_of_forall_dist_sum_le (hr : 0 < r) (h𝒜 : ∀ t ∈ 𝒜, t ⊆ s) (hf : ∀ i ∈ s, r ≤ ‖f i‖)
    (h𝒜r : ∀ u, u ∈ 𝒜 → ∀ v, v ∈ 𝒜 → dist (∑ i ∈ u, f i) (∑ i ∈ v, f i) < r) :
    #𝒜 ≤ (#s).choose (#s / 2) := sorry

end Finset
