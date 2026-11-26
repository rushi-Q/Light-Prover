/- Challenge for leanprover/cslib at 3951377e5a3f (Lean v4.33.0 -> v4.33.1, Mathlib db584cd6 -> 0df444a, the
   one-commit toolchain bump): the FLP impossibility theorem (Cslib.Computability.Distributed.FLP.Impossibility),
   statements and their section context copied verbatim (proofs: sorry). -/
module

public import Cslib.Computability.Distributed.FLP.OnePseudoConsensus
public import Cslib.Foundations.Data.OmegaSequence.InfOcc

@[expose] public section

namespace Cslib.FLP

open Function Set Multiset Fintype Filter ωSequence

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

variable {a : Algorithm P M S}

theorem Consensus.one_not_exists [Fintype P] (hc : card P ≥ 2) :
    ¬ ∃ a : Algorithm P M S, a.Consensus 1 := sorry

theorem Consensus.ge_one_not_exists [Fintype P] {f : ℕ} (hc : card P ≥ 2) (hf : f ≥ 1) :
    ¬ ∃ a : Algorithm P M S, a.Consensus f := sorry

end Cslib.FLP
