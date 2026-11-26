/- Challenge 2 for cedar-spec (cedar-lean) at e7e336260332: soundness and completeness of the SMT-based verification
   queries of the symbolic compiler (Cedar/Thm/Verification.lean), statements copied verbatim under exactly that file's
   imports and opens (proofs: sorry). Solution module: the lib root SymCC (imports Cedar.Thm.Verification).
   Expected: the proofs go through Cedar/Thm/SymCC/Data/Ext.lean and Cedar/Data/Int64.lean, which use `native_decide`
   (axiom Lean.ofReduceBool + trust in the compiler) -> not derivable from the permitted axioms. -/
import Cedar.Thm.SymCC.Verifier

namespace Cedar.Thm

open Spec SymCC

theorem verifyNeverErrors_is_sound  {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverErrors p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    (evaluate p.toExpr env.request env.entities).isOk := sorry

theorem verifyNeverErrors_is_complete {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverErrors p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    ¬ (evaluate p.toExpr env.request env.entities).isOk := sorry

theorem verifyAlwaysMatches_is_sound {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyAlwaysMatches p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    evaluate p.toExpr env.request env.entities = .ok true := sorry

theorem verifyAlwaysMatches_is_complete {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyAlwaysMatches p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    evaluate p.toExpr env.request env.entities ≠ .ok true := sorry

end Cedar.Thm
