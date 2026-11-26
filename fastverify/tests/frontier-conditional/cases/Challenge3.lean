-- a shape seen in PNT+ (BKLNW.thm_1a): the target's STATEMENT mentions a definition whose value carries a proof field that
-- cites a sorried lemma; Lake's compareAt compares that lemma by value with the challenge
theorem citation : 2 ≤ 3 := sorry
structure Inputs where
  b : Nat
  hb : 2 ≤ 3
def Inputs.default : Inputs := ⟨5, citation⟩
theorem target1 : Inputs.default.b = 5 := sorry
