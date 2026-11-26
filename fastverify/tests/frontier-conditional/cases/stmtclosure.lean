theorem citation : 2 ≤ 3 := sorry
structure Inputs where
  b : Nat
  hb : 2 ≤ 3
def Inputs.default : Inputs := ⟨5, citation⟩
theorem target1 : Inputs.default.b = 5 := rfl
