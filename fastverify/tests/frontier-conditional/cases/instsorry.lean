def myBound : Nat := 10
class Small (n : Nat) : Prop where
  pf : n ≤ 9
instance smallInst (n : Nat) : Small n := ⟨sorry⟩
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h2 := helperB n (Small.pf (n := n))
  omega
