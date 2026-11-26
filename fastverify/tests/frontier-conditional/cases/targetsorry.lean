def myBound : Nat := 10
theorem helperA : ∀ n : Nat, n < 10 → n ≤ 9 := by sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have _h1 := helperA n h
  sorry
