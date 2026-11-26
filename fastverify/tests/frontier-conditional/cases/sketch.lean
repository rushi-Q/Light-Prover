def myBound : Nat := 10
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h1 : n ≤ 9 := by sorry
  have h2 : n * n ≤ 9 * 9 := by sorry
  omega
