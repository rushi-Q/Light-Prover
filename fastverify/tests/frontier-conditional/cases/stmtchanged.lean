def myBound : Nat := 10
theorem helperA : ∀ n : Nat, n < 10 → n ≤ 9 := by sorry
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 101 := by
  intro n h
  have h2 := helperB n (helperA n h)
  omega
