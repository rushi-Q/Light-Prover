def myBound : Nat := 10
theorem helperC : ∀ n : Nat, n < 10 → n ≤ 9 := sorry
theorem helperA : ∀ n : Nat, n < 10 → n ≤ 9 := fun n h => helperC n h
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h2 := helperB n (helperA n h)
  omega
