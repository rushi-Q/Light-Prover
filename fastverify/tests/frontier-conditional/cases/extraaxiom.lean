def myBound : Nat := 10
axiom myAx : ∀ n : Nat, n < 10 → n ≤ 9
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h2 := helperB n (myAx n h)
  omega
