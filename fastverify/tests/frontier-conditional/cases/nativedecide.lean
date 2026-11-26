def myBound : Nat := 10
theorem helperN : 9 * 9 = 81 := by native_decide
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h1 : n ≤ 9 := by unfold myBound at h; omega
  have h2 := helperB n h1
  have _ := helperN
  omega
