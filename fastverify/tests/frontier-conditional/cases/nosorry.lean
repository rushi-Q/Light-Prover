def myBound : Nat := 10
theorem unusedSorry : 1 = 2 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h1 : n ≤ 9 := by unfold myBound at h; omega
  have h2 : n * n ≤ 9 * 9 := Nat.mul_le_mul h1 h1
  omega
