def myBound : Nat := 10
universe u
theorem helperU {α : Sort u} (a b : α) (h : a = b) : b = a := sorry
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h1 : n ≤ 9 := by unfold myBound at h; omega
  have h2 := helperB n (helperU _ _ (rfl : n = n) ▸ h1)
  omega
