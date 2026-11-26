def myBound : Nat := 10
def myBound2 : Nat := sorry
theorem helperA : ∀ n : Nat, n < 10 → n ≤ 9 := by sorry
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 + 0 * myBound2 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h2 := helperB n (helperA n h)
  simp at h2
  omega
