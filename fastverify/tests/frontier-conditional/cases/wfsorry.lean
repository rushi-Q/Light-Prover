def myBound : Nat := 10
def halve : Nat → Nat
  | 0 => 0
  | n + 1 => halve ((n + 1) / 2)
decreasing_by sorry
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h1 : n ≤ 9 := by unfold myBound at h; omega
  have _h0 : halve 0 = halve 0 := rfl
  have h2 := helperB n h1
  omega
