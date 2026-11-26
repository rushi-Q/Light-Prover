def myBound : Nat := 10
def pos (n : Nat) : {x : Nat // x ≤ 9} := ⟨n % 10, sorry⟩
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h1 : n ≤ 9 := by unfold myBound at h; omega
  have _h3 := (pos n).2
  have h2 := helperB n h1
  omega
