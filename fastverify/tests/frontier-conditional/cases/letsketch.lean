def myBound : Nat := 10
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  let m := n * n
  have hm : m < 100 ∧ True := by sorry
  exact hm.1
