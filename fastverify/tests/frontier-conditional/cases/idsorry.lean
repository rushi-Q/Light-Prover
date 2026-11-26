def myBound : Nat := 10
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := fun n h => id (by sorry)
