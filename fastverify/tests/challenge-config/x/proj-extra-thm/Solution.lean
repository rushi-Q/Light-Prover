def myDef : Nat := 5
theorem helper : myDef = 5 := rfl
theorem foo : myDef + 1 = 6 := by rw [helper]
theorem bar (n : Nat) : n + 0 = n := Nat.add_zero n
