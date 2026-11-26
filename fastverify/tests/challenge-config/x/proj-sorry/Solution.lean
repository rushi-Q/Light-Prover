def myDef : Nat := 5
theorem foo : myDef + 1 = 6 := rfl
theorem bar (n : Nat) : n + 0 = n := sorry
