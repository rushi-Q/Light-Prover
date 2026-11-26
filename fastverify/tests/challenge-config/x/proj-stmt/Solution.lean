def myDef : Nat := 5
theorem foo : 1 + myDef = 6 := rfl
theorem bar (n : Nat) : n + 0 = n := rfl
