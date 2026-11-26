def myDef : Nat := 2 + 3
theorem foo : myDef + 1 = 6 := rfl
theorem bar (n : Nat) : n + 0 = n := rfl
