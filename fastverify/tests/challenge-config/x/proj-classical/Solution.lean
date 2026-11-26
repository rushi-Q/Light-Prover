def myDef : Nat := 5
theorem foo : myDef + 1 = 6 := (Classical.em True).elim (fun _ => rfl) (fun _ => rfl)
theorem bar (n : Nat) : n + 0 = n := rfl
