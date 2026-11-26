theorem dupThm : True := by exact True.intro
theorem dupB : ∀ (y : Nat), y = y := fun _ => rfl
theorem dupC : ∀ {z : Nat}, z + 0 = z := rfl
