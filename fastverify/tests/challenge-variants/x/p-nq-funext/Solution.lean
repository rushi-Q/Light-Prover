theorem helper : (fun x : Nat => x + 0) = (fun x => x) := funext fun x => rfl
theorem foo (p q : Prop) (h : p ↔ q) : p = q := by
  have _ := helper
  exact propext h
