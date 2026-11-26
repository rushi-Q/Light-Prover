namespace DdC
/-- same statement as `DdA.a_two`, which is NOT imported here -/
theorem c_two : ∀ k : Nat, 0 + k = k := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ, ih]
theorem c_use : 0 + (0 + 3) = 3 := (DdC.c_two (0 + 3)).trans (DdC.c_two 3)
end DdC
