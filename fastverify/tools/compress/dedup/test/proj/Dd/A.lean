namespace DdA
theorem a_one (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => rfl
theorem a_two : ∀ n : Nat, 0 + n = n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
theorem a_imp {n : Nat} : n * 1 = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.succ_mul, ih]
end DdA
