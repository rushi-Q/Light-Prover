import Dd.A
namespace DdB
/-- same statement as `DdA.a_one`, a different proof; `DdA.a_one` is visible here -/
theorem b_one (n : Nat) : n + 0 = n := by
  cases n with
  | zero => rfl
  | succ k => rfl
theorem b_use (m : Nat) : m + 0 + 0 = m := (DdB.b_one (m + 0)).trans (DdB.b_one m)
/-- binder-info mismatch with `DdA.a_imp` (explicit `n`) -/
theorem b_imp (n : Nat) : n * 1 = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.succ_mul, ih]
theorem b_imp_use : 5 * 1 = 5 := DdB.b_imp 5
end DdB
