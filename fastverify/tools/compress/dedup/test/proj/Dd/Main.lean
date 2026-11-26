import Dd.B
import Dd.C
theorem main_thm : ∀ n : Nat, n + 0 + 0 = n := DdB.b_use
theorem main_thm2 : 0 + (0 + 3) = 3 ∧ 5 * 1 = 5 := ⟨DdC.c_use, DdB.b_imp_use⟩
