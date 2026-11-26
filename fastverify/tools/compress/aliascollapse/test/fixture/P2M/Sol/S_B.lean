import Definitions.DefB
import Theorems.Thm_A
import P2M.Util
namespace P2MW.S_B
@[simp] theorem helperB (n : Nat) : n + 0 = n := rfl
instance instFooUnit : Foo Unit := ⟨()⟩
theorem solution (n : Nat) : dA (n + 0) = n + 1 := by rw [helperB]; exact A n
end P2MW.S_B
