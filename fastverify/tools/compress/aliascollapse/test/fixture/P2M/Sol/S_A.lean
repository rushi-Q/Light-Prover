import Definitions.DefA
import P2M.Util
namespace P2MW.S_A
set_option autoImplicit false
namespace Inner
namespace Deep
private theorem helper (n : Nat) : dA n = Nat.succ n := rfl
end Inner.Deep
noncomputable section
theorem solution (n : Nat) : dA n = n + 1 := by simp
