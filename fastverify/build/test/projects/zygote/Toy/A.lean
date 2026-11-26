import Lean
namespace Toy
def double (n : Nat) : Nat := n + n
@[simp] theorem double_eq (n : Nat) : double n = 2 * n := by unfold double; omega
instance : Inhabited (Fin 3) := ⟨2⟩
end Toy
