import Lean
def filler32 (n : Nat) : Nat := n + 32
theorem filler32_spec (n : Nat) : filler32 n = n + 32 := rfl
