-- eligible: imports Lean (whose closure contains Lean.LibrarySuggestions.Basic)
/- a block comment /- nested -/ before the imports -/
import Lean
namespace ToyNs
def f (n : Nat) : Nat := n + 1
theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n
-- the type body head is a `let`, not a constant: only the namespace-root deny covers it
theorem let_head : let x := f 1; x = 2 := rfl
end ToyNs
