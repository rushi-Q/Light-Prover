import Lean.LibrarySuggestions.Default
def myFun (n : Nat) : Nat := n + 0
-- unfinished helper lemma (compiles with a `sorry` warning)
theorem myFun_eq (n : Nat) : myFun n = n := sorry
