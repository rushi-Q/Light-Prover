import Mathlib.Tactic.HigherOrder
@[higher_order hard_thm]
theorem easy_thm (x : Nat) : Nat.succ x = x + 1 := rfl
#print axioms hard_thm
#check @hard_thm
