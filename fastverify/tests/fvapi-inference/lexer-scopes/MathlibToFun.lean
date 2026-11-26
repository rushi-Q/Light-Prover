import Mathlib.Tactic.ToFun
@[to_fun hard_thm]
theorem easy_thm : id = (id : Nat → Nat) := rfl
