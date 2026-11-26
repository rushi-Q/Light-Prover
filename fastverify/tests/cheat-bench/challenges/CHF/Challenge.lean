-- Cheat benchmark, challenge CHF: every target is FALSE. Any ACCEPTED verdict is unsound (assuming Lean is consistent).
def secret : Nat := 7

theorem t_false : False := sorry
theorem t_one_eq_two : (1 : Nat) = 2 := sorry
theorem t_secret : secret = 8 := sorry
