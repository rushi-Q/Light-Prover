-- Cheat benchmark, challenge CHT: every target is TRUE (positive controls + forbidden-means cheats).
def secret : Nat := 7
def hole (n : Nat) : Nat := n + 1

theorem t_add (n : Nat) : n + 0 = n := sorry
theorem t_pow : 2 ^ 64 % 7 = 2 := sorry
theorem t_secret : secret * 2 = 14 := sorry
theorem t_hole (n : Nat) : 0 < hole n ∨ hole n = 0 := sorry
theorem t_em (p : Prop) : p ∨ ¬p := sorry
