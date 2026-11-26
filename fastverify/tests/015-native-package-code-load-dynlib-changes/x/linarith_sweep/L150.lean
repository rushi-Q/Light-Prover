import Mathlib.Tactic.Linarith

set_option maxHeartbeats 150 in
theorem t (a b c d e f : ℚ) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) (h5 : e < f) : a < f + 1 := by linarith
