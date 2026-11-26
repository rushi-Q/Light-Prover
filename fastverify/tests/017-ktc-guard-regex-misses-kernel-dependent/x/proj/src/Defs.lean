/-- a project tactic: decide the goal with the kernel -/
macro "kdecide" : tactic => `(tactic| decide +kernel)
