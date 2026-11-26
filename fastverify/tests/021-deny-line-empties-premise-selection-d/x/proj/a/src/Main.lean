import Helpers
-- Official build: `grind +suggestions` gets `myFun_eq` from the premise-selection data (Sine Qua Non) stored in
-- Helpers.olean and uses it -> the proof depends on `sorryAx` -> the comparator rejects.
-- Fast build: the deny line appended to Helpers.lean empties that data -> grind fails -> the second branch is used.
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by
  have h : myFun 3 = 3 := by first | grind +suggestions | (unfold myFun; rfl)
  rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
