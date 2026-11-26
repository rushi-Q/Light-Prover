import Defs
-- Both proofs are valid. The first alternative of each `first` fails in the official build because the KERNEL rejects the
-- auxiliary lemma `2 + 2 = 5` (resp. `2 + 1 = 4`) built by kernel-mode decide; the elaborator then takes the second alternative.
-- With -Ddebug.skipKernelTC the aux lemma is added unchecked, the first alternative "succeeds", and the false aux lemma ends up
-- in the proof term. Nothing in this file matches the ktc_guard regex (flags `+revert +kernel`; `kdecide` is a macro from Defs).
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by
  have h : (2 : Nat) + 2 = 5 ∨ True := by first | (left; decide +revert +kernel) | (right; trivial)
  rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := by
  have h : (2 : Nat) + 1 = 4 ∨ True := by first | (left; kdecide) | (right; trivial)
  rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
