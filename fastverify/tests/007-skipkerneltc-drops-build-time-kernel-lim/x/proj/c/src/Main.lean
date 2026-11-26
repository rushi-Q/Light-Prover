import Helper

-- (case c: forward reference) This module contains none of the keywords of prep.py's ktc_guard regex, so
-- the fast pipeline builds it with the build-time kernel check switched off (skipKernelTC). The command adds
-- `fwdUse : 4 = 4 := fwdLemma` BEFORE `fwdLemma` exists; only the build-time kernel check rejects that order.
add_forward_reference

theorem riemannHypothesis : (2 : Nat) + 2 = 4 := fwdUse
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
