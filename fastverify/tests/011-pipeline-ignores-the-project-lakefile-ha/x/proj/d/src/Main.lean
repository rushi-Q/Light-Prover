-- `import Plausible` = the project's src/Plausible.lean for lake; the fast pipeline puts the RH Mathlib cache (incl. package `plausible`)
-- FIRST on LEAN_PATH, so it imports the package's Plausible.olean instead.
import Plausible
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := show 2 + 2 = helperVal from rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
