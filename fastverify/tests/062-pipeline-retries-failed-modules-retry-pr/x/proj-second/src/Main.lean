import Lean
open Lean Elab Command
-- A module whose elaboration fails the FIRST time it is built and succeeds when it is built again in the same build
-- (it leaves a marker file in the build's working directory). Stands for any module that fails nondeterministically.
run_cmd do
  let marker : System.FilePath := ".attempt-marker"
  unless ← marker.pathExists do
    IO.FS.writeFile marker ""
    throwError "first elaboration attempt of this module fails"
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
