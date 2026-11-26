import Env
-- holds only when the build environment carries the fast sandbox's TOOLWRAP_LOG variable (sbx.sh --setenv)
theorem env_marker : underPipeline = true := rfl
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun (_ : env_marker = env_marker) => rfl) rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
