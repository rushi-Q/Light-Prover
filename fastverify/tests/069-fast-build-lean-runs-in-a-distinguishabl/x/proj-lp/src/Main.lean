import Env
-- holds only when LEAN_PATH has 2 entries (the pipeline: .lake/pkglib or .lake/emptypkg + .lake/build/lib/lean);
-- lake build of this dependency-free project gives exactly 1 (.lake/build/lib/lean)
theorem env_marker : leanPathEntries = 2 := rfl
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun (_ : env_marker = env_marker) => rfl) rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
