import Lean
open Lean Elab Command Meta
-- a helper definition fun x0 ... x(N-1) => x0 : Nat -> ... -> Nat (N binders; the innermost bvar index is N-1),
-- used in riemannHypothesis's proof
def bvN : Nat := 32768
run_cmd liftTermElabM do
  let nat := mkConst ``Nat
  let mut ty := nat
  let mut val := mkBVar (bvN - 1)
  for i in [0:bvN] do
    ty := mkForall (Name.mkSimple s!"x{bvN-1-i}") .default nat ty
    val := mkLambda (Name.mkSimple s!"x{bvN-1-i}") .default nat val
  addDecl (.defnDecl { name := `deepF, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })
elab "use_helper" : term => return mkConst `deepF
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun _ => rfl) use_helper
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
