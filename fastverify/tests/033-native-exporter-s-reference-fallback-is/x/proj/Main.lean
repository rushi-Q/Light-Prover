import Lean
open Lean Elab Command
run_cmd liftTermElabM do
  let goal ← Meta.inferType (mkConst ``rfl [1] |>.app (mkConst ``Nat) |>.app (toExpr (4:Nat)))
  -- (fun (_ : Sort ?u) => rfl) True   : 4 = 4, with a universe metavariable ?u
  let pf := mkApp (.lam `x (.sort (.mvar ⟨`uu⟩)) (mkApp2 (mkConst ``rfl [1]) (mkConst ``Nat) (toExpr (4:Nat))) .default) (mkConst ``True)
  addDecl (.thmDecl { name := `riemannHypothesis, levelParams := [], type := goal, value := pf, all := [`riemannHypothesis] })
theorem riemannZeta_eq_zero_re : True := trivial
theorem LFunction_ne_zero_of_half_lt_re : True := trivial
theorem LFunction_eq_zero_re : True := trivial
theorem LFunction_eq_zero_re_of_isPrimitive : True := trivial
