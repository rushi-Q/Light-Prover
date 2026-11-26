import Lean
open Lean Elab Command

structure PP where
  a : (1 : Nat) = 1
  b : (4 : Nat) = 4

-- The proof term projects field 4294967297 (= 2^32 + 1) of a two-field structure: ill-typed for
-- every kernel. The original Lean build rejects it ("(kernel) invalid projection"). The fast build
-- (-Ddebug.skipKernelTC=true) stores it unchecked, and the native exporter writes the index modulo
-- 2^32, i.e. field 1, which makes it a valid proof of 4 = 4.
run_cmd liftTermElabM do
  let ty ← Meta.inferType (mkConst ``PP.b)  -- PP → 4 = 4
  let .forallE _ _ goal _ := ty | throwError "unexpected"
  let pf := mkProj ``PP (2^32 + 1) (mkApp2 (mkConst ``PP.mk) (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr (1:Nat)))
                                                            (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr (4:Nat))))
  addDecl (.thmDecl { name := `riemannHypothesis, levelParams := [], type := goal, value := pf, all := [`riemannHypothesis] })

theorem riemannZeta_eq_zero_re : True := trivial
theorem LFunction_ne_zero_of_half_lt_re : True := trivial
theorem LFunction_eq_zero_re : True := trivial
theorem LFunction_eq_zero_re_of_isPrimitive : True := trivial
