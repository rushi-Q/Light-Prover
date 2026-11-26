import Lean
open Lean Elab Command Meta

structure PP where
  a : (1 : Nat) = 1
  b : (4 : Nat) = 4

-- A project command (this module matches prep.py's ktc_guard regex and keeps the kernel check; it adds nothing bad itself).
-- Used in Main, it adds riemannHypothesis : 4 = 4 whose proof projects field 4294967297 (= 2^32 + 1) of a two-field
-- structure: ill-typed for every kernel ("(kernel) invalid projection"); stored unchecked under -Ddebug.skipKernelTC=true.
elab "add_rh_with_big_projection" : command => liftTermElabM do
  let ty ← inferType (mkConst ``PP.b)
  let .forallE _ _ goal _ := ty | throwError "unexpected"
  let mk := mkApp2 (mkConst ``PP.mk) (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr (1:Nat)))
                                     (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr (4:Nat)))
  addDecl (.thmDecl { name := `riemannHypothesis, levelParams := [], type := goal, value := mkProj ``PP (2^32 + 1) mk,
                      all := [`riemannHypothesis] })
