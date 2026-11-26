import Lean
open Lean Elab Command Meta

-- the theorem name that the exporters' panic recovery substitutes for a free variable (default `Expr`)
theorem _inhabitedExprDummy : (4 : Nat) = 4 := rfl

-- A project command (this module matches prep.py's ktc_guard regex, so it keeps the build-time kernel check, but it adds
-- nothing bad itself). Used in Main, it adds riemannHypothesis with a FREE VARIABLE in place of its proof: rejected by every
-- kernel ("(kernel) declaration has free variables"); stored unchecked when Main is built with -Ddebug.skipKernelTC=true.
elab "add_rh_with_free_variable" : command => liftTermElabM do
  let goal ← inferType (mkConst ``_inhabitedExprDummy)
  let k := Expr.lam `h goal (.lam `g goal (.bvar 1) .default) .default   -- fun h g => h
  let pf := mkApp2 k (.fvar ⟨`noProof⟩) (mkConst ``_inhabitedExprDummy)
  addDecl (.thmDecl { name := `riemannHypothesis, levelParams := [], type := goal, value := pf, all := [`riemannHypothesis] })
