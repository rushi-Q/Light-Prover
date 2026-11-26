import Lean
open Lean Elab Command Meta
-- adds `fwdUse : 4 = 4 := fwdLemma` BEFORE `fwdLemma` exists (a forward reference), then `fwdLemma : 4 = 4 := rfl`
elab "add_forward_reference" : command => liftTermElabM do
  let goal ← mkEq (toExpr (4:Nat)) (toExpr (4:Nat))
  addDecl (.thmDecl { name := `fwdUse, levelParams := [], type := goal, value := mkConst `fwdLemma, all := [`fwdUse] })
  addDecl (.thmDecl { name := `fwdLemma, levelParams := [], type := goal, value := ← mkEqRefl (toExpr (4:Nat)), all := [`fwdLemma] })
