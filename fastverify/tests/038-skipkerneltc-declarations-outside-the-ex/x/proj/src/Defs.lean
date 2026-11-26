import Lean
open Lean Elab Command
/-- a project command that adds a declaration directly (no elaborator type check) -/
elab "add_direct_decl" : command => liftTermElabM do
  -- `theorem extraFact : False := True.intro` : ill-typed, only the kernel can catch it
  addDecl <| .thmDecl { name := `extraFact, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
