import Lean
open Lean Elab Command

-- An ordinary-looking helper namespace; the file simply ends inside it (legal Lean).
namespace Foo

/-- A local helper that happens to be called `Lean.modifyEnv` inside `Foo`. -/
def Lean.modifyEnv (_f : Environment → Environment) : CommandElabM Unit := do
  let id := mkIdent `_root_.helper
  elabCommand (← `(theorem $id : (2 : Nat) + 2 = 4 := rfl))
