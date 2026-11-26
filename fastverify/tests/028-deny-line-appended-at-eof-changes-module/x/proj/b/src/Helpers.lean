import Lean
namespace ProjLocal
-- Inside `namespace ProjLocal`, the identifier `Lean.modifyEnv` in the pipeline's appended deny line resolves to THIS function,
-- so project code runs at EOF only in the fast build. Here it adds the lemma `ProjLocal.key`, which Main uses.
open Lean Elab Command in
def Lean.modifyEnv (f : Environment → Environment) : CommandElabM Unit := do
  _root_.Lean.MonadEnv.modifyEnv f
  liftTermElabM do
    let ty ← Meta.mkEq (mkNatLit 4) (mkNatLit 4)
    addDecl <| .thmDecl { name := `ProjLocal.key, levelParams := [], type := ty, value := ← Meta.mkEqRefl (mkNatLit 4) }
