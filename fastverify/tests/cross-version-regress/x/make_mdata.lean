import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {} 0
  let natConst := mkConst ``Nat
  let boolFalse := mkConst ``Bool.false
  let sorryApp := mkApp2 (mkConst ``sorryAx [Level.succ Level.zero]) natConst boolFalse
  let mdataBody := mkMData (KVMap.empty.insert `mytag (.ofBool true)) sorryApp
  let defn : DefinitionVal := {
    name := `secret
    levelParams := []
    type := natConst
    value := mdataBody
    hints := .abbrev
    safety := .safe
  }
  let env ← match env.addDeclCore 0 0 (.defnDecl defn) none true with
    | .ok e => pure e
    | .error _ => throw <| IO.userError "addDecl secret failed"
  let zero := mkConst ``Nat.zero
  let eqTy := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) natConst (mkConst `secret) zero
  let thmVal : TheoremVal := {
    name := `goal
    levelParams := []
    type := eqTy
    value := mkApp2 (mkConst ``sorryAx [Level.zero]) eqTy boolFalse
  }
  let env ← match env.addDeclCore 0 0 (.thmDecl thmVal) none true with
    | .ok e => pure e
    | .error _ => throw <| IO.userError "addDecl goal failed"
  writeModule env (System.FilePath.mk "MDataChal.olean")
  IO.println "WROTE MDataChal.olean"
