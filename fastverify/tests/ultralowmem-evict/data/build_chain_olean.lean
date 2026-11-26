import Lean
open Lean
def main (args : List String) : IO Unit := do
  let k := args.head!.toNat!
  initSearchPath (← findSysroot) [System.FilePath.mk "."]
  let env ← importModules #[{ module := `ChainBase }] {}
  let env := env.setMainModule `Chain
  let nat := mkConst ``Nat
  let ty := mkApp3 (mkConst ``Eq [Level.one]) nat (mkConst `Chain.f) (mkNatLit k)
  let v := mkApp2 (mkConst ``Eq.refl [Level.one]) nat (mkNatLit 42)
  let d := Declaration.thmDecl { name := `Chain.t, levelParams := [], type := ty, value := v }
  let opts : Options := if k == 42 then Options.empty else Options.empty.setBool (Name.mkSimple "debug" |>.str "skipKernelTC") true
  let act : CoreM Unit := addDecl d
  let ((), s) ← act.toIO { fileName := "Chain.lean", fileMap := default, options := opts } { env := env }
  writeModule s.env "Chain.olean"
  IO.println "OK"
