import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot) [System.FilePath.mk "/tmp/lowmem_evict/sol/.lake/build/lib/lean"]
  let env ← importModules #[{ module := `DemoBase }] {}
  let env := env.setMainModule `Demo
  let b := Name.mkSimple "b"
  let n := Name.mkSimple "n"
  let x := Name.mkSimple "x"
  let nat := mkConst ``Nat
  let box := mkConst `Demo.Box
  let boxRec := mkConst `Demo.Box.rec [Level.zero]
  let box42 := mkApp box (mkNatLit 42)
  let eq42 := mkApp3 (mkConst ``Eq [Level.one]) nat (mkNatLit 42) (mkNatLit 42)
  let helperTy := Expr.forallE b box42 eq42 .default
  let motive := Expr.lam n nat (Expr.lam x (mkApp box (.bvar 0)) (mkApp3 (mkConst ``Eq [Level.one]) nat (.bvar 1) (mkNatLit 42)) .default) .default
  let refl42 := mkApp2 (mkConst ``Eq.refl [Level.one]) nat (mkNatLit 42)
  let helperVal := Expr.lam b box42 (mkApp4 boxRec motive refl42 (mkNatLit 42) (.bvar 0)) .default
  let d1 := Declaration.thmDecl {
    name := `Demo.helper, levelParams := [], type := helperTy, value := helperVal
  }
  let thmVal := Expr.letE x helperTy (mkConst `Demo.helper) refl42 true
  let d2 := Declaration.thmDecl {
    name := `Demo.thm, levelParams := [], type := eq42, value := thmVal
  }
  let act : CoreM Unit := do
    addDecl d1
    addDecl d2
  let ((), s) ← act.toIO { fileName := "Demo.lean", fileMap := default } { env := env }
  writeModule s.env "/tmp/lowmem_evict/sol/.lake/build/lib/lean/Demo.olean"
  IO.println "OK wrote Demo.olean"
