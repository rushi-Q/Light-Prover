import Lean
import LeanExport.Parse
import FastParse
import PChk.PersistentRead
import EnvDigest

open Lean

/-- Build an exponential shared DAG (`2^depth` tree nodes, `depth + 1` DAG nodes). -/
def mkDagExpr (depth : Nat) : Expr := Id.run do
  let mut e : Expr := .bvar 0
  for _ in [0:depth] do
    e := .app e e
  return e

/-- Build a deeply nested chain (`depth` apps) to test iterative C stack (no stack overflow). -/
def mkDeepExpr (depth : Nat) : Expr := Id.run do
  let f : Expr := .const `f []
  let mut e : Expr := .bvar 0
  for _ in [0:depth] do
    e := .app f e
  return e

unsafe def main (args : List String) : IO UInt32 := do
  let ok ← FV.EnvDigest.sha256SelfTest
  unless ok do
    IO.eprintln "FAIL: sha256 self-test"
    return 1
  if let [exportFile] := args then
    let env ← PChk.parseExportFileP exportFile
    let env ← Runtime.markPersistent env
    let d ← FV.EnvDigest.computeEnvDigests env.constMap 8
    IO.println s!"env_sha256_v1={d.v1}"
    IO.println s!"env_strict_sha256_v1={d.strictV1}"
    IO.println s!"const_count={d.constCount}"
    IO.println s!"digest_ms={d.ms}"
    return 0

  -- Synthetic stress test: exponential DAG (2^45 tree size!) + 50,000-deep chain + nondep/mdata diff
  let bigNat : Nat := (1 <<< 130) + 123456789012345678901
  let e1 : Expr := .letE `x (.const `Nat []) (.lit (.natVal bigNat)) (.bvar 0) false
  let e2 : Expr := .letE `x (.const `Nat []) (.lit (.natVal bigNat)) (.bvar 0) true
  let em : Expr := .mdata {} (.lit (.strVal "hello"))
  let ePlain : Expr := .lit (.strVal "hello")

  let ci1 : ConstantInfo := .thmInfo {
    name := `T.nondep, levelParams := [`u], type := .sort .zero, value := e1, all := [`T.nondep]
  }
  let ci2 : ConstantInfo := .thmInfo {
    name := `T.nondep, levelParams := [`u], type := .sort .zero, value := e2, all := [`T.nondep]
  }
  let cim : ConstantInfo := .thmInfo {
    name := `T.mdata, levelParams := [], type := .sort .zero, value := em, all := [`T.mdata]
  }
  let cip : ConstantInfo := .thmInfo {
    name := `T.mdata, levelParams := [], type := .sort .zero, value := ePlain, all := [`T.mdata]
  }
  let ciDag : ConstantInfo := .thmInfo {
    name := `T.dag, levelParams := [], type := .sort .zero, value := mkDagExpr 45, all := [`T.dag]
  }
  let ciDeep : ConstantInfo := .thmInfo {
    name := `T.deep, levelParams := [], type := .sort .zero, value := mkDeepExpr 50000, all := [`T.deep]
  }

  let m1 : Std.HashMap Name ConstantInfo := ({} : Std.HashMap Name ConstantInfo)
    |>.insert `T.nondep ci1 |>.insert `T.mdata cim |>.insert `T.dag ciDag |>.insert `T.deep ciDeep
  let m2 : Std.HashMap Name ConstantInfo := ({} : Std.HashMap Name ConstantInfo)
    |>.insert `T.nondep ci2 |>.insert `T.mdata cip |>.insert `T.dag ciDag |>.insert `T.deep ciDeep

  let d1 ← FV.EnvDigest.computeEnvDigests m1 4
  let d2 ← FV.EnvDigest.computeEnvDigests m2 4
  IO.println s!"m1 v1={d1.v1} strict={d1.strictV1} ({d1.ms} ms)"
  IO.println s!"m2 v1={d2.v1} strict={d2.strictV1} ({d2.ms} ms)"
  if d1.v1 != d2.v1 then
    IO.eprintln "FAIL: v1 should ignore letE.nondep and mdata"
    return 1
  if d1.strictV1 == d2.strictV1 then
    IO.eprintln "FAIL: strict_v1 MUST distinguish letE.nondep / mdata"
    return 1
  IO.println "PASS synthetic DAG(2^45) + deep(50000) + bigNat(2^130) + nondep/mdata strictness!"
  return 0
