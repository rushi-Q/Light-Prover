import LeanExport.Parse
import Lake.Check.Util
import Lean.Data.Json
open Lean

/-- OfficialDump EXPORT OUT: one JSON line per constant of the OFFICIAL reader's view (LeanExport.parseStream, the reader
ccmp's FastParse reproduces): name components, kind, Lake.Check.runForUsedConsts (what the comparator follows), and for a
definition whether `value.getLambdaBody.isAppOf sorryAx` (the 4.37 rule). Oracle for xvcheck.py's strict reader. -/
def nameJson (n : Name) : Json :=
  Json.arr (n.components.toArray.map fun c => match c with
    | .str _ s => Json.str s
    | .num _ i => Json.num (i : Nat)
    | .anonymous => Json.null)

def main (args : List String) : IO UInt32 := do
  let h ← IO.FS.Handle.mk args[0]! .read
  let env ← LeanExport.parseStream (.ofHandle h)
  let out ← IO.FS.Handle.mk args[1]! .write
  for n in env.constOrder do
    let ci := env.constMap[n]!
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    let used : Array Name := ((Lake.Check.runForUsedConsts (m := StateM (Array Name)) ci
      fun c => modify fun (a : Array Name) => a.push c).run #[]).2
    let sorried := match ci with
      | .defnInfo d => d.value.getLambdaBody.isAppOf ``sorryAx
      | _ => false
    out.putStrLn (Json.compress <| Json.mkObj [("name", nameJson n), ("kind", kind),
      ("used", Json.arr (used.map nameJson)), ("sorried", sorried)])
  return 0
