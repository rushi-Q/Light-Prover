/- tools/ci/list-theorems.lean — list the user-facing theorems of a project's modules (CI benchmark helper; UNTRUSTED,
   it only proposes target names for a challenge; the comparator decides everything).
   usage (inside the build sandbox, LEAN_PATH = the built project's search path):
     lean --run list-theorems.lean ROOT_MODULE MODULE_PREFIX
   prints one theorem name per line: theorems (not definitions, not axioms) declared in modules whose name starts with
   MODULE_PREFIX, excluding internal / private / auxiliary names (components starting with '_', `match_`, `proof_`,
   `eq_<n>`, `eq_def`, ...). -/
import Lean
open Lean

def isAux (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail || isPrivateName n ||
  n.components.any fun c => match c with
    | .str _ s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
                  s == "eq_def" || s.startsWith "sizeOf_spec" || s == "injEq" || s == "inj" || s.startsWith "ext_iff"
    | _ => false

def main (args : List String) : IO UInt32 := do
  let root := args[0]!.toName
  let pfx := args[1]!.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root }] {} (trustLevel := 1024)
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless pfx.isPrefixOf m do continue
    unless ci matches .thmInfo _ do continue
    if isAux n then continue
    out := out.push n
  for n in out.qsort (fun a b => a.toString < b.toString) do
    IO.println n
  return 0
