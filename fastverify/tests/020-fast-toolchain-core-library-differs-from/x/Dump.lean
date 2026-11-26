import Lean
open Lean
def main : IO Unit := do
  searchPathRef.set (← addSearchPathFromEnv {})
  let env ← importModules #[{module := `Lean}, {module := `Std}, {module := `Lake}] {} (loadExts := false)
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    out := out.push s!"{n}\t{hash ci.type}\t{(ci.value? (allowOpaque := true)).map hash |>.getD 0}"
  IO.println (String.intercalate "\n" (out.qsort (· < ·)).toList)
