import Lean
open Lean
-- print the .olean path of every module in the import closure of the given modules
def main (args : List String) : IO Unit := do
  searchPathRef.set (← addSearchPathFromEnv {})
  let env ← importModules (args.toArray.map fun m => {module := m.toName}) {} (loadExts := false)
  for m in env.header.moduleNames do
    IO.println (← findOLean m)
