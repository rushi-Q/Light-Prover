import Lean
open Lean
/-- Prints every constant name of the environment of the given root modules whose `toString` round-trips through
`Syntax.decodeNameLit` (the parser lean4export uses for its target arguments), one per line. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (args.toArray.map fun m => { module := m.toName }) {}
  let out ← IO.getStdout
  for (n, _) in env.constants.map₁.toList do
    let s := n.toString
    if Syntax.decodeNameLit ("`" ++ s) == some n then
      out.putStrLn s
