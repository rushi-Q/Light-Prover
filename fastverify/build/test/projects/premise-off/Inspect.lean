import Toy.B
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for m in [`Toy.A, `Toy.B] do
    let some idx := env.getModuleIdx? m | throwError "no module {m}"
    for ext in (← persistentEnvExtensionsRef.get) do
      if ext.name == `sineQueNon || ext.name == `symbolFrequency then
        let sizes := (ext.getModuleEntries env idx).map fun e => (unsafe (unsafeCast e : NameMap Unit)).size
        IO.println s!"META {m} {ext.name} {sizes.foldl (· + ·) 0}"
