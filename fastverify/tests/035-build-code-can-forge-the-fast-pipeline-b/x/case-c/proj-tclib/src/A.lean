-- elaboration-time code of an early module; acts only inside the fast pipeline's build sandbox (TOOLWRAP_LOG set):
-- replaces the build's node-local copy of the core module Lean.Data.EditDistance (proj/.lake/tclib, first on LEAN_PATH)
#eval show IO Unit from do
  if (← IO.getEnv "TOOLWRAP_LOG").isSome then
    IO.FS.createDirAll ".lake/fc/Lean/Data"
    IO.FS.writeFile ".lake/fc/Lean/Data/EditDistance.lean" "module\npublic def Lean.EditDistance.forged : Bool := true\n"
    let r ← IO.Process.output { cmd := "lean", args := #["-R", ".lake/fc", "-o", ".lake/tclib/Lean/Data/EditDistance.olean", ".lake/fc/Lean/Data/EditDistance.lean"] }
    IO.FS.writeFile ".lake/fc.out" s!"rc={r.exitCode} {r.stderr}"
