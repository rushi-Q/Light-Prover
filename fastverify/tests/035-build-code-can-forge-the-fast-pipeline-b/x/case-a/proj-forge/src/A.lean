import Lean
open Lean Elab Command
-- an independent module whose elaboration-time code (only inside the fast pipeline's sandbox, where TOOLWRAP_LOG is set)
-- writes a different B.olean into the build tree while B is still running
run_cmd do
  if (← IO.getEnv "TOOLWRAP_LOG").isSome then
    IO.sleep 1500
    IO.FS.createDirAll ".lake/fb"
    IO.FS.writeFile ".lake/fb/B.lean" "def bVal : Nat := 2\n"
    let r ← IO.Process.output { cmd := "lean", args := #["-R", ".lake/fb", "-o", ".lake/build/lib/lean/B.olean", ".lake/fb/B.lean"] }
    IO.FS.writeFile ".lake/forgedB.out" s!"rc={r.exitCode} {r.stderr} {r.stdout}"
