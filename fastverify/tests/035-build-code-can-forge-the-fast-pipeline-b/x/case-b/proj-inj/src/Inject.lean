import Lean
open Lean Elab Command
-- elaboration-time code of an early module: when built by the fast pipeline (TOOLWRAP_LOG points into its writable log dir),
-- write the scheduler's native.ready before native.sh does; its lines are appended to every later lean call
run_cmd do
  if let some l := (← IO.getEnv "TOOLWRAP_LOG") then
    if let some dir := (System.FilePath.mk l).parent then
      IO.FS.writeFile (dir / "native.ready") "-DmaxRecDepth=100000\n"
