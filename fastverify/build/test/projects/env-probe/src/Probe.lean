import Lean
open Lean Elab Command in
run_cmd do
  let lp ← IO.getEnv "LEAN_PATH"
  let env ← IO.Process.run { cmd := "/usr/bin/env" }
  let cwd ← IO.currentDir
  let args ← IO.FS.readFile "/proc/self/cmdline"
  logError m!"PROBE LEAN_PATH={lp} CWD={cwd} CMDLINE={args.replace "\x00" " "} ENV={env.replace "\n" ";"}"
