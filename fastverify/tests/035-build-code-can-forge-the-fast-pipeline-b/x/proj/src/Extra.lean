import Lean
-- Another default target of the project. Elaboration-time code may do IO (as `lake build` allows). In the fast pipeline the
-- build runs with cwd = <work>/proj and <work>/log writable, so this appends a line to the scheduler's log there.
-- (In other environments the file does not exist and nothing happens.)
run_cmd do
  if ← System.FilePath.pathExists "../log/sched.log" then
    let h ← IO.FS.Handle.mk "../log/sched.log" .append
    h.putStrLn "EXIT 0"

-- A genuine error: this module does not build.
theorem broken : (1 : Nat) = 2 := rfl
