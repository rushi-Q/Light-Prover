import Lean
open Lean Elab Term Command
-- print the environment variables this module's lean process sees
run_cmd do
  for v in ["LAKE", "LAKE_HOME", "LEAN_SYSROOT", "LEAN_AR", "LEAN_CC", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_GITHASH",
            "TOOLWRAP_LOG", "HOME", "PATH", "LD_LIBRARY_PATH", "LANG"] do
    logInfo m!"ENV {v}={(← IO.getEnv v).getD "<unset>"}"
-- same list into the project's own .lake (writable in both flows) so the harness can print it
run_cmd do
  let mut s := s!"cwd={← IO.currentDir}\n"
  for v in ["LAKE", "LEAN_PATH", "TOOLWRAP_LOG", "HOME", "PATH", "LANG", "USER", "TMPDIR"] do
    s := s ++ s!"{v}={(← IO.getEnv v).getD "<unset>"}\n"
  IO.FS.writeFile ".lake/envprobe.txt" s
-- an elaboration-time fact about the build environment that lake itself determines: the number of LEAN_PATH entries
-- (lake: one lib dir per package + the project's .lake/build/lib/lean; no inherited LEAN_PATH in either official harness)
elab "leanPathEntries%" : term => do
  return toExpr (((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.filter (· ≠ "") |>.length)
def leanPathEntries : Nat := leanPathEntries%
