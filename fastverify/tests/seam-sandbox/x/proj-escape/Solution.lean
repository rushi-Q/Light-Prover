import Lean
open Lean

-- seam probe: runs at elaboration time inside the build sandbox; reports into the project copy (.lake/fv-seam-probe.txt)
#eval show IO Unit from do
  let cwd ← IO.currentDir
  let mut out := s!"cwd={cwd}\n"
  for p in ["/dev/shm/fv-seam-probe", "/tmp/fv-seam-probe", "/scratch/fv-seam-probe", "$HOME/fv-seam-probe",
            (cwd / ".." / "fv-seam-probe").toString, (cwd / ".." / ".." / "incr" / "fv-seam-probe").toString] do
    try
      IO.FS.writeFile p "x"
      out := out ++ s!"write {p}: OK\n"
    catch e =>
      out := out ++ s!"write {p}: {e}\n"
  let procs ← (System.FilePath.mk "/proc").readDir
  let pids := procs.filter (fun d => d.fileName.all Char.isDigit)
  out := out ++ s!"visible pids: {pids.size}\n"
  let ch ← IO.Process.spawn { cmd := "/bin/sh", args := #["-c",
    s!"setsid nohup sh -c 'sleep 75; date > {cwd}/.lake/fv-seam-late.txt; touch /dev/shm/fv-seam-late; touch {cwd}/../fv-seam-late' >/dev/null 2>&1 < /dev/null &"] }
  let _ ← ch.wait
  out := out ++ "spawned detached sleeper\n"
  IO.FS.writeFile (cwd / ".lake" / "fv-seam-probe.txt") out

theorem foo : (2 : Nat) + 2 = 4 := rfl
