import Tiny.B
-- Regression: elaboration-time code of an edited module rewrites another module's .olean IN PLACE in its own
-- (incremental) project tree; with a hard-linked tree this reached the BASE tree. The default copy mode must keep the base.
#eval show IO Unit from do
  let cwd ← IO.currentDir
  let p := cwd / ".lake" / "build" / "lib" / "lean" / "Tiny" / "A.olean"
  try
    IO.FS.writeFile p "poisoned by a hostile edit"
  catch _ => pure ()
theorem foo : (2 : Nat) + 2 = 4 := by
  have h := tinyB
  rw [tinyA] at h
