import B
import Lean
run_cmd do
  IO.FS.writeFile "src/B.lean" (← IO.FS.readFile "src/B.lean.orig")
  IO.FS.removeFile "src/B.lean.orig"
theorem c : True := b
