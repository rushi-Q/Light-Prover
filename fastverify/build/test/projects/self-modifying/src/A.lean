import Lean
run_cmd do
  IO.FS.writeFile "src/B.lean" "theorem b : True := trivial -- rewritten by A\n"
theorem a : True := trivial
