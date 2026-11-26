import Lean
run_cmd do
  IO.FS.writeFile "src/B.lean.orig" (← IO.FS.readFile "src/B.lean")
  IO.FS.writeFile "src/B.lean" "import A\ntheorem b : True := trivial -- modified by A\n"
theorem a : True := trivial
