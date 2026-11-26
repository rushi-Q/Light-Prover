import Lean
-- Stand-in for the many upstream modules a real project has before its main file: it just waits 150 s, so that `Main`
-- starts after the fast pipeline's native package library (native.sh, ~50 s at 48 jobs) is ready. No other effect.
run_cmd (IO.sleep 150000 : IO Unit)
