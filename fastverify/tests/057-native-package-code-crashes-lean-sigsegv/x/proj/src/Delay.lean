module
import Lean
-- Stand-in for the upstream modules a real project has before these files: waits 240 s so that A1-A3 start after the fast
-- pipeline's native package library (native.sh, ~1 min at 48 jobs) is ready. No other effect.
run_cmd (IO.sleep 240000 : IO Unit)
