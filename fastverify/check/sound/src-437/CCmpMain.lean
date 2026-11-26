import CCmp
open Lake

/-!
`ccmp` (4.37 port): the official Lean 4.37.0-rc1 `lake comparator` judge (Lake/CLI/Check.lean, verbatim
except for the changes marked `C02`/`S03`/`D23` in `CCmp.lean`, derived by tools/mk_ccmp437.py), as a standalone executable
linked against the official 4.37.0-rc1 libraries (its `Lake.Check.Compare`/`Axioms` = the 4.37 judge code). No `--json`.

  ccmp SYSROOT CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT [--sandbox]

= `lake comparator --config CONFIG --challenge-from-export CHALLENGE_EXPORT --solution-from-export SOLUTION_EXPORT`
of the toolchain at SYSROOT (its `leanchecker`, `nanoda_bin` on PATH, ...). Without `--sandbox` the kernels run
without the comparator's own bwrap (`--inadvisably-no-sandbox`): use it only inside an outer sandbox.
Exit codes as `lake comparator`: 0 = okay, 1 = rejected/error, 2 = could not run.
-/
def main (args : List String) : IO UInt32 := do
  let (flags, args) := args.partition (·.startsWith "--")
  let [sysroot, cfg, chal, sol] := args
    | IO.eprintln "usage: ccmp SYSROOT CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT [--sandbox]"; return 2
  let lean ← LeanInstall.get sysroot
  let lake := LakeInstall.ofLean lean
  let rc ← Lake.Check.runComparator (some cfg) (some chal) (some sol) false (!flags.contains "--sandbox") false lean lake "."
  -- S03 early stop: after a rejection other legs may still be running on dedicated threads (waiting for their child
  -- processes); returning from `main` would wait for them, so exit the process right away (children are killed by
  -- the caller's sandbox / --die-with-parent). An accept (rc = 0) only happens after every leg has finished.
  if rc != 0 then
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    IO.Process.exit rc.toUInt8
  return rc
