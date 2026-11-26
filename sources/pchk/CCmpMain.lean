import CCmp
open Lake

/-!
`ccmp`: the official Lean 4.36 `lake comparator` judge (Lake/CLI/Check.lean, verbatim except
for the changes marked `C02` in `CCmp.lean`), as a standalone executable linked against the official 4.36
libraries.

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
  Lake.Check.runComparator (some cfg) (some chal) (some sol) false (!flags.contains "--sandbox") lean lake "."
