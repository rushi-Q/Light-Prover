import CCmpNotary
open Lake

def main (args : List String) : IO UInt32 := do
  let (flags, args) := args.partition (·.startsWith "--")
  let [sysroot, cfg, chal, sol] := args
    | IO.eprintln "usage: ccmp-notary SYSROOT CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT [--sandbox]"; return 2
  let lean ← LeanInstall.get sysroot
  let lake := LakeInstall.ofLean lean
  let rc ← Lake.Check.runComparator (some cfg) (some chal) (some sol) false (!flags.contains "--sandbox") lean lake "."
  if rc != 0 then
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    IO.Process.exit rc.toUInt8
  return rc
