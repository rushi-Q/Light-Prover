import CCmpLowMem
open Lake

@[extern "lean_internal_set_exit_on_panic"]
opaque setExitOnPanic (exit : Bool) : BaseIO Unit

def main (args : List String) : IO UInt32 := do
  setExitOnPanic true
  let (flags, args) := args.partition (·.startsWith "--")
  let compareOnly := flags.contains "--compare-only"
  let [sysroot, cfg, chal, sol] := args
    | IO.eprintln "usage: ccmp-lowmem SYSROOT CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT [--sandbox] [--compare-only]"; return 2
  let lean ← LeanInstall.get sysroot
  let lake := LakeInstall.ofLean lean
  let rc ← Lake.Check.runComparatorLowMem compareOnly (some cfg) (some chal) (some sol) false
    (!flags.contains "--sandbox") lean lake "."
  if rc != 0 then
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    IO.Process.exit rc.toUInt8
  return rc
