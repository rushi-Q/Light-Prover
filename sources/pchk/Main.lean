import Lean.CoreM
import Lean.Replay
import LeanExport.Parse
import PChk.Par
import FastParse
import PChk.PersistentRead

/-!
`pleanchecker --from-export FILE`: `leanchecker --from-export` (Lean 4.36 src/LeanChecker.lean
`checkExport`) with the replay done by `PChk.replayPar` (parallel kernel checks, see PChk/Par.lean).
Flags: `-jN` worker threads (default: CPUs in our affinity mask), `--seq` = official sequential
`Lean.Kernel.Environment.replay`, `--silent`, `-v` (phase timings on stderr).
-/

open Lean

def println (msg : String) (silent : Bool) : IO Unit :=
  unless silent do
    IO.println msg

/-- Number of CPUs this process may run on (Cpus_allowed_list of /proc/self/status), else 1. -/
def affinityCpus : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    for line in s.splitOn "\n" do
      if let some rest := line.dropPrefix? "Cpus_allowed_list:" then
        let mut n := 0
        for part in rest.toString.trimAscii.toString.splitOn "," do
          match part.splitOn "-" with
          | [a] => if a.toNat?.isSome then n := n + 1
          | [a, b] => n := n + (b.toNat!.succ - a.toNat!)
          | _ => pure ()
        return max 1 n
    return 1
  catch _ => return 1

unsafe def checkExport (exportFile : String) (silent seq verbose : Bool) (nthreads : Nat) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  do
    -- C05's fast reader (objects marked persistent per chunk, PChk/PersistentRead.lean): returns exactly what
    -- `LeanExport.parseStream` returns on this file, or falls back to it
    let exportEnv ← if seq then IO.FS.withFile exportFile .read fun handle => LeanExport.parseStream (.ofHandle handle)
      else PChk.parseExportFileP exportFile
    -- Like imported environments in Lean itself: never freed, no reference counting, no MT marking
    -- when shared with the worker threads. Safety: nothing else runs concurrently at this point.
    let tp ← IO.monoNanosNow
    let exportEnv ← if seq then pure exportEnv else Runtime.markPersistent exportEnv
    if verbose then
      IO.eprintln s!"[pchk] read {(tp - t0) / 1000000} ms, markPersistent {((← IO.monoNanosNow) - tp) / 1000000} ms"
    if verbose then
      IO.eprintln s!"[pchk] parse {((← IO.monoNanosNow) - t0) / 1000000} ms, {exportEnv.constMap.size} constants"
    let env ← Lean.mkEmptyEnvironment
    let mut kernelEnv := env.toKernelEnv
    let origConstMap := exportEnv.constMap
    -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
    -- multiple times leads to errors.
    let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
    let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
    try
      if seq then
        kernelEnv ← kernelEnv.replay kernelConstMap
      else
        kernelEnv ← PChk.replayPar kernelConstMap kernelEnv nthreads verbose
      if verbose then
        IO.eprintln s!"[pchk] replay done at {((← IO.monoNanosNow) - t0) / 1000000} ms"
      println "Lean default kernel accepts the solution" silent
    catch e =>
      println s!"Lean default kernel rejects the solution: {e}" silent
      return 1

    try
      let verifyTargets := `Quot :: quotTargets
      for quotTarget in verifyTargets do
        if let some info := origConstMap[quotTarget]? then
          let some info' := kernelEnv.find? quotTarget |
            throw <| .userError s!"Could not find quotient constant in final kernel env: {quotTarget}"
          if info != info' then
            throw <| IO.userError s!"Quotient constant mismatch on: {quotTarget}"
      return 0
    catch e =>
      println s!"Quotient post-check rejects the solution: {e}" silent
      return 1

/-- Lean's own binding (Lean.Shell `Internal.setExitOnPanic`). -/
@[extern "lean_internal_set_exit_on_panic"]
opaque setExitOnPanic (exit : Bool) : BaseIO Unit

unsafe def main (args : List String) : IO UInt32 := do
  -- The official comparator runs the Lean kernel with LEAN_ABORT_ON_PANIC=1 (Check.lean envOverride): a panic in the
  -- replay (e.g. `inductiveVal!` on a non-inductive, K04's false-accept repro) aborts = REJECT instead of continuing with a
  -- default value. We always behave like that, also when started without the variable (kernel-only runs).
  setExitOnPanic true
  let (flags, args) := args.partition fun s => s.startsWith "-"
  let silent := "--silent" ∈ flags
  let seq := "--seq" ∈ flags
  let verbose := "-v" ∈ flags || (← IO.getEnv "PCHK_VERBOSE").isSome
  let nthreads := (flags.findSome? fun f => (f.dropPrefix? "-j").bind (·.toString.toNat?)).getD 0
  let nthreads ← if nthreads > 0 then pure nthreads else affinityCpus
  -- Stack: Lean executables run `main` in a fresh lthread (lean_run_main -> run_with_thread_stack, src/runtime/thread.cpp),
  -- so the official leanchecker's kernel runs on a thread with lthread's stack size (1 GB default, or LEAN_STACK_SIZE_KB).
  -- Our kernel worker threads are lthreads too (dedicated tasks) and get exactly the same size: nothing to do here.
  let [exportFile] := args |
    throw <| IO.userError s!"Exactly one export file expected but got: {args}"
  checkExport exportFile silent seq verbose nthreads
