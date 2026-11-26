import Lean.CoreM
import Lean.Replay
import LeanExport.Parse
import PChk.Par
import FastParse
import PChk.PersistentRead
import EnvDigest

/-!
`pleanchecker-notary`: offline parallel Lean 4.36 kernel replay linked against UNMODIFIED
official Lean 4.36 release libraries, with canonical environment SHA-256 digest output
(`--digest-out=FILE` or `PCHK_DIGEST_OUT`).
-/

open Lean

def println (msg : String) (silent : Bool) : IO Unit :=
  unless silent do
    IO.println msg

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

def parseHintName (s : String) : Name := Id.run do
  let mut comps : Array String := #[]
  let mut cur := ""
  let mut esc := false
  for c in s.toList do
    if esc then
      if c == '»' then esc := false else cur := cur.push c
    else if c == '«' then esc := true
    else if c == '.' then
      comps := comps.push cur
      cur := ""
    else cur := cur.push c
  comps := comps.push cur
  return comps.foldl (init := Name.anonymous) fun n c =>
    if !c.isEmpty && c.all Char.isDigit then Name.mkNum n c.toNat! else Name.mkStr n c

unsafe def checkExport (exportFile : String) (silent seq verbose : Bool) (nthreads : Nat)
    (digestOut? : Option String) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  do
    let exportEnv ← if seq then IO.FS.withFile exportFile .read fun handle => LeanExport.parseStream (.ofHandle handle)
      else PChk.parseExportFileP exportFile
    let tp ← IO.monoNanosNow
    let exportEnv ← if seq then pure exportEnv else Runtime.markPersistent exportEnv
    if verbose then
      IO.eprintln s!"[pchk] read {(tp - t0) / 1000000} ms, markPersistent {((← IO.monoNanosNow) - tp) / 1000000} ms"
      IO.eprintln s!"[pchk] parse {((← IO.monoNanosNow) - t0) / 1000000} ms, {exportEnv.constMap.size} constants"

    let origConstMap := exportEnv.constMap
    -- compute canonical env SHA-256 digests over the exact parsed `origConstMap`
    let digestTask? ← match digestOut? with
      | some outPath => do
        let t ← IO.asTask (prio := .dedicated) do
          let d ← FV.EnvDigest.computeEnvDigests origConstMap nthreads
          FV.EnvDigest.writeDigestFile outPath d
          return d
        pure (some t)
      | none => pure none

    let env ← Lean.mkEmptyEnvironment
    let mut kernelEnv := env.toKernelEnv
    let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
    let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
    try
      if seq then
        kernelEnv ← kernelEnv.replay kernelConstMap
      else
        let prio ← match ← IO.getEnv "PCHK_PRIO_FILE" with
          | some f => do
            let txt ← (IO.FS.readFile f).catchExceptions fun _ => pure ""
            pure <| txt.splitOn "\n" |>.foldl (init := ({} : NameSet)) fun acc l =>
              let l := l.trimAscii.toString
              if l.isEmpty then acc else acc.insert (parseHintName l)
          | none => pure {}
        let logMinMs := ((← IO.getEnv "PCHK_SLOW_MS").bind (·.toNat?)).getD 0
        if verbose && !prio.isEmpty then IO.eprintln s!"[pchk] {prio.size} priority names"
        kernelEnv ← PChk.replayPar kernelConstMap kernelEnv nthreads verbose prio logMinMs
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
    catch e =>
      println s!"Quotient post-check rejects the solution: {e}" silent
      return 1

    if let some dt := digestTask? then
      let d ← IO.ofExcept (← IO.wait dt)
      if verbose then
        IO.eprintln s!"[pchk] env_sha256_v1={d.v1} strict={d.strictV1} ({d.constCount} consts, {d.ms} ms)"
    return 0

@[extern "lean_internal_set_exit_on_panic"]
opaque setExitOnPanic (exit : Bool) : BaseIO Unit

unsafe def main (args : List String) : IO UInt32 := do
  setExitOnPanic true
  let (flags, args) := args.partition fun s => s.startsWith "-"
  let silent := "--silent" ∈ flags
  let seq := "--seq" ∈ flags
  let verbose := "-v" ∈ flags || (← IO.getEnv "PCHK_VERBOSE").isSome
  let nthreads := (flags.findSome? fun f => (f.dropPrefix? "-j").bind (·.toString.toNat?)).getD 0
  let nthreads ← if nthreads > 0 then pure nthreads else affinityCpus
  let digestFlag := flags.findSome? fun f => (f.dropPrefix? "--digest-out=").map (·.toString)
  let digestOut? ← match digestFlag with
    | some p => pure (some p)
    | none => IO.getEnv "PCHK_DIGEST_OUT"
  let [exportFile] := args |
    throw <| IO.userError s!"Exactly one export file expected but got: {args}"
  checkExport exportFile silent seq verbose nthreads digestOut?
