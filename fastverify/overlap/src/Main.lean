import Lean.CoreM
import Lean.Replay
import LeanExport.Parse
import PChk.Par
import FastParse
import PChk.PersistentRead
import PChk.Incr

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

/-- S03: a declaration name as printed by `Name.toString` (components separated by `.`, `«…»` escapes, all-digit
components are numeric). Used only for scheduling hints: a misparse only means the hint does not match. -/
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

/-- Parse an export exactly as `checkExport` always did (S08: factored out, unchanged). -/
unsafe def parseExport (exportFile : String) (seq verbose : Bool) (t0 : Nat) : IO LeanExport.ExportedEnv := do
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
    return exportEnv

/-- The replay + quotient post-check of `checkExport` on a parsed export (S08: factored out, unchanged). -/
unsafe def checkParsed (exportEnv : LeanExport.ExportedEnv) (silent seq verbose : Bool) (nthreads : Nat) (t0 : Nat) :
    IO UInt32 := do
  do
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
        -- S03: optional scheduling hint (order only, never verdict-relevant): PCHK_PRIO_FILE = file with one
        -- declaration name per line (unknown names are ignored); PCHK_SLOW_MS = log jobs slower than this (with -v)
        -- (an unreadable hint file is ignored: hints can never influence the verdict, not even by failing)
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
      return 0
    catch e =>
      println s!"Quotient post-check rejects the solution: {e}" silent
      return 1

unsafe def checkExport (exportFile : String) (silent seq verbose : Bool) (nthreads : Nat) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let exportEnv ← parseExport exportFile seq verbose t0
  checkParsed exportEnv silent seq verbose nthreads t0

/-- A nonce is exactly 32 lowercase hex digits (so it can be used as a file-name part). -/
def isNonce (s : String) : Bool := s.length == 32 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

def hexOf (b : ByteArray) : String :=
  b.foldl (init := "") fun acc x =>
    let d := "0123456789abcdef"
    acc.push (d.get ⟨(x / 16).toNat⟩) |>.push (d.get ⟨(x % 16).toNat⟩)

/-- Size and modification time of a file ("SIZE SEC NSEC"; "missing" if it cannot be read). -/
def fileStamp (path : String) : IO String := do
  try
    let md ← System.FilePath.metadata path
    return s!"{md.byteSize} {md.modified.sec} {md.modified.nsec}"
  catch _ => return "missing"

/-- `--incremental[=DIR]` (S08, see PChk/Incr.lean). Commands, one per line, on stdin or (with DIR) on the FIFO
`DIR/cmd` (opened read-write, so writers may come and go): `snap PATH` and `final PATH [NONCE]`.
ACCEPT (0) either by the incremental path (every condition of PChk/Incr.lean holds) or by `checkParsed`; every
non-accept is `checkParsed`'s verdict on the final export PATH. With DIR, the process holds an exclusive lock on
`DIR/lock` for its whole life and, for `final PATH NONCE`, writes its exit code to `DIR/res-NONCE` (atomically, before
exiting) for the `--attach=DIR` client. Exit 2 = protocol error (no verdict). -/
unsafe def incremental (dir? : Option String) (silent verbose : Bool) (nthreads : Nat) : IO UInt32 := do
  let t00 ← IO.monoNanosNow
  -- DIR mode: hold the lock (the client's liveness test), read commands from the FIFO
  let lockH? ← match dir? with
    | some d => do
      let h ← IO.FS.Handle.mk (System.FilePath.mk d / "lock") .readWrite
      h.lock (exclusive := true)
      pure (some h)
    | none => pure none
  let cmdH ← match dir? with
    | some d => IO.FS.Handle.mk (System.FilePath.mk d / "cmd") .readWrite
    | none => IO.FS.Handle.mk "/dev/stdin" .read
  let mut env := (← Lean.mkEmptyEnvironment).toKernelEnv
  let mut nsnap := 0
  let mut nok := 0
  -- S03's scheduling hint (order only, never verdict-relevant), as in checkParsed
  let prio ← match ← IO.getEnv "PCHK_PRIO_FILE" with
    | some f => do
      let txt ← (IO.FS.readFile f).catchExceptions fun _ => pure ""
      pure <| txt.splitOn "\n" |>.foldl (init := ({} : NameSet)) fun acc l =>
        let l := l.trimAscii.toString
        if l.isEmpty then acc else acc.insert (parseHintName l)
    | none => pure {}
  -- Commands are read by a dedicated reader task, so that a snapshot received while another one is being replayed is
  -- already parsed meanwhile (parse-ahead). Snapshots are still ingested one by one in arrival order; a `final` that
  -- arrives skips the snapshots queued before it that have not started (they are simply not ingested).
  let ch ← Std.CloseableChannel.new (α := String)
  let _reader ← IO.asTask (prio := .dedicated) do
    repeat
      let raw ← cmdH.getLine
      discard <| (ch.sync.send raw).toBaseIO
      if raw.isEmpty then break
  let startParse (path : String) : IO (Task (Except IO.Error LeanExport.ExportedEnv)) := do
    let t0 ← IO.monoNanosNow
    IO.asTask (prio := .dedicated) (parseExport path false verbose t0)
  -- queue of received commands: (line, parse task for snapshots)
  let mut q : Array (String × Option (Task (Except IO.Error LeanExport.ExportedEnv))) := #[]
  repeat
    -- take every command that is already there (non-blocking); if none is queued, wait for one
    let mut more := true
    while more do
      match ← ch.sync.tryRecv with
      | some raw =>
        let l : String := (raw.trimAsciiEnd).toString
        if raw.isEmpty then q := q.push ("", none)
        else if let some p := l.dropPrefix? "snap " then q := q.push (l, some (← startParse p.toString))
        else q := q.push (l, none)
      | none => more := false
    if q.isEmpty then
      let raw ← match ← ch.sync.recv with
        | some r => pure r
        | none => pure ""
      let l : String := (raw.trimAsciiEnd).toString
      if raw.isEmpty then q := q.push ("", none)
      else if let some p := l.dropPrefix? "snap " then q := q.push (l, some (← startParse p.toString))
      else q := q.push (l, none)
      continue
    let (line, task?) := q[0]!
    q := q.extract 1 q.size
    if line.isEmpty then
      IO.eprintln "[incr] command stream closed before a final command: no verdict"
      return 2
    if let some path := line.dropPrefix? "snap " then
      nsnap := nsnap + 1
      let label := s!"snapshot {nsnap}"
      if dir?.isSome && q.any (fun (l, _) => l.startsWith "final ") then
        IO.eprintln s!"[incr] {label} ({path}): a final request is waiting; snapshot skipped"
        continue
      try
        let ex ← match task? with
          | some t => IO.ofExcept (← IO.wait t)
          | none => parseExport path.toString false verbose (← IO.monoNanosNow)
        match ← PChk.Incr.ingestSnapshot env ex.constMap nthreads verbose label prio with
        | .ok (env', same, done, left) =>
          env := env'
          nok := nok + 1
          -- information for the (untrusted) snapshot driver: what was left out may be exported again later
          if let some d := dir? then
            try IO.FS.writeFile (System.FilePath.mk d / s!"leftout-{nsnap}.txt")
                  (left.foldl (fun acc n => acc ++ toString n ++ "\n") "")
            catch _ => pure ()
          IO.eprintln s!"[incr] {label} ingested ({ex.constMap.size} constants: {same} known, {done} checked, {left.size} left out) at {((← IO.monoNanosNow) - t00) / 1000000} ms"
        | .error e => IO.eprintln s!"[incr] {e}; snapshot dropped"
      catch e =>
        IO.eprintln s!"[incr] {label} ({path}): {e}; snapshot dropped"
    else if let some rest := line.dropPrefix? "final " then
      -- `final PATH NONCE` (DIR mode, from the client) or `final PATH`
      let rest := rest.toString
      let ws := rest.splitOn " "
      let (path, nonce?) :=
        if dir?.isSome && ws.length ≥ 2 && isNonce ws.getLast! then
          (" ".intercalate ws.dropLast, some ws.getLast!)
        else (rest, none)
      let t0 ← IO.monoNanosNow
      let stamp0 ← fileStamp path
      let exportEnv ← parseExport path false verbose t0
      let m := exportEnv.constMap
      let why : Option String ← do
        match ← PChk.Incr.firstUnclosed m nthreads with
        | some (n, r) => pure (some s!"final export not closed: '{n}' references '{r}', which it does not declare")
        | none => PChk.Incr.finalCheck env m nthreads verbose nsnap nok prio
      let rc ← match why with
        | none =>
          println "Lean default kernel accepts the solution" silent
          pure (0 : UInt32)
        | some r =>
          IO.eprintln s!"[incr] incremental path not usable ({r}); judging the final export with the non-incremental check"
          checkParsed exportEnv silent false verbose nthreads t0
      -- the file must not have changed while it was judged; the answer names exactly what was judged
      let stamp1 ← fileStamp path
      let rc : UInt32 := if stamp0 == stamp1 then rc else 2
      if let (some d, some n) := (dir?, nonce?) then
        let tmp := System.FilePath.mk d / s!".res-{n}.tmp"
        IO.FS.writeFile tmp s!"{rc} {stamp1} {path}\n"
        IO.FS.rename tmp (System.FilePath.mk d / s!"res-{n}")
        -- DIR mode: keep serving (another request, e.g. a self-test or an injected one, must not end the service);
        -- the orchestrator stops the process when the check is over
        IO.eprintln s!"[incr] answered {path} with {rc}"
        continue
      if let some h := lockH? then h.unlock
      return rc
    else
      IO.eprintln s!"[incr] unknown command: {line}"
  return 2

/-- `--attach=DIR` (S08): the Lean-kernel leg as the comparator starts it (`--silent --from-export PATH`), served by a
running `--incremental=DIR` process: sends `final PATH NONCE` (fresh random nonce) on `DIR/cmd` and returns the exit
code that process wrote to `DIR/res-NONCE` (0 accept / 1 reject, printing the verdict line like `checkExport`). If no
such process holds `DIR/lock`, or it ends without answering THIS nonce, the export is judged here by the unchanged
`checkExport`. So the result is always either the verdict of a `--incremental=DIR` process for exactly PATH, or
`checkExport PATH`. -/
unsafe def attach (dir exportFile : String) (silent verbose : Bool) (nthreads : Nat) : IO UInt32 := do
  let d := System.FilePath.mk dir
  let serverAlive : IO Bool := do
    try
      let h ← IO.FS.Handle.mk (d / "lock") .read
      let free ← h.tryLock (exclusive := true)
      if free then h.unlock
      return !free
    catch _ => return false
  let fallback (why : String) : IO UInt32 := do
    IO.eprintln s!"[attach] {why}: judging {exportFile} with the non-incremental check"
    checkExport exportFile silent false verbose nthreads
  unless (← serverAlive) do return ← fallback "no incremental process"
  let nonce := hexOf (← IO.getRandomBytes 16)
  if !isNonce nonce || exportFile.any (· == '\n') then return ← fallback "cannot form a request"
  try
    let h ← IO.FS.Handle.mk (d / "cmd") .readWrite
    h.putStr s!"final {exportFile} {nonce}\n"
    h.flush
  catch e => return ← fallback s!"cannot send the request ({e})"
  let res := d / s!"res-{nonce}"
  -- an answer counts only if it names exactly this file with its current size/mtime (the server writes what it
  -- judged: "RC SIZE SEC NSEC PATH"); anything else -> no verdict from the server (2) -> plain replay here
  let readRes : IO (Option UInt32) := do
    if ← res.pathExists then
      let s := (← IO.FS.readFile res).trimAscii.toString
      let mine ← fileStamp exportFile
      match s.splitOn " " with
      | rc :: a :: b :: c :: rest =>
        if " ".intercalate rest == exportFile && s!"{a} {b} {c}" == mine && mine != "missing" then
          match rc with
          | "0" => return some 0
          | "1" => return some 1
          | _ => return some 2
        else return some 2
      | _ => return some 2
    return none
  repeat
    if let some rc ← readRes then
      if rc == 0 then println "Lean default kernel accepts the solution" silent
      else if rc == 1 then println "Lean default kernel rejects the solution (incremental process)" silent
      if rc == 2 then return ← fallback "incremental process gave no verdict"
      return rc
    unless (← serverAlive) do
      if let some rc ← readRes then
        if rc == 0 then println "Lean default kernel accepts the solution" silent
        else if rc == 1 then println "Lean default kernel rejects the solution (incremental process)" silent
        if rc == 2 then return ← fallback "incremental process gave no verdict"
        return rc
      return ← fallback "incremental process ended without answering this request"
    IO.sleep 100
  return 2

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
  if "--incremental" ∈ flags || flags.any (·.startsWith "--incremental=") then
    unless args.isEmpty && !seq do
      throw <| IO.userError s!"--incremental takes no export argument (commands on stdin / DIR/cmd) and no --seq"
    let dir? := flags.findSome? fun f => (f.dropPrefix? "--incremental=").map (·.toString)
    return ← incremental dir? silent verbose nthreads
  if let some dir := flags.findSome? (fun f => (f.dropPrefix? "--attach=").map (·.toString)) then
    let [exportFile] := args |
      throw <| IO.userError s!"Exactly one export file expected but got: {args}"
    unless !seq do throw <| IO.userError "--attach and --seq exclude each other"
    return ← attach dir exportFile silent verbose nthreads
  let [exportFile] := args |
    throw <| IO.userError s!"Exactly one export file expected but got: {args}"
  checkExport exportFile silent seq verbose nthreads
