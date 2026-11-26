/-
fvfork — UNTRUSTED compile worker of the fvserve service. Not part of any trusted base: it only produces
`.olean` files from which the untrusted exporter produces an export that the unchanged trusted check judges.

The official `lean --incr-load=SNAP FILE -o OLEAN` (Lean 4.33.1, `Lean.Elab.runFrontend`) maps the header snapshot of
`import Mathlib` and runs every module initializer on EVERY call (0.5-1.4 s of mostly page-fault work per attempt). This
program does that ONCE: it loads the snapshot exactly as `runFrontend` does (sequentially, so that no task-manager worker
thread exists yet), runs the initializers, and then serves requests from stdin; every request is elaborated in a
`fork()`ed child that runs the body of `runFrontend` (Language.Lean.process with the loaded snapshot as `old?`,
reporting, lint recording, `writeModule`) on the attempt file. The child restricts its own file writes to its output
directory (Landlock) and writes its messages to OUTDIR/log. Copies of the private helpers of
`Lean/Elab/Frontend.lean` v4.33.1 (Apache 2.0, (c) Microsoft Corporation; authors Leonardo de Moura, Sebastian Ullrich)
are marked below.

Protocol (stdin, one request per line, TAB-separated):  ID  SRC  OUTDIR  MODULE  (read unbuffered by the shim)
Answers (stdout): `READY <threads>` once, then `DONE ID RC` per request (RC = child exit status, 128+sig on a signal).
-/
import Lean
open Lean Elab

namespace FvFork

@[extern "fv_decode_lossy_utf8"] opaque decodeLossyUTF8 (a : @& ByteArray) : String   -- shim.c: the release's own decode
@[extern "fv_fork"] opaque fork : IO UInt32
@[extern "fv_reap"] opaque reap : IO UInt64            -- 0 = no exited child, else (pid <<< 32) ||| status
@[extern "fv_exit"] opaque exitNow (code : UInt32) : IO Unit
@[extern "fv_nthreads"] opaque nthreads : IO UInt32
@[extern "fv_child_setup2"] opaque childSetup (outdir : @& String) (src : @& String) : IO UInt32   -- Landlock + seccomp
@[extern "fv_next_line"] opaque nextLine (ms : UInt32) : IO String   -- "" = nothing yet, "\x04" = EOF

/-- layout of the private `Lean.Elab.Frontend.IncrSnapshot` (copy) -/
structure IncrSnapshot where
  snap        : Language.Lean.InitialSnapshot
  initModIdxs : Array Nat

/-- copy of the private `readModuleArtifactRegions` of Frontend.lean v4.33.1 -/
unsafe def readModuleArtifactRegions (arts : ModuleArtifacts) : IO (Array CompactedRegion) := do
  let mut oleanRegions : Array CompactedRegion := #[]
  for partPath in arts.oleanParts do
    let (_, region) ← CompactedRegion.read (α := ModuleData) partPath oleanRegions
    oleanRegions := oleanRegions.push region
  let mut irRegions : Array CompactedRegion := #[]
  for partPath in arts.irParts do
    let (_, region) ← CompactedRegion.read (α := ModuleData) partPath irRegions
    irRegions := irRegions.push region
  return oleanRegions ++ irRegions

/-- `loadIncrSnapshot` of Frontend.lean v4.33.1 with ONE sequential reader instead of `numWorkers` tasks (no thread may
exist before the first fork) -/
unsafe def loadIncrSnapshotSeq (fname : System.FilePath) : IO IncrSnapshot := do
  let depsFile := fname.addExtension "deps"
  let moduleArts : Array ModuleArtifacts ←
    match Json.parse (← IO.FS.readFile depsFile) >>= fromJson? with
    | .ok arts => pure arts
    | .error e => throw <| IO.userError s!"failed to parse snapshot deps file {depsFile}: {e}"
  let mut depRegions : Array CompactedRegion := Array.emptyWithCapacity (moduleArts.size * 4)
  for arts in moduleArts do
    depRegions := depRegions ++ (← readModuleArtifactRegions arts)
  let (data, _region) ← CompactedRegion.read (α := IncrSnapshot) fname depRegions
  return data

/-- copy of the private `setMainModule` of Frontend.lean v4.33.1 -/
def setMainModule (snap : Language.Lean.InitialSnapshot) (m : Name) :
    Language.Lean.InitialSnapshot := Id.run do
  let some parsed := snap.result? | return snap
  let processed := parsed.processedSnap.get
  let some hps := processed.result? | return snap
  if hps.cmdState.env.header.mainModule == m then
    return snap
  let newEnv := hps.cmdState.env.setMainModule m
  let newCmdState := { hps.cmdState with
    env := newEnv
    auxDeclNGen := { hps.cmdState.auxDeclNGen with namePrefix := mkPrivateName newEnv .anonymous } }
  let newProcessed : Language.Lean.HeaderProcessedSnapshot := { processed with
    result? := some { hps with cmdState := newCmdState } }
  { snap with
    result? := some { parsed with
      processedSnap := .finished none newProcessed } }

/-- copy of the private `collectCommandLints` of Frontend.lean v4.33.1 -/
partial def collectCommandLints (t : Language.SnapshotTree) (cmdStx? : Option Syntax)
    (acc : Array (Option Syntax × MessageLog)) : Array (Option Syntax × MessageLog) :=
  let acc := acc.push (cmdStx?, t.element.diagnostics.msgLog)
  t.children.foldl (init := acc) fun acc child =>
    collectCommandLints child.get (child.stx? <|> cmdStx?) acc

/-- the part of `runFrontend` (v4.33.1) after the snapshot load, for `lean FILE -o OLEAN` with the snapshot as `old?`
(no ilean, no incr-save, no profiler output) -/
def elabFile (incr : IncrSnapshot) (fileName olean : String) (mainModuleName : Name) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let input := decodeLossyUTF8 (← IO.FS.readBinFile fileName)
  let inputCtx := Parser.mkInputContext input fileName
  let opts : Options := {}
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet opts true
  let opts := Elab.async.setIfNotSet opts true
  let ctx := { inputCtx with }
  let setup stx := do
    return .ok {
      imports := stx.imports
      isModule := stx.isModule
      mainModuleName, opts, trustLevel := 0, plugins := #[]
    }
  let snap := setMainModule incr.snap mainModuleName
  let snap ← Language.Lean.process setup (some snap) ctx
  let snaps := Language.toSnapshotTree snap
  let hasErrors ← snaps.runAndReport opts false {}
  let t1 ← IO.monoMsNow
  let some cmdState := Language.Lean.waitForFinalCmdState? snap
    | return 1
  let env := cmdState.env
  let finalOpts := cmdState.scopes[0]!.opts
  if hasErrors then
    return 1
  let commandLints := collectCommandLints snaps none #[]
  let env ← Linter.recordLints inputCtx.fileMap env commandLints
  let t2 ← IO.monoMsNow
  writeModule (writeIR := !Compiler.compiler.postponeCompile.get finalOpts) env olean
  let t3 ← IO.monoMsNow
  IO.eprintln s!"fvfork-times elab+report {t1 - t0} ms, lints {t2 - t1} ms, write {t3 - t2} ms"
  return 0

partial def serve (incr : IncrSnapshot) (stdout : IO.FS.Stream) (live : Std.HashMap UInt32 String) : IO Unit := do
  let mut live := live
  repeat   -- report exited children
    let r ← reap
    if r == 0 then break
    let pid := (r >>> 32).toUInt32
    if let some id := live[pid]? then
      stdout.putStrLn s!"DONE {id} {(r &&& 0xffffffff).toUInt32}"
      stdout.flush
      live := live.erase pid
  let line ← nextLine 20
  if line == "" then
    serve incr stdout live
  else if line == "\x04" then   -- EOF on stdin: wait for the running children, then exit
    while !live.isEmpty do
      let r ← reap
      if r == 0 then IO.sleep 10; continue
      let pid := (r >>> 32).toUInt32
      if let some id := live[pid]? then
        stdout.putStrLn s!"DONE {id} {(r &&& 0xffffffff).toUInt32}"
        stdout.flush
        live := live.erase pid
  else
    match line.splitOn "\t" with
    | [id, src, outdir, modName] =>
      let pid ← fork
      if pid == 0 then
        let rc ← (do
          if (← childSetup outdir src) != 0 then return (97 : UInt32)
          elabFile incr src (outdir ++ "/m.olean") modName.toName) <|> pure 98
        exitNow rc
      else
        serve incr stdout (live.insert pid id)
    | _ =>
      stdout.putStrLn s!"BAD {line}"
      stdout.flush
      serve incr stdout live

end FvFork

def main (args : List String) : IO UInt32 := do
  let some snapFile := args.head?
    | IO.eprintln "usage: fvfork SNAPFILE"; return 2
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution   -- the C++ `lean` main does this first (lean_enable_initializer_execution)
  let incr ← unsafe FvFork.loadIncrSnapshotSeq snapFile
  if let some res := incr.snap.processedResult.get then
    withImporting do
      unsafe Lean.runInitAttrsForModules res.cmdState.env incr.initModIdxs {}
  unsafe enableInitializersExecution   -- as runFrontend: `withImporting` resets the flag
  let stdout ← IO.getStdout
  stdout.putStrLn s!"READY {← FvFork.nthreads} sandbox=2"   -- fvserve uses only a server announcing the child sandbox
  stdout.flush
  FvFork.serve incr stdout {}
  return 0
