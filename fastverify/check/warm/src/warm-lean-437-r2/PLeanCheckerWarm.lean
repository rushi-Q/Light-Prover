/-
Persistent multi-query official-Lean-4.37.0-rc1-kernel replay leg (`pleanchecker-warm-437`, encapsulated replay via PCHK_HIDE_FILE).

Soundness (soundness rule S1(4), docs/concepts/soundness.md):
  1. Linked against the unmodified official Lean 4.36 kernel libraries (`PChk.replayPar` + `addDeclCore`).
  2. At startup (`--base B_PATH [--base-layer1 L1_PATH]`):
     - Parses B_PATH with unchanged trusted `PChk.parseExportFileP`.
     - VERIFIES EVERY CONSTANT OF B_PATH FROM SCRATCH using unchanged `PChk.replayPar` + quotient post-check.
       (If `--base-layer1 L1_PATH` is given: verifies L1 from scratch -> `layer1Env`, confirms every constant of L1
        matches B by `WarmBase.ciStrictEqual`, then replays B \ L1 on top -> `baseEnv`.)
     - Refuses to start (exits 1) if base verification fails!
     - Builds shared `WarmBase.BaseIndex` on B.
  3. On each `CHECK_DELTA <nonce> <delta_path>`:
     - Parses tiny `delta_path` with `FastExport.parseExportFile` (non-persistent -> freed after query, 0 leak).
     - Calls shared `WarmBase.computeOverlay base dmap`:
       - Any override/introduction/dirtying of `implicitNames` or `Quot.*` -> `"fallback"` (never accepts!).
       - Any unclosed safe constant -> `"reject"`; unclosed unsafe/partial -> `"fallback"`.
     - Case 1 (`plan.dirtySet.isEmpty`, pure extension): replays `plan.toCheck` directly on immutable `baseEnv`
       with unchanged `PChk.replayPar`.
     - Case 2 (`!plan.dirtySet.isEmpty`, edits/overrides): collects forward deps `need ⊆ K = B \ dirtySet` of
       `plan.toCheck` plus all `base.implicitSet` (and their forward deps in K); builds `envD` from `layer1Env`
       (when `dirtySet ∩ dom(layer1) = ∅`) or empty env + `PChk.envAdd` for non-Quot constants in `need` +
       `addDeclCore Declaration.quotDecl` (with quotient post-check against B) if `Quot` is needed; replays
       `plan.toCheck` on top of `envD` with unchanged `PChk.replayPar`.
  4. On `CHECK_FULL <nonce> <full_path>`: runs unchanged cold `PChk.replayPar` + quotient post-check from empty env.
  5. Outputs ONE structured JSON object per query on stdout (no log scraping; stack overflow -> `"decline"`).
-/
import Lean.CoreM
import Lean.Replay
import LeanExport.Parse
import PChk.Par
import FastParse
import PChk.PersistentRead
import WarmBase

open Lean

namespace PLeanCheckerWarm

@[extern "lean_internal_set_exit_on_panic"]
opaque setExitOnPanic (exit : Bool) : BaseIO Unit

def quotPostCheck (m : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) : Except String Unit := do
  for q in `Quot :: WarmBase.quotTargets do
    if let some info := m[q]? then
      let some info' := env.find? q
        | throw s!"Could not find quotient constant in final kernel env: {q}"
      if info != info' then
        throw s!"Quotient constant mismatch on: {q}"

/-- D23/S03 name parser (matches check/sound/src-437/Main.lean `parseHintName`). -/
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

structure EncapCfg where
  encapOn : Bool := false
  hide : NameSet := {}
  budgetMs : Nat := 600000
  liveMs : Nat := 0

def loadEncapCfg : IO EncapCfg := do
  let (encapOn, hide) ← match ← IO.getEnv "PCHK_HIDE_FILE" with
    | some f => do
      let txt ← (IO.FS.readFile f).catchExceptions fun _ => pure ""
      pure (true, txt.splitOn "\n" |>.foldl (init := ({} : NameSet)) fun acc l =>
        let l := l.trimAscii.toString
        if l.isEmpty then acc else acc.insert (parseHintName l))
    | none => pure (false, {})
  let envNat (v : String) (dflt : Nat) : IO Nat := do
    pure (((← IO.getEnv v).bind String.toNat?).getD dflt)
  let budgetMs ← envNat "PCHK_ENCAP_BUDGET_MS" 600000
  let liveMs ← envNat "PCHK_LIVE_MS" 0
  return { encapOn, hide, budgetMs, liveMs }

def replayFull (m : Std.HashMap Name ConstantInfo) (nthreads : Nat) (ecfg : EncapCfg) :
    IO (Except String (Kernel.Environment × Kernel.Environment)) := do
  let env ← Lean.mkEmptyEnvironment
  let kenv := env.toKernelEnv
  let kmap := WarmBase.quotTargets.foldl (init := m) (·.erase ·)
  try
    let (kenv', encapEnv') ← PChk.replayParEx kmap kenv nthreads false {} 0 ecfg.encapOn ecfg.hide ecfg.budgetMs ecfg.liveMs none
    match quotPostCheck m kenv' with
    | .ok () => return .ok (kenv', encapEnv')
    | .error e => return .error e
  catch e =>
    return .error (toString e)

def isStackOrResourceErr (msg : String) : Bool :=
  (msg.splitOn "Stack overflow").length > 1 ||
  (msg.splitOn "deep recursion").length > 1 ||
  (msg.splitOn "out of memory").length > 1 ||
  (msg.splitOn "bad_alloc").length > 1

def emitJson (nonce status msg : String) (deltaConsts overridden dirty eff replayed ms : Nat) : IO Unit := do
  IO.println s!"\{\"nonce\":{WarmBase.jsonEscape nonce},\"leg\":\"lean4\",\"status\":{WarmBase.jsonEscape status},\"delta_consts\":{deltaConsts},\"overridden\":{overridden},\"dirty\":{dirty},\"eff\":{eff},\"replayed\":{replayed},\"ms\":{ms},\"msg\":{WarmBase.jsonEscape msg}}"
  (← IO.getStdout).flush

unsafe def handleCheckDelta (base : WarmBase.BaseIndex)
    (baseEnv baseEncapEnv layer1Env layer1EncapEnv : Kernel.Environment)
    (layer1Set : NameSet) (implicitIds : Array Nat) (nthreads : Nat) (ecfg : EncapCfg)
    (nonce deltaPath : String) : IO Unit := do
  let q0 ← IO.monoMsNow
  let dEnv ←
    try FastExport.parseExportFile deltaPath
    catch e =>
      let em := toString e
      let st := if isStackOrResourceErr em || (em.splitOn "No such file").length > 1 || (em.splitOn "Permission denied").length > 1
                then "decline" else "reject"
      emitJson nonce st s!"parse error: {em}" 0 0 0 0 0 ((← IO.monoMsNow) - q0)
      return
  match WarmBase.computeOverlay base dEnv.constMap with
  | .error (.fallback why) =>
    emitJson nonce "fallback" why dEnv.constMap.size 0 0 0 0 ((← IO.monoMsNow) - q0)
  | .error (.reject why) =>
    emitJson nonce "reject" why dEnv.constMap.size 0 0 0 0 ((← IO.monoMsNow) - q0)
  | .ok plan =>
    let nCheck := plan.toCheck.size
    if nCheck == 0 then
      emitJson nonce "ok" "all delta constants match verified base" plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount 0 ((← IO.monoMsNow) - q0)
      return
    let nt := if nCheck <= 8 then 1 else min nthreads nCheck
    let kmap := WarmBase.quotTargets.foldl (init := plan.toCheck) (·.erase ·)
    if plan.dirtySet.isEmpty then
      -- Case 1: pure extension directly on top of immutable verified baseEnv
      try
        let _ ← PChk.replayPar kmap baseEnv nt false {} 0 ecfg.encapOn ecfg.hide ecfg.budgetMs ecfg.liveMs (if ecfg.encapOn then some baseEncapEnv else none)
        emitJson nonce "ok" "Lean default kernel accepts the delta" plan.deltaConsts plan.overriddenCount 0 plan.effectiveCount nCheck ((← IO.monoMsNow) - q0)
      catch e =>
        let em := toString e
        let st := if isStackOrResourceErr em then "decline" else "reject"
        emitJson nonce st em plan.deltaConsts plan.overriddenCount 0 plan.effectiveCount nCheck ((← IO.monoMsNow) - q0)
      return
    -- Case 2: edits/overrides -> build clean envD holding need ⊆ K = B \ dirtySet
    let mut seedIds : Array Nat := implicitIds
    for (_, ci) in plan.toCheck.toArray do
      for r in WarmBase.refsOf ci do
        if !plan.toCheck.contains r && !plan.dirtySet.contains r then
          if let some id := base.ids[r]? then
            seedIds := seedIds.push id
    let needIds := WarmBase.reachFwdClean base plan.dirtySet seedIds
    let useLayer1 := !layer1Set.isEmpty && !plan.dirtyIds.any (fun id => layer1Set.contains base.arr[id]!.1)
    let emptyKEnv := (← Lean.mkEmptyEnvironment).toKernelEnv
    let mut envD := if useLayer1 then layer1Env else emptyKEnv
    let mut encapEnvD := if useLayer1 then layer1EncapEnv else emptyKEnv
    let mut needQuot := false
    let mut missingClean : Option Name := none
    for id in needIds do
      let nm := base.arr[id]!.1
      if useLayer1 && layer1Set.contains nm then continue
      if WarmBase.quotNames.contains nm then
        needQuot := true
        continue
      match baseEnv.find? nm with
      | some ci =>
        envD := PChk.envAdd envD ci
        if ecfg.encapOn then
          encapEnvD := PChk.envAdd encapEnvD (PChk.encapRecord ecfg.hide ci)
      | none => missingClean := some nm; break
    if let some mnm := missingClean then
      emitJson nonce "fallback" s!"clean constant '{mnm}' missing from baseEnv" plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount 0 ((← IO.monoMsNow) - q0)
      return
    if needQuot && (envD.find? `Quot).isNone then
      match envD.addDeclCore 0 0 Declaration.quotDecl (cancelTk? := none) with
      | .ok e =>
        envD := e
        match quotPostCheck base.constMap envD with
        | .ok () => pure ()
        | .error qe =>
          emitJson nonce "fallback" qe plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount 0 ((← IO.monoMsNow) - q0)
          return
        if ecfg.encapOn && (encapEnvD.find? `Quot).isNone then
          match encapEnvD.addDeclCore 0 0 Declaration.quotDecl (cancelTk? := none) with
          | .ok ee => encapEnvD := ee
          | .error _ =>
            emitJson nonce "fallback" "quotDecl failed while building clean encapEnvD" plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount 0 ((← IO.monoMsNow) - q0)
            return
      | .error _ =>
        emitJson nonce "fallback" "quotDecl failed while building clean envD" plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount 0 ((← IO.monoMsNow) - q0)
        return
    try
      let _ ← PChk.replayPar kmap envD nt false {} 0 ecfg.encapOn ecfg.hide ecfg.budgetMs ecfg.liveMs (if ecfg.encapOn then some encapEnvD else none)
      emitJson nonce "ok" "Lean default kernel accepts the delta" plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount nCheck ((← IO.monoMsNow) - q0)
    catch e =>
      let em := toString e
      let st := if isStackOrResourceErr em then "decline" else "reject"
      emitJson nonce st em plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount nCheck ((← IO.monoMsNow) - q0)

unsafe def runServer (basePath : String) (layer1Path? : Option String) (nthreads : Nat) : IO UInt32 := do
  setExitOnPanic true
  let t0 ← IO.monoMsNow
  let baseExport ← PChk.parseExportFileP basePath
  let base ← WarmBase.buildBaseIndex baseExport.constMap nthreads
  if !base.isClosed then
    IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":\"base export is not closed\"}"
    (← IO.getStdout).flush
    return 1
  let ecfg ← loadEncapCfg
  -- Verify base from scratch (optionally via verified layer1 checkpoint)
  let mut layer1Set : NameSet := {}
  let mut layer1Env := (← Lean.mkEmptyEnvironment).toKernelEnv
  let mut layer1EncapEnv := layer1Env
  let mut baseEnv := (← Lean.mkEmptyEnvironment).toKernelEnv
  let mut baseEncapEnv := baseEnv
  match layer1Path? with
  | some l1p =>
    let l1Export ← PChk.parseExportFileP l1p
    -- Check L1 ⊆ B with strict equality
    for (n, ci) in l1Export.constMap.toArray do
      match base.constMap[n]? with
      | some bci =>
        if !WarmBase.ciStrictEqual ci bci then
          IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"layer1 constant '{n}' differs from base"}}"
          (← IO.getStdout).flush
          return 1
      | none =>
        IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"layer1 constant '{n}' missing from base"}}"
        (← IO.getStdout).flush
        return 1
    match ← replayFull l1Export.constMap nthreads ecfg with
    | .error e =>
      IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"layer1 verification failed: {e}"}}"
      (← IO.getStdout).flush
      return 1
    | .ok (l1e, l1ee) =>
      layer1Env := l1e
      layer1EncapEnv := l1ee
      for (n, _) in l1Export.constMap.toArray do
        layer1Set := layer1Set.insert n
      -- Replay remaining B \ L1 on top of verified layer1Env
      let mut rest : Std.HashMap Name ConstantInfo := {}
      for (n, ci) in base.arr do
        if !layer1Set.contains n then
          rest := rest.insert n ci
      let restMap := WarmBase.quotTargets.foldl (init := rest) (·.erase ·)
      try
        let (be, bee) ← PChk.replayParEx restMap layer1Env nthreads false {} 0 ecfg.encapOn ecfg.hide ecfg.budgetMs ecfg.liveMs (if ecfg.encapOn then some layer1EncapEnv else none)
        baseEnv := be
        baseEncapEnv := bee
        match quotPostCheck base.constMap baseEnv with
        | .error e =>
          IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape e}}"
          (← IO.getStdout).flush
          return 1
        | .ok () => pure ()
      catch e =>
        IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"base replay on layer1 failed: {e}"}}"
        (← IO.getStdout).flush
        return 1
  | none =>
    match ← replayFull base.constMap nthreads ecfg with
    | .error e =>
      IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"base verification failed: {e}"}}"
      (← IO.getStdout).flush
      return 1
    | .ok (be, bee) =>
      baseEnv := be
      baseEncapEnv := bee
  -- Precompute implicit seed ids in base
  let mut implicitIds : Array Nat := #[]
  for p in WarmBase.implicitNames do
    if let some id := base.ids[p]? then
      implicitIds := implicitIds.push id
  let readyMs := (← IO.monoMsNow) - t0
  IO.println s!"\{\"ready\":true,\"leg\":\"lean4\",\"base_consts\":{base.arr.size},\"layer1_consts\":{layer1Set.size},\"encap\":{if ecfg.encapOn then "true" else "false"},\"hide_count\":{ecfg.hide.size},\"ms\":{readyMs}}"
  (← IO.getStdout).flush
  let stdin ← IO.getStdin
  repeat
    let raw ← stdin.getLine
    if raw.isEmpty then break
    let line := raw.trimAscii.toString
    if line.isEmpty then continue
    if line == "QUIT" then break
    let parts := line.splitOn "\t"
    match parts with
    | ["CHECK_DELTA", nonce, deltaPath] =>
      handleCheckDelta base baseEnv baseEncapEnv layer1Env layer1EncapEnv layer1Set implicitIds nthreads ecfg nonce deltaPath
    | ["CHECK_FULL", nonce, fullPath] =>
      let q0 ← IO.monoMsNow
      try
        let fullEnv ← FastExport.parseExportFile fullPath
        match ← replayFull fullEnv.constMap nthreads ecfg with
        | .ok _ =>
          emitJson nonce "ok" "Lean default kernel accepts the solution" fullEnv.constMap.size 0 0 fullEnv.constMap.size fullEnv.constMap.size ((← IO.monoMsNow) - q0)
        | .error em =>
          let st := if isStackOrResourceErr em then "decline" else "reject"
          emitJson nonce st em fullEnv.constMap.size 0 0 fullEnv.constMap.size fullEnv.constMap.size ((← IO.monoMsNow) - q0)
      catch e =>
        let em := toString e
        let st := if isStackOrResourceErr em || (em.splitOn "No such file").length > 1 || (em.splitOn "Permission denied").length > 1
                  then "decline" else "reject"
        emitJson nonce st s!"full parse/check error: {em}" 0 0 0 0 0 ((← IO.monoMsNow) - q0)
    | _ =>
      emitJson "unknown" "error" "unknown command" 0 0 0 0 0 0
  return 0

end PLeanCheckerWarm

unsafe def main (args : List String) : IO UInt32 := do
  let mut base := ""
  let mut layer1? : Option String := none
  let mut nthreads := 16
  let mut i := 0
  let arr := args.toArray
  while i < arr.size do
    match arr[i]! with
    | "--base" =>
      if i + 1 < arr.size then base := arr[i + 1]!; i := i + 2 else return 2
    | "--base-layer1" =>
      if i + 1 < arr.size then layer1? := some arr[i + 1]!; i := i + 2 else return 2
    | s =>
      if let some rest := s.dropPrefix? "-j" then
        nthreads := rest.toString.toNat?.getD nthreads
        i := i + 1
      else
        IO.eprintln s!"pleanchecker-warm: unknown argument '{s}'"
        return 2
  if base.isEmpty then
    IO.eprintln "usage: pleanchecker-warm --base BASE_EXPORT [--base-layer1 LAYER1_EXPORT] [-jN]"
    return 2
  PLeanCheckerWarm.runServer base layer1? nthreads
