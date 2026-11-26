/-
Persistent multi-query official-Lean-4.36-kernel replay leg (`pleanchecker-warm`).

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
Veto-only checks (every check only adds failures):
  C1 (Lean #16489): `PChk.checkInductNoLooseBVars` on every map handed to `PChk.replayPar` (base, layer1, B \ L1, CHECK_FULL,
     both delta cases): no inductive block with a loose bound variable in an inductive or constructor type reaches the kernel.
  C2 (export-record check, Lean #15100/#15101): `PChk.replayPar` compares every record of the map it replays with the final environment
     (PChk/Par.lean); in addition (a) at startup D23-H of ALL of B against `baseEnv` (the layer1 split replays B in two maps),
     (b) Case 2: a delta record that is not dirty, under the name of a constant an UNCHANGED base inductive block generated,
     must equal that constant (`r9CheckCleanGenerated`), (c) both cases: a clean base record under the name of a constant the
     kernel generated for one of the delta's inductive blocks must equal it (`r9CheckDeltaGenerated`). Together: every record
     of E_eff whose name is a constant of the environment the delta was accepted in (K's part of baseEnv + the replayed
     delta) equals that constant, the condition D23-H establishes for the cold replay of E_eff.
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

/-- C2: the base inductive block that generated `c` (a type / constructor / recursor), if one of its types is a CLEAN
base constant (in B and not dirty). -/
def r9CleanOwner (base : WarmBase.BaseIndex) (dirty : NameSet) (c : ConstantInfo) : Option Name :=
  let owners : List Name := match c with
    | .ctorInfo v => [v.induct]
    | .recInfo v => v.all
    | .inductInfo v => v.all
    | _ => []
  owners.find? (fun o => base.ids.contains o && !dirty.contains o)

/-- C2 (b), Case 2 (VETO ONLY): the replay of the delta runs in `envD`, which holds only the clean constants the delta
needs, so a delta record under the name of a constant that an UNCHANGED (clean) base inductive block generated - e.g. `T.rec`
when B did not export it - is never compared with it, although the cold replay of E_eff generates it from that block. Such a
record must equal the generated constant (in `baseEnv`; a dirty record is re-checked with its whole block, never here). -/
def r9CheckCleanGenerated (base : WarmBase.BaseIndex) (baseEnv : Kernel.Environment) (dirty : NameSet)
    (kmap : Std.HashMap Name ConstantInfo) : Except String Unit := do
  for (n, ci) in kmap do
    if dirty.contains n then continue
    if let some c := baseEnv.find? n then
      if let some o := r9CleanOwner base dirty c then
        if !(c == ci) then
          throw s!"Export record of {n} differs from the kernel's constant (generated by the unchanged base inductive block of {o})"

/-- C2 (c), both cases (VETO ONLY): the kernel generated, for each inductive block of the delta, its types, their
constructors, `T.rec` and the auxiliary recursors `<main>.rec_<i>` of nested blocks (kernel `inductive.cpp`
`mk_rec_name`, `mk_aux_rec_name_map`; the candidates below are a superset). A CLEAN base record under such a name (part of
E_eff, not replayed with the delta: e.g. an unsafe record of B the base replay skipped, or a record the clean environment
did not need) must equal the generated constant; the delta's own records are compared by `replayPar`'s D23-H. -/
def r9CheckDeltaGenerated (base : WarmBase.BaseIndex) (dirty : NameSet) (kmap : Std.HashMap Name ConstantInfo)
    (envAfter : Kernel.Environment) : Except String Unit := do
  for (_, ci) in kmap do
    if let .inductInfo v := ci then
      for t in v.all do
        let mut cands : Array Name := #[t, Name.str t "rec"]
        if let some (.inductInfo tv) := envAfter.find? t then
          for c in tv.ctors do cands := cands.push c
          for i in [1:tv.numNested + 1] do cands := cands.push (Name.str t s!"rec_{i}")
        for g in cands do
          if kmap.contains g || dirty.contains g then continue
          if let some bi := base.ids[g]? then
            if let some c := envAfter.find? g then
              if !(c == base.arr[bi]!.2) then
                throw s!"Export record of {g} differs from the kernel's constant (generated for the delta's inductive block of {t})"

def replayFull (m : Std.HashMap Name ConstantInfo) (nthreads : Nat) : IO (Except String Kernel.Environment) := do
  let env ← Lean.mkEmptyEnvironment
  let kenv := env.toKernelEnv
  let kmap := WarmBase.quotTargets.foldl (init := m) (·.erase ·)
  try
    PChk.checkInductNoLooseBVars kmap   -- C1 (veto only)
    let kenv' ← PChk.replayPar kmap kenv nthreads false {} 0   -- (C2 = the record check inside replayPar)
    match quotPostCheck m kenv' with
    | .ok () => return .ok kenv'
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

unsafe def handleCheckDelta (base : WarmBase.BaseIndex) (baseEnv layer1Env : Kernel.Environment)
    (layer1Set : NameSet) (implicitIds : Array Nat) (nthreads : Nat)
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
        PChk.checkInductNoLooseBVars kmap   -- C1 (veto only)
        let env' ← PChk.replayPar kmap baseEnv nt false {} 0   -- (C2 = the record check on the delta's records inside replayPar)
        if let .error e := r9CheckDeltaGenerated base plan.dirtySet kmap env' then throw (IO.userError e)   -- C2 (c)
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
    let mut needQuot := false
    let mut missingClean : Option Name := none
    for id in needIds do
      let nm := base.arr[id]!.1
      if useLayer1 && layer1Set.contains nm then continue
      if WarmBase.quotNames.contains nm then
        needQuot := true
        continue
      match baseEnv.find? nm with
      | some ci => envD := PChk.envAdd envD ci
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
      | .error _ =>
        emitJson nonce "fallback" "quotDecl failed while building clean envD" plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount 0 ((← IO.monoMsNow) - q0)
        return
    try
      PChk.checkInductNoLooseBVars kmap   -- C1 (veto only)
      if let .error e := r9CheckCleanGenerated base baseEnv plan.dirtySet kmap then throw (IO.userError e)   -- C2 (b)
      let envD' ← PChk.replayPar kmap envD nt false {} 0   -- (C2 = the record check on the delta's records inside replayPar)
      if let .error e := r9CheckDeltaGenerated base plan.dirtySet kmap envD' then throw (IO.userError e)   -- C2 (c)
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
  -- Verify base from scratch (optionally via verified layer1 checkpoint)
  let mut layer1Set : NameSet := {}
  let mut layer1Env := (← Lean.mkEmptyEnvironment).toKernelEnv
  let mut baseEnv := (← Lean.mkEmptyEnvironment).toKernelEnv
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
    match ← replayFull l1Export.constMap nthreads with
    | .error e =>
      IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"layer1 verification failed: {e}"}}"
      (← IO.getStdout).flush
      return 1
    | .ok l1e =>
      layer1Env := l1e
      for (n, _) in l1Export.constMap.toArray do
        layer1Set := layer1Set.insert n
      -- Replay remaining B \ L1 on top of verified layer1Env
      let mut rest : Std.HashMap Name ConstantInfo := {}
      for (n, ci) in base.arr do
        if !layer1Set.contains n then
          rest := rest.insert n ci
      let restMap := WarmBase.quotTargets.foldl (init := rest) (·.erase ·)
      try
        PChk.checkInductNoLooseBVars restMap   -- C1 (veto only)
        baseEnv ← PChk.replayPar restMap layer1Env nthreads false {} 0
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
    match ← replayFull base.constMap nthreads with
    | .error e =>
      IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"base verification failed: {e}"}}"
      (← IO.getStdout).flush
      return 1
    | .ok be => baseEnv := be
  -- C2 (a): the record check of ALL of B against the verified base environment (with --base-layer1 B is replayed as two maps, each
  -- compared by replayPar only with its own records); refuse to start on a mismatch, like any other base verification failure
  try PChk.checkExportRecords (WarmBase.quotTargets.foldl (init := base.constMap) (·.erase ·)) baseEnv
  catch e =>
    IO.println s!"\{\"ready\":false,\"leg\":\"lean4\",\"error\":{WarmBase.jsonEscape s!"base verification failed: {e}"}}"
    (← IO.getStdout).flush
    return 1
  -- Precompute implicit seed ids in base
  let mut implicitIds : Array Nat := #[]
  for p in WarmBase.implicitNames do
    if let some id := base.ids[p]? then
      implicitIds := implicitIds.push id
  let readyMs := (← IO.monoMsNow) - t0
  IO.println s!"\{\"ready\":true,\"leg\":\"lean4\",\"base_consts\":{base.arr.size},\"layer1_consts\":{layer1Set.size},\"ms\":{readyMs}}"
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
      handleCheckDelta base baseEnv layer1Env layer1Set implicitIds nthreads nonce deltaPath
    | ["CHECK_FULL", nonce, fullPath] =>
      let q0 ← IO.monoMsNow
      try
        let fullEnv ← FastExport.parseExportFile fullPath
        match ← replayFull fullEnv.constMap nthreads with
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
