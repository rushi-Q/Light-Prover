/-
Persistent multi-query statement + axiom judge (`ccmp-warm`) built on the official
Lean 4.36 comparator code (`Lake.Check.compareAt`, `Lake.Check.runForUsedConsts`, `FastParse`, `ParAxioms`).

Soundness (docs/concepts/soundness.md):
  1. Loads pinned official challenge export C and base export B once into persistent memory.
  2. Precomputes exact reverse-BFS axiom reachability (`baseAxMask`/`baseAxExtra`) and missing-ref
     reachability (`baseMissing`) on B using the EXACT official `Lake.Check.runForUsedConsts` edges.
  3. For each query `CHECK_DELTA NONCE DELTA_PATH CFG_PATH`:
     - Parses tiny DELTA_PATH with unchanged trusted `FastExport.parseExportFile` (non-persistent -> freed).
     - Calls shared `WarmBase.computeOverlay base dmap` -> gets `dirtySet` (reverse-closed under `refsOf`
       and atomic inductive blocks; fails closed to `fallback` if any implicit/Quot constant is touched).
     - Statement check: materializes `solSlice` for ONLY the names reachable in C from
       `primitiveTargets ++ theoremNames ++ legalAxioms ++ definitionNames` using `WarmBase.lookupEff`,
       and calls the LITERAL UNMODIFIED `Lake.Check.compareAt C { constMap := solSlice } ...`.
       Since `Lake.Check.compareAt` ALWAYS looks up `challenge.constMap[n]?` before `solution.constMap[n]?`,
       the result is mathematically identical to `compareAt C E_eff`.
     - Axiom check: checks target existence/kind in `E_eff`, then BFSes `dmap` using `runForUsedConsts`.
       At every boundary constant `k in K = B \ dirtySet`, because `K` is downward-closed under `refsOf >=
       runForUsedConsts`, `k`'s exact transitive axioms and missing-ref status in `E_eff` equal its
       precomputed values in B (O(1) lookup!).
  4. Also supports `CHECK_FULL` (cold full-export path via official `compareAt` + `ParAxioms.checkAxiomsPar`).
     Conditional frontier mode uses the zero-new-TCB axiom-rewrite + frontier-challenge C'
     construction (no inertness rule in the TCB!).
  5. Outputs ONE structured JSON object per query on stdout (no log scraping).
-/
import Lean.Declaration
import Lean.Data.Json.FromToJson
import LeanExport.Parse
import Lake.Check.Compare
import Lake.Check.Axioms
import Lake.Check.Util
import FastParse
import ParAxioms
import PChk.PersistentRead
import WarmBase

open Lean

namespace CCmpWarm

/-- Exact comparator `primitiveTargets` from Lean 4.36 `Lake/CLI/Check.lean` (CCmp.lean:478-511). -/
def primitiveTargets : Array Name := #[
  `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod,
  `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight,
  `String.ofList, `Char.ofNat, `List, `eagerReduce,
  `Nat, `String, `String.mk, `Char,
  `optParam, `autoParam, `semiOutParam, `outParam
]

structure QueryConfig where
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  deriving FromJson

/-- Precomputed exact `Lake.Check.runForUsedConsts` axiom + missing reachability on base B. -/
structure BaseAxiomIndex where
  /-- Exact list of axiom names appearing in B (index -> Name). -/
  axiomNames : Array Name
  /-- Bitmask of reachable axioms (indices < 64) for each constant `i` in B. -/
  axMask : Array UInt64
  /-- Overflow axiom indices (>= 64) per constant `i` (empty in all normal bases). -/
  axOverflow : Std.HashMap Nat (Array Nat)
  /-- 1 iff `i` transitively reaches a missing constant under `runForUsedConsts` in B. -/
  reachMissing : ByteArray
  /-- Exact `runForUsedConsts` direct used names (as dense ids) for diagnostics. -/
  usedIds : Array (Array Nat)

/-- Collect `Lake.Check.runForUsedConsts` names into an array. -/
def usedConstsOf (ci : ConstantInfo) : Array Name :=
  ((Lake.Check.runForUsedConsts (m := StateM (Array Name)) ci fun n => modify (·.push n)).run #[]).2

/-- Precompute exact axiom & missing-ref reachability over `B` in O((|Ax|+1) * (V+E)). -/
def buildBaseAxiomIndex (base : WarmBase.BaseIndex) (nthreads : Nat) : IO BaseAxiomIndex := do
  let n := base.arr.size
  -- Extract exact `runForUsedConsts` edges and direct missing flags in parallel
  let parts ← WarmBase.parChunks n nthreads fun lo hi => Id.run do
    let mut ds := Array.mkEmpty (hi - lo)
    let mut ms := Array.mkEmpty (hi - lo)
    for i in [lo:hi] do
      let u := usedConstsOf base.arr[i]!.2
      let mut arr : Array Nat := #[]
      let mut miss := false
      for nm in u do
        match base.ids[nm]? with
        | some j => arr := arr.push j
        | none => miss := true
      ds := ds.push arr
      ms := ms.push miss
    return (ds, ms)
  let mut usedIds : Array (Array Nat) := Array.mkEmpty n
  let mut missSeeds : Array Nat := #[]
  for (ds, ms) in parts do
    for k in [0:ds.size] do
      let idx := usedIds.size
      usedIds := usedIds.push ds[k]!
      if ms[k]! then missSeeds := missSeeds.push idx
  -- CSR reverse graph specifically for `runForUsedConsts`
  let mut revStart : Array Nat := Array.replicate (n + 1) 0
  for d in usedIds do
    for j in d do revStart := revStart.set! (j + 1) (revStart[j + 1]! + 1)
  for i in [0:n] do revStart := revStart.set! (i + 1) (revStart[i + 1]! + revStart[i]!)
  let mut fill := revStart
  let mut revAdj : Array Nat := Array.replicate revStart[n]! 0
  for i in [0:n] do
    for j in usedIds[i]! do
      revAdj := revAdj.set! fill[j]! i
      fill := fill.set! j (fill[j]! + 1)
  -- Reverse BFS helper on `usedIds`
  let revBfs (seeds : Array Nat) : ByteArray := Id.run do
    let mut seen := ByteArray.mk (Array.replicate n 0)
    let mut st := seeds
    for s in seeds do seen := seen.set! s 1
    while !st.isEmpty do
      let j := st.back!
      st := st.pop
      for k in [revStart[j]!:revStart[j + 1]!] do
        let u := revAdj[k]!
        if seen.get! u == 0 then
          seen := seen.set! u 1
          st := st.push u
    return seen
  let reachMissing := if missSeeds.isEmpty then ByteArray.mk (Array.replicate n 0) else revBfs missSeeds
  -- Collect all axioms in B
  let mut axiomNames : Array Name := #[]
  let mut axiomIds : Array Nat := #[]
  for h : i in [0:n] do
    if let .axiomInfo info := base.arr[i].2 then
      axiomNames := axiomNames.push info.name
      axiomIds := axiomIds.push i
  let mut axMask : Array UInt64 := Array.replicate n 0
  let mut axOverflow : Std.HashMap Nat (Array Nat) := {}
  for h : aIdx in [0:axiomIds.size] do
    let reached := revBfs #[axiomIds[aIdx]]
    if aIdx < 64 then
      let bit : UInt64 := (1 : UInt64) <<< aIdx.toUInt64
      for i in [0:n] do
        if reached.get! i != 0 then
          axMask := axMask.set! i (axMask[i]! ||| bit)
    else
      for i in [0:n] do
        if reached.get! i != 0 then
          let cur := (axOverflow[i]?).getD #[]
          axOverflow := axOverflow.insert i (cur.push aIdx)
  return { axiomNames, axMask, axOverflow, reachMissing, usedIds }

/-- Exact per-constant target check matching `Lake.Check.compareAt` lines 71-86. -/
def checkThmOrAxTarget (chalCi : ConstantInfo) (solCi? : Option ConstantInfo) (target : Name) : Except String Unit := do
  let some solCi := solCi? | throw s!"Const not found in solution: '{target}'"
  let (cc, sc) ←
    match chalCi, solCi with
    | .thmInfo cc, .thmInfo sc
    | .axiomInfo cc, .axiomInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
    | _, _ => throw s!"Challenge and solution constant kind don't match: '{target}'"
  if cc != sc then
    throw s!"Challenge and solution theorem statement do not match: '{target}'"

/-- Exact per-constant definition hole check matching `Lake.Check.compareAt` lines 89-103. -/
def checkDefHoleTarget (chalCi : ConstantInfo) (solCi? : Option ConstantInfo) (target : Name) : Except String Unit := do
  let some solCi := solCi? | throw s!"Const not found in solution: '{target}'"
  let .defnInfo cc := chalCi | throw s!"Challenge constant is not a definition: '{target}'"
  let .defnInfo sc := solCi | throw s!"Solution constant is not a definition: '{target}'"
  unless cc.value.getLambdaBody.isAppOf ``sorryAx do
    throw s!"Challenge definition is not sorried: '{target}'"
  if !Lake.Check.definitionHoleMatches cc sc then
    throw s!"Const does not match between challenge and target '{target}'"

/-- Precomputed per-(targets, defs) comparison slice on `(chalEnv, base)` making `compareDelta`
O(|dmap| + |dirty| + |badBase|) per query while remaining 100% mathematically identical to
`Lake.Check.compareAt C E_eff targets defs primitiveTargets` (the overlay construction above). -/
structure CompareCache where
  chalErr? : Option String
  thmSet : NameSet
  defSet : NameSet
  nonTargetSet : NameSet
  badBaseThms : Array Name
  badBaseDefs : Array Name
  badBaseNonTargets : Array Name

def buildCompareCache (challenge : LeanExport.ExportedEnv) (base : WarmBase.BaseIndex)
    (theoremTargets definitionTargets : Array Name) : CompareCache := Id.run do
  let thmSet := theoremTargets.foldl (init := ({} : NameSet)) (·.insert ·)
  let defSet := definitionTargets.foldl (init := ({} : NameSet)) (·.insert ·)
  let mut worklist := primitiveTargets
  let mut badBaseThms : Array Name := #[]
  let mut badBaseDefs : Array Name := #[]
  let mut badBaseNonTargets : Array Name := #[]
  -- Step 1: validate theoremTargets in challenge & pre-check against base
  for t in theoremTargets do
    let some cc := challenge.constMap[t]?
      | return { chalErr? := some s!"Const not found in challenge: '{t}'", thmSet, defSet, nonTargetSet := {}, badBaseThms, badBaseDefs, badBaseNonTargets }
    match checkThmOrAxTarget cc base.constMap[t]? t with
    | .ok () => pure ()
    | .error _ => badBaseThms := badBaseThms.push t
    worklist := worklist ++ cc.type.getUsedConstants
  -- Step 2: validate definitionTargets in challenge & pre-check against base
  for d in definitionTargets do
    let some cc := challenge.constMap[d]?
      | return { chalErr? := some s!"Const not found in challenge: '{d}'", thmSet, defSet, nonTargetSet := {}, badBaseThms, badBaseDefs, badBaseNonTargets }
    match checkDefHoleTarget cc base.constMap[d]? d with
    | .ok () => pure ()
    | .error _ => badBaseDefs := badBaseDefs.push d
    worklist := worklist.push d
  -- Step 3: BFS challenge slice (identical to `Lake.Check.Compare.loop`) & pre-check non-targets against base
  let mut seen : NameSet := {}
  let mut nonTargetSet : NameSet := {}
  while !worklist.isEmpty do
    let nm := worklist.back!
    worklist := worklist.pop
    if seen.contains nm then continue
    seen := seen.insert nm
    let some chalCi := challenge.constMap[nm]?
      | return { chalErr? := some s!"Const not found in challenge '{nm}'", thmSet, defSet, nonTargetSet, badBaseThms, badBaseDefs, badBaseNonTargets }
    if defSet.contains nm || thmSet.contains nm then
      for u in chalCi.type.getUsedConstants do
        if !seen.contains u then worklist := worklist.push u
    else
      nonTargetSet := nonTargetSet.insert nm
      match base.constMap[nm]? with
      | some bci =>
        if chalCi != bci then
          badBaseNonTargets := badBaseNonTargets.push nm
      | none =>
        badBaseNonTargets := badBaseNonTargets.push nm
      for u in usedConstsOf chalCi do
        if !seen.contains u then worklist := worklist.push u
  return { chalErr? := none, thmSet, defSet, nonTargetSet, badBaseThms, badBaseDefs, badBaseNonTargets }

/-- Exact O(|dmap| + |dirty| + |badBase|) statement comparison on `E_eff = (B \ dirtySet) U dmap`.
Every constant in the challenge slice NOT in `dmap U dirtySet` resolves to `base[nm]`, which was
already verified against `challenge[nm]` when `cache` was constructed (any mismatch is in `badBase*`). -/
def compareDeltaCached (challenge : LeanExport.ExportedEnv) (base : WarmBase.BaseIndex)
    (cache : CompareCache) (dmap : Std.HashMap Name ConstantInfo) (dirtySet : NameSet) : Except String Unit := do
  if let some e := cache.chalErr? then
    throw e
  -- 1. Check all pre-existing mismatches in base (must be fixed by delta)
  for t in cache.badBaseThms do
    let some chalCi := challenge.constMap[t]? | throw s!"Const not found in challenge: '{t}'"
    checkThmOrAxTarget chalCi (WarmBase.lookupEff base dmap dirtySet t) t
  for d in cache.badBaseDefs do
    let some chalCi := challenge.constMap[d]? | throw s!"Const not found in challenge: '{d}'"
    checkDefHoleTarget chalCi (WarmBase.lookupEff base dmap dirtySet d) d
  for nm in cache.badBaseNonTargets do
    let some chalCi := challenge.constMap[nm]? | throw s!"Const not found in challenge '{nm}'"
    let some solCi := WarmBase.lookupEff base dmap dirtySet nm | throw s!"Const not found in solution '{nm}'"
    if chalCi != solCi then
      throw s!"Const does not match between challenge and target '{nm}'"
  -- 2. Check every constant touched by delta or dirtied by base overrides
  let checkTouched (nm : Name) : Except String Unit := do
    if cache.thmSet.contains nm then
      let some chalCi := challenge.constMap[nm]? | throw s!"Const not found in challenge: '{nm}'"
      checkThmOrAxTarget chalCi (WarmBase.lookupEff base dmap dirtySet nm) nm
    if cache.defSet.contains nm then
      let some chalCi := challenge.constMap[nm]? | throw s!"Const not found in challenge: '{nm}'"
      checkDefHoleTarget chalCi (WarmBase.lookupEff base dmap dirtySet nm) nm
    if cache.nonTargetSet.contains nm then
      let some chalCi := challenge.constMap[nm]? | throw s!"Const not found in challenge '{nm}'"
      let some solCi := WarmBase.lookupEff base dmap dirtySet nm | throw s!"Const not found in solution '{nm}'"
      if chalCi != solCi then
        throw s!"Const does not match between challenge and target '{nm}'"
  for (nm, _) in dmap.toArray do
    checkTouched nm
  for nm in dirtySet do
    checkTouched nm
  return ()

/-- Find the exact missing constant name reachable from base id `startId` (diagnostic only, rare). -/
def findMissingInBase (base : WarmBase.BaseIndex) (startId : Nat) : Name := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut st : Array Nat := #[startId]
  while !st.isEmpty do
    let i := st.back!
    st := st.pop
    if seen.contains i then continue
    seen := seen.insert i
    for nm in usedConstsOf base.arr[i]!.2 do
      match base.ids[nm]? with
      | some j => if !seen.contains j then st := st.push j
      | none => return nm
  return .anonymous

/-- Exact axiom check on `E_eff = (B \ dirtySet) U dmap`, mathematically identical to `Lake.Check.checkAxioms`.
Visits `dmap` directly and uses O(1) precomputed `BaseAxiomIndex` at every clean boundary node `k in K`. -/
def checkAxiomsDelta (base : WarmBase.BaseIndex) (axIdx : BaseAxiomIndex)
    (dmap : Std.HashMap Name ConstantInfo) (dirtySet : NameSet)
    (theoremTargets definitionTargets legalAxioms : Array Name) : Except String Unit := do
  let mut worklist : Array Name := #[]
  for target in theoremTargets do
    let some ci := WarmBase.lookupEff base dmap dirtySet target
      | throw s!"Const not found in solution: '{target}'"
    let .thmInfo thm := ci
      | throw s!"Solution constant is not a theorem: '{target}'"
    worklist := worklist.push thm.name
  for target in definitionTargets do
    let some ci := WarmBase.lookupEff base dmap dirtySet target
      | throw s!"Const not found in solution: '{target}'"
    let .defnInfo defn := ci
      | throw s!"Solution constant is not a definition: '{target}'"
    worklist := worklist.push defn.name
  let legalSet := Std.HashSet.ofArray legalAxioms
  -- Precompute bitmask of ILLEGAL base axioms (indices < 64)
  let mut illegalMask : UInt64 := 0
  let nAx := axIdx.axiomNames.size
  for aIdx in [0:min nAx 64] do
    if !legalSet.contains axIdx.axiomNames[aIdx]! then
      illegalMask := illegalMask ||| ((1 : UInt64) <<< aIdx.toUInt64)
  let mut checked : Std.HashSet Name := {}
  while !worklist.isEmpty do
    let target := worklist.back!
    worklist := worklist.pop
    if checked.contains target then continue
    checked := checked.insert target
    match dmap[target]? with
    | some ci =>
      -- Validate constant in delta and traverse its `runForUsedConsts`
      for u in usedConstsOf ci do
        let some uci := WarmBase.lookupEff base dmap dirtySet u
          | throw s!"Constant not found in solution '{u}'"
        if let .axiomInfo ainfo := uci then
          if !legalSet.contains ainfo.name then
            throw s!"Illegal axiom detected: '{u}'"
        if !checked.contains u then
          worklist := worklist.push u
    | none =>
      if dirtySet.contains target then
        throw s!"Constant not found in solution '{target}'"
      let some i := base.ids[target]?
        | throw s!"Constant not found in solution '{target}'"
      -- Clean boundary constant in K = B \ dirtySet: all transitive deps are in K!
      if axIdx.reachMissing.get! i != 0 then
        let mnm := findMissingInBase base i
        throw s!"Constant not found in solution '{mnm}'"
      let badBits := axIdx.axMask[i]! &&& illegalMask
      if badBits != 0 then
        -- Find first illegal axiom name
        for aIdx in [0:min nAx 64] do
          if (badBits &&& ((1 : UInt64) <<< aIdx.toUInt64)) != 0 then
            throw s!"Illegal axiom detected: '{axIdx.axiomNames[aIdx]!}'"
      if let some ov := axIdx.axOverflow[i]? then
        for aIdx in ov do
          let anm := axIdx.axiomNames[aIdx]!
          if !legalSet.contains anm then
            throw s!"Illegal axiom detected: '{anm}'"
  return ()

def parseConfig (cfgPath : String) : IO (Except String (Array Name × Array Name × Array Name)) := do
  try
    let contents ← IO.FS.readFile cfgPath
    match Json.parse contents >>= fromJson? (α := QueryConfig) with
    | .error e => return .error s!"malformed config: {e}"
    | .ok cfg =>
      let thms := cfg.theorem_names.map String.toName
      let defs := (cfg.definition_names.getD #[]).map String.toName
      let axs := cfg.permitted_axioms.map String.toName
      if thms.isEmpty && defs.isEmpty then
        return .error "config names no theorems or definitions"
      return .ok (thms, defs, axs)
  catch e =>
    return .error s!"cannot read config: {e}"

def emitJson (nonce status msg : String) (deltaConsts overridden dirty eff ms : Nat) : IO Unit := do
  IO.println s!"\{\"nonce\":{WarmBase.jsonEscape nonce},\"leg\":\"ccmp\",\"status\":{WarmBase.jsonEscape status},\"delta_consts\":{deltaConsts},\"overridden\":{overridden},\"dirty\":{dirty},\"eff\":{eff},\"ms\":{ms},\"msg\":{WarmBase.jsonEscape msg}}"
  (← IO.getStdout).flush

def runServer (chalPath basePath : String) (nthreads : Nat) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  -- Parse challenge & base concurrently (persistent once for daemon lifetime)
  let ct ← IO.asTask (prio := .dedicated) (unsafe PChk.parseExportFileP chalPath)
  let baseEnv ← unsafe PChk.parseExportFileP basePath
  let chalEnv ← IO.ofExcept (← IO.wait ct)
  let base ← WarmBase.buildBaseIndex baseEnv.constMap nthreads
  let axIdx ← buildBaseAxiomIndex base nthreads
  let readyMs := (← IO.monoMsNow) - t0
  IO.println s!"\{\"ready\":true,\"leg\":\"ccmp\",\"challenge_consts\":{chalEnv.constMap.size},\"base_consts\":{base.arr.size},\"base_axioms\":{axIdx.axiomNames.size},\"base_closed\":{base.isClosed},\"ms\":{readyMs}}"
  (← IO.getStdout).flush
  -- Bounded LRU-like cache of `CompareCache` keyed by (targets, defs) string (typically 1 entry for repo daemons!)
  let mut cmpCaches : Std.HashMap String CompareCache := {}
  let stdin ← IO.getStdin
  repeat
    let raw ← stdin.getLine
    if raw.isEmpty then break
    let line := raw.trimAscii.toString
    if line.isEmpty then continue
    if line == "QUIT" then break
    let parts := line.splitOn "\t"
    match parts with
    | ["CHECK_DELTA", nonce, deltaPath, cfgPath] =>
      let q0 ← IO.monoMsNow
      match ← parseConfig cfgPath with
      | .error e => emitJson nonce "error" e 0 0 0 0 ((← IO.monoMsNow) - q0)
      | .ok (thms, defs, axs) =>
        try
          let dEnv ← FastExport.parseExportFile deltaPath
          match WarmBase.computeOverlay base dEnv.constMap with
          | .error (.fallback why) =>
            emitJson nonce "fallback" why dEnv.constMap.size 0 0 0 ((← IO.monoMsNow) - q0)
          | .error (.reject why) =>
            emitJson nonce "reject" why dEnv.constMap.size 0 0 0 ((← IO.monoMsNow) - q0)
          | .ok plan =>
            let targets := thms ++ axs
            let cacheKey := String.intercalate "," (targets.toList.map toString) ++ "|" ++ String.intercalate "," (defs.toList.map toString)
            let mut cache : CompareCache := match cmpCaches[cacheKey]? with
              | some c => c
              | none => buildCompareCache chalEnv base targets defs
            if !cmpCaches.contains cacheKey then
              if cmpCaches.size >= 16 then cmpCaches := {}
              cmpCaches := cmpCaches.insert cacheKey cache
            match compareDeltaCached chalEnv base cache dEnv.constMap plan.dirtySet with
            | .error e =>
              emitJson nonce "reject" e plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount ((← IO.monoMsNow) - q0)
            | .ok () =>
              match checkAxiomsDelta base axIdx dEnv.constMap plan.dirtySet thms defs axs with
              | .error e =>
                emitJson nonce "reject" e plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount ((← IO.monoMsNow) - q0)
              | .ok () =>
                emitJson nonce "ok" "statements and axioms match challenge" plan.deltaConsts plan.overriddenCount plan.dirtyIds.size plan.effectiveCount ((← IO.monoMsNow) - q0)
        catch e =>
          let em := toString e
          let st := if (em.splitOn "No such file").length > 1 || (em.splitOn "Permission denied").length > 1 then "decline" else "reject"
          emitJson nonce st s!"parse/check error: {em}" 0 0 0 0 ((← IO.monoMsNow) - q0)
    | ["CHECK_FULL", nonce, fullPath, cfgPath] =>
      let q0 ← IO.monoMsNow
      match ← parseConfig cfgPath with
      | .error e => emitJson nonce "error" e 0 0 0 0 ((← IO.monoMsNow) - q0)
      | .ok (thms, defs, axs) =>
        try
          let solEnv ← FastExport.parseExportFile fullPath
          let targets := thms ++ axs
          match Lake.Check.compareAt chalEnv solEnv targets defs primitiveTargets with
          | .error e => emitJson nonce "reject" e solEnv.constMap.size 0 0 solEnv.constMap.size ((← IO.monoMsNow) - q0)
          | .ok () =>
            match ← ParAxioms.checkAxiomsPar solEnv thms defs axs nthreads with
            | .error e => emitJson nonce "reject" e solEnv.constMap.size 0 0 solEnv.constMap.size ((← IO.monoMsNow) - q0)
            | .ok () => emitJson nonce "ok" "full statements and axioms match challenge" solEnv.constMap.size 0 0 solEnv.constMap.size ((← IO.monoMsNow) - q0)
        catch e =>
          let em := toString e
          let st := if (em.splitOn "No such file").length > 1 || (em.splitOn "Permission denied").length > 1 then "decline" else "reject"
          emitJson nonce st s!"full parse/check error: {em}" 0 0 0 0 ((← IO.monoMsNow) - q0)
    | _ =>
      emitJson "unknown" "error" s!"unknown command" 0 0 0 0 0
  return 0

end CCmpWarm

def main (args : List String) : IO UInt32 := do
  let mut chal := ""
  let mut base := ""
  let mut nthreads := 16
  let mut i := 0
  let arr := args.toArray
  while i < arr.size do
    match arr[i]! with
    | "--challenge" =>
      if i + 1 < arr.size then chal := arr[i + 1]!; i := i + 2 else return 2
    | "--base" =>
      if i + 1 < arr.size then base := arr[i + 1]!; i := i + 2 else return 2
    | s =>
      if let some rest := s.dropPrefix? "-j" then
        nthreads := rest.toString.toNat?.getD nthreads
        i := i + 1
      else
        IO.eprintln s!"ccmp-warm: unknown argument '{s}'"
        return 2
  if chal.isEmpty || base.isEmpty then
    IO.eprintln "usage: ccmp-warm --challenge CHALLENGE_EXPORT --base BASE_EXPORT [-jN]"
    return 2
  CCmpWarm.runServer chal base nthreads
