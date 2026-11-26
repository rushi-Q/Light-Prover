/-
Parallel `Lean.Kernel.Environment.replay` (Lean 4.36 src/Lean/Replay.lean) for `leanchecker --from-export`.

WALK (sequential, cheap): the SAME depth-first traversal as `Lean.Replay`: top level = the initial
`remaining` NameSet in its iteration order; children = `ci.getUsedConstantsAsSet` in its iteration
order; same remaining/pending state machine; same inductive/ctor/rec/quot handling; same
duplicate-theorem rule. Representation only: `remaining`/`pending` are a per-constant state byte
(0 = in neither, 1 = remaining, 2 = pending) over dense ids, and the used-constant sets are
precomputed in parallel as id arrays in NameSet order (names that are not keys of `newConstants`
are dropped: `isTodo` is false for them, so visiting them is a no-op in `Lean.Replay`).

DEFERRED CHECKS: whenever `Lean.Replay` calls the kernel (`addDeclCore E d`) the walk records a job
(E = env snapshot just before, d) and continues with an environment that equals the result of a
successful `addDeclCore E d`:
 * axiom/defn/thm/opaque: `addDeclWithoutChecking E d` = `environment::add(constant_info(d))`, which
   is literally what the checking path returns after its checks (src/kernel/environment.cpp).
 * inductive block: E plus the block's constants taken from the export (the inductive types of `all`,
   their constructors, and every exported recursor whose `all` equals the block's `all`), inserted
   with the kernel's own `lean_environment_add`. The job then runs the checking `addDeclCore E d`
   and verifies that the constants it added are EXACTLY these (same name set, every field equal,
   expressions compared with `Expr.equal` = structural incl. binder names/infos).
 * Quot: synchronous `addDeclCore` (checked, once).
N worker threads run the unchanged kernel function `addDeclCore E d` on every job.
VERDICT: accept iff every job succeeds. By induction over the walk: if all jobs succeed, every
snapshot equals the environment `Lean.Replay` has at that point, so every kernel call got the same
arguments as in the sequential replay. If a job fails with a kernel error, the first such job in
walk order is where `Lean.Replay` fails (same error). If an inductive job's kernel-generated
constants differ from the exported ones (never for a genuine export; the official replay itself
then reports a constructor/recursor mismatch, or ignores a differing inductive-type record), we do
not try to be clever: the whole check is redone with the official sequential `Lean.Replay`.
-/
import Lean.CoreM
import Lean.AddDecl
import Lean.Replay
import Lean.Util.FoldConsts
import Std.Sync.Channel

namespace PChk
open Lean

/-- The kernel's own insertion function (`Kernel.Environment.add`, private in Lean). -/
@[extern "lean_environment_add"]
opaque envAdd (env : Kernel.Environment) (cinfo : ConstantInfo) : Kernel.Environment

inductive JobKind where
  | decl
  /-- inductive block; the constants inserted speculatively into the walk's environment -/
  | induct (spec : Array ConstantInfo)

structure Job where
  name : Name
  env : Kernel.Environment
  decl : Declaration
  kind : JobKind

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  ids : Std.HashMap Name Nat
  cis : Array ConstantInfo
  deps : Array (Array Nat)
  /-- recursor names by their `all` field -/
  recsByAll : Std.HashMap (List Name) (Array Name)
  /-- speculative constants per inductive block (keyed by the walked name), learned in phase 1 -/
  overrides : Std.HashMap Name (Array ConstantInfo) := {}
  /-- streaming: jobs are handed to the workers in batches (index of the first job, jobs) while the walk runs -/
  emit : Nat × Array Job → IO Unit := fun _ => pure ()
  /-- only jobs satisfying this are emitted (phase 1: inductive jobs only) -/
  emitFilter : Job → Bool := fun _ => true
  batchSize : Nat := 64

structure State where
  env : Kernel.Environment
  st : ByteArray
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  jobs : Array Job := #[]
  /-- jobs not yet emitted: (index, job) -/
  pendingEmit : Array Job := #[]
  pendingStart : Nat := 0

abbrev M := ReaderT Context <| StateRefT State IO

def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Synchronous checked add (Quot). -/
def addDeclSync (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException ex

/-- Hand the pending batch to the workers. -/
def flushEmit : M Unit := do
  let s ← get
  if !s.pendingEmit.isEmpty then
    let b := (s.pendingStart, s.pendingEmit)
    modify fun s => { s with pendingEmit := #[], pendingStart := s.jobs.size }
    (← read).emit b

/-- Record a job (walk order = index in `jobs`) and stream it to the workers in batches.
Batches carry consecutive indices only: a job that is filtered out closes the current batch. -/
def pushJob (j : Job) : M Unit := do
  let ctx ← read
  let idx := (← get).jobs.size
  if ctx.emitFilter j then
    if (← get).pendingEmit.isEmpty then modify fun s => { s with pendingStart := idx }
    modify fun s => { s with jobs := s.jobs.push j, pendingEmit := s.pendingEmit.push j }
    if (← get).pendingEmit.size >= ctx.batchSize then flushEmit
  else
    flushEmit
    modify fun s => { s with jobs := s.jobs.push j }

/-- Deferred checked add for axiom/defn/thm/opaque. -/
def addDeclDeferred (name : Name) (d : Declaration) : M Unit := do
  let env := (← get).env
  match env.addDeclWithoutChecking d with
  | .ok env' =>
    modify fun s => { s with env := env' }
    pushJob { name, env, decl := d, kind := .decl }
  | .error ex => throwKernelException ex

/-- Deferred checked add of an inductive block with speculative constants `spec`. -/
def addInductDeferred (name : Name) (d : Declaration) (spec : Array ConstantInfo) : M Unit := do
  let env := (← get).env
  let env' := spec.foldl (init := env) envAdd
  modify fun s => { s with env := env' }
  pushJob { name, env, decl := d, kind := .induct spec }

@[inline] def getSt (i : Nat) : M UInt8 := do return (← get).st.get! i
@[inline] def setSt (i : Nat) (v : UInt8) : M Unit := modify fun s => { s with st := s.st.set! i v }

mutual
partial def replayId (i : Nat) : M Unit := do
  if (← getSt i) == 1 then
    setSt i 2
    let ctx ← read
    let ci := ctx.cis[i]!
    let name := ci.name
    for j in ctx.deps[i]! do replayId j
    if (← getSt i) == 2 then
      try
        match ci with
        | .defnInfo   info =>
          addDeclDeferred name (Declaration.defnDecl   info)
        | .thmInfo    info =>
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              return
          addDeclDeferred name (Declaration.thmDecl    info)
        | .axiomInfo  info =>
          addDeclDeferred name (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          addDeclDeferred name (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            -- `remaining.erase o.name; pending.erase o.name`
            if let some k := ctx.ids[o.name]? then setSt k 0
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              pure ((← read).newConstants[n]!))
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayNames ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          -- speculative constants: learned from the kernel in phase 1, else the exported records
          let spec ← match ctx.overrides[name]? with
            | some spec => pure spec
            | none => do
              let mut spec : Array ConstantInfo := #[]
              for (ci, ctors) in ctorInfo do
                spec := spec.push ci
                for ctor in ctors do spec := spec.push ctor
              for r in (ctx.recsByAll[info.all]?).getD #[] do
                if let some rci := ctx.newConstants[r]? then spec := spec.push rci
              pure spec
          addInductDeferred name (Declaration.inductDecl lparams nparams types false) spec
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayName `Eq
          addDeclSync (Declaration.quotDecl)
        setSt i 0
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

partial def replayName (n : Name) : M Unit := do
  if let some i := (← read).ids[n]? then replayId i

partial def replayNames (names : NameSet) : M Unit := do
  for n in names do replayName n
end

def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

/-- Strict structural equality of the constant records an inductive declaration generates. -/
def ciStrictEq : ConstantInfo → ConstantInfo → Bool
  | .inductInfo a, .inductInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type &&
    a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
    a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type &&
    a.induct == b.induct && a.cidx == b.cidx && a.numParams == b.numParams && a.numFields == b.numFields &&
    a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type &&
    a.all == b.all && a.numParams == b.numParams && a.numIndices == b.numIndices &&
    a.numMotives == b.numMotives && a.numMinors == b.numMinors &&
    a.rules.length == b.rules.length &&
    (a.rules.zip b.rules).all (fun (r, s) => r.ctor == s.ctor && r.nfields == s.nfields && r.rhs.equal s.rhs) &&
    a.k == b.k && a.isUnsafe == b.isUnsafe
  | _, _ => false

/-- Result of one job: `ok`, a kernel rejection, or a failed speculation (=> sequential fallback). -/
inductive JobResult where
  | ok
  | kernelError (ex : Kernel.Exception)
  | specMismatch (msg : String)
  /-- not run or interrupted because the verdict was already decided (another job failed / speculation failed) -/
  | cancelled

/-- Did `addDeclCore` turn `old` into exactly `old + spec`? -/
def sameAdded (old new : Kernel.Environment) (spec : Array ConstantInfo) : Option String := Id.run do
  if new.constants.stage₁ || old.constants.stage₁ then return some "stage1 constant map"
  if new.constants.map₁.size != old.constants.map₁.size then
    return some "map1 changed"
  if new.quotInit != old.quotInit then return some "quotInit changed"
  let added := new.constants.map₂.foldlNewEntries (fun acc k v => acc.push (k, v)) old.constants.map₂ #[]
  if added.size != spec.size then
    return some s!"kernel added {added.size} constants, export block has {spec.size}"
  let mut m : Std.HashMap Name ConstantInfo := {}
  for c in spec do m := m.insert c.name c
  if m.size != spec.size then return some "duplicate names in export block"
  for (k, v) in added do
    match m[k]? with
    | some c => if !ciStrictEq v c then return some s!"kernel-generated {k} differs from the export"
    | none => return some s!"kernel generated {k}, not in the export block"
  return none

/-- Phase 1: the constants the kernel adds for an inductive job, if it accepts it and they differ
(strictly) from the job's speculative constants. -/
@[noinline] def learnInduct (tk : IO.CancelToken) (j : Job) : Option (Array ConstantInfo) :=
  match j.kind with
  | .decl => none
  | .induct spec =>
    match j.env.addDeclCore 0 0 j.decl (cancelTk? := some tk) with
    | .error _ => none
    | .ok env' =>
      match sameAdded j.env env' spec with
      | none => none
      | some _ => some (env'.constants.map₂.foldlNewEntries (fun acc _ v => acc.push v) j.env.constants.map₂ #[])

@[noinline] def runJob (tk : IO.CancelToken) (j : Job) : JobResult :=
  match j.env.addDeclCore 0 0 j.decl (cancelTk? := some tk) with
  | .error .interrupted => .cancelled
  | .error ex => .kernelError ex
  | .ok env' =>
    match j.kind with
    | .decl => .ok
    | .induct spec =>
      match sameAdded j.env env' spec with
      | none => .ok
      | some msg => .specMismatch msg

/-- Used-constant ids of `cis[lo:hi]`, in `getUsedConstantsAsSet` iteration order. -/
def depsChunk (ids : Std.HashMap Name Nat) (cis : Array ConstantInfo) (lo hi : Nat) : Array (Array Nat) := Id.run do
  let mut out := Array.mkEmpty (hi - lo)
  for i in [lo:hi] do
    let s := cis[i]!.getUsedConstantsAsSet
    out := out.push <| s.foldl (init := #[]) fun acc n =>
      match ids[n]? with
      | some j => acc.push j
      | none => acc
  return out

def nowMs (t0 : Nat) : IO Nat := do return ((← IO.monoNanosNow) - t0) / 1000000

/-- Run `f` on `n` dedicated threads; each thread repeatedly takes the next index `< total`. -/
def parallelFor {α : Type} (n total : Nat) (f : Nat → α) : IO (Array (Array (Nat × α))) := do
  let next ← IO.mkRef 0
  let mut ts := #[]
  for _ in [0:max 1 n] do
    ts := ts.push (← IO.asTask (prio := .dedicated) do
      let mut out : Array (Nat × α) := #[]
      repeat
        let i ← next.modifyGet fun k => (k, k + 1)
        if i < total then
          out := out.push (i, f i)
        else
          break
      return out)
  let mut res := #[]
  for t in ts do
    match ← IO.wait t with
    | .ok out => res := res.push out
    | .error e => throw e
  return res

/-- Like `parallelFor` with an IO body. -/
def parallelForIO {α : Type} (n total : Nat) (f : Nat → IO α) : IO (Array (Array (Nat × α))) := do
  let next ← IO.mkRef 0
  let mut ts := #[]
  for _ in [0:max 1 n] do
    ts := ts.push (← IO.asTask (prio := .dedicated) do
      let mut out : Array (Nat × α) := #[]
      repeat
        let i ← next.modifyGet fun k => (k, k + 1)
        if i < total then
          out := out.push (i, ← f i)
        else
          break
      return out)
  let mut res := #[]
  for t in ts do
    match ← IO.wait t with
    | .ok out => res := res.push out
    | .error e => throw e
  return res

/-- Unbounded channel of job batches. -/
abbrev JobChan := Std.CloseableChannel (Nat × Array Job)

def chanSend (ch : JobChan) (b : Nat × Array Job) : IO Unit := do
  match ← (ch.sync.send b).toBaseIO with
  | .ok () => pure ()
  | .error _ => throw <| IO.userError "internal error: job channel closed"

def chanClose (ch : JobChan) : IO Unit := do
  match ← ch.close.toBaseIO with
  | .ok () => pure ()
  | .error _ => throw <| IO.userError "internal error: job channel closed twice"

/-- Per-worker diagnostics: finish time (monotonic ns), longest job (ns, index). -/
structure WorkerStats where
  finish : Nat := 0
  maxDur : Nat := 0
  maxIdx : Nat := 0
  deriving Inhabited

/-- `n` dedicated worker threads applying `f` to every job of every batch received on a fresh channel,
until it is closed and drained. Each worker returns its (job index, result) pairs. -/
def startPool {α : Type} (n : Nat) (f : IO.CancelToken → Job → α) (skip : α) (stop : α → Bool) :
    IO (JobChan × Array IO.CancelToken × Array (Task (Except IO.Error (Array (Nat × α) × WorkerStats)))) := do
  let ch ← Std.CloseableChannel.new (α := Nat × Array Job)
  let nw := max 1 n
  -- index-aware cancellation: when job t "decides" (stop), jobs with index > t are skipped / interrupted; jobs < t still
  -- run to completion, because the verdict is determined by the FIRST deciding job in walk order.
  let cancelAbove ← IO.mkRef (2 ^ 62)
  let mut slots : Array (IO.CancelToken × IO.Ref Nat) := #[]
  for _ in [0:nw] do
    slots := slots.push ((← IO.CancelToken.new), (← IO.mkRef (0 : Nat)))
  let mut ts := #[]
  for (tk, cur) in slots do
    ts := ts.push (← IO.asTask (prio := .dedicated) do
      let mut out : Array (Nat × α) := #[]
      let mut ws : WorkerStats := {}
      repeat
        match ← ch.sync.recv with
        | some (start, js) =>
          for h : k in [0:js.size] do
            let idx := start + k
            if idx > (← cancelAbove.get) || (← tk.isSet) then
              out := out.push (idx, skip)
            else
              cur.set idx
              let a ← IO.monoNanosNow
              let r := f tk js[k]
              out := out.push (idx, r)
              if stop r then
                let c ← cancelAbove.modifyGet fun c => let c' := min c idx; (c', c')
                for (tk', cur') in slots do
                  if (← cur'.get) > c then tk'.set
              let b ← IO.monoNanosNow
              if b - a > ws.maxDur then ws := { ws with maxDur := b - a, maxIdx := idx }
        | none => break
      return (out, { ws with finish := ← IO.monoNanosNow }))
  return (ch, slots.map (·.1), ts)

/-- Close the channel if still open (ignore "already closed"). -/
def chanCloseQuiet (ch : JobChan) : IO Unit := do
  discard <| ch.close.toBaseIO

/-- Time budget (ms, after walk 1) for the optional inductive-learning phase. -/
def learnCapMs : Nat := 30000

/-- Parallel replay. Returns the final environment or throws like `Lean.Kernel.Environment.replay`. -/
def replayPar (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) (nthreads : Nat)
    (verbose := false) : IO Kernel.Environment := do
  let t0 ← IO.monoNanosNow
  let log (msg : String) : IO Unit := do if verbose then IO.eprintln s!"[pchk {← nowMs t0} ms] {msg}"
  let nw := max 1 nthreads
  -- dense ids
  let arr := newConstants.toArray
  let cis := arr.map (·.2)
  let mut ids : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity arr.size
  for h : i in [0:arr.size] do
    ids := ids.insert arr[i].1 i
  -- used constants, in parallel (started first; `remaining` etc. are built on this thread meanwhile)
  let nchunks := max 1 (min (nw * 16) (arr.size / 64))
  let csz := (arr.size + nchunks - 1) / nchunks
  let depsTask ← IO.asTask (prio := .dedicated) <| parallelFor nw nchunks fun c =>
    let lo := c * csz
    let hi := min arr.size (lo + csz)
    if lo < hi then depsChunk ids cis lo hi else #[]
  -- `remaining` exactly as in `Lean.Replay.replay`
  let mut remaining : NameSet := ∅
  let mut st := ByteArray.mk (Array.replicate arr.size 0)
  let mut recsByAll : Std.HashMap (List Name) (Array Name) := {}
  for h : i in [0:arr.size] do
    let (n, ci) := arr[i]
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
      st := st.set! i 1
    if let .recInfo r := ci then
      recsByAll := recsByAll.alter r.all fun | some a => some (a.push n) | none => some #[n]
  log s!"remaining built, {arr.size} constants"
  let res ← IO.ofExcept (← IO.wait depsTask)
  let mut parts : Array (Array (Array Nat)) := Array.replicate nchunks #[]
  for out in res do
    for (c, a) in out do parts := parts.set! c a
  let mut deps : Array (Array Nat) := Array.mkEmpty arr.size
  for a in parts do
    deps := deps ++ a
  if deps.size != arr.size then throw <| .userError "internal error: deps size"
  log "deps done"
  -- phase 1: walk with the exported inductive records as speculation; learn the kernel-generated
  -- records of every inductive block (parallel, streamed while the walk runs) where they differ
  -- (e.g. binder names: the export shares expressions up to binder names)
  let ctx0 : Context := { newConstants, ids, cis, deps, recsByAll }
  let walk (ctx : Context) : IO State := do
    let (_, s) ← StateRefT'.run (s := { env, st : State }) do
      ReaderT.run (r := ctx) do
        for n in remaining do
          replayName n
        flushEmit
    return s
  -- Liveness: phase-1 snapshots may contain declarations that are ill-typed (they are checked only in phase 2) or
  -- exported inductive records that differ from the kernel's, so a learner's kernel call may not terminate where the
  -- official replay would have stopped. Learning only affects speed (phase 2 verifies strictly, else falls back to the
  -- official replay), so learners are cancelled after a generous time budget (LEARN_CAP_MS after the walk, plus twice the
  -- walk's own duration); a cancelled learner just learns nothing.
  let (lch, ltks, lws) ← startPool nw (fun tk j => learnInduct tk j) none (fun _ => false)
  let cancelLearners : IO Unit := for t in ltks do t.set
  let isInd : Job → Bool := fun j => match j.kind with | .induct _ => true | .decl => false
  let tw0 ← IO.monoNanosNow
  let s1 ← try walk { ctx0 with emit := chanSend lch, emitFilter := isInd, batchSize := 1 }
    catch e => cancelLearners; chanCloseQuiet lch; throw e
  chanClose lch
  let tw1 ← IO.monoNanosNow
  log s!"walk 1 done, {s1.jobs.size} jobs"
  let learnDone ← IO.mkRef false
  let capNs := learnCapMs * 1000000 + 2 * (tw1 - tw0)
  let _watchdog ← IO.asTask (prio := .dedicated) do
    repeat
      if ← learnDone.get then break
      if (← IO.monoNanosNow) - tw1 > capNs then
        cancelLearners
        IO.eprintln "[pchk] inductive learning exceeded its time budget; remaining learners cancelled"
        break
      IO.sleep 20
  let mut overrides : Std.HashMap Name (Array ConstantInfo) := {}
  for w in lws do
    for (i, r?) in (← IO.ofExcept (← IO.wait w)).1 do
      if let some r := r? then
        if let some j := s1.jobs[i]? then overrides := overrides.insert j.name r
  learnDone.set true
  log s!"inductives learned, {overrides.size} blocks differ from the export"
  -- phase 2: walk with the learned records, every job streamed to the kernel workers as soon as it exists;
  -- all jobs are checked, inductive ones STRICTLY. The first kernel rejection or speculation failure decides the verdict
  -- (reject / official fallback), so it cancels all other kernel calls (liveness: later snapshots may contain the
  -- rejected declaration and loop where the official replay has already stopped).
  let ctx := { ctx0 with overrides }
  let decided : JobResult → Bool := fun | .kernelError _ => true | .specMismatch _ => true | _ => false
  let (ch, tks, workers) ← startPool nw (fun tk j => runJob tk j) .cancelled decided
  let s ← try
      if overrides.isEmpty then do
        -- nothing to re-learn: the phase-1 walk is the final walk
        let mut k := 0
        while k < s1.jobs.size do
          chanSend ch (k, s1.jobs.extract k (k + 64))
          k := k + 64
        pure s1
      else walk { ctx with emit := chanSend ch }
    catch e => (for t in tks do t.set); chanCloseQuiet ch; throw e
  chanClose ch
  log s!"walk 2 done, {s.jobs.size} jobs"
  let jobs := s.jobs
  let postponed : Option IO.Error ← try
      let _ ← StateRefT'.run (s := s) do
        ReaderT.run (r := ctx) do
          checkPostponedConstructors
          checkPostponedRecursors
      pure none
    catch e => pure (some e)
  let mut res := #[]
  let mut stats : Array WorkerStats := #[]
  for w in workers do
    let (out, ws) ← IO.ofExcept (← IO.wait w)
    res := res.push out
    stats := stats.push ws
  log "checks done"
  if verbose && !stats.isEmpty then
    let fmin := stats.foldl (fun m w => min m w.finish) stats[0]!.finish
    let fmax := stats.foldl (fun m w => max m w.finish) 0
    let big := stats.foldl (fun (m : WorkerStats) w => if w.maxDur > m.maxDur then w else m) {}
    log s!"workers finished between {(fmin - t0) / 1000000} and {(fmax - t0) / 1000000} ms; longest job {big.maxDur / 1000000} ms ({(jobs[big.maxIdx]?.map (·.name)).getD .anonymous}, walk index {big.maxIdx} of {jobs.size})"
  let mut firstErr : Option (Nat × Kernel.Exception) := none
  let mut spec : Option (Nat × String) := none
  -- ACCEPT needs a POSITIVE record of success for every job (hardening suggested by C03): a lost result can only reject
  let mut okSeen := ByteArray.mk (Array.replicate jobs.size 0)
  let mut nOk := 0
  for out in res do
    for (i, r) in out do
      match r with
      | .ok =>
        if i < jobs.size && okSeen.get! i == 0 then
          okSeen := okSeen.set! i 1
          nOk := nOk + 1
        else
          throw <| .userError s!"internal error: job {i} reported twice or out of range"
      | .kernelError ex =>
        match firstErr with
        | some (k, _) => if i < k then firstErr := some (i, ex)
        | none => firstErr := some (i, ex)
      | .specMismatch msg =>
        match spec with
        | some (k, _) => if i < k then spec := some (i, msg)
        | none => spec := some (i, msg)
      | .cancelled => pure ()   -- only jobs AFTER a deciding job (index-aware cancellation); never a success
  -- The FIRST deciding job in walk order decides (every job before it ran to completion and succeeded, so its
  -- snapshot is the official environment): speculation failure => official sequential replay; kernel error => reject.
  let specFirst : Bool := match spec, firstErr with
    | some (k, _), some (i, _) => k < i
    | some _, none => true
    | none, _ => false
  if specFirst then
    let msg := (spec.map (·.2)).getD ""
    -- never happens for a genuine export; redo everything with the official sequential replay
    IO.eprintln s!"[pchk] inductive speculation failed ({msg}); falling back to the sequential Lean.Replay"
    return ← env.replay newConstants
  if let some (i, ex) := firstErr then
    let msg ← (ex.toMessageData {} |>.toString)
    throw <| .userError s!"while replaying declaration '{(jobs[i]?.map (·.name)).getD .anonymous}':\n{msg}"
  if let some e := postponed then throw e
  if nOk != jobs.size then
    throw <| .userError s!"internal error: only {nOk} of {jobs.size} kernel checks reported success"
  return s.env

end PChk
