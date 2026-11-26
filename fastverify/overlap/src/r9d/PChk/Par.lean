/-
Parallel `Lean.Kernel.Environment.replay` (Lean 4.36 src/Lean/Replay.lean) for `leanchecker --from-export`.
Design (argument: check/sound/README.md): NO EXPORT RECORD OF AN INDUCTIVE BLOCK EVER
ENTERS AN ENVIRONMENT THE KERNEL READS. The earlier walk inserted the export's inductive-type, constructor and recursor
records UNVERIFIED into its environment (phase-1 "speculation"; phase 2 / the sequential fallback caught wrong records), so
kernel calls on later snapshots (the phase-1 learners, the decl jobs) read attacker-chosen `recursor_val` / `constructor_val`
fields that the C++ kernel relies on as invariants: a recursor record with `numMotives`/`numMinors` lowered by one made
`recursor_val::get_major_induct()` take `const_name` of a bound variable (SIGSEGV, exit 139). Now every inductive constant in
every environment handed to the kernel was produced by the kernel itself from the block's inductive declaration:
 * phase 1 (speculation, speed only; runs before phase 2) learns the kernel's constants of every block with the
   unchanged checking `addDeclCore` of its inductive declaration, in parallel, in dependency order (a block's learner starts
   only when every block it depends on has its result), on walk environments that hold the export's deferred declarations
   and, for inductive blocks, only the constants learned so far;
 * phase 2 (the verdict) puts a learned block's KERNEL-GENERATED constants into its environment and checks them strictly in
   the block's exact snapshot (as the earlier phase 2 did with its learned overrides); a block that was not learned is checked
   synchronously on the walk thread (`addDeclChecked`) and the walk continues with the environment the kernel returns;
   a speculation failure redoes phase 2 with every block checked synchronously (no speculation at all).
The export's constructor and recursor records are compared with the kernel's constants by the official postponed checks
(`==`) and every export record under a name of the final environment (inductive types included) by the record check C2
(`checkExportRecords`): a mismatch REJECTS, as `Lean.Replay` does. A declaration whose name is already a constant of the
walk's environment (e.g. a definition named like a generated recursor) is handed to the checking kernel at once ("already
declared", like `Lean.Replay`) instead of being inserted over that constant. Liveness: the walk's synchronous kernel calls run
under the walk's own cancel token, which the worker pool sets (index-aware, like the workers' tokens) when an EARLIER job is
rejected; every earlier job has been handed to the workers before such a call starts; phase-1 learners have a per-call and an
overall time budget (an unlearned block is checked synchronously).

WALK (sequential, cheap): the SAME depth-first traversal as `Lean.Replay`: top level = the initial
`remaining` NameSet in its iteration order; children = `ci.getUsedConstantsAsSet` in its iteration
order; same remaining/pending state machine; same inductive/ctor/rec/quot handling; same
duplicate-theorem rule. Representation only: `remaining`/`pending` are a per-constant state byte
(0 = in neither, 1 = remaining, 2 = pending) over dense ids, and the used-constant sets are
precomputed in parallel as id arrays in NameSet order (names that are not keys of `newConstants`
are dropped: `isTodo` is false for them, so visiting them is a no-op in `Lean.Replay`).

DEFERRED CHECKS (phase 2): whenever `Lean.Replay` calls the kernel (`addDeclCore E d`) the walk records a
job (E = env snapshot just before, d) and continues with an environment that equals the result of a
successful `addDeclCore E d`:
 * axiom/defn/thm/opaque whose name is not yet a constant of E: `addDeclWithoutChecking E d` =
   `environment::add(constant_info(d))`, which is literally what the checking path returns after its
   checks (src/kernel/environment.cpp); a worker runs the checking `addDeclCore E d` later.
 * inductive block learned in phase 1: E plus the constants the KERNEL generated for it in phase 1,
   inserted with the kernel's own `lean_environment_add`; a worker runs the checking `addDeclCore E d`
   and verifies that the constants it adds are EXACTLY these (same name set, every field equal,
   expressions compared with `Expr.equal` = structural incl. binder names/infos).
 * unlearned inductive block, Quot, and a declaration whose name is already a constant of E:
   SYNCHRONOUS checking `addDeclCore E d` on the walk thread; the walk continues with the kernel's
   result. The job is recorded with its outcome (success, or the kernel error, after which the walk
   stops: the official replay stops there too, or earlier).
N worker threads run the unchanged kernel function `addDeclCore E d` on every deferred job.
VERDICT: accept iff every job succeeds (and the walk completed). By induction over the walk: if all
jobs succeed, every snapshot equals the environment `Lean.Replay` has at that point, so every kernel
call got the same arguments as in the sequential replay. If a job fails with a kernel error, the
first such job in walk order is where `Lean.Replay` fails (same error). If a learned block's
constants differ from the ones the kernel generates in its exact snapshot (never for a genuine
export), phase 2 is redone without speculation. The postponed constructor / recursor checks compare
the export's records with the kernel's constants, as `Lean.Replay`.
Hardening (VETO ONLY): + `checkExportRecords` (record check C2; called after the parallel replay and its
sequential fallback, as in the hardened check/sound/src) and `checkInductNoLooseBVars` (C1; called by Main.lean
`checkParsed` and PChk/Incr.lean before every replay); both texts byte-identical to the hardened default walk.
Incremental leg: the walk, phase 1 and phase 2 are byte-identical to check/sound/src/PChk/Par.lean; the incremental
additions (`cancel?`, the targeted `skip`) keep their meaning: a cancel also abandons phase 1 and interrupts the walk's own
kernel calls; only deferred (`.decl`) jobs can be skipped (never an inductive block, Quot, or a synchronous check).
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
  /-- deferred: a worker runs the checking `addDeclCore env decl` -/
  | decl
  /-- already checked synchronously on the walk thread (inductive block, Quot, or a declaration whose name was taken);
  `none` = the kernel accepted it (the walk continued with the kernel's result), `some ex` = the kernel's error (the walk
  stopped). A worker only reports this outcome. -/
  | done (err : Option Kernel.Exception)
  /-- inductive block whose constants in the walk's environment are `spec` = the constants THE KERNEL generated for this
  declaration in phase 1 (never the export's records); the job runs the checking `addDeclCore env decl` and verifies
  that the constants it adds are EXACTLY `spec` (`sameAdded`) -/
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
  /-- cancel token of the walk's own (synchronous) kernel calls; set by the worker pool when a job with a smaller walk
  index is rejected (index-aware cancellation, like the workers' tokens) -/
  walkTk : IO.CancelToken
  /-- walk index of the walk's current synchronous kernel call (read by the worker pool's cancellation) -/
  walkCur : IO.Ref Nat
  /-- the worker pool's cancellation bound (smallest walk index of a rejected job so far; `2^62` = none) -/
  cancelAbove : IO.Ref Nat
  /-- streaming: jobs are handed to the workers in batches (index of the first job, jobs) while the walk runs -/
  emit : Nat × Array Job → IO Unit := fun _ => pure ()
  batchSize : Nat := 64
  /-- phase 1 (`learn`): the walk only learns the kernel's constants of every inductive block (no jobs recorded) -/
  learn : Bool := false
  /-- phase 2: the constants THE KERNEL generated in phase 1 for the inductive block with this ordinal and walked name
  (blocks until phase 1 has decided it; `none` = not learned) -/
  learned? : Nat → Name → IO (Option (Array ConstantInfo)) := fun _ _ => pure none
  /-- phase 1: publish the decision for a block (ordinal, walked name, the kernel's constants or none) to phase 2 -/
  lpublish : Nat × Name × Option (Array ConstantInfo) → IO Unit := fun _ => pure ()
  /-- phase 1: learning abandoned (time budget exhausted, or the learning walk failed): stop the walk -/
  lstop : IO Bool := pure false
  /-- phase 1: hand a learner job (block ordinal, job) to the learners -/
  lsend : Nat × Job → IO Unit := fun _ => pure ()
  /-- phase 1: a learner result (block ordinal, the kernel's constants or none), non-blocking resp. blocking -/
  lpoll : IO (Option (Nat × Option (Array ConstantInfo))) := pure none
  lwait : IO (Option (Nat × Option (Array ConstantInfo))) := pure none
  /-- phase 1: ids of the constants the kernel looks up without a syntactic reference (PChk/Incr.lean `lookupNames`) -/
  lookupIds : Array Nat := #[]
  /-- Scheduling hint: emitted jobs whose declaration name satisfies `isPrio` are handed, one per batch, to
  `prioEmit` (the priority channel, served first by every worker) instead of `emit`. Order/timing only: every job
  is still recorded in `jobs` at its walk index and checked exactly once; the verdict logic is unchanged. -/
  isPrio : Name → Bool := fun _ => false
  prioEmit : Nat × Array Job → IO Unit := fun _ => pure ()

structure State where
  env : Kernel.Environment
  st : ByteArray
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  jobs : Array Job := #[]
  /-- jobs not yet emitted: (index, job) -/
  pendingEmit : Array Job := #[]
  pendingStart : Nat := 0
  /-- the walk stopped (a synchronous kernel call failed or was cancelled because an earlier job was rejected); the
  replay can then never accept -/
  stopped : Bool := false
  /-- phase 1: per constant id, 1 + the ordinal of the latest inductive block it depends on (0 = none) -/
  lastInd : Array Nat := #[]
  /-- phase 1: per block ordinal: walked name, result received (0/1) -/
  lNames : Array Name := #[]
  lDone : ByteArray := ByteArray.empty
  /-- phase 1: every block with ordinal < `wm` has its result -/
  wm : Nat := 0
  /-- phase 1: learners emitted and not yet answered -/
  lInflight : Nat := 0
  /-- phase 1: constant id of an inductive type -> its block ordinal -/
  blockOrd : Std.HashMap Nat Nat := {}
  /-- phase 1: blocks waiting for their dependencies: ordinal -> (number of blocks still awaited, walked name, declaration) -/
  lWaiting : Std.HashMap Nat (Nat × Name × Declaration) := {}
  /-- phase 1: block ordinal -> the waiting blocks that await it -/
  lWaiters : Std.HashMap Nat (Array Nat) := {}
  /-- phase 1: number of blocks learned (inserted) -/
  nLearned : Nat := 0
  /-- phase 2: number of inductive blocks walked so far (the ordinal of the next one) -/
  nInd : Nat := 0

abbrev M := ReaderT Context <| StateRefT State IO

def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Hand the pending batch to the workers. -/
def flushEmit : M Unit := do
  let s ← get
  if !s.pendingEmit.isEmpty then
    let b := (s.pendingStart, s.pendingEmit)
    modify fun s => { s with pendingEmit := #[], pendingStart := s.jobs.size }
    (← read).emit b

/-- Record a job (walk order = index in `jobs`) and stream it to the workers in batches of consecutive indices. -/
def pushJob (j : Job) : M Unit := do
  let ctx ← read
  let idx := (← get).jobs.size
  if ctx.isPrio j.name then
    -- a priority job closes the current batch and travels alone on the priority channel
    flushEmit
    modify fun s => { s with jobs := s.jobs.push j }
    ctx.prioEmit (idx, #[j])
  else
    if (← get).pendingEmit.isEmpty then modify fun s => { s with pendingStart := idx }
    modify fun s => { s with jobs := s.jobs.push j, pendingEmit := s.pendingEmit.push j }
    if (← get).pendingEmit.size >= ctx.batchSize then flushEmit

/-- SYNCHRONOUS checked add (inductive block, Quot, a declaration whose name is already taken): the unchanged kernel
function `addDeclCore E d` on the walk's current environment `E`, on the walk thread. On success the walk continues with the
environment the KERNEL returns (for an inductive block: with the inductive types, constructors and recursors the kernel
generated - never the export's records) and the job is recorded as succeeded; on a kernel error the job is recorded with
that error and the walk stops (the official replay stops at this declaration, or at an earlier one if an earlier deferred
job fails). Every earlier job is handed to the workers first, and the call runs under the walk's cancel token, which the
pool sets when an earlier job is rejected (liveness: `E` may contain an ill-typed earlier declaration on which the call does
not terminate; the official replay never gets here then). Cancelled (or an earlier job already rejected): the walk stops
without recording a job; the earlier rejection decides. -/
def addDeclChecked (name : Name) (d : Declaration) : M Unit := do
  if (← get).stopped then return
  let ctx ← read
  flushEmit
  let idx := (← get).jobs.size
  let env := (← get).env
  ctx.walkCur.set idx
  if (← ctx.cancelAbove.get) < idx || (← ctx.walkTk.isSet) then
    modify fun s => { s with stopped := true }
    return
  match env.addDeclCore 0 0 d (cancelTk? := some ctx.walkTk) with
  | .ok env' =>
    modify fun s => { s with env := env' }
    pushJob { name, env, decl := d, kind := .done none }
  | .error .interrupted =>
    modify fun s => { s with stopped := true }
  | .error ex =>
    pushJob { name, env, decl := d, kind := .done (some ex) }
    flushEmit
    modify fun s => { s with stopped := true }

/-- Deferred checked add for axiom/defn/thm/opaque. If the name is already a constant of the walk's environment (e.g. a
definition named like a recursor the kernel generated for an earlier block), the kernel's check of `d` fails `check_name`
("already declared"); it is run synchronously instead of inserting `d` over that constant, so no snapshot ever holds a
record under the name of a constant the kernel generated other than the kernel's own. -/
def addDeclDeferred (name : Name) (d : Declaration) : M Unit := do
  if (← get).stopped then return
  let env := (← get).env
  if (env.find? name).isSome then
    if (← read).learn then return   -- phase 1: left out (phase 2 hands it to the kernel)
    addDeclChecked name d
    return
  match env.addDeclWithoutChecking d with
  | .ok env' =>
    modify fun s => { s with env := env' }
    unless (← read).learn do pushJob { name, env, decl := d, kind := .decl }
  | .error ex => throwKernelException ex

/-- Phase 2: an inductive block whose constants THE KERNEL generated in phase 1 (`spec`, never the export's records): they
go into the walk's environment and the job checks `addDeclCore E d` STRICTLY against them (`sameAdded`). -/
def addInductDeferred (name : Name) (d : Declaration) (spec : Array ConstantInfo) : M Unit := do
  if (← get).stopped then return
  let env := (← get).env
  let env' := spec.foldl (init := env) envAdd
  modify fun s => { s with env := env' }
  pushJob { name, env, decl := d, kind := .induct spec }

/-! Phase 1 (speculative inductive learning, affects speed only). The walk's environment holds the export's deferred
declarations (as in phase 2) and, for inductive blocks, ONLY constants the kernel generated: a block's learner runs the
checking `addDeclCore` of the inductive declaration on that environment once every block it depends on has its result
(dependency order: the blocks reachable through `deps` from the constants its types and constructor types use and from the
kernel-implicit lookup names), and its result (the constants the kernel added) is inserted when it arrives. -/

@[inline] def getLI (i : Nat) : M Nat := do return (← get).lastInd[i]!
@[inline] def setLI (i v : Nat) : M Unit := modify fun s => { s with lastInd := s.lastInd.set! i v }

/-- phase 1: hand block `o` to a learner, on the CURRENT environment. -/
def learnEmit (o : Nat) (name : Name) (d : Declaration) : M Unit := do
  let env := (← get).env
  modify fun s => { s with lInflight := s.lInflight + 1 }
  (← read).lsend (o, { name, env, decl := d, kind := .decl })

/-- phase 1: the result of block `o` arrived. The kernel's constants are inserted into the walk's environment, unless one
of their names is already taken there (then the block stays unlearned: phase 2 checks it synchronously). Then the watermark
advances and the blocks waiting for it are emitted. -/
def learnInsert (o : Nat) (r : Option (Array ConstantInfo)) : M Unit := do
  modify fun s => { s with lInflight := s.lInflight - 1, lDone := s.lDone.set! o 1 }
  let name := (← get).lNames[o]!
  let mut pub : Option (Array ConstantInfo) := none
  if let some cs := r then
    let env := (← get).env
    if !cs.isEmpty && cs.all (fun c => (env.find? c.name).isNone) then
      modify fun s => { s with env := cs.foldl (init := s.env) envAdd, nLearned := s.nLearned + 1 }
      pub := some cs
  (← read).lpublish (o, name, pub)
  repeat
    let s ← get
    if s.wm < s.lDone.size && s.lDone.get! s.wm == 1 then
      modify fun s => { s with wm := s.wm + 1 }
    else break
  -- the blocks that waited for this one: emitted once they await nothing more
  if let some ws := (← get).lWaiters[o]? then
    modify fun s => { s with lWaiters := s.lWaiters.erase o }
    for w in ws do
      if let some (c, n', d') := (← get).lWaiting[w]? then
        if c ≤ 1 then
          modify fun s => { s with lWaiting := s.lWaiting.erase w }
          learnEmit w n' d'
        else
          modify fun s => { s with lWaiting := s.lWaiting.insert w (c - 1, n', d') }

/-- phase 1: take every learner result that has arrived (non-blocking). -/
def learnDrain : M Unit := do
  repeat
    match ← (← read).lpoll with
    | some (o, r) => learnInsert o r
    | none => break

/-- phase 1: the blocks without a result yet among those the constants `roots` depend on (transitively, through `deps`;
the search stops at constants all of whose blocks have results (`lastInd ≤ wm`) and at inductive types, i.e. blocks: a block
with a result was learned only after every block it depends on had its result). -/
def learnUnfinished (roots : Array Nat) : M (Array Nat) := do
  let ctx ← read
  let s ← get
  let mut seen : Std.HashSet Nat := {}
  let mut stack := roots
  let mut out : Array Nat := #[]
  while !stack.isEmpty do
    let u := stack.back!
    stack := stack.pop
    if seen.contains u then continue
    seen := seen.insert u
    if s.lastInd[u]! ≤ s.wm then continue
    match s.blockOrd[u]? with
    | some o => if s.lDone.get! o == 0 && !out.contains o then out := out.push o
    | none => for v in ctx.deps[u]! do stack := stack.push v
  return out

/-- phase 1: a new inductive block (types `typeIds`, dependency roots `roots` = the constants its types and constructor
types use, and the kernel-implicit lookup names): its learner is emitted now if every block it depends on has its result,
else as soon as the last of them has. Returns the block's ordinal. -/
def learnBlock (name : Name) (d : Declaration) (roots typeIds : Array Nat) : M Nat := do
  let o := (← get).lNames.size
  if ← (← read).lstop then
    -- learning abandoned: no more learners; this block and every later one stay unlearned
    modify fun s => { s with stopped := true }
    return o
  learnDrain
  let wait ← learnUnfinished roots
  modify fun s => { s with lNames := s.lNames.push name, lDone := s.lDone.push 0 }
  for k in typeIds do
    modify fun s => { s with lastInd := s.lastInd.set! k (o + 1), blockOrd := s.blockOrd.insert k o }
  if wait.isEmpty then learnEmit o name d
  else
    modify fun s => { s with lWaiting := s.lWaiting.insert o (wait.size, name, d) }
    for w in wait do
      modify fun s => { s with lWaiters := s.lWaiters.alter w fun
        | some a => some (a.push o)
        | none => some #[o] }
  return o

/-- phase 1: the quotient declaration, checked synchronously once every block `roots` depend on (`Eq`) has its result
(waiting gives up if no learner is running); a failure ends the learning. -/
def learnQuot (roots : Array Nat) : M Unit := do
  if (← get).stopped then return
  repeat
    learnDrain
    if (← learnUnfinished roots).isEmpty || (← get).lInflight == 0 then break
    match ← (← read).lwait with
    | some (o, r) => learnInsert o r
    | none => break
  match (← get).env.addDeclCore 0 0 Declaration.quotDecl (cancelTk? := none) with
  | .ok env' => modify fun s => { s with env := env' }
  | .error _ => modify fun s => { s with stopped := true }

/-- phase 1: end of the walk: wait for every learner. -/
def learnFinish : M Unit := do
  repeat
    learnDrain
    if (← get).lInflight == 0 then break
    match ← (← read).lwait with
    | some (o, r) => learnInsert o r
    | none => break

@[inline] def getSt (i : Nat) : M UInt8 := do return (← get).st.get! i
@[inline] def setSt (i : Nat) (v : UInt8) : M Unit := modify fun s => { s with st := s.st.set! i v }

mutual
partial def replayId (i : Nat) : M Unit := do
  if (← get).stopped then return   -- the walk stopped (the replay cannot accept): unwind
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
          let d := Declaration.inductDecl lparams nparams types false
          if ctx.learn then
            -- phase 1: the learner waits for the blocks that the constants its types and constructor types use, and the
            -- kernel-implicit lookup names, depend on (transitively)
            let mut roots : Array Nat := ctx.lookupIds
            let mut typeIds : Array Nat := #[]
            for (tci, ctors) in ctorInfo do
              if let some k := ctx.ids[tci.name]? then
                typeIds := typeIds.push k
                roots := roots ++ ctx.deps[k]!
              for c in ctors do
                if let some k := ctx.ids[c.name]? then
                  roots := roots ++ ctx.deps[k]!
            discard <| learnBlock name d roots typeIds
          else if !(← get).stopped then
            let k := (← get).nInd
            modify fun s => { s with nInd := k + 1 }
            match ← ctx.learned? k name with
            -- phase 2: the constants the kernel generated in phase 1, checked strictly by a worker
            | some spec => addInductDeferred name d spec
            -- not learned: checked by the kernel NOW; the walk continues with the constants the kernel generated
            | none => addDeclChecked name d
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayName `Eq
          if ctx.learn then
            learnQuot ((ctx.ids[`Eq]?).toArray ++ ctx.deps[i]!)
          else
            addDeclChecked name (Declaration.quotDecl)
        if ctx.learn then
          -- phase 1: 1 + the latest block this constant depends on (its used constants were walked first)
          let mut m ← getLI i
          for u in ctx.deps[i]! do m := max m (← getLI u)
          setLI i m
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

/-- Record check C2 (VETO ONLY; the same function as in the 4.37 port check/sound/src-437; after Lean #15100/#15101): the official `Lean.Replay` never looks at
export RECORDS flagged `isUnsafe`/`isPartial` (they are not in `remaining`: not replayed, and a constructor/recursor record
among them is never compared by `checkPostponedConstructors`), and it adds the four canonical quotient constants for ANY
`quotInfo` record whatever its name. So an export can carry, under the name of a constant the kernel generated (a
constructor or recursor of a safe inductive), a record of another kind or with other fields, or a quotient record with an
arbitrary name, without the official single-kernel replay noticing (the comparator's closure compare and the kernel still
protect the targets; gruszka vetoes). After the replay we therefore require that EVERY record of the export whose name is
a constant of the final kernel environment equal that constant (the same `==` as `checkPostponedConstructors`; for the
records the walk itself added this is trivially true: the environment's constant was built from the record, so the
comparison is a pointer-equality fast path), and that every `quotInfo` record be one of `Quot`, `Quot.mk`, `Quot.lift`,
`Quot.ind`. A genuine export (lean4export writes the kernel's own constants, names are unique in a kernel environment)
always satisfies both; a failure is a rejection, never an acceptance. Applied to the parallel replay, its sequential
fallback and `--seq` alike (Main.lean). -/
def checkExportRecords (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) : IO Unit := do
  for (n, ci) in newConstants do
    if let .quotInfo _ := ci then
      unless n == ``Quot || n == ``Quot.mk || n == ``Quot.lift || n == ``Quot.ind do
        throw <| IO.userError s!"Unexpected quotient declaration {n}"
    if let some c := env.find? n then
      if !(c == ci) then throw <| IO.userError s!"Export record of {n} differs from the kernel's constant"

/-- C1 (VETO ONLY; Lean #16489, fixed after v4.36.0 by lean4#16512 = 427023483c): the 4.36
kernel's `environment::add_inductive` does not apply `check_no_loose_bvars` to the declaration's inductive types and
constructor types (the 4.37 kernel does, as its first check), so an inductive block whose constructor type has a loose bound
variable is accepted and stored with a different type. `Lean.Replay` (and the walk, `replayId`) builds every inductive
declaration it hands to the kernel from an `inductInfo` record `I` of the export: the types are the records named in `I.all`,
the constructors of each are the records named in that record's `ctors` (looked up by NAME, whatever their kind or
`isUnsafe`/`isPartial` flags). Before any replay (parallel, its sequential fallback, `--seq`: Main.lean) we reject the export
if, for ANY `inductInfo` record `I`, a record named `I.name` or in `I.all`, or a record named in the `ctors` of such a record,
has a type with a loose bound variable (`Expr.hasLooseBVars` = the cached `looseBVarRange > 0`, the datum the kernel's
`has_loose_bvars` reads). This covers every inductive block any replay path can submit (a superset: blocks that are never
submitted are checked too), so no block with a loose bound variable in an inductive or constructor type reaches the 4.36
kernel. A genuine export never fails it: every inductive type and constructor type of a kernel environment is closed (the
kernel type-checks what it stores with `infer_type`, which rejects loose bound variables; lean4export writes those
constants). Only adds `throw`s. -/
def checkInductNoLooseBVars (newConstants : Std.HashMap Name ConstantInfo) : IO Unit := do
  let mut seen : NameSet := {}
  for (_, ci) in newConstants do
    if let .inductInfo info := ci then
      for n in info.name :: info.all do
        unless seen.contains n do
          seen := seen.insert n
          if let some a := newConstants[n]? then
            if a.type.hasLooseBVars then
              throw <| IO.userError s!"C1 (Lean #16489): the type of inductive type {n} has loose bound variables"
            if let .inductInfo ai := a then
              for c in ai.ctors do
                if let some r := newConstants[c]? then
                  if r.type.hasLooseBVars then
                    throw <| IO.userError s!"C1 (Lean #16489): the type of constructor {c} of {n} has loose bound variables"

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

/-- Result of one job: `ok`, a kernel rejection, a failed speculation (=> the replay is redone without speculation), or
not run. -/
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
    return some s!"kernel added {added.size} constants, learned block has {spec.size}"
  let mut m : Std.HashMap Name ConstantInfo := {}
  for c in spec do m := m.insert c.name c
  if m.size != spec.size then return some "duplicate names in learned block"
  for (k, v) in added do
    match m[k]? with
    | some c => if !ciStrictEq v c then return some s!"kernel-generated {k} differs from the learned one"
    | none => return some s!"kernel generated {k}, not in the learned block"
  return none

/-- phase 1: the constants the kernel adds for an inductive declaration on the job's environment, if it accepts it. -/
@[noinline] def learnInduct (tk : IO.CancelToken) (j : Job) : Option (Array ConstantInfo) :=
  match j.env.addDeclCore 0 0 j.decl (cancelTk? := some tk) with
  | .error _ => none
  | .ok env' =>
    if env'.constants.stage₁ || j.env.constants.stage₁ then none
    else some (env'.constants.map₂.foldlNewEntries (fun acc _ v => acc.push v) j.env.constants.map₂ #[])

@[noinline] def runJob (tk : IO.CancelToken) (j : Job) : JobResult :=
  match j.kind with
  | .done none => .ok                  -- checked synchronously by the walk, accepted
  | .done (some ex) => .kernelError ex -- checked synchronously by the walk, rejected
  | .decl =>
    match j.env.addDeclCore 0 0 j.decl (cancelTk? := some tk) with
    | .error .interrupted => .cancelled
    | .error ex => .kernelError ex
    | .ok _ => .ok
  | .induct spec =>
    match j.env.addDeclCore 0 0 j.decl (cancelTk? := some tk) with
    | .error .interrupted => .cancelled
    | .error ex => .kernelError ex
    | .ok env' =>
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

/-- Per-worker diagnostics: finish time (monotonic ns), longest job (ns, index), and (diagnostics only, when
`logMinNs > 0`) every job that took at least `logMinNs`: (index, start ns, duration ns). -/
structure WorkerStats where
  finish : Nat := 0
  maxDur : Nat := 0
  maxIdx : Nat := 0
  slow : Array (Nat × Nat × Nat) := #[]
  deriving Inhabited

/-- `n` dedicated worker threads applying `f` to every job of every batch received on two fresh channels: the
walk-order channel `ch` and the priority channel `pch`. Before taking the next batch from `ch`, a worker takes a
waiting batch of `pch` if there is one; once `ch` is closed and drained, it drains `pch` and stops. So every batch sent
to either channel is processed exactly once, by the same loop body; only the order differs. The caller must close both
channels. Each worker returns its (job index, result) pairs. `extra` = further (cancel token, current walk index) slots
that the index-aware cancellation also serves (the walk's own synchronous kernel calls), `cancelAbove?` = the cancellation
bound shared with the caller (fresh if `none`). -/
def startPools {α : Type} (n : Nat) (f : IO.CancelToken → Job → α) (skip : α) (stop : α → Bool)
    (logMinNs : Nat := 0) (extra : Array (IO.CancelToken × IO.Ref Nat) := #[])
    (cancelAbove? : Option (IO.Ref Nat) := none) :
    IO (JobChan × JobChan × Array IO.CancelToken ×
        Array (Task (Except IO.Error (Array (Nat × α) × WorkerStats)))) := do
  let ch ← Std.CloseableChannel.new (α := Nat × Array Job)
  let pch ← Std.CloseableChannel.new (α := Nat × Array Job)
  let nw := max 1 n
  -- index-aware cancellation: when job t "decides" (stop), jobs with index > t are skipped / interrupted; jobs < t still
  -- run to completion, because the verdict is determined by the FIRST deciding job in walk order.
  let cancelAbove ← match cancelAbove? with
    | some r => pure r
    | none => IO.mkRef (2 ^ 62)
  let mut slots : Array (IO.CancelToken × IO.Ref Nat) := #[]
  for _ in [0:nw] do
    slots := slots.push ((← IO.CancelToken.new), (← IO.mkRef (0 : Nat)))
  let cslots := slots ++ extra
  let mut ts := #[]
  for (tk, cur) in slots do
    ts := ts.push (← IO.asTask (prio := .dedicated) do
      let mut out : Array (Nat × α) := #[]
      let mut ws : WorkerStats := {}
      let mut draining := false
      repeat
        let mut next : Option (Nat × Array Job) := none
        if draining then
          next ← pch.sync.recv
        else
          next ← pch.tryRecv
          if next.isNone then
            next ← ch.sync.recv
            if next.isNone then
              draining := true
              next ← pch.sync.recv
        match next with
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
                for (tk', cur') in cslots do
                  if (← cur'.get) > c then tk'.set
              let b ← IO.monoNanosNow
              if b - a > ws.maxDur then ws := { ws with maxDur := b - a, maxIdx := idx }
              if logMinNs > 0 && b - a >= logMinNs then ws := { ws with slow := ws.slow.push (idx, a, b - a) }
        | none => break
      return (out, { ws with finish := ← IO.monoNanosNow }))
  return (ch, pch, slots.map (·.1), ts)

/-- Close the channel if still open (ignore "already closed"). -/
def chanCloseQuiet (ch : JobChan) : IO Unit := do
  discard <| ch.close.toBaseIO

/-- phase 1: the names the 4.36 kernel looks up without a syntactic reference (= PChk/Incr.lean `lookupNames`):
every learner waits until the blocks they depend on are learned. -/
def learnLookupNames : Array Name := #[
  `Nat, `Nat.zero, `Nat.succ, `String, `String.ofList, `Char, `Char.ofNat, `List, `List.cons, `List.nil,
  `Bool, `Bool.true, `Bool.false, `Eq, `Eq.refl, `Quot, `Quot.mk, `Quot.lift, `Quot.ind]

/-- phase 1: time budget of one learner call (ms); a longer call is cancelled (the block stays unlearned). -/
def learnCallMs : Nat := 30000
/-- phase 1: learning is abandoned (remaining learners cancelled, unlearned blocks are checked synchronously in phase 2)
`learnTotalCapMs` after its start. -/
def learnTotalCapMs : Nat := 600000

abbrev LearnChan := Std.CloseableChannel (Nat × Job)
abbrev ResultChan := Std.CloseableChannel (Nat × Option (Array ConstantInfo))

/-- phase 1: `n` learner threads. Each takes (ordinal, job) from the job channel, runs `learnInduct` (the checking
`addDeclCore` of the inductive declaration on the job's environment) and sends (ordinal, result) to the result channel:
exactly one result per job taken. A call is cancelled (result none) after `learnCallMs`, or as soon as `abandon` is set. -/
def startLearners (n : Nat) (abandon : IO.Ref Bool) :
    IO (LearnChan × ResultChan × Array (Task (Except IO.Error Unit))) := do
  let lch ← Std.CloseableChannel.new (α := Nat × Job)
  let rch ← Std.CloseableChannel.new (α := Nat × Option (Array ConstantInfo))
  let nw := max 1 n
  let mut slots : Array (IO.Ref (Nat × IO.CancelToken)) := #[]
  for _ in [0:nw] do
    slots := slots.push (← IO.mkRef (0, ← IO.CancelToken.new))
  let active ← IO.mkRef nw
  let mut ts := #[]
  for slot in slots do
    ts := ts.push (← IO.asTask (prio := .dedicated) do
      repeat
        match ← lch.sync.recv with
        | none => break
        | some (o, j) =>
          let tk ← IO.CancelToken.new
          slot.set ((← IO.monoNanosNow), tk)
          if ← abandon.get then tk.set
          let r := if ← tk.isSet then none else learnInduct tk j
          slot.set (0, tk)
          match ← (rch.sync.send (o, r)).toBaseIO with
          | .ok () => pure ()
          | .error _ => break
      active.modify (· - 1))
  -- per-call budget and abandonment
  let _wd ← IO.asTask (prio := .dedicated) do
    repeat
      IO.sleep 20
      if (← active.get) == 0 then break
      let now ← IO.monoNanosNow
      let ab ← abandon.get
      for slot in slots do
        let (a, tk) ← slot.get
        if a > 0 && (ab || now - a > learnCallMs * 1000000) then tk.set
  return (lch, rch, ts)

/-- Parallel replay. Returns the final environment or throws like `Lean.Kernel.Environment.replay`. -/
def replayPar (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) (nthreads : Nat)
    (verbose := false) (prio : NameSet := {}) (logMinMs : Nat := 0) (cancel? : Option IO.CancelToken := none)
    (skip : NameSet := {}) (skipImplicit : Array (Name × Bool) := #[]) :
    IO Kernel.Environment := do
  -- (targeted incremental mode, PChk/Incr.lean `verifiedTargets`): the deferred (`.decl`) jobs of the declarations in
  -- `skip` count as done without a kernel call. The caller guarantees that each of them was accepted by this kernel code
  -- in an environment whose constants looked up by that check are content-identical to this export's (its whole closure
  -- and every kernel-implicit name). The walk is unchanged (the declaration is still added at its position like every
  -- deferred one); inductive jobs and the official sequential fallback never skip anything. Default: nothing skipped.
  -- (VETO ONLY) every kernel check of a declaration also asks whether its OWN
  -- name is free (`check_name`: "already declared"), and the answer depends on the walk's snapshot at the job's position
  -- (an earlier inductive block may have generated a constant of that name), which the target's check in the incremental
  -- environment never saw; the walk's `addDeclWithoutChecking` does not ask it either. So a job is skipped only if its name
  -- is absent from its own snapshot (`j.env`); otherwise it runs the unchanged kernel call, which reports "already declared".
  -- (VETO ONLY) the check also looks up the names
  -- the kernel uses without a syntactic reference (PChk/Incr.lean `lookupNames`: literal types and expansion, Bool results,
  -- quotient init) and, by unfolding them, their whole closure. The target's check saw exactly those of them the export
  -- declares, with the export's versions and closures (PChk/Incr.lean `verifiedTargets`); `skipImplicit` = every
  -- `lookupNames` entry with "declared in the export". A job is skipped only if each of them is present in its snapshot iff
  -- the export declares it - the closures of the present ones then are too (the walk adds a constant after everything it
  -- uses), with the export's (= the kernel's, by C2) versions. Otherwise the unchanged kernel call runs.
  let isSkipped : Job → Bool := fun j =>
    !skip.isEmpty && (match j.kind with | .decl => true | _ => false) && skip.contains j.name && (j.env.find? j.name).isNone
      && skipImplicit.all (fun (p, b) => (j.env.find? p).isSome == b)
  -- `cancel?` (the incremental leg's snapshot ingestion only) aborts the replay: every kernel call is interrupted
  -- through the workers' own cancel tokens, jobs report `cancelled` (never a success), so replayPar throws (below: an
  -- accept needs a positive success record for every job). A cancelled replay therefore never returns an environment.
  let cancelled : IO Bool := match cancel? with | some c => c.isSet | none => pure false
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
  for h : i in [0:arr.size] do
    let (n, ci) := arr[i]
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
      st := st.set! i 1
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
  let lookupIds := learnLookupNames.filterMap (ids[·]?)
  let isPrio : Name → Bool := fun n => !prio.isEmpty && prio.contains n
  -- phase 2's kernel-call tokens (workers + the walk's), known once its pools exist; a watcher forwards `cancel?` to
  -- every one of them and abandons phase 1
  let p2tks ← IO.mkRef (#[] : Array IO.CancelToken)
  let replayDone ← IO.mkRef false
  let abandon ← IO.mkRef false
  if let some c := cancel? then
    let _cw ← IO.asTask (prio := .dedicated) do
      repeat
        if ← replayDone.get then break
        if ← c.isSet then
          abandon.set true
          for t in ← p2tks.get do t.set
        IO.sleep 50
  try
    -- PHASE 1 (speculation; speed only), BEFORE phase 2: learn the kernel's constants of every inductive block, in
    -- parallel, in dependency order, on walk environments that hold ONLY kernel-generated inductive constants (never an export
    -- record of a block); every decision (ordinal, walked name, constants or none) goes to phase 2 through `resCh`, read when
    -- phase 2's walk reaches that block. PCHK_F7_SYNC (any value) skips phase 1: every block is then checked synchronously in
    -- phase 2.
    let resCh ← Std.CloseableChannel.new (α := Nat × Name × Option (Array ConstantInfo))
    let learnPhase : IO Unit := do
      let (lch, rch, ltasks) ← startLearners nw abandon
      let ctx : Context := { newConstants, ids, cis, deps, walkTk := ← IO.CancelToken.new, walkCur := ← IO.mkRef 0,
                             cancelAbove := ← IO.mkRef (2 ^ 62), learn := true, lookupIds,
                             lsend := fun x => do
                               match ← (lch.sync.send x).toBaseIO with
                               | .ok () => pure ()
                               | .error _ => throw <| IO.userError "internal error: learner channel closed",
                             lpoll := rch.tryRecv, lwait := rch.sync.recv,
                             lpublish := fun x => do discard <| (resCh.sync.send x).toBaseIO,
                             lstop := abandon.get }
      let tw0 ← IO.monoNanosNow
      let learnDone ← IO.mkRef false
      let _cap ← IO.asTask (prio := .dedicated) do
        repeat
          IO.sleep 20
          if ← learnDone.get then break
          if (← IO.monoNanosNow) > tw0 + learnTotalCapMs * 1000000 then
            abandon.set true
            IO.eprintln "[pchk] inductive learning exceeded its time budget; remaining learners cancelled"
            break
      let (_, s) ← StateRefT'.run (s := { env, st, lastInd := Array.replicate arr.size 0 : State }) do
        ReaderT.run (r := ctx) do
          try
            for n in remaining do
              replayName n
          catch _ =>
            modify fun s => { s with stopped := true }
          if (← get).stopped then abandon.set true
          learnFinish
      learnDone.set true
      abandon.set true
      discard <| lch.close.toBaseIO
      for t in ltasks do discard <| IO.wait t
      log s!"phase 1 done: {s.lNames.size} inductive blocks, {s.nLearned} learned by the kernel{if s.stopped then " (learning stopped early)" else ""}"
    let syncOnly := (← IO.getEnv "PCHK_F7_SYNC").isSome
    unless syncOnly do
      -- phase 1 never decides anything: a failure only means fewer learned blocks
      try learnPhase catch e => IO.eprintln s!"[pchk] inductive learning failed ({e}); unlearned blocks are checked synchronously"
    discard <| resCh.close.toBaseIO
    -- phase 2's view of phase 1's decisions: ordinal -> (walked name, constants or none), buffered in arrival order
    let lbuf ← IO.mkRef ({} : Std.HashMap Nat (Name × Option (Array ConstantInfo)))
    let learnedFromPhase1 : Nat → Name → IO (Option (Array ConstantInfo)) := fun k n => do
      repeat
        if let some (n', r) := (← lbuf.get)[k]? then
          lbuf.modify (·.erase k)
          return if n' == n then r else none
        match ← resCh.sync.recv with
        | some (o, n', r) => lbuf.modify (·.insert o (n', r))
        | none => return none
      return none
    -- PHASE 2 (the verdict): ONE walk; deferred jobs are streamed to the kernel workers as soon as they exist; an inductive
    -- block learned in phase 1 enters the environment with the KERNEL's constants and its job checks them strictly; an
    -- unlearned block, Quot and a declaration under a taken name are checked by the kernel ON THE WALK THREAD and the walk
    -- continues with the kernel's result. The first kernel rejection or speculation failure in walk order decides the verdict,
    -- so it cancels all kernel calls on later snapshots (workers' and the walk's: liveness, later snapshots may contain the
    -- rejected declaration and loop where the official replay has already stopped). Result: `.ok env` = accepted, `.error msg`
    -- = speculation failed (the caller redoes the replay without speculation); a rejection throws.
    let finalPhase (learned? : Nat → Name → IO (Option (Array ConstantInfo))) : IO (Except String Kernel.Environment) := do
      let decided : JobResult → Bool := fun | .kernelError _ => true | .specMismatch _ => true | _ => false
      let walkTk ← IO.CancelToken.new
      let walkCur ← IO.mkRef (0 : Nat)
      let cancelAbove ← IO.mkRef (2 ^ 62)
      -- jobs of the declarations named in `prio` (a scheduling hint; order only) go to the priority channel, which
      -- every worker serves before the walk-order channel, so that known-expensive kernel calls start as soon as the walk
      -- reaches them instead of queueing behind every earlier job. Every job is still checked exactly once and the verdict
      -- below is computed exactly as before.
      if ← cancelled then
        throw <| .userError "replay cancelled"
      let (ch, pch, tks, workers) ← startPools nw (fun tk j => if isSkipped j then .ok else runJob tk j) .cancelled decided
        (logMinMs * 1000000) (extra := #[(walkTk, walkCur)]) (cancelAbove? := some cancelAbove)
      p2tks.set (tks.push walkTk)
      if ← cancelled then
        for t in tks do t.set
        walkTk.set
      let chs := #[ch, pch]
      let ctx : Context := { newConstants, ids, cis, deps, walkTk, walkCur, cancelAbove, learned?,
                             emit := chanSend ch, isPrio, prioEmit := chanSend pch }
      let s ← try
          let (_, s) ← StateRefT'.run (s := { env, st : State }) do
            ReaderT.run (r := ctx) do
              for n in remaining do
                replayName n
              flushEmit
          pure s
        catch e => (for t in tks do t.set); (for c in chs do chanCloseQuiet c); throw e
      for c in chs do chanClose c
      log s!"walk done, {s.jobs.size} jobs{if s.stopped then " (stopped: a kernel check failed or an earlier job was rejected)" else ""}"
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
      if verbose && logMinMs > 0 then
        let slow := (stats.foldl (fun acc w => acc ++ w.slow) #[]).qsort (fun a b => a.2.2 > b.2.2)
        for (i, a, d) in slow do
          IO.eprintln s!"[pchk-slow] {d / 1000000} ms start {(a - t0) / 1000000} ms walk index {i} {(jobs[i]?.map (·.name)).getD .anonymous}{if isPrio ((jobs[i]?.map (·.name)).getD .anonymous) then " [prio]" else ""}"
      let mut firstErr : Option (Nat × Kernel.Exception) := none
      let mut spec : Option (Nat × String) := none
      -- ACCEPT needs a POSITIVE record of success for every job (hardening): a lost result can only reject
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
      -- snapshot is the official environment): speculation failure => redo without speculation; kernel error => reject.
      let specFirst : Bool := match spec, firstErr with
        | some (k, _), some (i, _) => k < i
        | some _, none => true
        | none, _ => false
      if specFirst then
        return .error ((spec.map (·.2)).getD "")
      if let some (i, ex) := firstErr then
        let msg ← (ex.toMessageData {} |>.toString)
        throw <| .userError s!"while replaying declaration '{(jobs[i]?.map (·.name)).getD .anonymous}':\n{msg}"
      -- a stopped walk never accepts (it stops only after recording a kernel error, or when an earlier job was rejected)
      if s.stopped then
        throw <| .userError "internal error: the replay walk stopped without a recorded kernel rejection"
      if let some e := postponed then throw e
      if nOk != jobs.size then
        throw <| .userError s!"internal error: only {nOk} of {jobs.size} kernel checks reported success"
      if verbose && !skip.isEmpty then
        let inSkip := jobs.foldl (fun k j => if skip.contains j.name && (match j.kind with | .decl => true | _ => false) then k + 1 else k) 0
        let skipped := jobs.foldl (fun k j => if isSkipped j then k + 1 else k) 0
        IO.eprintln s!"[pchk] targeted: {skipped} of {inSkip} pre-verified jobs skipped, {inSkip - skipped} checked by the kernel (name taken, or a looked-up kernel-implicit constant of the export not yet in their snapshot)"
      checkExportRecords newConstants s.env   -- record check C2 (veto only)
      return .ok s.env
    -- phase 2 with phase 1's decisions; on a speculation failure (never for a genuine export) redo it without speculation
    -- (every inductive block checked synchronously by the kernel on the walk thread)
    match ← finalPhase learnedFromPhase1 with
    | .ok env' => return env'
    | .error msg =>
      IO.eprintln s!"[pchk] inductive speculation failed ({msg}); redoing the replay with every inductive block checked synchronously"
      match ← finalPhase (fun _ _ => pure none) with
      | .ok env' => return env'
      | .error msg => throw <| .userError s!"internal error: speculation failure without speculation ({msg})"
  finally
    replayDone.set true

end PChk
