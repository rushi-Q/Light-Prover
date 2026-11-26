/-
LightFastExact: a plugin for the OFFICIAL `lean` (`--plugin=libLightFastExact.so`), UNTRUSTED build accelerator.


`with_unfolding_all exact (x :)` normally elaborates `x` and then checks `isDefEq (type of x) goal` with the Meta
unifier at transparency `all` (twice: in the type ascription `(x :)` and in `exact`). On the RH critical path
(generated "transport" modules) that Meta-level check dominates: e.g. OmPinsTr spends 379 s in tactic execution
while the kernel re-checks the same declarations in 3.5 s. This plugin elaborates `x` exactly as the official
elaborator does (same transparency, same synthesis), and if the goal type, the value and its type are all free
of metavariables, it asks the KERNEL's definitional-equality checker (`Lean.Kernel.isDefEq`) instead of the Meta
unifier. If the kernel confirms, the value is assigned (this is the term the official elaborator produces whenever
its own check succeeds, since without metavariables `isDefEq` cannot change the term). In every other case (kernel
says no / throws, metavariables present, any exception) the state is restored and the official tactic runs.

Why this cannot cause a false ACCEPT: the build is untrusted; every declaration of the export is re-checked by
the trusted kernels (official Lean kernel + second kernel). The plugin only changes how fast a build produces
its .olean files; a wrong term can only make the trusted check REJECT.

Byte identity (v13): the plugin allocates exactly the macro scopes the official tactics allocate (v12 skipped the
tactic framework's `evalTactic` steps and the ascription's macro attempt, 5 scopes per fast decision, which renumbered
hygienic binder names in later auxiliary constants: kernel-irrelevant, but the export was not byte-identical).

Env (read once per call; absent = defaults): LIGHT_FASTEXACT_DEBUG (stderr log), LIGHT_FASTEXACT_MODE=off (no fast
path at all: the official tactics, for comparisons). The kernel check runs synchronously (no time budget).
-/
import Lean
open Lean Elab Tactic Meta

namespace LightFastExact

def dbg (msg : String) : IO Unit := do
  if (← IO.getEnv "LIGHT_FASTEXACT_DEBUG").isSome then IO.eprintln msg

/-- the kernel's definitional equality check (true only on a definite yes) -/
def kcheck (env : Environment) (lctx : LocalContext) (a b : Expr) : Bool × String :=
  match Kernel.isDefEq env lctx a b with
  | .ok true => (true, "")
  | .ok false => (false, "kernel: not defeq")
  | .error (.unknownConstant _ n) => (false, s!"kernel exception: unknown constant {n}")
  | .error (.declTypeMismatch ..) => (false, "kernel exception: declTypeMismatch")
  | .error (.other msg) => (false, s!"kernel exception: {msg.take 200}")
  | .error (.deterministicTimeout ..) => (false, "kernel exception: deterministic timeout")
  | .error (.excessiveMemory ..) => (false, "kernel exception: excessive memory")
  | .error (.deepRecursion ..) => (false, "kernel exception: deep recursion")
  | .error (.interrupted ..) => (false, "kernel exception: interrupted")
  | .error _ => (false, "kernel exception: other")

/-- The kernel check, synchronously in the elaboration thread. (An earlier version ran it in a dedicated task with a
time budget and polled with `IO.sleep`; `Kernel.isDefEq` takes a `Lean.Environment`, whose kernel view is
`env.checked.get`, i.e. it waits for the pending asynchronously elaborated declarations; under `-j1` those need the one
worker thread that was busy polling, so every call ran into the budget. A `Task.get` in the elaboration thread instead
lets Lean's task manager add a worker, exactly as the elaborator's own `addDecl` does.) The local context must be
metavariable-free after instantiation (the kernel does not support metavariables). -/
def kcheckSync (a b : Expr) : MetaM (Bool × String) := do
  let lctx ← instantiateLCtxMVars (← getLCtx)
  if lctx.any (fun d => d.type.hasMVar || (d.value?.map (·.hasMVar)).getD false) then
    return (false, "local context has metavariables")
  return kcheck (← getEnv) lctx a b

/-- `with_unfolding_all exact e` with a single tactic -> `e` -/
def matchExact? (stx : Syntax) : Option Syntax :=
  let seq := stx[1]          -- tacticSeq
  let inner := seq[0]        -- tacticSeq1Indented | tacticSeqBracketed
  if inner.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    let tacs := inner[0].getSepArgs
    if h : tacs.size = 1 then
      let t := tacs[0]
      if t.getKind == ``Lean.Parser.Tactic.exact then some t[1] else none
    else none
  else none

def scopeNow : TacticM Nat := return (← getThe Core.State).nextMacroScope

/-- Undo the macro scopes a discarded attempt consumed (`Core.SavedState.restore` keeps `nextMacroScope`), so that the
official tactic that runs instead allocates exactly the scopes it allocates without the plugin: hygienic names (binder
names of auxiliary `_proof_N` / `match_N` constants) and hence the export stay byte-identical. -/
def resetScope (sc : Nat) : TacticM Unit :=
  modifyThe Core.State fun st => { st with nextMacroScope := sc }

def targetKey : Name := `lightFastExact.target
def targetEndKey : Name := `lightFastExact.targetEnd

/-- the official `exact e` (`closeMainGoalUsing exact fun type _ => elabTermEnsuringType e type`) minus its Meta
`isDefEq` checks, replaced by the kernel's check. For `e = (x :)` the ascription node itself is elaborated (same macro
expansion attempt, same `withSynthesize (postpone := .no)` elaboration of `x` without expected type, as
`elabTypeAscription` does) with no expected type, so that its trailing `ensureHasType` is a no-op; then `exact`'s own
final `isDefEq` is replaced by the kernel check. Every step that allocates macro scopes is the official one. -/
def fastPath (e : Syntax) : TacticM Unit :=
  closeMainGoalUsing `exact fun type _ => do
    let t0 ← IO.monoMsNow
    let type ← instantiateMVars type
    if type.hasMVar then throwError "fastexact: goal has metavariables"
    let v ← match e with
      | `(($_ :)) => Tactic.elabTerm e none
      | _ => Tactic.elabTerm e (some type)
    let t1 ← IO.monoMsNow
    if v.hasMVar then throwError "fastexact: value has metavariables"
    let vty ← instantiateMVars (← inferType v)
    if vty.hasMVar then throwError "fastexact: type has metavariables"
    let (ok, why) ← kcheckSync vty type
    let t2 ← IO.monoMsNow
    let line := ((← getFileMap).toPosition (e.getPos?.getD 0)).line
    dbg s!"fx: {if ok then "ok" else "KERNEL-NO"} elab {t1-t0} kernel {t2-t1} ms {why}{if t1-t0 > 2000 || t2-t1 > 2000 then " SLOW at line " ++ toString line else ""}"
    unless ok do throwError "fastexact: kernel does not confirm"
    return v

/-- `with_unfolding_all exact e` (single tactic): exactly the official `evalWithUnfoldingAll`
(`withTransparency .all <| evalTactic stx[1]`, so the tactic framework allocates the same macro scopes), with the
`exact` node marked (its position range, in the options of the context: thread-local, scoped) so that the `exact`
elaborator below takes the fast path for exactly that node. -/
@[builtin_tactic Lean.Parser.Tactic.withUnfoldingAll]
def evalWithUnfoldingAllFast : Tactic := fun stx => do
  let some _ := matchExact? stx | throwUnsupportedSyntax
  let mode := (← IO.getEnv "LIGHT_FASTEXACT_MODE").getD "all"
  let t := stx[1][0][0].getSepArgs[0]!
  match mode, t.getPos?, t.getTailPos? with
  | "off", _, _ => withTransparency TransparencyMode.all <| evalTactic stx[1]
  | _, some p, some q =>
    withOptions (fun o => (o.set targetKey (p.byteIdx + 1 : Nat)).set targetEndKey (q.byteIdx : Nat)) <|
      withTransparency TransparencyMode.all <| evalTactic stx[1]
  | _, _, _ => withTransparency TransparencyMode.all <| evalTactic stx[1]

/-- the marked `exact`: fast path; on any failure restore the state (and the macro scope counter) and run the official
`exact`. The mark is removed first, so that no `exact` inside `e` can see it. -/
def innerExact (e : Syntax) : TacticM Unit :=
  withOptions (fun o => (o.erase targetKey).erase targetEndKey) do
    let s ← saveState
    let sc ← scopeNow
    let ok ← try fastPath e; pure true catch _ => pure false
    unless ok do
      dbg s!"fx: fallback to the official tactic at {(← getRef).getPos?}"
      s.restore (restoreInfo := true)
      resetScope sc
      closeMainGoalUsing `exact fun type _ => elabTermEnsuringType e type

/-- strip `( ... )` around a term -/
partial def stripParens (stx : Syntax) : Syntax :=
  if stx.getKind == ``Lean.Parser.Term.paren then stripParens stx[1] else stx

/-- `exact (by with_unfolding_all ...)`: the by-block is closed by the tactic above, but `exact` then compares the
value's type with the goal again with the Meta unifier (`elabTermEnsuringType`), which costs as much as the
inner check. Same treatment: official elaboration, kernel check instead of the final Meta `isDefEq`. -/
def isByUnfoldingAll (e : Syntax) : Bool :=
  let b := stripParens e
  if b.getKind == ``Lean.Parser.Term.byTactic then
    let inner := b[1][0]   -- byTactic: "by" tacticSeq ; tacticSeq -> tacticSeq1Indented
    if inner.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := inner[0].getSepArgs
      tacs.size == 1 && tacs[0]!.getKind == ``Lean.Parser.Tactic.withUnfoldingAll
    else false
  else false

def outerFast (e : Syntax) : TacticM Unit :=
  closeMainGoalUsing `exact fun type _ => do
    let t0 ← IO.monoMsNow
    let type ← instantiateMVars type
    if type.hasMVar then throwError "fastexact: goal has metavariables"
    let v ← Tactic.elabTerm e (some type)
    if v.hasMVar then throwError "fastexact: value has metavariables"
    let vty ← instantiateMVars (← inferType v)
    if vty.hasMVar then throwError "fastexact: type has metavariables"
    let t1 ← IO.monoMsNow
    let (ok, why) ← kcheckSync vty type
    let t2 ← IO.monoMsNow
    dbg s!"fx-outer: {if ok then "ok" else "KERNEL-NO"} elab {t1-t0} kernel {t2-t1} ms {why}"
    unless ok do throwError "fastexact: kernel does not confirm"
    return v

@[builtin_tactic Lean.Parser.Tactic.exact]
def evalExactFast : Tactic := fun stx => do
  let e := stx[1]
  let o ← getOptions
  let tgt := o.get targetKey (0 : Nat)
  if tgt != 0 && stx.getPos?.map (·.byteIdx + 1) == some tgt &&
      stx.getTailPos?.map (·.byteIdx) == some (o.get targetEndKey (0 : Nat)) then
    innerExact e
    return
  unless isByUnfoldingAll e do throwUnsupportedSyntax
  if ((← IO.getEnv "LIGHT_FASTEXACT_MODE").getD "all") == "off" then throwUnsupportedSyntax
  let s ← saveState
  let sc ← scopeNow
  let ok ← try outerFast e; pure true catch _ => pure false
  unless ok do
    dbg s!"fx-outer: fallback to the official exact at {(← getRef).getPos?}"
    s.restore (restoreInfo := true)
    resetScope sc
    closeMainGoalUsing `exact fun type _ => elabTermEnsuringType e type

end LightFastExact
