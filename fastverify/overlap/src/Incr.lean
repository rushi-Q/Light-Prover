/-
Incremental Lean-kernel leg: overlap the official-kernel replay with the build.

`pleanchecker --incremental` reads commands on stdin, one per line:
  `snap PATH`   ingest the export PATH (an untrusted snapshot of already-built modules) into the growing kernel env E;
  `final PATH`  judge the final solution export B = PATH (the export the other legs judge) and exit.
Exit codes and the verdict line are those of `pleanchecker --from-export B` (0 = accept, 1 = reject).

INGEST of an export X (snapshots and B alike), into the kernel environment E (initially empty):
  * every constant of X whose name is already in E must be equal (`ConstantInfo` BEq; expressions up to alpha-
    equivalence = `Expr.eqv`, the kernel's own `is_equal`) to E's constant, else X is a CONFLICT;
  * the other constants N(X) are replayed on top of E with the unchanged parallel replay `PChk.replayPar N(X) E`
    (official 4.36 kernel, `addDeclCore` on every declaration, inductive blocks verified as in `Lean.Replay`, official
    sequential `Lean.Replay` as its fallback), with the quotient handling of `checkExport` (Quot.mk/lift/ind are added by
    the `Quot` declaration and post-checked).
  A snapshot that conflicts or fails in any way is simply dropped (E unchanged: Kernel.Environment is a value) and
  later snapshots are still tried; a snapshot can never make the verdict REJECTED or ACCEPTED by itself.

FINAL (B): ACCEPT on the incremental path iff
  (1) B ingests without conflict and without any error (its new constants are kernel-checked on top of E);
  (2) B is closed: every constant referenced by a safe constant of B (type, value, inductive `all`/ctors, ctor `induct`,
      recursor `all`/rule ctors/rule rhs) is declared in B;
  (3) every name the kernel can look up WITHOUT a syntactic reference (`implicitNames`: literal types and constructor
      expansion, GMP-accelerated Nat operations, Bool results, quotient init's `Eq`, ...) that is in the final env is
      also declared in B;
  (4) the quotient post-check of `checkExport` passes.
  In EVERY other case (conflict, kernel error, panic-free exception, closure or implicit-name violation, any snapshot
  trouble that leaves B's constants unchecked) the verdict is that of the unchanged non-incremental check of B
  (`checkParsed` = the body of `checkExport`), i.e. the incremental path can only ever turn into an ACCEPT what the
  official kernel accepts, and every non-accept goes through the unmodified code path.

WHY (1)-(4) IMPLY THAT THE OFFICIAL KERNEL ACCEPTS B IN A DEPENDENCY-CORRECT ORDER. E only ever grows by successful
`addDeclCore` calls of the official kernel (replayPar's contract), so every constant c of B is in the final env E' and
was accepted by the kernel in an environment E_c (a prefix of E'); by (1) E'[c] equals B[c] for every c in B. A
successful kernel check of c looked up only (a) constants occurring in the expressions it processed, i.e. in c's
declaration or (transitively) in the values/types of constants it unfolded/inferred - all in c's syntactic closure,
which is inside B by (2), present in E_c (an absent constant throws "unknown constant"), and equal to B's version by (1)
- and (b) the implicit names, which are in B by (3) and equal to B's version by (1). Additional constants of E_c that
are not in B are never looked up. So each check of c computed exactly what the official kernel computes when c is
added to the environment consisting of B's constants that precede c in E'-order, and that order is dependency-correct
(every looked-up constant precedes c). Inductive blocks: E' holds kernel-verified records (replayPar verifies the
kernel-generated constructors/recursors against the exported ones exactly as Lean.Replay does), and B's records are
equal to them by (1). Quotients: as in checkExport (4).
-/
import Lean.CoreM
import Lean.Replay
import PChk.Par

namespace PChk.Incr
open Lean

/-- Names the 4.36 kernel can look up without a syntactic reference in the declaration being checked: every constant
the kernel creates itself (`git grep "name{\"" src/kernel/`, `new_persistent_expr_const`, `lit_type`,
`mk_bool_true/false`: literal types, `Nat.zero/succ` of literal expansion, the GMP-accelerated `Nat` operations,
`String.ofList`/`Char.ofNat`/`List.cons`/`List.nil` of string-literal expansion, `Bool.true/false`, `eagerReduce`,
quotient init's `Eq`/`Eq.refl`, the quotient constants, `dontcare`) plus the comparator's `primitiveTargets`. -/
def implicitNames : Array Name := #[
  `Nat, `Nat.zero, `Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod, `Nat.beq,
  `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight,
  `String, `String.ofList, `String.mk, `Char, `Char.ofNat, `List, `List.cons, `List.nil,
  `Bool, `Bool.true, `Bool.false, `eagerReduce, `Eq, `Eq.refl,
  `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `dontcare,
  `optParam, `autoParam, `semiOutParam, `outParam]

/-- The kernel's own insertion function (`Kernel.Environment.add`, private in Lean; no checking). -/
@[extern "lean_environment_add"]
opaque kenvAdd (env : Kernel.Environment) (cinfo : ConstantInfo) : Kernel.Environment

/-- Quot.mk/lift/ind are added by the `Quot` declaration (Lean.Replay / checkExport erase them from the replay map). -/
def quotTargets : List Name := [`Quot.mk, `Quot.lift, `Quot.ind]

/-- Every name a constant needs to be declared in the same export: `getUsedConstantsAsSet` plus the block structure
Lean.Replay looks up by name (inductive `all` and ctors, ctor `induct`, recursor `all`, rule ctors and rule rhs). -/
def refsOf (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo v =>
    for n in v.all do s := s.insert n
    for n in v.ctors do s := s.insert n
  | .ctorInfo v => s := s.insert v.induct
  | .recInfo v =>
    for n in v.all do s := s.insert n
    for r in v.rules do
      s := s.insert r.ctor
      s := r.rhs.foldConsts s fun c acc => acc.insert c
  | .quotInfo _ => s := s.insert `Eq
  | _ => pure ()
  return s

/-- Chunk bounds for `n` items over `nthreads` workers. -/
def chunks (n nthreads : Nat) : Nat × Nat :=
  let nchunks := max 1 (min (nthreads * 16) (n / 256))
  (nchunks, (n + nchunks - 1) / nchunks)

/-- Split `m` against `env`: constants absent from `env` (to be replayed), number of constants present AND equal, and
the names present but different (conflicts). Parallel; pure reads of persistent / MT objects. -/
def splitAgainst (env : Kernel.Environment) (m : Std.HashMap Name ConstantInfo) (nthreads : Nat) :
    IO (Std.HashMap Name ConstantInfo × Nat × Array Name) := do
  let arr := m.toArray
  let (nchunks, csz) := chunks arr.size nthreads
  let res ← parallelFor nthreads nchunks fun c => Id.run do
    let lo := c * csz
    let hi := min arr.size (lo + csz)
    let mut fresh : Array Nat := #[]
    let mut same := 0
    let mut bad : Array Nat := #[]
    for i in [lo:hi] do
      let (n, ci) := arr[i]!
      match env.find? n with
      | some ci' =>
        if ci == ci' then same := same + 1
        else bad := bad.push i
      | none => fresh := fresh.push i
    return (fresh, same, bad)
  let mut out : Std.HashMap Name ConstantInfo := {}
  let mut same := 0
  let mut bad : Array Name := #[]
  for part in res do
    for (_, (fresh, s, b)) in part do
      same := same + s
      for i in fresh do
        let (n, ci) := arr[i]!
        out := out.insert n ci
      for i in b do bad := bad.push arr[i]!.1
  return (out, same, bad)

/-- First name (if any) referenced by a safe constant of `m` and not declared in `m`. Parallel, pure. -/
def firstUnclosed (m : Std.HashMap Name ConstantInfo) (nthreads : Nat) : IO (Option (Name × Name)) := do
  let arr := m.toArray
  let (nchunks, csz) := chunks arr.size nthreads
  let res ← parallelFor nthreads nchunks fun c => Id.run do
    let lo := c * csz
    let hi := min arr.size (lo + csz)
    for i in [lo:hi] do
      let (n, ci) := arr[i]!
      if !ci.isUnsafe && !ci.isPartial then
        for r in refsOf ci do
          if !m.contains r then return some (n, r)
    return none
  for part in res do
    for (_, r) in part do
      if let some x := r then return some x
  return none

/-- Dense ids of `arr`'s names and, per constant, the ids of its `refsOf` names that are in `arr` and (for `seedOf`) a
flag computed from the names that are not (parallel). -/
def depGraph (arr : Array (Name × ConstantInfo)) (nthreads : Nat) (outside : Name → Bool := fun _ => false) :
    IO (Std.HashMap Name Nat × Array (Array Nat) × ByteArray) := do
  let mut ids : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity arr.size
  for h : i in [0:arr.size] do ids := ids.insert arr[i].1 i
  let (nchunks, csz) := chunks arr.size nthreads
  let res ← parallelFor nthreads nchunks fun c => Id.run do
    let lo := c * csz
    let hi := min arr.size (lo + csz)
    let mut ins : Array (Array Nat) := #[]
    let mut flags : Array Bool := #[]
    for i in [lo:hi] do
      let mut a : Array Nat := #[]
      let mut fl := false
      for r in refsOf arr[i]!.2 do
        match ids[r]? with
        | some j => a := a.push j
        | none => if outside r then fl := true
      ins := ins.push a
      flags := flags.push fl
    return (ins, flags)
  let mut parts : Array (Array (Array Nat) × Array Bool) := Array.replicate nchunks (#[], #[])
  for part in res do
    for (c, x) in part do parts := parts.set! c x
  let mut deps : Array (Array Nat) := Array.mkEmpty arr.size
  let mut flags := ByteArray.mk (Array.replicate arr.size 0)
  for (a, f) in parts do
    for k in [0:a.size] do
      if f[k]! then flags := flags.set! deps.size 1
      deps := deps.push a[k]!
  if deps.size != arr.size then throw <| .userError "internal error: dependency graph size"
  return (ids, deps, flags)

/-- Ids that reach a seed (including the seeds) through `deps` edges (i -> deps[i]), i.e. the transitive dependents. -/
def reachRev (deps : Array (Array Nat)) (seeds : Array Nat) : ByteArray := Id.run do
  let n := deps.size
  let mut start : Array Nat := Array.replicate (n + 1) 0
  for d in deps do
    for j in d do start := start.set! (j + 1) (start[j + 1]! + 1)
  for i in [0:n] do start := start.set! (i + 1) (start[i + 1]! + start[i]!)
  let mut fill := start
  let mut adj : Array Nat := Array.replicate start[n]! 0
  for h : i in [0:n] do
    for j in deps[i] do
      adj := adj.set! fill[j]! i
      fill := fill.set! j (fill[j]! + 1)
  let mut seen := ByteArray.mk (Array.replicate n 0)
  let mut stack := seeds
  while !stack.isEmpty do
    let j := stack.back!
    stack := stack.pop
    if seen.get! j == 0 then
      seen := seen.set! j 1
      for k in [start[j]!:start[j + 1]!] do
        let i := adj[k]!
        if seen.get! i == 0 then stack := stack.push i
  return seen

/-- Ids reachable from the seeds (including them) along `deps` edges, i.e. the transitive dependencies. -/
def reachFwd (deps : Array (Array Nat)) (seeds : Array Nat) : ByteArray := Id.run do
  let mut seen := ByteArray.mk (Array.replicate deps.size 0)
  let mut stack := seeds
  while !stack.isEmpty do
    let j := stack.back!
    stack := stack.pop
    if seen.get! j == 0 then
      seen := seen.set! j 1
      for i in deps[j]! do
        if seen.get! i == 0 then stack := stack.push i
  return seen

/-- The quotient post-check of `checkExport`: every quotient constant of `m` that `pick` selects is in `env`, unchanged. -/
def quotPostCheck (m : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) (pick : Name → Bool := fun _ => true) :
    Except String Unit := do
  for q in `Quot :: quotTargets do
    if pick q then
      if let some info := m[q]? then
        let some info' := env.find? q | throw s!"Could not find quotient constant in final kernel env: {q}"
        if info != info' then throw s!"Quotient constant mismatch on: {q}"

/-- Replay `fresh` (minus Quot.mk/lift/ind, added by `Quot`) on top of `env` with the unchanged parallel replay. -/
def replayOnTop (env : Kernel.Environment) (fresh : Std.HashMap Name ConstantInfo) (nthreads : Nat) (verbose : Bool)
    (prio : NameSet := {}) : IO Kernel.Environment :=
  PChk.replayPar (quotTargets.foldl (init := fresh) (·.erase ·)) env nthreads verbose prio

/-- SNAPSHOT ingest (untrusted input): the constants of `m` that are new to `env`, do not conflict with `env`, and whose
references are all in `env` or among these constants (fixpoint), are replayed on top of `env`; the others are left out
(they are checked at the final step if the final export contains them). Returns the new env (or an error: env must then
be kept unchanged) and (already checked, replayed, left out). -/
def ingestSnapshot (env : Kernel.Environment) (m : Std.HashMap Name ConstantInfo) (nthreads : Nat) (verbose : Bool)
    (label : String) (prio : NameSet := {}) : IO (Except String (Kernel.Environment × Nat × Nat × Array Name)) := do
  let t0 ← IO.monoNanosNow
  let (fresh, same, conflicts) ← splitAgainst env m nthreads
  let arr := fresh.toArray
  let conflictSet : NameSet := conflicts.foldl (·.insert ·) {}
  -- seeds of exclusion: fresh constants referencing a conflicting name or a name that is neither fresh nor in env
  let (_, deps, flags) ← depGraph arr nthreads (fun r => conflictSet.contains r || (env.find? r).isNone)
  let mut seeds : Array Nat := #[]
  for i in [0:arr.size] do
    if flags.get! i != 0 then seeds := seeds.push i
  let mut badB := if seeds.isEmpty then ByteArray.mk (Array.replicate arr.size 0) else reachRev deps seeds
  let t1 ← IO.monoNanosNow
  -- a kernel rejection names its declaration ("while replaying declaration 'X'"): leave X and its dependents out and
  -- try the rest again (a few times; which subset is replayed only matters for speed, every replayed constant is checked)
  let mut lastErr := ""
  for _ in [0:4] do
    let mut ok : Std.HashMap Name ConstantInfo := {}
    let mut left : Array Name := #[]
    for h : i in [0:arr.size] do
      if badB.get! i == 0 then ok := ok.insert arr[i].1 arr[i].2 else left := left.push arr[i].1
    try
      let env' ← replayOnTop env ok nthreads verbose prio
      match quotPostCheck m env' (fun q => ok.contains q || (env.find? q).isSome) with
      | .error e => return .error s!"{label}: {e}"
      | .ok () =>
        if verbose then
          IO.eprintln s!"[incr] {label}: {m.size} constants, {same} already checked, {ok.size} replayed, {left.size} left out ({conflicts.size} conflicts); split {(t1 - t0) / 1000000} ms, replay {((← IO.monoNanosNow) - t1) / 1000000} ms"
        return .ok (env', same, ok.size, left)
    catch e =>
      lastErr := toString e
      let failed? := match lastErr.splitOn "while replaying declaration '" with
        | _ :: rest :: _ => (rest.splitOn "'").head?
        | _ => none
      let some fs := failed? | break
      let some fi := (List.range arr.size).find? (fun i => toString arr[i]!.1 == fs) | break
      if badB.get! fi != 0 then break
      IO.eprintln s!"[incr] {label}: kernel rejected '{fs}'; leaving it and its dependents out and retrying"
      seeds := seeds.push fi
      badB := reachRev deps seeds
  return .error s!"{label}: replay failed: {lastErr}"

/-- FINAL check of the final export `m` (closed: checked by the caller) against the checked environment `env`:
  * constants of `m` equal to `env`'s are already checked;
  * DIRTY = conflicting names (in `env` with another value) and every constant of `m` that transitively references
    one of them; FRESH = constants of `m` not in `env`;
  * FRESH \ DIRTY is replayed on top of `env` (giving `env1`);
  * DIRTY is replayed on top of a separate environment `envD` that holds exactly `m`'s versions of the clean
    constants DIRTY needs (taken from `env1`, where they are equal to `m`'s; inserted with the kernel's own insertion
    function, the quotient constants by the checked `Quot` declaration);
  * every kernel-implicit name present in `env1` must be declared in `m`; quotient post-check.
Returns `none` on success, else the reason (the caller then runs the non-incremental check). -/
def finalCheck (env : Kernel.Environment) (m : Std.HashMap Name ConstantInfo) (nthreads : Nat) (verbose : Bool)
    (nsnap nok : Nat) (prio : NameSet := {}) : IO (Option String) := do
  let t0 ← IO.monoNanosNow
  let (fresh, same, conflicts) ← splitAgainst env m nthreads
  -- a kernel-implicit constant (looked up WITHOUT a syntactic reference, e.g. `Nat` as the type of a raw literal) whose
  -- checked version differs from B's would make the dirty set (syntactic dependents only) incomplete: no incremental path
  if let some p := conflicts.find? (fun n => implicitNames.contains n) then
    return some s!"the checked version of the kernel-implicit constant '{p}' differs from the final export's"
  let marr := m.toArray
  -- dependency graph of m (only needed when something conflicts)
  let (ids, deps, _) ← if conflicts.isEmpty then pure ({}, #[], ByteArray.empty) else depGraph marr nthreads
  let dirtyB := if conflicts.isEmpty then ByteArray.empty else reachRev deps (conflicts.filterMap (ids[·]?))
  let mut dirty : NameSet := {}
  for h : i in [0:dirtyB.size] do
    if dirtyB.get! i != 0 then dirty := dirty.insert marr[i]!.1
  let freshClean := if dirty.isEmpty then fresh else dirty.foldl (init := fresh) (·.erase ·)
  let t1 ← IO.monoNanosNow
  try
    let env1 ← replayOnTop env freshClean nthreads verbose prio
    if let .error e := quotPostCheck m env1 (fun q => !dirty.contains q) then return some e
    let t2 ← IO.monoNanosNow
    if !dirty.isEmpty then
      -- clean constants needed by DIRTY: its closure within m (m is closed), minus DIRTY
      let mut dseeds : Array Nat := #[]
      for i in [0:dirtyB.size] do
        if dirtyB.get! i != 0 then dseeds := dseeds.push i
      let closB := reachFwd deps dseeds
      let mut need : NameSet := {}
      let mut envD := (← Lean.mkEmptyEnvironment).toKernelEnv
      let isQuot (n : Name) := n == `Quot || quotTargets.contains n
      for h : i in [0:closB.size] do
        if closB.get! i != 0 && dirtyB.get! i == 0 then
          let n := marr[i]!.1
          need := need.insert n
          if !isQuot n then
            let some ci := env1.find? n | return some s!"internal: clean constant {n} missing"
            envD := kenvAdd envD ci
      if need.contains `Quot then
        match envD.addDeclCore 0 0 Declaration.quotDecl (cancelTk? := none) with
        | .ok e => envD := e
        | .error _ => return some "quotient declaration rejected while rebuilding the clean environment"
        if let .error e := quotPostCheck m envD (fun q => need.contains q) then return some e
      let dmap : Std.HashMap Name ConstantInfo := dirty.foldl (init := {}) fun acc n =>
        match m[n]? with | some ci => acc.insert n ci | none => acc
      let envD' ← replayOnTop envD dmap nthreads verbose prio
      if let .error e := quotPostCheck m envD' (fun q => dirty.contains q) then return some e
      IO.eprintln s!"[incr] final: {conflicts.size} conflicting constants -> {dirty.size} re-checked against {need.size} clean ones in {((← IO.monoNanosNow) - t2) / 1000000} ms"
    match implicitNames.find? (fun p => (env1.find? p).isSome && !m.contains p) with
    | some p => return some s!"kernel-implicit constant '{p}' is in the checked environment but not in the final export"
    | none => pure ()
    IO.eprintln s!"[incr] final: {m.size} constants: {same} equal to checked ones ({nok} of {nsnap} snapshots ingested), {freshClean.size} fresh checked now, {dirty.size} dirty re-checked; split {(t1 - t0) / 1000000} ms, total {((← IO.monoNanosNow) - t0) / 1000000} ms"
    return none
  catch e =>
    return some s!"final replay failed: {e}"

end PChk.Incr
