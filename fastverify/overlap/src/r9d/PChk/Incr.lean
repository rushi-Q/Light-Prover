/-
Incremental Lean-kernel leg: overlap the official-kernel replay with the build.
Full argument: fastverify/overlap/README.md. Summary:

`pleanchecker --incremental[=DIR]` reads commands (`snap PATH`, `final PATH [NONCE]`) on stdin or on the FIFO DIR/cmd.
SNAPSHOT (untrusted input) -> `ingestSnapshot`: the constants new to the checked environment E, not conflicting with E
and whose references are all in E or among themselves are replayed on top of E with the unchanged `PChk.replayPar`
(official kernel `addDeclCore` on every declaration, inductive blocks verified as in `Lean.Replay`); the rest is left out
(also every declaration the kernel rejects, with its dependents). E only ever grows by kernel-accepted constants.
FINAL (the export B the other legs judge) -> `finalCheck`, incremental ACCEPT iff:
  (1) B is closed (every name a safe constant of B references via `refsOf` is declared in B);
  (2) no kernel-implicit constant (`implicitNames`) has a checked version that differs from B's;
  (3) constants of B equal (ConstantInfo BEq, Expr.eqv) to E's and not DIRTY are already checked; DIRTY = the
      conflicting names and all their transitive dependents in B, re-checked in a separate environment that holds
      exactly B's versions of their clean closure; FRESH \ DIRTY replayed on top of E;
  (4) every kernel-implicit name present in the checked environment is declared in B; quotient post-check.
Anything else -> the caller runs the unchanged non-incremental check of B (`checkParsed`).
Hardening (VETO ONLY): C1 (`PChk.checkInductNoLooseBVars`, Lean #16489) runs on every map `replayOnTop`
hands to the kernel (snapshots, FRESH, DIRTY) and on the final export at the start of `finalCheck`; C2 (`checkExportRecords`
= record check) runs inside every `replayPar` (PChk/Par.lean). A failure is a dropped snapshot or "no incremental path" (the
hardened `checkParsed` then judges B), never an acceptance.
C2 in `finalCheck` (VETO ONLY): `replayPar`'s own record check sees
only the map it replays, so `finalCheck` adds (a) the canonical-name rule for every quotient record of B, (b) "no incremental
path" when a DIRTY name of B is a constant that a NOT dirty inductive block of B generates (env1 holds it as a type /
constructor / recursor of a block whose type B declares clean: the plain replay would generate it from that block, so B's
record of that name can never be the kernel's constant), and (c) after the dirty re-check, the record check on ALL of B against the
re-check environment envD' (a record that is not dirty may carry the name of a constant a dirty block generates).
Together with the record checks inside the two `replayPar` calls, every record of B whose name is a constant of the
environment the incremental path accepts (env1 for clean names, envD' for dirty names and the constants dirty blocks
generate) equals that constant - the condition `checkParsed`'s record check establishes for the plain replay.
Targeted mode: a pre-verified target is skipped only if its name is free in the walk's snapshot at
its position (PChk/Par.lean); with C2 on the final replay this closes both attacks (a theorem named like a generated
recursor; a forged constructor record used by the target's check in the admitted environment).
Implicit lookups: the kernel also reaches the CLOSURE of the names it looks
up without a syntactic reference (`lookupNames`; it unfolds them: a string literal reaches `Char.ofNatAux`). Full mode: no
incremental path if one of them is dirty or fresh, and the dirty re-check environment holds all of them with their closure.
Targeted mode: `verifiedTargets` compares the closure of every one of them present in envD like the target's own closure,
and the replay skips a target only where its walk snapshot holds exactly the `lookupNames` constants B declares.
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

/-- The kernel-implicit names the 4.36 kernel can LOOK UP in the environment without a syntactic
reference in the declaration being checked (official v4.36.0 sources): the literal types `Nat` / `String` (`Literal.type`,
exported as `lean_lit_type`, `kernel/expr.cpp` 70); `Nat.zero` / `Nat.succ` of Nat-literal expansion and `String.ofList` /
`Char.ofNat` / `List.cons` / `List.nil` / `Char` of string-literal expansion (`kernel/inductive.cpp` 1378-1389,
`kernel/type_checker.cpp` 1249, 1250, 1265); `Bool.true` / `Bool.false`, the results of the GMP `Nat.beq` / `Nat.ble`
(`type_checker.cpp` 665), with their type `Bool`; `Eq` / `Eq.refl` (quotient init, `kernel/quot.cpp` 20-43) and the quotient
constants (`quot.cpp` 107-113). The other `implicitNames` are only compared by name, never looked up (the GMP `Nat`
operations and `eagerReduce`: `type_checker.cpp` 170, 1251-1264), substituted only where they cannot occur (`dontcare`,
`type_checker.cpp` 768) or not used by the 4.36 kernel at all (`String.mk`, the comparator's primitives). The kernel unfolds
these constants, so a check can reach their whole `refsOf` closure (`Char.ofNat` -> `Char.ofNatAux`). Same set as an
independent derivation of the kernel's implicit lookups. -/
def lookupNames : Array Name := #[
  `Nat, `Nat.zero, `Nat.succ, `String, `String.ofList, `Char, `Char.ofNat, `List, `List.cons, `List.nil,
  `Bool, `Bool.true, `Bool.false, `Eq, `Eq.refl, `Quot, `Quot.mk, `Quot.lift, `Quot.ind]

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
      let ci := arr[i]!.2
      let safe := !ci.isUnsafe && !ci.isPartial
      for r in refsOf ci do
        match ids[r]? with
        | some j => a := a.push j
        | none => if safe && outside r then fl := true
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
    (prio : NameSet := {}) (cancel? : Option IO.CancelToken := none) : IO Kernel.Environment := do
  let m := quotTargets.foldl (init := fresh) (·.erase ·)
  PChk.checkInductNoLooseBVars m   -- C1 (veto only): no inductive block with a loose bvar reaches the kernel, also from snapshots
  PChk.replayPar m env nthreads verbose prio (cancel? := cancel?)

/-- SNAPSHOT ingest (untrusted input): the constants of `m` that are new to `env`, do not conflict with `env`, and whose
references are all in `env` or among these constants (fixpoint), are replayed on top of `env`; the others are left out
(they are checked at the final step if the final export contains them). Returns the new env (or an error: env must then
be kept unchanged) and (already checked, replayed, left out). -/
def ingestSnapshot (env : Kernel.Environment) (m : Std.HashMap Name ConstantInfo) (nthreads : Nat) (verbose : Bool)
    (label : String) (prio : NameSet := {}) (cancel? : Option IO.CancelToken := none) :
    IO (Except String (Kernel.Environment × Nat × Nat × Array Name)) := do
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
      let env' ← replayOnTop env ok nthreads verbose prio cancel?
      match quotPostCheck m env' (fun q => ok.contains q || (env.find? q).isSome) with
      | .error e => return .error s!"{label}: {e}"
      | .ok () =>
        if verbose then
          IO.eprintln s!"[incr] {label}: {m.size} constants, {same} already checked, {ok.size} replayed, {left.size} left out ({conflicts.size} conflicts); split {(t1 - t0) / 1000000} ms, replay {((← IO.monoNanosNow) - t1) / 1000000} ms"
        return .ok (env', same, ok.size, left)
    catch e =>
      lastErr := toString e
      if let some c := cancel? then
        if ← c.isSet then return .error s!"{label}: ingestion aborted for a final request"
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
  -- C1 (veto only): the final export itself must pass C1 (else no incremental path: checkParsed judges it, and its C1
  -- rejects); covers B's inductive blocks that are taken from E (checked from snapshot records) as well
  let mK := quotTargets.foldl (init := m) (·.erase ·)
  try PChk.checkInductNoLooseBVars mK
  catch e => return some s!"{e}"
  -- C2 (record check part (2), veto only): every quotient record of B is one of the four canonical constants
  for (n, ci) in m do
    if let .quotInfo _ := ci then
      unless n == ``Quot || n == ``Quot.mk || n == ``Quot.lift || n == ``Quot.ind do
        return some s!"Unexpected quotient declaration {n}"
  let (fresh, same, conflicts) ← splitAgainst env m nthreads
  -- a kernel-implicit constant (looked up WITHOUT a syntactic reference, e.g. `Nat` as the type of a raw literal) whose
  -- checked version differs from B's would make the dirty set (syntactic dependents only) incomplete: no incremental path
  if let some p := conflicts.find? (fun n => implicitNames.contains n) then
    return some s!"the checked version of the kernel-implicit constant '{p}' differs from the final export's"
  if !conflicts.isEmpty then
    IO.eprintln s!"[incr] final: {conflicts.size} constants differ from their checked versions, e.g. {(conflicts.extract 0 20).toList}"
  let marr := m.toArray
  -- dependency graph of m, computed once: (1) closure: no safe constant references a name m does not declare;
  -- (2) DIRTY = the transitive dependents of the conflicting names
  let (ids, deps, outsideB) ← depGraph marr nthreads (fun _ => true)
  for h : i in [0:outsideB.size] do
    if outsideB.get! i != 0 then
      let bad := (refsOf marr[i]!.2).toList.find? (fun r => !m.contains r)
      return some s!"final export not closed: '{marr[i]!.1}' references '{(bad.map toString).getD "?"}', which it does not declare"
  let dirtyB := if conflicts.isEmpty then ByteArray.mk (Array.replicate marr.size 0) else reachRev deps (conflicts.filterMap (ids[·]?))
  let mut dirty : NameSet := {}
  for h : i in [0:dirtyB.size] do
    if dirtyB.get! i != 0 then dirty := dirty.insert marr[i]!.1
  -- (VETO ONLY) the kernel looks the `lookupNames`
  -- up WITHOUT a syntactic reference (e.g. a string literal expands to `String.ofList [Char.ofNat ..]`) and then unfolds
  -- them, so it can reach their whole `refsOf` closure. A check of a clean constant done in E is the check in B only if
  -- that closure is the same in E and B: no such constant may be DIRTY (its closure in B reaches a conflicting constant,
  -- e.g. `Char.ofNat` -> a changed `Char.ofNatAux`) or FRESH (absent from E, where the clean constants were checked).
  -- Otherwise: no incremental path (the hardened plain replay decides).
  if let some p := lookupNames.find? (fun p => dirty.contains p) then
    return some s!"the kernel-implicit constant '{p}' depends on a constant whose checked version differs from the final export's"
  if let some p := lookupNames.find? (fun p => fresh.contains p) then
    return some s!"the kernel-implicit constant '{p}' is new in the final export (absent from the checked environment)"
  let freshClean := if dirty.isEmpty then fresh else dirty.foldl (init := fresh) (·.erase ·)
  let t1 ← IO.monoNanosNow
  try
    let env1 ← replayOnTop env freshClean nthreads verbose prio
    if let .error e := quotPostCheck m env1 (fun q => !dirty.contains q) then return some e
    -- C2 (veto only): a DIRTY name that an inductive block of B which is NOT dirty generates (its constant in
    -- env1 is a type / constructor / recursor of a block one of whose types B declares and is clean) would be declared
    -- twice by the plain replay of B (once by that unchanged block, once from B's own record), so B's record is never the
    -- kernel's constant: no incremental path (attack: snapshot with T, final B adds a record named T.rec)
    for h : i in [0:dirtyB.size] do
      if dirtyB.get! i == 0 then continue
      let n := marr[i]!.1
      if let some c := env1.find? n then
        let owners : List Name := match c with
          | .ctorInfo v => [v.induct]
          | .recInfo v => v.all
          | .inductInfo v => v.all
          | _ => []
        if let some o := owners.find? (fun o => m.contains o && !dirty.contains o) then
          return some s!"R9 C2: final export record '{n}' is a constant generated by the unchanged inductive block of '{o}'"
    let t2 ← IO.monoNanosNow
    if !dirty.isEmpty then
      -- clean constants needed by DIRTY: its closure within m (m is closed), minus DIRTY
      let mut dseeds : Array Nat := #[]
      for i in [0:dirtyB.size] do
        if dirtyB.get! i != 0 then dseeds := dseeds.push i
      -- the clean environment also holds every `lookupNames` constant of B and its closure (none of them is dirty,
      -- see above), so the dirty re-check's implicit lookups see B's constants
      for p in lookupNames do
        if let some id := ids[p]? then dseeds := dseeds.push id
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
      let t3 ← IO.monoNanosNow
      let envD' ← replayOnTop envD dmap nthreads verbose prio
      IO.eprintln s!"[incr] final: clean environment of {need.size} constants built in {(t3 - t2) / 1000000} ms, {dmap.size} dirty constants replayed in {((← IO.monoNanosNow) - t3) / 1000000} ms"
      if let .error e := quotPostCheck m envD' (fun q => dirty.contains q) then return some e
      -- C2 (veto only): EVERY record of B whose name the re-check environment holds must equal that
      -- constant (a record that is not itself dirty, e.g. an unsafe one or a fresh clean one, may carry the name of a
      -- constant a DIRTY inductive block generates); the clean constants of envD are B's own (equal by construction)
      PChk.checkExportRecords mK envD'
      IO.eprintln s!"[incr] final: {conflicts.size} conflicting constants -> {dirty.size} re-checked against {need.size} clean ones in {((← IO.monoNanosNow) - t2) / 1000000} ms"
    match implicitNames.find? (fun p => (env1.find? p).isSome && !m.contains p) with
    | some p => return some s!"kernel-implicit constant '{p}' is in the checked environment but not in the final export"
    | none => pure ()
    IO.eprintln s!"[incr] final: {m.size} constants: {same} equal to checked ones ({nok} of {nsnap} snapshots ingested), {freshClean.size} fresh checked now, {dirty.size} dirty re-checked; split {(t1 - t0) / 1000000} ms, total {((← IO.monoNanosNow) - t0) / 1000000} ms"
    return none
  catch e =>
    return some s!"final replay failed: {e}"


/-! ### TARGETED mode (`pleanchecker --incremental=DIR --targeted=FILE`)

During the build only the TARGETS (a list of declaration names, e.g. the longest kernel jobs of an earlier run) are kernel
checked; every other snapshot constant is merely ADMITTED into the environment `E` with the kernel's own insertion
function (no check) so that the targets' closures are present. At the final export `B`, a target `d` whose check finished
successfully is skipped by the (otherwise unchanged) replay of `B` iff `B[d]` is exactly the checked declaration, every
constant reachable from `d` in `B` (`refsOf`, transitively) is present in `E` with an equal `ConstantInfo` (expressions up
to `Expr.eqv`, the kernel's `is_equal`), and every kernel-implicit name has the same version (or is absent) in `E` and `B`.
Why sound: the kernel's check of `d` looks up `d`'s syntactic closure, the names it looks up without a syntactic reference
(`lookupNames`) together with THEIR closures (the kernel unfolds them, e.g. a string literal -> `String.ofList` ->
`Char.ofNat` -> `Char.ofNatAux`; comparing only the
implicit names themselves is not enough) AND `d`'s own name (`check_name`, "already declared"). Both closures
are content-identical in `E` (= `envD`) and `B` (and, by the C2 record check of the final replay, equal to the kernel's
constants of the replay); `d`'s own name is free in the environment of its check, and the replay skips `d` only if its name
is also free in the walk's snapshot at `d`'s position and that snapshot holds exactly the `lookupNames` constants `B`
declares, hence (the walk adds a constant only after its references) their closures too (PChk/Par.lean `isSkipped`), so the check
computed exactly what the kernel computes when `d` is replayed on top of `B`'s constants. Admitted constants are never trusted: each of them that is in `B` is
checked by the replay of `B` like any other constant, and admitted constants that are not in `B` are never looked up by
`d`'s check (they are not in its closure). Inductive type, constructor and recursor records of a
snapshot are never admitted (the kernel would read them as invariants), so only targets whose closure contains no inductive
constant can start. Every anomaly (target not finished, unequal, not closed, implicit difference)
only removes `d` from the skip set. -/

/-- The declaration of a constant that a target check can run on (Lean.Replay's deferred kinds; unsafe/partial: never). -/
def targetDecl? (ci : ConstantInfo) : Option Declaration :=
  if ci.isUnsafe || ci.isPartial then none else
  match ci with
  | .thmInfo v => some (.thmDecl v)
  | .defnInfo v => some (.defnDecl v)
  | .opaqueInfo v => some (.opaqueDecl v)
  | .axiomInfo v => some (.axiomDecl v)
  | _ => none

/-- Adjacency cache of the targeted mode: `refsOf` of the constant `E` holds under each name (computed once, when the
constant is admitted; entries are never replaced, like `E`'s). -/
abbrev Adj := Std.HashMap Name (Array Name)

/-- `refsOf` of every constant of `cs` (parallel for big inputs; pure). -/
def refsPar (cs : Array (Name × ConstantInfo)) (nthreads : Nat) : IO (Array (Name × Array Name)) := do
  if cs.size < 4096 then return cs.map fun (n, ci) => (n, (refsOf ci).toArray)
  let (nchunks, csz) := chunks cs.size nthreads
  let parts ← parallelFor (min nthreads nchunks) nchunks fun k => Id.run do
    let lo := k * csz
    let hi := min cs.size (lo + csz)
    let mut out : Array (Name × Array Name) := #[]
    for i in [lo:hi] do
      let (n, ci) := cs[i]!
      out := out.push (n, (refsOf ci).toArray)
    return out
  let mut res : Array (Name × Array Name) := #[]
  for part in parts do
    for (_, out) in part do res := res ++ out
  return res

/-- Admit the constants of `m` that are new to `env` (kernel insertion, no check; the quotient package through the
checked `Quot` declaration), except the checkable targets, which are returned instead (name, constant): they are admitted
only when their own check starts (`startReady`). The adjacency of every inserted constant is added to `adj`. -/
def admitTargeted (env : Kernel.Environment) (adj : Adj) (m : Std.HashMap Name ConstantInfo) (targets : NameSet)
    (nthreads : Nat) : IO (Kernel.Environment × Adj × Array (Name × ConstantInfo)) := do
  let mut env := env
  let mut tgts : Array (Name × ConstantInfo) := #[]
  let mut added : Array (Name × ConstantInfo) := #[]
  let mut quot := false
  for (n, ci) in m.toArray do
    if (env.find? n).isSome then continue
    if n == `Quot || quotTargets.contains n then
      quot := true
      continue
    -- an inductive type, constructor or recursor record of the (untrusted) snapshot is NEVER admitted: the
    -- target checks run the C++ kernel on `E`, which would read its fields as kernel invariants (a lying recursor record
    -- crashes the kernel). Consequence: a target whose closure reaches an inductive block never becomes complete, never
    -- starts and is never skipped (the final replay checks it, like every other declaration).
    match ci with
    | .inductInfo _ | .ctorInfo _ | .recInfo _ => continue
    | _ => pure ()
    if targets.contains n && (targetDecl? ci).isSome then tgts := tgts.push (n, ci)
    else
      env := kenvAdd env ci
      added := added.push (n, ci)
  if quot && (env.find? `Quot).isNone then
    match env.addDeclCore 0 0 Declaration.quotDecl (cancelTk? := none) with
    | .ok e =>
      env := e
      for q in `Quot :: quotTargets do
        if let some ci := env.find? q then added := added.push (q, ci)
    | .error _ => pure ()
  let mut adj := adj
  for (n, rs) in ← refsPar added nthreads do adj := adj.insert n rs
  return (env, adj, tgts)

/-- the adjacency of `c` in `env` (cached; computed for constants that are not in the cache) -/
@[inline] def adjOf (env : Kernel.Environment) (adj : Adj) (c : Name) : Option (Array Name) :=
  match adj[c]? with
  | some rs => some rs
  | none => (env.find? c).map fun ci => (refsOf ci).toArray

/-- Is the `refsOf` closure of `roots` complete in `env` (every reachable name present)? `done` = names already known to
have a complete closure there (grows monotonically: `env` only grows, entries are never replaced). -/
def closureComplete (env : Kernel.Environment) (adj : Adj) (roots : Array Name) (done : Std.HashSet Name) :
    Bool × Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := roots
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c || done.contains c then continue
    seen := seen.insert c
    match adjOf env adj c with
    | some rs => for r in rs do stack := stack.push r
    | none => return (false, done)
  let mut done := done
  for n in seen do done := done.insert n
  return (true, done)

/-- Check one target with the unchanged kernel function on `env` (which must not contain it). Interrupted = false. -/
@[noinline] def checkTarget (env : Kernel.Environment) (ci : ConstantInfo) (tk : IO.CancelToken) : Bool :=
  match targetDecl? ci with
  | none => false
  | some d =>
    match env.addDeclCore 0 0 d (cancelTk? := some tk) with
    | .ok _ => true
    | .error _ => false

/-- A started target check: the checked constant, the environment it is checked in, the check and its cancel token (set
only for checks whose result will not be used). -/
structure TargetCheck where
  name : Name
  ci : ConstantInfo
  envD : Kernel.Environment
  task : Task Bool
  tk : IO.CancelToken

/-- Start the checks of the pending targets whose closure is complete in `env` (repeatedly: a started target is admitted,
which may complete another one's closure). Returns the new env and adjacency (started targets admitted), the remaining
pending targets, the started checks and the completeness memo. -/
def startReady (env : Kernel.Environment) (adj : Adj) (pending : Array (Name × ConstantInfo)) (done : Std.HashSet Name) :
    BaseIO (Kernel.Environment × Adj × Array (Name × ConstantInfo) × Array TargetCheck × Std.HashSet Name) := do
  let mut env := env
  let mut adj := adj
  let mut pending := pending
  let mut done := done
  let mut started : Array TargetCheck := #[]
  let mut progress := true
  while progress do
    progress := false
    let mut rest : Array (Name × ConstantInfo) := #[]
    for (d, ci) in pending do
      if (env.find? d).isSome then continue   -- another version is already in E: never a target here
      let rs := (refsOf ci).toArray
      let (ok, done') := closureComplete env adj rs done
      done := done'
      if ok then
        let envD := env
        let tk ← IO.CancelToken.new
        let task := Task.spawn (prio := .dedicated) fun _ => checkTarget envD ci tk
        started := started.push { name := d, ci, envD, task, tk }
        env := kenvAdd env ci
        adj := adj.insert d rs
        progress := true
      else rest := rest.push (d, ci)
    pending := rest
  return (env, adj, pending, started, done)

/-- The started targets the replay of `m` may skip: `m[d]` is exactly the checked constant (and `E`'s), every
kernel-implicit name is absent from both or equal in `envD` and `m`, and every constant reachable from `d` in `m`
(`refsOf`) is in `m`, present in `envD` (the environment of `d`'s check) and equal to `E`'s version (= `envD`'s: entries
are never replaced). The traversal uses `E`'s cached adjacency: for a constant with `m[c] == E[c]` it is `refsOf m[c]`
(equal constants reference the same names), and the traversal stops at the first constant that is not equal.
Whether the check itself succeeded is NOT decided here: the caller must wait for it before it may report an accept.
Cost: one sequential pass over the union of the candidates' closures (cached adjacency, hash sets), the `==`
comparisons of that union in parallel, then one traversal per target (parallel). -/
def verifiedTargets (env : Kernel.Environment) (adj : Adj) (cands : Array TargetCheck) (m : Std.HashMap Name ConstantInfo)
    (nthreads : Nat) (verbose := false) : IO NameSet := do
  if cands.isEmpty then return {}
  -- 1. union of the candidates' closures in E
  let mut seen : Std.HashSet Name := {}
  let mut uarr : Array Name := #[]
  let mut stack : Array Name := #[]
  for t in cands do stack := stack ++ (refsOf t.ci).toArray
  -- and the closure of every `lookupNames` constant of E (the target checks may have unfolded them)
  for p in lookupNames do
    if (env.find? p).isSome then stack := stack.push p
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    uarr := uarr.push c
    if let some rs := adjOf env adj c then
      for r in rs do stack := stack.push r
  -- 2. ok = in m, in E, equal (parallel)
  let okOf : Name → Bool := fun c =>
    match m[c]?, env.find? c with
    | some b, some e => b == e
    | _, _ => false
  let (nchunks, csz) := chunks uarr.size nthreads
  let parts ← parallelFor (min nthreads nchunks) nchunks fun k => Id.run do
    let lo := k * csz
    let hi := min uarr.size (lo + csz)
    let mut bad : Array Name := #[]
    for i in [lo:hi] do
      let c := uarr[i]!
      unless okOf c do bad := bad.push c
    return bad
  let mut notOk : Std.HashSet Name := {}
  for part in parts do
    for (_, bad) in part do
      for c in bad do notOk := notOk.insert c
  -- 3. per target (parallel)
  let one (t : TargetCheck) : Option String := Id.run do
    let some bci := m[t.name]? | return some "not in the final export"
    unless bci == t.ci do return some "final export's version differs from the checked one"
    match env.find? t.name with
    | some eci => unless eci == bci do return some "E's version differs"
    | none => return some "not in E"
    for p in implicitNames do
      match t.envD.find? p, m[p]? with
      | none, none => pure ()
      | some a, some b => unless a == b do return some s!"implicit name {p} differs"
      | some _, none => return some s!"implicit name {p} in envD, not in the final export"
      | none, some _ => return some s!"implicit name {p} absent from envD"
    let mut vis : Std.HashSet Name := {}
    -- the traversal covers the target's closure AND the closure of every `lookupNames` constant of envD: the kernel
    -- looks those up without a syntactic reference and may unfold them (e.g. `Char.ofNat`
    -- -> `Char.ofNatAux` reached through a string literal); every constant of both closures must be in the final export,
    -- in E (= envD's version) and equal there (own name + closure of refs(d) ++ implicit names)
    let mut stack : Array Name := (refsOf t.ci).toArray ++ lookupNames.filter (fun p => (t.envD.find? p).isSome)
    while !stack.isEmpty do
      let c := stack.back!
      stack := stack.pop
      if vis.contains c then continue
      vis := vis.insert c
      if notOk.contains c || !seen.contains c then
        return some (if !m.contains c then s!"closure constant {c} not in the final export"
          else if (env.find? c).isNone then s!"closure constant {c} not in E"
          else s!"closure constant {c} differs between E and the final export")
      if (t.envD.find? c).isNone then return some s!"closure constant {c} absent from envD"
      match adjOf env adj c with
      | some rs => for r in rs do stack := stack.push r
      | none => return some s!"closure constant {c} not in E"
    return none
  let tasks := cands.map fun t => Task.spawn (prio := .dedicated) fun _ => (t.name, one t)
  let mut res : NameSet := {}
  for tk in tasks do
    match tk.get with
    | (n, none) => res := res.insert n
    | (n, some why) => if verbose then IO.eprintln s!"[incr] target {n} not skipped: {why}"
  return res

end PChk.Incr
