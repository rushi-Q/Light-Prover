/-
Shared trusted delta/overlay core for `ccmp-warm` and `pleanchecker-warm`.

Soundness invariants (soundness rules S1-S5, docs/concepts/soundness.md):
  Given a closed, kernel-verified base export B and a candidate delta NDJSON export D:
  1. `refsOf ci` is a strict superset of BOTH `Lake.Check.runForUsedConsts ci` and `PChk.Incr.refsOf ci`
     (including `opaqueInfo.value`, `Expr.proj` struct names, inductive `all`/`ctors`, ctor `induct`,
     recursor `all`/`rules`, and `Quot -> Eq`).
  2. Inductive blocks `{inducts in all} U {ctors} U {recs with same all}` are treated atomically:
     if any member is overridden or dirty, every member of the block enters `dirty`.
  3. `dirty` is the reverse-transitive closure in B of all overridden base constants (`n in D ∩ B` with
     `!ciStrictEqual D[n] B[n]`), closed under atomic inductive blocks.
  4. Therefore `K = dom(B) \ dirty` is strictly downward-closed under `refsOf` in B: no constant in K
     references any constant outside K.
  5. If D introduces, overrides, or dirties ANY kernel-implicit name (`implicitNames`, matching
     S08's reviewed `PChk.Incr.implicitNames` + comparator `primitiveTargets`) or ANY quotient name
     (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`), `computeOverlay` returns `.fallback` (never accepts
     on the delta path; caller falls back to full export + cold check).
  6. Closure check: every constant `(n, ci)` in D must have every `r in refsOf ci` present in
     `dom(D) U K`. A missing reference in a safe non-partial constant is `.reject`; in an unsafe or
     partial constant it is `.fallback` (fail-closed).
  7. Both `ccmp-warm` and `pleanchecker-warm` run THIS exact module and emit `(deltaConsts, overridden,
     dirtyCount, effectiveCount)` in their structured JSON verdict; `fvcheckd` requires all legs to agree.
-/
import Lean.Declaration
import Lean.Util.FoldConsts
import Lake.Check.Util
import PChk.Par

namespace WarmBase
open Lean

/-- Exact kernel-implicit names (S08 reviewed `PChk.Incr.implicitNames` + comparator `primitiveTargets`). -/
def implicitNames : Array Name := #[
  `Nat, `Nat.zero, `Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod, `Nat.beq,
  `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight,
  `String, `String.ofList, `String.mk, `Char, `Char.ofNat, `List, `List.cons, `List.nil,
  `Bool, `Bool.true, `Bool.false, `eagerReduce, `Eq, `Eq.refl,
  `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `dontcare,
  `optParam, `autoParam, `semiOutParam, `outParam]

def quotNames : Array Name := #[`Quot, `Quot.mk, `Quot.lift, `Quot.ind]
def quotTargets : List Name := [`Quot.mk, `Quot.lift, `Quot.ind]

def isImplicitOrQuot (n : Name) : Bool :=
  implicitNames.contains n || quotNames.contains n

/-- Strict structural equality on `ConstantInfo` (uses `Expr.equal`, stronger than `Expr.eqv`).
If a delta changes even a binder name or metadata flag, it is treated as overridden and re-checked. -/
def ciStrictEqual : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type && a.isUnsafe == b.isUnsafe
  | .defnInfo a, .defnInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type && a.value.equal b.value &&
    a.hints == b.hints && a.safety == b.safety && a.all == b.all
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type && a.value.equal b.value &&
    a.all == b.all
  | .opaqueInfo a, .opaqueInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type && a.value.equal b.value &&
    a.isUnsafe == b.isUnsafe && a.all == b.all
  | .quotInfo a, .quotInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type && a.kind == b.kind
  | a@(.inductInfo _), b@(.inductInfo _) => PChk.ciStrictEq a b
  | a@(.ctorInfo _), b@(.ctorInfo _) => PChk.ciStrictEq a b
  | a@(.recInfo _), b@(.recInfo _) => PChk.ciStrictEq a b
  | _, _ => false

/-- Strict superset of `Lake.Check.runForUsedConsts` AND `PChk.Incr.refsOf` (excluding self). -/
def refsOf (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := ci.getUsedConstantsAsSet
  s := ci.type.foldConsts s fun c acc => acc.insert c
  if let some val := ci.value? (allowOpaque := true) then
    s := val.foldConsts s fun c acc => acc.insert c
  match ci with
  | .inductInfo v =>
    for n in v.all do s := s.insert n
    for n in v.ctors do s := s.insert n
  | .ctorInfo v =>
    s := s.insert v.induct
  | .recInfo v =>
    for n in v.all do s := s.insert n
    for r in v.rules do
      s := s.insert r.ctor
      s := r.rhs.foldConsts s fun c acc => acc.insert c
  | .quotInfo _ =>
    s := s.insert `Eq
  | _ => pure ()
  return s

/-- Run `f` over chunks `0..nchunks` in parallel across `nthreads` tasks. -/
def parChunks {α : Type} (n nthreads : Nat) (f : Nat → Nat → α) : IO (Array α) := do
  let nt := max 1 nthreads
  let nchunks := max 1 (min (nt * 8) (n / 256 + 1))
  let csz := (n + nchunks - 1) / nchunks
  if nchunks == 1 then
    return #[f 0 n]
  let mut tasks := Array.mkEmpty nchunks
  for c in [0:nchunks] do
    let lo := min n (c * csz)
    let hi := min n (lo + csz)
    tasks := tasks.push (Task.spawn (prio := .dedicated) fun _ => f lo hi)
  let mut out := Array.mkEmpty nchunks
  for t in tasks do
    out := out.push t.get
  return out

structure BaseIndex where
  constMap : Std.HashMap Name ConstantInfo
  arr : Array (Name × ConstantInfo)
  ids : Std.HashMap Name Nat
  /-- Forward dependencies (by dense id) under `refsOf`. -/
  fwdDeps : Array (Array Nat)
  /-- CSR reverse-adjacency list over `fwdDeps` for O(|dirty|) reverse reachability. -/
  revStart : Array Nat
  revAdj : Array Nat
  /-- For any constant in an inductive block (induct/ctor/rec), all dense ids of that block. -/
  blockMembers : Array (Array Nat)
  /-- `implicitNames` present in `B`. -/
  implicitSet : NameSet
  /-- 1 if constant `i` has a direct `refsOf` reference not present in `B`. -/
  directMissing : ByteArray
  /-- `B` is closed for safe non-partial constants (0 missing direct refs). -/
  isClosed : Bool

/-- Build `BaseIndex` once from a parsed base export `B`. -/
def buildBaseIndex (constMap : Std.HashMap Name ConstantInfo) (nthreads : Nat) : IO BaseIndex := do
  let arr := constMap.toArray
  let n := arr.size
  let mut ids : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity n
  for h : i in [0:n] do
    ids := ids.insert arr[i].1 i
  -- Compute forward deps and direct missing flags in parallel
  let parts ← parChunks n nthreads fun lo hi => Id.run do
    let mut deps := Array.mkEmpty (hi - lo)
    let mut miss := Array.mkEmpty (hi - lo)
    for i in [lo:hi] do
      let mut d : Array Nat := #[]
      let mut m := false
      for r in refsOf arr[i]!.2 do
        match ids[r]? with
        | some j => d := d.push j
        | none => m := true
      deps := deps.push d
      miss := miss.push m
    return (deps, miss)
  let mut fwdDeps : Array (Array Nat) := Array.mkEmpty n
  let mut directMissing := ByteArray.mk (Array.replicate n 0)
  let mut closed := true
  for (ds, ms) in parts do
    for k in [0:ds.size] do
      let idx := fwdDeps.size
      fwdDeps := fwdDeps.push ds[k]!
      if ms[k]! then
        directMissing := directMissing.set! idx 1
        let ci := arr[idx]!.2
        if !ci.isUnsafe && !ci.isPartial then
          closed := false
  -- Build atomic inductive block map keyed by `all` list
  let mut byAll : Std.HashMap (List Name) (Array Nat) := {}
  for h : i in [0:n] do
    match arr[i].2 with
    | .inductInfo v =>
      let mut mem := (byAll[v.all]?).getD #[]
      mem := mem.push i
      for c in v.ctors do
        if let some ci := ids[c]? then mem := mem.push ci
      byAll := byAll.insert v.all mem
    | .recInfo v =>
      let mut mem := (byAll[v.all]?).getD #[]
      mem := mem.push i
      byAll := byAll.insert v.all mem
    | _ => pure ()
  let mut blockMembers : Array (Array Nat) := Array.replicate n #[]
  for (_, mem) in byAll.toArray do
    -- deduplicate small block member list
    let mut uniq : Array Nat := #[]
    for x in mem do
      if !uniq.contains x then uniq := uniq.push x
    for x in uniq do
      blockMembers := blockMembers.set! x uniq
  -- Build CSR reverse-adjacency list for `fwdDeps`
  let mut revStart : Array Nat := Array.replicate (n + 1) 0
  for d in fwdDeps do
    for j in d do
      revStart := revStart.set! (j + 1) (revStart[j + 1]! + 1)
  for i in [0:n] do
    revStart := revStart.set! (i + 1) (revStart[i + 1]! + revStart[i]!)
  let mut fill := revStart
  let mut revAdj : Array Nat := Array.replicate revStart[n]! 0
  for i in [0:n] do
    for j in fwdDeps[i]! do
      revAdj := revAdj.set! fill[j]! i
      fill := fill.set! j (fill[j]! + 1)
  let mut implicitSet : NameSet := {}
  for p in implicitNames do
    if ids.contains p then implicitSet := implicitSet.insert p
  return {
    constMap, arr, ids, fwdDeps, revStart, revAdj, blockMembers, implicitSet,
    directMissing, isClosed := closed
  }

/-- Reverse reachability from `seeds` in CSR `revStart`/`revAdj`, closed under `blockMembers`.
Runs in O(|dirty| + edges(dirty)), independent of `|B|`. -/
def reachRevDirty (base : BaseIndex) (seeds : Array Nat) : Array Nat × NameSet := Id.run do
  if seeds.isEmpty then return (#[], {})
  let mut seen : Std.HashSet Nat := {}
  let mut stack : Array Nat := #[]
  let mut outIds : Array Nat := #[]
  let mut outNames : NameSet := {}
  for s in seeds do
    if !seen.contains s then
      seen := seen.insert s
      stack := stack.push s
  while !stack.isEmpty do
    let j := stack.back!
    stack := stack.pop
    outIds := outIds.push j
    outNames := outNames.insert base.arr[j]!.1
    -- Atomic inductive block expansion
    for bm in base.blockMembers[j]! do
      if !seen.contains bm then
        seen := seen.insert bm
        stack := stack.push bm
    -- Reverse dependency edges
    let lo := base.revStart[j]!
    let hi := base.revStart[j + 1]!
    for k in [lo:hi] do
      let u := base.revAdj[k]!
      if !seen.contains u then
        seen := seen.insert u
        stack := stack.push u
  return (outIds, outNames)

/-- Forward reachability inside `K = B \ dirtySet` from a set of clean base ids. -/
def reachFwdClean (base : BaseIndex) (dirtySet : NameSet) (seeds : Array Nat) : Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut stack : Array Nat := #[]
  let mut out : Array Nat := #[]
  for s in seeds do
    if !seen.contains s && !dirtySet.contains base.arr[s]!.1 then
      seen := seen.insert s
      stack := stack.push s
  while !stack.isEmpty do
    let i := stack.back!
    stack := stack.pop
    out := out.push i
    for dep in base.fwdDeps[i]! do
      if !seen.contains dep && !dirtySet.contains base.arr[dep]!.1 then
        seen := seen.insert dep
        stack := stack.push dep
  return out

inductive OverlayStop where
  | fallback (reason : String)
  | reject (reason : String)

structure OverlayPlan where
  deltaConsts : Nat
  overriddenCount : Nat
  freshCount : Nat
  dirtyIds : Array Nat
  dirtySet : NameSet
  /-- Constants from `D` that must be kernel-checked (all fresh constants + all constants in `dirtySet`). -/
  toCheck : Std.HashMap Name ConstantInfo
  /-- Exact number of constants in effective env `E_eff = (B \ dirty) U D`. -/
  effectiveCount : Nat

/-- Compute the exact delta overlay plan, enforcing every S1-S5 safety guard. -/
def computeOverlay (base : BaseIndex) (dmap : Std.HashMap Name ConstantInfo) :
    Except OverlayStop OverlayPlan := do
  let mut overriddenIds : Array Nat := #[]
  let mut freshNames : Array Name := #[]
  for (n, ci) in dmap.toArray do
    if isImplicitOrQuot n then
      match base.ids[n]? with
      | some i =>
        if !ciStrictEqual ci base.arr[i]!.2 then
          throw (.fallback s!"kernel-implicit or quotient constant '{n}' overridden in delta")
      | none =>
        throw (.fallback s!"kernel-implicit or quotient constant '{n}' introduced in delta")
    match base.ids[n]? with
    | some i =>
      if !ciStrictEqual ci base.arr[i]!.2 then
        overriddenIds := overriddenIds.push i
    | none =>
      freshNames := freshNames.push n
  let (dirtyIds, dirtySet) := reachRevDirty base overriddenIds
  for did in dirtyIds do
    let dn := base.arr[did]!.1
    if isImplicitOrQuot dn then
      throw (.fallback s!"kernel-implicit or quotient constant '{dn}' dirtied by delta")
  -- Closure check: every constant in D must reference only constants in D U (B \ dirtySet)
  let mut toCheck : Std.HashMap Name ConstantInfo := {}
  let mut dirtyResupplied : Nat := 0
  for (n, ci) in dmap.toArray do
    let inBase := base.ids.contains n
    let isDirty := dirtySet.contains n
    if !inBase || isDirty then
      toCheck := toCheck.insert n ci
      if isDirty then dirtyResupplied := dirtyResupplied + 1
    for r in refsOf ci do
      let ok := dmap.contains r || (base.ids.contains r && !dirtySet.contains r)
      if !ok then
        if ci.isUnsafe || ci.isPartial then
          throw (.fallback s!"unsafe/partial constant '{n}' references missing/dirty constant '{r}'")
        else
          throw (.reject s!"Constant not found in solution '{r}' (referenced by '{n}')")
  let effectiveCount := base.arr.size - dirtySet.size + freshNames.size + dirtyResupplied
  return {
    deltaConsts := dmap.size
    overriddenCount := overriddenIds.size
    freshCount := freshNames.size
    dirtyIds
    dirtySet
    toCheck
    effectiveCount
  }

/-- Virtual lookup in `E_eff = (B \ dirtySet) U D`. -/
@[inline] def lookupEff (base : BaseIndex) (dmap : Std.HashMap Name ConstantInfo)
    (dirtySet : NameSet) (n : Name) : Option ConstantInfo :=
  match dmap[n]? with
  | some ci => some ci
  | none => if dirtySet.contains n then none else base.constMap[n]?

/-- Escape a string as a JSON string literal (exact RFC 8259). -/
def jsonEscape (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c    =>
      if c.toNat < 0x20 then
        let hexDigit (k : Nat) : Char :=
          if k < 10 then Char.ofNat ('0'.toNat + k) else Char.ofNat ('a'.toNat + k - 10)
        let hi := hexDigit (c.toNat / 16)
        let lo := hexDigit (c.toNat % 16)
        acc ++ s!"\\u00{hi}{lo}"
      else acc.push c
  "\"" ++ body ++ "\""

end WarmBase
