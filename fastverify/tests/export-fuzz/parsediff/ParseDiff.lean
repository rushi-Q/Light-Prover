import LeanExport.Parse
import FastParse
import PChk.PersistentRead

/-!
`parsediff FILE...` (parser agreement): for every export file, run
  (1) the OFFICIAL reader `LeanExport.parseStream` (Lean 4.36),
  (2) the trusted fast reader's fast path `FastExport.parseFileStream?` (used by ccmp for the challenge),
  (3) `PChk.parseFileStreamP?` (used by ccmp for the solution and by pleanchecker),
  (4) `FastExport.parseBytesPar?` with k = 1 and k = 7 tokenizer tasks (whole-file variant),
and compare STRICTLY: same constOrder, same key set, every ConstantInfo field-equal with `Expr.equal` (binder names and
binder infos included). The exactness contract of FastParse: (2)/(3) return `none` or exactly (1)'s result.
One output line per file:  <status>\t<file>\t<detail>
  status: SAME (fast path agreed), FALLBACK (fast path declined -> official result used), BOTHFAIL (official throws and
  the fast path declined), DIVERGE-* (a contract violation: fast path returned something else than the official reader).
-/
open Lean

def lvlEq (a b : List Level) : Bool := a == b

def ciEq : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type && a.isUnsafe == b.isUnsafe
  | .defnInfo a, .defnInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type
      && a.value.equal b.value && a.hints == b.hints && a.safety == b.safety && a.all == b.all
  | .thmInfo a, .thmInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type
      && a.value.equal b.value && a.all == b.all
  | .opaqueInfo a, .opaqueInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type
      && a.value.equal b.value && a.isUnsafe == b.isUnsafe && a.all == b.all
  | .quotInfo a, .quotInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type && a.kind == b.kind
  | .inductInfo a, .inductInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type
      && a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors
      && a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type
      && a.induct == b.induct && a.cidx == b.cidx && a.numParams == b.numParams && a.numFields == b.numFields
      && a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type
      && a.all == b.all && a.numParams == b.numParams && a.numIndices == b.numIndices && a.numMotives == b.numMotives
      && a.numMinors == b.numMinors && a.k == b.k && a.isUnsafe == b.isUnsafe
      && a.rules.length == b.rules.length
      && (a.rules.zip b.rules).all fun (r, s) => r.ctor == s.ctor && r.nfields == s.nfields && r.rhs.equal s.rhs
  | _, _ => false

/-- none = equal; some msg = first difference -/
def envDiff (o : LeanExport.ExportedEnv) (m : Std.HashMap Name ConstantInfo) (order : Array Name) : Option String := Id.run do
  if o.constOrder.size != order.size then
    return some s!"constOrder size {o.constOrder.size} vs {order.size}"
  for i in [0:order.size] do
    if o.constOrder[i]! != order[i]! then
      return some s!"constOrder[{i}] {o.constOrder[i]!} vs {order[i]!}"
  if o.constMap.size != m.size then
    return some s!"constMap size {o.constMap.size} vs {m.size}"
  for (n, ci) in o.constMap.toList do
    match m[n]? with
    | none => return some s!"missing {n}"
    | some cj => if !ciEq ci cj then return some s!"constant differs: {n}"
  return none

/-- run one fast variant and compare it with the official result right away (so at most two environments are alive) -/
def cmpOne (off : Except IO.Error LeanExport.ExportedEnv) (lbl : String)
    (act : IO (Option (Std.HashMap Name ConstantInfo × Array Name))) : IO (String × Nat × Bool) := do
  let r ← (act).toBaseIO
  let r := match r with | .ok x => x | .error _ => none
  match r with
  | none => return (s!"{lbl}:none", 0, false)
  | some (m, o) =>
    match off with
    | .error _ => return (s!"{lbl}:SOME({o.size}) but official failed", 1, true)
    | .ok e => match envDiff e m o with
      | none => return (s!"{lbl}:same", 1, false)
      | some d => return (s!"{lbl}:DIFF {d}", 1, true)

unsafe def checkFile (f : String) (streamOnly : Bool) : IO String := do
  let off ← (IO.FS.withFile f .read fun h => LeanExport.parseStream (.ofHandle h)).toBaseIO
  let offS := match off with | .ok e => s!"official ok {e.constOrder.size} consts" | .error e => s!"official error: {(toString e).take 120}"
  let mut res : Array String := #[]
  let mut nfast := 0
  let mut bad := false
  let mut nvar := 0
  -- (2) streaming fast path (ccmp: challenge), (3) persistent streaming fast path (ccmp: solution; pleanchecker)
  let (s2, n2, b2) ← cmpOne off "stream" ((FastExport.parseFileStream? f).map (·.map fun (m, o, _, _) => (m, o)))
  res := res.push s2; nfast := nfast + n2; bad := bad || b2; nvar := nvar + 1
  let (s3, n3, b3) ← cmpOne off "streamP" ((PChk.parseFileStreamP? f).map (·.map fun (m, o, _, _) => (m, o)))
  res := res.push s3; nfast := nfast + n3; bad := bad || b3; nvar := nvar + 1
  unless streamOnly do
    -- (4) whole-file variants with 1 and 7 tokenizer tasks
    let (s4, n4, b4) ← cmpOne off "bytes1" (do let b ← IO.FS.readBinFile f; pure ((FastExport.parseBytesPar? b 1).map fun (m, o, _) => (m, o)))
    res := res.push s4; nfast := nfast + n4; bad := bad || b4; nvar := nvar + 1
    let (s5, n5, b5) ← cmpOne off "bytes7" (do let b ← IO.FS.readBinFile f; pure ((FastExport.parseBytesPar? b 7).map fun (m, o, _) => (m, o)))
    res := res.push s5; nfast := nfast + n5; bad := bad || b5; nvar := nvar + 1
  let st :=
    if bad then (match off with | .error _ => "DIVERGE-FASTOK-OFFICIALFAIL" | .ok _ => "DIVERGE-ENV")
    else if nfast == 0 then (match off with | .ok _ => "FALLBACK" | .error _ => "BOTHFAIL")
    else if nfast < nvar then "PARTIAL"
    else "SAME"
  return s!"{st}\t{f}\t{offS}; {String.intercalate " " res.toList}"

unsafe def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  let streamOnly := (← IO.getEnv "PD_STREAM_ONLY").isSome
  for f in args do
    let line ← checkFile f streamOnly
    IO.println line
    (← IO.getStdout).flush
    if line.startsWith "DIVERGE" then bad := bad + 1
  return if bad > 0 then 1 else 0
