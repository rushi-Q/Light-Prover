/-
DeadLetCheck: compares two .olean files of the same module (Lean 4.33): A = original, B = edited (dead `have`s
removed). For every constant: kind, universe parameters and type must be Expr.equal (binder names included); the value
must be Expr.equal ("same"), or alpha-equivalent (Expr.eqv: binder names/infos ignored - hygienic binder names change
when a module's source changes; "alpha"), or alpha-equivalent after contracting every unused `let` (`let x := v; b`
with `x` not in `b` -> `b`) and dropping metadata (`mdata`, ignored by the kernel) in both values ("moddead"). Types: equal or alpha-equivalent (counted in "alphaType").
Anything else is "different". If the module is not certified that way, a second comparison modulo a RENUMBERING of
auxiliary constants (`_proof_N`, `_simp_N`, `match_N`, `_auxLemma.N`: same multiset of aux contents, every other constant
equal once aux references are renamed to their content class) can still certify it: then the SUMMARY carries
`auxmod=1` (raw counts in rawdifferent/rawonlyA/rawonlyB).
  lean --run DeadLetCheck.lean A.olean B.olean      (or --list FILE with lines "NAME A.olean B.olean")
Output: per-constant lines for non-identical constants and a final line
  SUMMARY same=N alpha=A moddead=M different=K onlyA=X onlyB=Y alphaType=T
Exit 0 iff different=0, onlyA=0, onlyB=0.
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def valOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

/-- contract unused lets and drop metadata nodes (the kernel ignores `mdata`; the export format drops its payload) -/
partial def contract (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .letE _ _ _ b _ => if b.hasLooseBVar 0 then none else some (contract (b.lowerLooseBVars 1 1))
    | .mdata _ b => some (contract b)
    | _ => none

/-- compiler-generated auxiliary constants whose numbering depends on elaboration order (`foo._proof_3`,
`foo._simp_1_2`, `foo.match_1`, `_auxLemma.7`) -/
def isAuxName : Name → Bool
  | .str _ s =>
    ["_proof_", "_simp_", "proof_", "match_"].any (fun p => s.startsWith p) &&
      (s.toList.dropWhile (fun c => !c.isDigit)).all (fun c => c.isDigit || c == '_')
  | .num (.str _ s) _ => s == "_auxLemma"
  | _ => false

def normAux (m : Name → Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n us => if isAuxName n then some (.const (m n) us) else none
    | _ => none

/-- binder names and infos erased (Expr.hash depends on them; the key must not) -/
partial def eraseBinders (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .lam _ t b _ => some (.lam `x (eraseBinders t) (eraseBinders b) .default)
    | .forallE _ t b _ => some (.forallE `x (eraseBinders t) (eraseBinders b) .default)
    | .letE _ t v b nd => some (.letE `x (eraseBinders t) (eraseBinders v) (eraseBinders b) nd)
    | _ => none

def auxKey (c : ConstantInfo) : UInt64 :=
  let t := (eraseBinders (normAux (fun _ => `_aux) (contract c.type))).hash
  match valOf? c with
  | some v => mixHash t (eraseBinders (normAux (fun _ => `_aux) (contract v))).hash
  | none => mixHash t 7

/-- equality modulo a renumbering of auxiliary constants: the auxiliary constants of both modules must be the same
multiset of contents (keyed by a structural hash with auxiliary references blanked), and every other constant must be
equal after renaming each auxiliary reference to its content class (and contracting dead lets / dropping mdata) -/
def auxModEqual (ma mb : Array ConstantInfo) : Bool := Id.run do
  let ka := ma.filter (isAuxName ·.name) |>.map auxKey |>.qsort (· < ·)
  let kb := mb.filter (isAuxName ·.name) |>.map auxKey |>.qsort (· < ·)
  if ka != kb then return false
  let mA : Std.HashMap Name Name := ma.foldl (fun m c => if isAuxName c.name then m.insert c.name (Name.mkNum `_aux (auxKey c).toNat) else m) {}
  let mB : Std.HashMap Name Name := mb.foldl (fun m c => if isAuxName c.name then m.insert c.name (Name.mkNum `_aux (auxKey c).toNat) else m) {}
  let fa := fun n => mA.getD n n
  let fb := fun n => mB.getD n n
  let nb : Std.HashMap Name ConstantInfo := mb.foldl (fun m c => if isAuxName c.name then m else m.insert c.name c) {}
  let na := ma.filter (!isAuxName ·.name)
  if na.size != nb.size then return false
  for ca in na do
    match nb[ca.name]? with
    | none => return false
    | some cb =>
      if kindOf ca != kindOf cb || ca.levelParams != cb.levelParams then return false
      if !(normAux fa (contract ca.type)).eqv (normAux fb (contract cb.type)) then return false
      match valOf? ca, valOf? cb with
      | some x, some y => if !(normAux fa (contract x)).eqv (normAux fb (contract y)) then return false
      | none, none => pure ()
      | _, _ => return false
  return true

/-- first structural difference (Expr.eqv) between two expressions: the innermost pair of differing subterms on the
first differing path (children compared left to right) -/
partial def firstDiff (a b : Expr) : Expr × Expr :=
  let pairs : List (Expr × Expr) := match a, b with
    | .app f x, .app g y => [(f, g), (x, y)]
    | .lam _ t x _, .lam _ u y _ => [(t, u), (x, y)]
    | .forallE _ t x _, .forallE _ u y _ => [(t, u), (x, y)]
    | .letE _ t v x _, .letE _ u w y _ => [(t, u), (v, w), (x, y)]
    | .mdata _ x, .mdata _ y => [(x, y)]
    | .proj _ _ x, .proj _ _ y => [(x, y)]
    | _, _ => []
  match pairs.find? (fun (x, y) => !x.eqv y) with
  | some (x, y) => if pairs.length > 0 then firstDiff x y else (a, b)
  | none => (a, b)

/-- compare one pair; prints detail lines prefixed with `pfx`; returns the summary string and ok flag -/
def checkPair (a b : String) (pfx : String) (verbose : Bool) : IO (String × Bool) := do
    let (ma, _) ← readModuleData a
    let (mb, _) ← readModuleData b
    let mapB : Std.HashMap Name ConstantInfo := mb.constants.foldl (fun m c => m.insert c.name c) {}
    let setA : Std.HashSet Name := ma.constants.foldl (fun s c => s.insert c.name) {}
    let mut same := 0; let mut alpha := 0; let mut moddead := 0; let mut different := 0; let mut onlyA := 0
    let mut alphaType := 0
    for ca in ma.constants do
      match mapB[ca.name]? with
      | none =>
        onlyA := onlyA + 1
        IO.println s!"{pfx}onlyA {ca.name}"
      | some cb =>
        let hdr := kindOf ca == kindOf cb && ca.levelParams == cb.levelParams && ca.type.eqv cb.type
        if hdr && !ca.type.equal cb.type then alphaType := alphaType + 1
        if !hdr then
          different := different + 1
          IO.println s!"{pfx}different-statement {ca.name}"
          if verbose then
            IO.println s!"  A: {(toString ca.type).take 600}"
            IO.println s!"  B: {(toString cb.type).take 600}"
        else
          match valOf? ca, valOf? cb with
          | some x, some y =>
            if x.equal y then same := same + 1
            else if x.eqv y then alpha := alpha + 1
            else if (contract x).eqv (contract y) then
              moddead := moddead + 1
              IO.println s!"{pfx}moddead {ca.name}"
            else
              different := different + 1
              IO.println s!"{pfx}different-value {ca.name}"
              if verbose then
                let (dx, dy) := firstDiff (contract x) (contract y)
                IO.println s!"  A: {(toString dx).take 1500}"
                IO.println s!"  B: {(toString dy).take 1500}"
          | none, none => same := same + 1
          | _, _ =>
            different := different + 1
            IO.println s!"{pfx}different-kind {ca.name}"
    let onlyB := (mb.constants.filter fun c => !setA.contains c.name).size
    for c in mb.constants do
      if !setA.contains c.name then IO.println s!"{pfx}onlyB {c.name}"
    let ok := different == 0 && onlyA == 0 && onlyB == 0
    if !ok && auxModEqual ma.constants mb.constants then
      -- certified modulo renumbering of auxiliary constants (the raw counts are kept in raw*)
      return (s!"SUMMARY same={same} alpha={alpha} moddead={moddead} different=0 onlyA=0 onlyB=0 alphaType={alphaType} auxmod=1 rawdifferent={different} rawonlyA={onlyA} rawonlyB={onlyB}", true)
    return (s!"SUMMARY same={same} alpha={alpha} moddead={moddead} different={different} onlyA={onlyA} onlyB={onlyB} alphaType={alphaType}", ok)

def main (args : List String) : IO UInt32 := do
  let verbose := (← IO.getEnv "DLC_VERBOSE").isSome
  match args with
  | ["--list", f] =>
    -- batch mode: lines "NAME A.olean B.olean"; one "NAME SUMMARY ..." line per pair (errors: "NAME ERROR msg")
    let mut allOk := true
    for line in (← IO.FS.lines f) do
      match line.splitOn " " with
      | [n, a, b] =>
        try
          let (sm, ok) ← checkPair a b s!"{n} " verbose
          IO.println s!"{n} {sm}"
          allOk := allOk && ok
        catch e =>
          IO.println s!"{n} ERROR {e}"
          allOk := false
      | _ => pure ()
    return (if allOk then 0 else 1)
  | [a, b] =>
    let (sm, ok) ← checkPair a b "" verbose
    IO.println sm
    return (if ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: lean --run DeadLetCheck.lean A.olean B.olean | --list FILE"
    return 2
