import Std.Data.HashMap
import Std.Data.HashSet
import Lean.Data.Json
import Lean.Util.ReplaceExpr
import Lake.Check.Util
import FastParse
import FrontierJudge

/-!
# Fast UNTRUSTED preparer of the frontier construction: `fvfrontier-prep`

Nothing here decides a verdict. The verdict of `tools/frontier/frontier.py` comes from two runs of the UNCHANGED trusted
check (`check/sound/check-sound.sh`): check A judges the frontier challenge C' against the official challenge C, check B
judges the rewritten solution S' against C'. A bug here can only make one of them reject or give no verdict.

  fvfrontier-prep scan CONFIG EXPORT [--list FILE] [--axioms FILE]
      the frontier of the targets' closure (D05 semantics): a non-target THEOREM whose own value mentions `sorryAx` is a
      frontier lemma (with --list: only listed ones) and its value is not followed; blockers (sorry in a target / in a
      definition, other axioms, missing constants) with a path from a target; the printed statement of every frontier
      lemma. One JSON object on stdout.
  fvfrontier-prep mint CHALLENGE_EXPORT SOLUTION_PRIME_EXPORT FRONTIER_FILE OUT
      C' = CHALLENGE_EXPORT verbatim + the closure in S' of the frontier axioms (their types, every constant those
      mention, definition bodies, whole inductive blocks), stopping at constants the challenge already has, re-emitted
      with fresh dense indices after the challenge's own. JSON stats on stdout.
-/

namespace FrontierPrep
open Lean FrontierJudge

def readNames (p : System.FilePath) : IO (Array String) := do
  let t ← IO.FS.readFile p
  return (t.splitOn "\n").toArray.map (·.trimAscii.toString) |>.filter (fun l => !l.isEmpty && !l.startsWith "#")

def nameOfStr (s : String) : Name := s.toName

/-! ## scan -/

def valueMentionsSorry (ci : ConstantInfo) : Bool :=
  match ci.value? (allowOpaque := true) with
  | some v => v.getUsedConstants.contains ``sorryAx
  | none => false

/-- the canonical names of an allowed list: each line read by `String.toName` (the parser the trusted wrapper mirrors);
a line that is not a Lean name names nothing -/
def allowedNames (lines : Array String) : Std.HashSet Name :=
  lines.foldl (fun acc l => let n := l.toName; if n.isAnonymous then acc else acc.insert n) {}

/-- an allowed-list entry matches EXACTLY the declaration of that canonical name. A PRIVATE declaration
`_private.<module>.0.<x>` must be listed with its full kernel name, module included (the earlier "source spelling"
match let a private `<x>` of ANY module stand in for an allowed `<x>`); check-frontier.sh enforces the same rule on F
itself in trusted code. -/
def allowedHas (allowed : Std.HashSet Name) (n : Name) : Bool := allowed.contains n

/-- informational only (the ledger probe of an earlier result, never a frontier decision): the public spelling of a
private name `_private.<module>.0.<x>` -/
def privateSourceMatch (p : String) (n : Name) : Bool := Id.run do
  let rec stripPriv : Name → Option Name
    | .str q str => (stripPriv q).map (Name.str · str)
    | .num q k => if k == 0 && q.getRoot == `_private then some .anonymous else (stripPriv q).map (Name.num · k)
    | .anonymous => none
  if n.getRoot == `_private then
    if let some pub := stripPriv n then
      return toString pub == p
  return false

def scanEnv (cfgPath : System.FilePath) (env : Std.HashMap Name ConstantInfo) (list? axioms? : Option System.FilePath)
    (probe? : Option System.FilePath := none) :
    IO (Json × Array Name × Array Name × Std.HashMap Name (Array Name) × Array Name × Array Name) := do
  let cfgJson ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
  let cfg : FrontierJudge.Config ← IO.ofExcept (fromJson? cfgJson)
  let T := cfg.theorem_names.map nameOfStr
  let D := cfg.definition_names.getD #[] |>.map nameOfStr
  let A : Std.HashSet Name := Std.HashSet.ofArray (cfg.permitted_axioms.map nameOfStr)
  let listedLines? : Option (Array String) ← match list? with
    | some p => pure (some (← readNames p))
    | none => pure none
  let listed? : Option (Std.HashSet Name) := listedLines?.map allowedNames
  let extraAx : Std.HashSet String ← match axioms? with
    | some p => pure (Std.HashSet.ofArray (← readNames p))
    | none => pure {}
  let tset : Std.HashSet Name := Std.HashSet.ofArray T
  -- the official used-name lists of every constant (with and without the value) + "value mentions sorryAx", in parallel
  let arr := env.toArray
  let nchunks := max 1 (min 256 (arr.size / 256 + 1))
  let csz := (arr.size + nchunks - 1) / nchunks
  let tasks := (List.range nchunks).toArray.map fun c => Task.spawn (prio := .dedicated) fun _ => Id.run do
    let lo := min arr.size (c * csz); let hi := min arr.size (lo + csz)
    let mut out : Array (Array Name × Array Name × Bool) := Array.mkEmpty (hi - lo)
    for i in [lo:hi] do
      let ci := arr[i]!.2
      out := out.push (usedNames ci,
        usedNames (.axiomInfo { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false }),
        valueMentionsSorry ci)
    return out
  let mut pre : Std.HashMap Name (Array Name × Array Name × Bool) := Std.HashMap.emptyWithCapacity arr.size
  let mut k := 0
  for t in tasks do
    for x in t.get do
      pre := pre.insert arr[k]!.1 x; k := k + 1
  let mut seen : Std.HashSet Name := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut stack : Array Name := (T ++ D).reverse
  let mut frontier : Array Name := #[]
  let mut frontierAx : Array Name := #[]
  let mut sorryTargets : Array Name := #[]
  let mut sorryDefs : Array Name := #[]
  let mut otherAx : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut sorryOutside : Array Name := #[]
  for r in T ++ D do seen := seen.insert r
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    let some ci := env[n]? | do missing := missing.push n; continue
    let (refsAll, refsType, vSorry) := pre[n]?.getD (usedNames ci, #[], valueMentionsSorry ci)
    let mut followValue := true
    match ci with
    | .axiomInfo _ =>
      if !A.contains n && n != ``sorryAx then
        if extraAx.contains (toString n) then frontierAx := frontierAx.push n else otherAx := otherAx.push n
    | .thmInfo _ =>
      if tset.contains n then
        if vSorry then sorryTargets := sorryTargets.push n
      else if vSorry then
        if (listed?.map (allowedHas · n)).getD true then
          frontier := frontier.push n; followValue := false
        else sorryOutside := sorryOutside.push n
    | .defnInfo _ | .opaqueInfo _ =>
      if vSorry then sorryDefs := sorryDefs.push n
    | _ => pure ()
    let refs : Array Name := if followValue then refsAll else refsType
    for m in refs do
      if !seen.contains m then
        seen := seen.insert m
        parent := parent.insert m n
        stack := stack.push m
  -- (diagnostics only): the STATEMENT closure as Lake's compareAt walks it - from the targets' types, then every
  -- non-target constant with its FULL value. An open lemma met there is compared BY VALUE with the official challenge
  -- (where it is sorried), so no conditional verdict exists for it: a blocker, reported with its path.
  let tdset : Std.HashSet Name := Std.HashSet.ofArray (T ++ D)
  let mut sSeen : Std.HashSet Name := tdset   -- targets are compared by type only; their types are the roots
  let mut sParent : Std.HashMap Name Name := {}
  let mut sStack : Array Name := #[]
  for r in T ++ D do
    if let some ci := env[r]? then
      let tyRefs : Array Name := match pre[r]? with
        | some x => x.2.1
        | none => usedNames (.axiomInfo { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false })
      for m in tyRefs do
        if !sSeen.contains m then
          sSeen := sSeen.insert m; sParent := sParent.insert m r; sStack := sStack.push m
  while h : sStack.size > 0 do
    let n := sStack[sStack.size - 1]
    sStack := sStack.pop
    let some ci := env[n]? | continue
    let refs : Array Name := if tdset.contains n then (pre[n]?.map (·.2.1)).getD #[] else (pre[n]?.map (·.1)).getD (usedNames ci)
    for m in refs do
      if !sSeen.contains m then
        sSeen := sSeen.insert m; sParent := sParent.insert m n; sStack := sStack.push m
  let stmtOpen : Array Name := frontier.filter (fun n => sSeen.contains n)
  let stmtDefs : Array Name := sorryDefs.filter (fun n => sSeen.contains n)
  let spath (n : Name) : Json := Id.run do
    let mut out := #[n]; let mut cur := n
    for _ in [0:64] do
      match sParent[cur]? with
      | some p => out := out.push p; cur := p
      | none => break
    return Json.arr (out.reverse.map nameJ)
  let path (n : Name) : Json := Id.run do
    let mut out := #[n]; let mut cur := n
    for _ in [0:64] do
      match parent[cur]? with
      | some p => out := out.push p; cur := p
      | none => break
    return Json.arr (out.reverse.map nameJ)
  let sortN (a : Array Name) := a.qsort (fun x y => toString x < toString y)
  let fr := sortN frontier
  let stm := Json.arr <| (fr ++ sortN frontierAx).map fun n =>   -- open lemmas, then declared project axioms (--axioms)
    let ci := env[n]!
    let ty := toString ci.type
    Json.mkObj [("name", nameJ n), ("kind", jstr (kindOf ci)), ("level_params", Json.arr (ci.levelParams.toArray.map nameJ)),
      ("type", jstr ty), ("canonical_sorry", Json.bool (isCanonicalSorry (ci.value?.getD (.const ``Unit []))) ),
      ("used_by", match parent[n]? with | some p => nameJ p | none => Json.null)]
  -- probe (ledger support, untrusted): what became of earlier open lemmas? open / proved (still used, no sorry of its own) /
  -- absent (no longer in the targets' closure: dropped, maybe still sorried in the sources) / other
  let probeJ : Json ← match probe? with
    | none => pure Json.null
    | some pf => do
      let ps ← readNames pf
      let frSet : Std.HashSet Name := Std.HashSet.ofArray frontier
      let outSet : Std.HashSet Name := Std.HashSet.ofArray sorryOutside
      let mut byStr : Std.HashMap String Name := {}
      for m in seen.toArray do byStr := byStr.insert (toString m) m
      let mut kv : List (String × Json) := []
      for p in ps do
        let hit : Option Name := match byStr[p]? with
          | some m => some m
          | none => seen.toArray.find? (fun m => privateSourceMatch p m)
        let st : String := match hit with
          | none => "absent"
          | some m => if frSet.contains m then "open" else if outSet.contains m then "open-not-allowed"
            else match env[m]? with | some (.thmInfo _) => "proved" | some _ => "other" | none => "absent"
        kv := kv ++ [(p, jstr st)]
      pure (Json.mkObj kv)
  let frSetC : Std.HashSet Name := Std.HashSet.ofArray fr
  let closed : Array String := match listedLines? with
    | some l => ((l.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]).filter
        (fun s => !frSetC.contains s.toName)).qsort (· < ·)
    | none => #[]
  return (Json.mkObj [
    ("tool", jstr "fvfrontier-prep scan"), ("targets", Json.arr (T.map nameJ)), ("definition_targets", Json.arr (D.map nameJ)),
    ("frontier", Json.arr (fr.map nameJ)), ("frontier_axioms", Json.arr ((sortN frontierAx).map nameJ)),
    ("statements", stm), ("frontier_closed", Json.arr (closed.map jstr)),
    ("sorry_in_targets", Json.arr ((sortN sorryTargets).map nameJ)),
    ("sorry_in_definitions", Json.arr ((sortN sorryDefs).map fun d => Json.mkObj [("name", nameJ d), ("path", path d)])),
    ("other_axioms", Json.arr ((sortN otherAx).map fun d => Json.mkObj [("name", nameJ d), ("path", path d)])),
    ("missing", Json.arr ((sortN missing).map nameJ)), ("closure_size", (seen.size : Nat)),
    ("sorry_outside_allowed", Json.arr ((sortN sorryOutside).map fun d => Json.mkObj [("name", nameJ d), ("path", path d)])),
    ("open_lemma_in_statement", Json.arr ((sortN stmtOpen).map fun d => Json.mkObj [("name", nameJ d), ("path", spath d)])),
    ("sorry_def_in_statement", Json.arr ((sortN stmtDefs).map nameJ)),
    ("probe", probeJ),
    ("export_constants", (env.size : Nat)), ("sorry_reached", Json.bool (seen.contains ``sorryAx)),
    ("blockers", Json.bool (!(sorryTargets.isEmpty && sorryDefs.isEmpty && otherAx.isEmpty && missing.isEmpty && sorryOutside.isEmpty
      && stmtOpen.isEmpty)))],
    fr, sortN frontierAx, pre.fold (fun m k v => m.insert k v.1) {}, sortN sorryTargets, sortN sorryDefs)

def scan (cfgPath exportPath : System.FilePath) (list? axioms? : Option System.FilePath) : IO Json := do
  let sol ← FastExport.parseExportFile exportPath
  return (← scanEnv cfgPath sol.constMap list? axioms?).1

/-! ## mint -/

/-- next free indices of a canonical (dense) export: 1 + #name records, 1 + #level records, #expr records. Classified by
the record's first key (lean4export writes sorted keys): names `{"in":`, levels `{"il":`, expressions `{"ie":` or a first
key that sorts before "ie" (`app`, `bvar`, `const`, `forallE`); declarations start with `{"axiom"`, `{"def"`, `{"thm"`,
`{"opaque"`, `{"quot"`, `{"inductive"`. (Untrusted: wrong indices only make the trusted check reject C'.) -/
def nextIndices (path : System.FilePath) : IO (Nat × Nat × Nat) := do
  let b ← IO.FS.readBinFile path
  let mut nn := 0; let mut nl := 0; let mut ne := 0
  let mut i := 0
  let sz := b.size
  while i < sz do
    if i + 6 < sz && b.get! i == 123 && b.get! (i+1) == 34 then
      let c2 := b.get! (i+2); let c3 := b.get! (i+3); let c4 := b.get! (i+4)
      if c2 == 105 && c4 == 34 then          -- {"i?"
        if c3 == 110 then nn := nn + 1        -- {"in"
        else if c3 == 108 then nl := nl + 1   -- {"il"
        else if c3 == 101 then ne := ne + 1   -- {"ie"
        else pure ()
      else if (c2 == 97 && c3 == 112 && c4 == 112) || (c2 == 98 && c3 == 118) || (c2 == 99 && c3 == 111 && c4 == 110)
          || (c2 == 102 && c3 == 111 && c4 == 114) then   -- {"app" {"bv" {"con" {"for"
        ne := ne + 1
      else pure ()
    -- next line
    let mut j := i
    while j < sz && b.get! j != 10 do j := j + 1
    i := j + 1
  return (nn + 1, nl + 1, ne)

/-- the challenge export's name and level tables (first index of every value) + next free indices, one pass: the minted
records REUSE the challenge's index for every name / level already present (lean4export never emits duplicates and
gruszka identifies names by index) -/
def loadTables (path : System.FilePath) : IO (Std.HashMap Name Nat × Std.HashMap Level Nat × Nat × Nat × Nat) := do
  let b ← IO.FS.readBinFile path
  let mut names : Array Name := #[.anonymous]
  let mut levels : Array Level := #[.zero]
  let mut nmap : Std.HashMap Name Nat := {}
  let mut lmap : Std.HashMap Level Nat := {}
  let mut ne := 0
  let mut i := 0
  let sz := b.size
  while i < sz do
    let mut j := i
    while j < sz && b.get! j != 10 do j := j + 1
    if i + 6 < j && b.get! i == 123 && b.get! (i+1) == 34 then
      let c2 := b.get! (i+2); let c3 := b.get! (i+3); let c4 := b.get! (i+4)
      if c2 == 105 && c4 == 34 && (c3 == 110 || c3 == 108) then   -- {"in" / {"il"
        let some line := String.fromUTF8? (b.extract i j) | throw (IO.userError "challenge: line is not UTF-8")
        let jl ← IO.ofExcept (Json.parse line)
        if c3 == 110 then
          let nm ← match jl.getObjVal? "str", jl.getObjVal? "num" with
            | .ok o, _ => do
              let pre ← IO.ofExcept (o.getObjValAs? Nat "pre"); let s ← IO.ofExcept (o.getObjValAs? String "str")
              pure (Name.str (names[pre]?.getD .anonymous) s)
            | _, .ok o => do
              let pre ← IO.ofExcept (o.getObjValAs? Nat "pre"); let k ← IO.ofExcept (o.getObjValAs? Nat "i")
              pure (Name.num (names[pre]?.getD .anonymous) k)
            | _, _ => throw (IO.userError "challenge: bad name record")
          if !nmap.contains nm then nmap := nmap.insert nm names.size
          names := names.push nm
        else
          let lv : Level ← match jl.getObjVal? "succ", jl.getObjVal? "max", jl.getObjVal? "imax", jl.getObjVal? "param" with
            | .ok x, _, _, _ => do let k ← IO.ofExcept x.getNat?; pure (Level.succ (levels[k]?.getD .zero))
            | _, .ok x, _, _ => do
              let a ← IO.ofExcept x.getArr?; let p ← IO.ofExcept (a[0]?.getD 0).getNat?; let q ← IO.ofExcept (a[1]?.getD 0).getNat?
              pure (Level.max (levels[p]?.getD .zero) (levels[q]?.getD .zero))
            | _, _, .ok x, _ => do
              let a ← IO.ofExcept x.getArr?; let p ← IO.ofExcept (a[0]?.getD 0).getNat?; let q ← IO.ofExcept (a[1]?.getD 0).getNat?
              pure (Level.imax (levels[p]?.getD .zero) (levels[q]?.getD .zero))
            | _, _, _, .ok x => do let k ← IO.ofExcept x.getNat?; pure (Level.param (names[k]?.getD .anonymous))
            | _, _, _, _ => throw (IO.userError "challenge: bad level record")
          if !lmap.contains lv then lmap := lmap.insert lv levels.size
          levels := levels.push lv
      else if (c2 == 105 && c3 == 101 && c4 == 34) || (c2 == 97 && c3 == 112 && c4 == 112) || (c2 == 98 && c3 == 118) ||
          (c2 == 99 && c3 == 111 && c4 == 110) || (c2 == 102 && c3 == 111 && c4 == 114) then
        ne := ne + 1
      else pure ()
    i := j + 1
  return (nmap, lmap, names.size, levels.size, ne)

structure Em where
  out : Array String := #[]
  names : Std.HashMap Name Nat := {}
  levels : Std.HashMap Level Nat := {}
  exprs : Std.HashMap Expr Nat := {}
  nn : Nat
  nl : Nat
  ne : Nat

abbrev EmM := StateM Em

def emit (j : Json) : EmM Unit := modify fun s => { s with out := s.out.push j.compress }

def emitS (line : String) : EmM Unit := modify fun s => { s with out := s.out.push line }

def jsonStr (x : String) : String := (Json.str x).compress

partial def eName (n : Name) : EmM Nat := do
  if n.isAnonymous then return 0
  if let some i := (← get).names[n]? then return i
  match n with
  | .str p x =>
    let pi ← eName p
    let i := (← get).nn
    modify fun st => { st with nn := i + 1, names := st.names.insert n i }
    emitS s!"\{\"in\":{i},\"str\":\{\"pre\":{pi},\"str\":{jsonStr x}}}"
    return i
  | .num p k =>
    let pi ← eName p
    let i := (← get).nn
    modify fun st => { st with nn := i + 1, names := st.names.insert n i }
    emitS s!"\{\"in\":{i},\"num\":\{\"i\":{k},\"pre\":{pi}}}"
    return i
  | .anonymous => return 0

partial def eLevel (l : Level) : EmM Nat := do
  if l matches .zero then return 0
  if let some i := (← get).levels[l]? then return i
  let body : String ← match l with
    | .succ a => do pure s!"\"succ\":{← eLevel a}"
    | .max a b => do let x ← eLevel a; let y ← eLevel b; pure s!"\"max\":[{x},{y}]"
    | .imax a b => do let x ← eLevel a; let y ← eLevel b; pure s!"\"imax\":[{x},{y}]"
    | .param n => do pure s!"\"param\":{← eName n}"
    | _ => pure "\"param\":0"   -- zero handled above; metavariables cannot occur in an export
  let i := (← get).nl
  modify fun st => { st with nl := i + 1, levels := st.levels.insert l i }
  emitS s!"\{\"il\":{i},{body}}"
  return i

def biStr : BinderInfo → String
  | .default => "default" | .implicit => "implicit" | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit"

/-- canonical lean4export lines (sorted keys, compact), written directly -/
partial def eExpr (e : Expr) : EmM Nat := do
  if let some i := (← get).exprs[e]? then return i
  let mk : Nat → String ← match e with
    | .bvar k => pure fun i => s!"\{\"bvar\":{k},\"ie\":{i}}"
    | .sort l => do let li ← eLevel l; pure fun i => s!"\{\"ie\":{i},\"sort\":{li}}"
    | .const n us => do
      let ni ← eName n
      let ui ← us.toArray.mapM eLevel
      let us' := ",".intercalate (ui.toList.map toString)
      pure fun i => s!"\{\"const\":\{\"name\":{ni},\"us\":[{us'}]},\"ie\":{i}}"
    | .app f a => do
      let fi ← eExpr f; let ai ← eExpr a
      pure fun i => s!"\{\"app\":\{\"arg\":{ai},\"fn\":{fi}},\"ie\":{i}}"
    | .lam n t b bi => do
      let ni ← eName n; let ti ← eExpr t; let bj ← eExpr b
      pure fun i => s!"\{\"ie\":{i},\"lam\":\{\"binderInfo\":\"{biStr bi}\",\"body\":{bj},\"name\":{ni},\"type\":{ti}}}"
    | .forallE n t b bi => do
      let ni ← eName n; let ti ← eExpr t; let bj ← eExpr b
      pure fun i => s!"\{\"forallE\":\{\"binderInfo\":\"{biStr bi}\",\"body\":{bj},\"name\":{ni},\"type\":{ti}},\"ie\":{i}}"
    | .letE n t v b nd => do
      let ni ← eName n; let ti ← eExpr t; let vi ← eExpr v; let bj ← eExpr b
      pure fun i => s!"\{\"ie\":{i},\"letE\":\{\"body\":{bj},\"name\":{ni},\"nondep\":{if nd then "true" else "false"},\"type\":{ti},\"value\":{vi}}}"
    | .proj sn k x => do
      let si ← eName sn; let xi ← eExpr x
      pure fun i => s!"\{\"ie\":{i},\"proj\":\{\"idx\":{k},\"struct\":{xi},\"typeName\":{si}}}"
    | .lit (.natVal k) => pure fun i => s!"\{\"ie\":{i},\"natVal\":\"{k}\"}"
    | .lit (.strVal x) => pure fun i => s!"\{\"ie\":{i},\"strVal\":{jsonStr x}}"
    | .mdata _ x => do let xi ← eExpr x; pure fun i => s!"\{\"ie\":{i},\"mdata\":\{\"data\":\{},\"expr\":{xi}}}"
    | .fvar .. | .mvar .. => pure fun i => s!"\{\"bvar\":0,\"ie\":{i}}"   -- cannot occur in an export
  let i := (← get).ne
  modify fun st => { st with ne := i + 1, exprs := st.exprs.insert e i }
  emitS (mk i)
  return i

def namesJ (ns : List Name) : EmM Json := do return Json.arr ((← ns.toArray.mapM eName).map fun (x : Nat) => (x : Json))

def hintsJ : ReducibilityHints → Json
  | .opaque => jstr "opaque" | .abbrev => jstr "abbrev" | .regular k => Json.mkObj [("regular", (k.toNat : Nat))]

def safetyStr : DefinitionSafety → String
  | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"

def quotStr : QuotKind → String
  | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"

def inductJ (v : InductiveVal) : EmM Json := do
  let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type
  let all ← namesJ v.all; let ctors ← namesJ v.ctors
  return Json.mkObj [("all", all), ("ctors", ctors), ("isReflexive", Json.bool v.isReflexive), ("isRec", Json.bool v.isRec),
    ("isUnsafe", Json.bool v.isUnsafe), ("levelParams", lp), ("name", (n : Nat)), ("numIndices", (v.numIndices : Nat)),
    ("numNested", (v.numNested : Nat)), ("numParams", (v.numParams : Nat)), ("type", (t : Nat))]

def ctorJ (v : ConstructorVal) : EmM Json := do
  let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type; let ind ← eName v.induct
  return Json.mkObj [("cidx", (v.cidx : Nat)), ("induct", (ind : Nat)), ("isUnsafe", Json.bool v.isUnsafe), ("levelParams", lp),
    ("name", (n : Nat)), ("numFields", (v.numFields : Nat)), ("numParams", (v.numParams : Nat)), ("type", (t : Nat))]

def recJ (v : RecursorVal) : EmM Json := do
  let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type; let all ← namesJ v.all
  let rules ← v.rules.toArray.mapM fun r => do
    let c ← eName r.ctor; let rhs ← eExpr r.rhs
    pure (Json.mkObj [("ctor", (c : Nat)), ("nfields", (r.nfields : Nat)), ("rhs", (rhs : Nat))])
  return Json.mkObj [("all", all), ("isUnsafe", Json.bool v.isUnsafe), ("k", Json.bool v.k), ("levelParams", lp), ("name", (n : Nat)),
    ("numIndices", (v.numIndices : Nat)), ("numMinors", (v.numMinors : Nat)), ("numMotives", (v.numMotives : Nat)),
    ("numParams", (v.numParams : Nat)), ("rules", Json.arr rules), ("type", (t : Nat))]

def declJ (ci : ConstantInfo) : EmM Json := do
  match ci with
  | .axiomInfo v => do
    let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type
    return Json.mkObj [("axiom", Json.mkObj [("isUnsafe", Json.bool v.isUnsafe), ("levelParams", lp), ("name", (n : Nat)), ("type", (t : Nat))])]
  | .defnInfo v => do
    let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type; let x ← eExpr v.value; let all ← namesJ v.all
    return Json.mkObj [("def", Json.mkObj [("all", all), ("hints", hintsJ v.hints), ("levelParams", lp), ("name", (n : Nat)),
      ("safety", jstr (safetyStr v.safety)), ("type", (t : Nat)), ("value", (x : Nat))])]
  | .thmInfo v => do
    let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type; let x ← eExpr v.value; let all ← namesJ v.all
    return Json.mkObj [("thm", Json.mkObj [("all", all), ("levelParams", lp), ("name", (n : Nat)), ("type", (t : Nat)), ("value", (x : Nat))])]
  | .opaqueInfo v => do
    let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type; let x ← eExpr v.value; let all ← namesJ v.all
    return Json.mkObj [("opaque", Json.mkObj [("all", all), ("isUnsafe", Json.bool v.isUnsafe), ("levelParams", lp), ("name", (n : Nat)),
      ("type", (t : Nat)), ("value", (x : Nat))])]
  | .quotInfo v => do
    let n ← eName v.name; let lp ← namesJ v.levelParams; let t ← eExpr v.type
    return Json.mkObj [("quot", Json.mkObj [("kind", jstr (quotStr v.kind)), ("levelParams", lp), ("name", (n : Nat)), ("type", (t : Nat))])]
  | _ => return Json.null   -- inductive members are emitted as whole blocks

/-- the closure of the frontier in S' (= S with the frontier theorems as axioms), re-emitted after C's records -/
def mintEnv (chalPath : System.FilePath) (chalMap : Std.HashMap Name ConstantInfo) (solMap : Std.HashMap Name ConstantInfo)
    (solOrder : Array Name) (frontier : Array Name) (outPath : System.FilePath)
    (tables : Std.HashMap Name Nat × Std.HashMap Level Nat × Nat × Nat × Nat) : IO Json := do
  let mut env := solMap
  for n in frontier do   -- S': the frontier theorems are axioms of the same name, universes and type
    if let some (.thmInfo v) := env[n]? then
      env := env.insert n (.axiomInfo { name := v.name, levelParams := v.levelParams, type := v.type, isUnsafe := false })
  let sol : LeanExport.ExportedEnv := { constMap := env, constOrder := solOrder }
  let chal : LeanExport.ExportedEnv := { constMap := chalMap, constOrder := #[] }
  let getC (n : Name) : Option ConstantInfo := env[n]?
  let inC (n : Name) : Bool := chal.constMap.contains n
  -- recursors of every inductive block (keyed by the block's `all`)
  let mut recsOf : Std.HashMap (List Name) (Array Name) := {}
  for n in sol.constOrder do
    if let some (.recInfo r) := env[n]? then
      recsOf := recsOf.insert r.all ((recsOf.getD r.all #[]).push n)
  -- closure of the frontier in S', stopping at constants the challenge has
  let mut need : Std.HashSet Name := {}
  let mut stack := frontier
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if need.contains n || inC n then continue
    let some ci := env[n]? | throw (IO.userError s!"mint: constant {n} not in the solution export")
    need := need.insert n
    let block : Array Name := match ci with
      | .inductInfo v => (v.all.toArray) ++ (v.all.toArray.flatMap fun t => match getC t with
          | some (.inductInfo w) => w.ctors.toArray | _ => #[]) ++ recsOf.getD v.all #[]
      | .ctorInfo v => #[v.induct]
      | .recInfo v => v.all.toArray
      | _ => #[]
    for m in block ++ usedNames ci do
      if !need.contains m && !inC m then stack := stack.push m
  let (cNames, cLevels, nn, nl, ne) := tables
  -- emit in the solution's export order; an inductive block once, at its first member
  let mut st : Em := { nn, nl, ne, names := cNames, levels := cLevels }
  let mut doneBlocks : Std.HashSet (List Name) := {}
  let mut ndecl := 0
  for n in sol.constOrder do
    if !need.contains n then continue
    let some ci := env[n]? | continue
    let blockAll? : Option (List Name) := match ci with
      | .inductInfo v => some v.all | .ctorInfo v => (match getC v.induct with | some (.inductInfo w) => some w.all | _ => none)
      | .recInfo v => some v.all | _ => none
    match blockAll? with
    | some all =>
      if doneBlocks.contains all then continue
      doneBlocks := doneBlocks.insert all
      let types := all.toArray.filterMap fun t => match getC t with | some (.inductInfo w) => some w | _ => none
      let ctors := types.flatMap fun w => w.ctors.toArray.filterMap fun c => match getC c with | some (.ctorInfo cv) => some cv | _ => none
      let recs := (recsOf.getD all #[]).filterMap fun r => match getC r with | some (.recInfo rv) => some rv | _ => none
      let (j, st') := (do
        let ts ← types.mapM inductJ; let cs ← ctors.mapM ctorJ; let rs ← recs.mapM recJ
        pure (Json.mkObj [("inductive", Json.mkObj [("ctors", Json.arr cs), ("recs", Json.arr rs), ("types", Json.arr ts)])])).run st
      st := st'; st := { st with out := st.out.push j.compress }; ndecl := ndecl + 1
    | none =>
      let (j, st') := (declJ ci).run st
      st := st'
      if !(j matches .null) then st := { st with out := st.out.push j.compress }; ndecl := ndecl + 1
  -- C' = C verbatim + the new records
  let cbytes ← IO.FS.readBinFile chalPath
  let tmp := outPath.toString ++ ".tmp"
  IO.FS.withFile tmp .write fun h => do
    h.write cbytes
    if cbytes.size > 0 && cbytes.get! (cbytes.size - 1) != 10 then h.putStr "\n"
    -- write in chunks (one write per ~64k lines instead of one per line)
    let n := st.out.size
    let mut k := 0
    while k < n do
      let hi := min n (k + 65536)
      let mut buf : String := ""
      for t in [k:hi] do buf := buf ++ st.out[t]! ++ "\n"
      h.putStr buf
      k := hi
  IO.FS.rename tmp outPath
  let needArr := need.toArray.qsort (fun a b => toString a < toString b)
  return Json.mkObj [("tool", jstr "fvfrontier-prep mint"), ("appended_declarations", (ndecl : Nat)),
    ("appended_records", (st.out.size : Nat)), ("constants", Json.arr (needArr.map nameJ)),
    ("next_indices_before", Json.arr #[(nn : Nat), (nl : Nat), (ne : Nat)]),
    ("reused_challenge_names", (cNames.size : Nat))]

def mint (chalPath solPath frontierPath outPath : System.FilePath) : IO Json := do
  let frontier := (← readNames frontierPath).map nameOfStr
  let chal ← FastExport.parseExportFile chalPath
  let sol ← FastExport.parseExportFile solPath
  mintEnv chalPath chal.constMap sol.constMap sol.constOrder frontier outPath (← loadTables chalPath)

/-! ## rewrite S -> S' (streaming; frontier theorem records -> axiom records in place) -/

def rewriteFile (src dst : System.FilePath) (frontier : Std.HashSet Name) : IO (Array Name) := do
  let hin ← IO.FS.Handle.mk src .read
  let hout ← IO.FS.Handle.mk (dst.toString ++ ".tmp") .write
  let mut names : Array Name := #[.anonymous]   -- dense indices (FastParse would refuse anything else anyway)
  let mut done : Array Name := #[]
  let mut carry : ByteArray := .empty
  let mut out : ByteArray := ByteArray.emptyWithCapacity (1 <<< 24)
  repeat
    let chunk ← hin.read ((1 <<< 24 : Nat).toUSize)
    let eof := chunk.isEmpty
    let buf := if eof then carry else carry ++ chunk
    let mut i := 0
    let mut lastEnd := 0
    let n := buf.size
    while i < n do
      let mut j := i
      while j < n && buf.get! j != 10 do j := j + 1
      if j == n && !eof then break
      -- line buf[i:j]
      let isIn := j - i > 7 && buf.get! i == 123 && buf.get! (i+1) == 34 && buf.get! (i+2) == 105 && buf.get! (i+3) == 110 && buf.get! (i+4) == 34
      let isThm := j - i > 8 && buf.get! i == 123 && buf.get! (i+1) == 34 && buf.get! (i+2) == 116 && buf.get! (i+3) == 104 && buf.get! (i+4) == 109 && buf.get! (i+5) == 34
      let mut replaced := false
      if isIn || isThm then
        let some line := String.fromUTF8? (buf.extract i j) | throw (IO.userError "rewrite: line is not UTF-8")
        let j' ← IO.ofExcept (Json.parse line)
        if isIn then
          let idx ← IO.ofExcept (j'.getObjValAs? Nat "in")
          let nm ← match j'.getObjVal? "str", j'.getObjVal? "num" with
            | .ok o, _ => do
              let pre ← IO.ofExcept (o.getObjValAs? Nat "pre"); let str ← IO.ofExcept (o.getObjValAs? String "str")
              pure (Name.str (names[pre]?.getD .anonymous) str)
            | _, .ok o => do
              let pre ← IO.ofExcept (o.getObjValAs? Nat "pre"); let k ← IO.ofExcept (o.getObjValAs? Nat "i")
              pure (Name.num (names[pre]?.getD .anonymous) k)
            | _, _ => throw (IO.userError "rewrite: bad name record")
          if idx != names.size then throw (IO.userError "rewrite: name indices are not dense")
          names := names.push nm
        else
          let o ← IO.ofExcept (j'.getObjVal? "thm")
          let ni ← IO.ofExcept (o.getObjValAs? Nat "name")
          let nm := names[ni]?.getD .anonymous
          if frontier.contains nm then
            let lp ← IO.ofExcept (o.getObjVal? "levelParams"); let ty ← IO.ofExcept (o.getObjVal? "type")
            let rec' := Json.mkObj [("axiom", Json.mkObj [("isUnsafe", Json.bool false), ("levelParams", lp), ("name", (ni : Nat)), ("type", ty)])]
            out := out ++ buf.extract lastEnd i
            out := out ++ (rec'.compress ++ "\n").toUTF8
            lastEnd := min n (j + 1)
            done := done.push nm
            replaced := true
      let _ := replaced
      i := j + 1
    out := out ++ buf.extract lastEnd (min i n)
    if out.size ≥ (1 <<< 24) then hout.write out; out := ByteArray.emptyWithCapacity (1 <<< 24)
    carry := buf.extract (min i n) n
    if eof then break
  hout.write out
  hout.flush
  IO.FS.rename (dst.toString ++ ".tmp") dst
  return done

/-! ## SORRY ABSTRACTION (sketch verification): a Prop-sorry `sorryAx.{0} A b args` inside the value of a TARGET or a
DEFINITION becomes the application `D._fv_sorry_k x_1 .. x_n args'` of a fresh open lemma
`D._fv_sorry_k : ∀ (x_1 : T_1) .. (x_n : T_n), A'` closed over every enclosing binder (lets become ∀s); for Lean >= 4.17
unique sorries `sorryAx (Lean.Name → P) b name` the name argument is dropped (A' = P). Non-Prop (data) sorries are not
abstracted: they stay blockers. Untrusted: the kernel re-checks the declaration with its new value and the lemma
(emitted in redirect form, so its type must be a proposition). -/

structure AbsSt where
  lemmas : Array (Name × Expr) := #[]
  dataSorry : Bool := false
  memo : Std.HashMap Expr Bool := {}

abbrev AbsM := StateM AbsSt

/-- `λ* sorryAx ...` literally (only lambdas / metadata before the sorry): the whole proof is a placeholder -/
partial def wholeSorry : Expr → Bool
  | .lam _ _ b _ => wholeSorry b
  | .mdata _ b => wholeSorry b
  | e => match e.getAppFn with | .const n _ => n == ``sorryAx | _ => false

/-- metadata-free, `let`-free (zeta) form of a statement; used ONLY by the anti-vacuity test below -/
partial def vacNorm (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .mdata _ b => some (vacNorm b)
    | .letE _ _ v b _ => some (vacNorm (b.instantiate1 v))
    | _ => none

/-- the abstraction of declaration D is the vacuous reduction "D follows from D" when one of its subgoals'
statements IS D's own type (alpha-equivalence, binder annotations ignored, after dropping metadata and unfolding lets):
`fun xs => sorry` (also caught by `wholeSorry`), `id (by sorry)`, `(by sorry : T)`, `(fun h => h) (by sorry)`,
`let x := v; by sorry`, ... Such a declaration is not abstracted: it stays a blocker (sorry_in_targets /
sorry_in_definitions), exactly like a bare `by sorry`. -/
def vacuousSubgoal (declType : Expr) (ls : Array (Name × Expr)) : Bool :=
  let t := vacNorm declType
  ls.any fun (_, lt) => vacNorm lt == t

partial def hasSorry (e : Expr) : AbsM Bool := do
  if !e.hasLevelParam && !e.hasLooseBVars && e.approxDepth == 0 then
    return (match e with | .const n _ => n == ``sorryAx | _ => false)
  if let some b := (← get).memo[e]? then return b
  let r ← match e with
    | .const n _ => pure (n == ``sorryAx)
    | .app f a => do pure ((← hasSorry f) || (← hasSorry a))
    | .lam _ t b _ | .forallE _ t b _ => do pure ((← hasSorry t) || (← hasSorry b))
    | .letE _ t v b _ => do pure ((← hasSorry t) || (← hasSorry v) || (← hasSorry b))
    | .mdata _ x | .proj _ _ x => hasSorry x
    | _ => pure false
  modify fun st => { st with memo := st.memo.insert e r }
  return r

partial def absGo (base : Name) (lps : List Name) (ctx : Array (Name × Expr × BinderInfo × Option Expr)) (e : Expr) : AbsM Expr := do
  if !(← hasSorry e) then return e
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n us =>
      if n == ``sorryAx && args.size ≥ 2 then
        if us != [Level.zero] then
          modify fun st => { st with dataSorry := true }; return e
        let A := args[0]!
        let (ty, restStart) := match A with
          | .forallE _ (.const nm []) P' _ =>
            if nm == ``Lean.Name && !P'.hasLooseBVar 0 && args.size ≥ 3 then (P'.lowerLooseBVars 1 1, 3) else (A, 2)
          | _ => (A, 2)
        let mut rest : Array Expr := #[]
        for i in [restStart:args.size] do rest := rest.push (← absGo base lps ctx args[i]!)
        let k := (← get).lemmas.size + 1
        let nm := Name.str base s!"_fv_sorry_{k}"
        -- ∀ over lambda/∀ binders; a `let` binder stays a `let` inside the statement (quantifying it would turn
        -- a provable subgoal into a false one); only the ∀-bound variables are passed at the call site
        let lemTy := ctx.foldr (fun (bn, bt, bi, lv?) acc => match lv? with
          | some v => Expr.letE bn bt v acc false
          | none => Expr.forallE bn bt acc bi) ty
        modify fun st => { st with lemmas := st.lemmas.push (nm, lemTy) }
        let n := ctx.size
        let mut vars : Array Expr := #[]
        for i in [0:n] do
          if ctx[i]!.2.2.2.isNone then vars := vars.push (Expr.bvar (n - 1 - i))
        return mkAppN (mkAppN (.const nm (lps.map Level.param)) vars) rest
      else
        let mut args' : Array Expr := #[]
        for a in args do args' := args'.push (← absGo base lps ctx a)
        return mkAppN fn args'
    | _ =>
      let fn' ← absGo base lps ctx fn
      let mut args' : Array Expr := #[]
      for a in args do args' := args'.push (← absGo base lps ctx a)
      return mkAppN fn' args'
  | .lam n t b bi => return .lam n (← absGo base lps ctx t) (← absGo base lps (ctx.push (n, t, bi, none)) b) bi
  | .forallE n t b bi => return .forallE n (← absGo base lps ctx t) (← absGo base lps (ctx.push (n, t, bi, none)) b) bi
  | .letE n t v b nd =>
    let t' ← absGo base lps ctx t
    let vSorry ← hasSorry v
    let v' ← absGo base lps ctx v
    -- a `let` whose value has no sorry keeps its value in later subgoals' statements (`let n := m + 0` must not
    -- become an arbitrary n); a non-dependent `have`, or a let whose value is (or contains) a sorry, is a hypothesis
    let keep : Option Expr := if nd || vSorry then none else some v
    return .letE n t' v' (← absGo base lps (ctx.push (n, t, .default, keep)) b) nd
  | .mdata d x => return .mdata d (← absGo base lps ctx x)
  | .proj sn i x => return .proj sn i (← absGo base lps ctx x)
  | _ => return e

/-- (new value, open lemmas, ok); ok = false if a data sorry remains (then nothing is abstracted) -/
def abstractSorries (base : Name) (lps : List Name) (value : Expr) : Expr × Array (Name × Expr) × Bool :=
  let (v', st) := (absGo base lps #[] value).run {}
  (v', st.lemmas, !st.dataSorry)

/-! ## REDIRECT helpers -/

def axName (n : Name) : Name := .str n "_fv_frontier_axiom"

def setIdx (j : Json) (key : String) (i : Nat) : Json :=
  match j with
  | .obj kv => Json.mkObj (kv.toArray.toList.map fun (k, v) => if k == key then (k, (i : Json)) else (k, v))
  | x => x

/-! ## REDIRECT by MOVING declarations (D01's redirect design without renumbering): every open lemma `L` stays a theorem
whose value becomes the fresh axiom `L._fv_frontier_axiom.{us}`. The new name / level / constant records go to the END of
the export (fresh dense indices after all existing ones; existing `param u` levels reused); the declaration records of
L and of every constant that transitively uses an open lemma move, in their original order, behind them, each new axiom
right before its theorem. Expression, name and level records never move, so no index changes; every declaration still
comes after its dependencies (gruszka needs that; moving a record behind its users makes gruszka reject, renumbering or
out-of-order appended indices would make FastParse decline). Two phases: (1) a PARALLEL index of the export's lines
(names, `param` levels, counts, declaration records), run concurrently with the scan, (2) the output once the frontier is
known. Untrusted: a mistake only makes the trusted check reject. -/

inductive NameComp where | s (x : String) | n (k : Nat)

/-- raw name record: (pre, last component); `none` -> not canonical (the caller parses it) -/
def nameRaw (b : ByteArray) (i j : Nat) : Option (Nat × NameComp) := Id.run do
  let mut k := i + 6
  while k < j && b.get! k >= 48 && b.get! k <= 57 do k := k + 1
  let lit (k : Nat) (s : String) : Bool := Id.run do
    let bs := s.toUTF8
    if k + bs.size > j then return false
    for t in [0:bs.size] do
      if b.get! (k + t) != bs.get! t then return false
    return true
  let num (k : Nat) : Nat × Nat := Id.run do
    let mut v := 0; let mut q := k
    while q < j && b.get! q >= 48 && b.get! q <= 57 do v := v * 10 + (b.get! q - 48).toNat; q := q + 1
    return (v, q)
  if lit k ",\"str\":{\"pre\":" then
    let (pre, q) := num (k + 14)
    if !lit q ",\"str\":\"" then return none
    let st := q + 8
    let mut e := st
    while e < j && b.get! e != 34 do
      if b.get! e == 92 then return none
      e := e + 1
    if !lit e "\"}}" then return none
    match String.fromUTF8? (b.extract st e) with
    | some str => return some (pre, .s str)
    | none => return none
  else if lit k ",\"num\":{\"i\":" then
    let (iv, q) := num (k + 13)
    if !lit q ",\"pre\":" then return none
    let (pre, q2) := num (q + 7)
    if !lit q2 "}}" then return none
    return some (pre, .n iv)
  else return none

inductive LevelRaw where
  | succ (a : Nat) | max (a b : Nat) | imax (a b : Nat) | param (n : Nat)

structure ChunkIdx where
  names : Array (Nat × NameComp) := #[]
  levels : Array LevelRaw := #[]
  params : Array (Nat × Nat) := #[]           -- (level index, name index) of `param` levels
  nlev : Nat := 0
  nexp : Nat := 0
  decls : Array (Nat × Nat × Json × Array Nat) := #[]   -- (line start, line end incl. newline, record, constant name idxs)
  err : Option String := none

def declNameIdxs (jl : Json) : Array Nat :=
  match jl with
  | .obj kv => kv.toArray.foldl (fun acc (k, v) =>
      if k == "inductive" then
        ["types", "ctors", "recs"].foldl (fun acc2 key => match v.getObjValAs? (Array Json) key with
          | .ok arr => acc2 ++ arr.filterMap (fun m => (m.getObjValAs? Nat "name").toOption)
          | .error _ => acc2) acc
      else match v.getObjValAs? Nat "name" with | .ok x => acc.push x | .error _ => acc) #[]
  | _ => #[]

def indexChunk (b : ByteArray) (a z : Nat) : ChunkIdx := Id.run do
  let mut c : ChunkIdx := {}
  let mut i := a
  while i < z do
    let mut j := i
    while j < z && b.get! j != 10 do j := j + 1
    let lineEnd := min z (j + 1)
    if j - i ≥ 7 && b.get! i == 123 && b.get! (i+1) == 34 then
      let c2 := b.get! (i+2); let c3 := b.get! (i+3); let c4 := b.get! (i+4)
      if c2 == 105 && c3 == 110 && c4 == 34 then
        match nameRaw b i j with
        | some r => c := { c with names := c.names.push r }
        | none =>
          match (String.fromUTF8? (b.extract i j)).map Json.parse with
          | some (.ok jl) =>
            match jl.getObjVal? "str", jl.getObjVal? "num" with
            | .ok o, _ => match o.getObjValAs? Nat "pre", o.getObjValAs? String "str" with
              | .ok pre, .ok str => c := { c with names := c.names.push (pre, .s str) }
              | _, _ => c := { c with err := some "bad name record" }
            | _, .ok o => match o.getObjValAs? Nat "pre", o.getObjValAs? Nat "i" with
              | .ok pre, .ok k => c := { c with names := c.names.push (pre, .n k) }
              | _, _ => c := { c with err := some "bad name record" }
            | _, _ => c := { c with err := some "bad name record" }
          | _ => c := { c with err := some "bad name record" }
      else if c2 == 105 && c3 == 108 && c4 == 34 then
        -- {"il":N,"param":P} canonical: look for ,"param": quickly through Json (levels are few)
        if let some (.ok jl) := (String.fromUTF8? (b.extract i j)).map Json.parse then
          let two (x : Json) : Nat × Nat := match x.getArr? with
            | .ok a => ((a[0]?.getD 0).getNat?.toOption.getD 0, (a[1]?.getD 0).getNat?.toOption.getD 0)
            | .error _ => (0, 0)
          let raw : Option LevelRaw := match jl.getObjVal? "succ", jl.getObjVal? "max", jl.getObjVal? "imax", jl.getObjVal? "param" with
            | .ok x, _, _, _ => x.getNat?.toOption.map LevelRaw.succ
            | _, .ok x, _, _ => let (a, b2) := two x; some (.max a b2)
            | _, _, .ok x, _ => let (a, b2) := two x; some (.imax a b2)
            | _, _, _, .ok x => x.getNat?.toOption.map LevelRaw.param
            | _, _, _, _ => none
          match raw with
          | some r => c := { c with levels := c.levels.push r }
          | none => c := { c with err := some "bad level record" }
          if let .ok p := jl.getObjValAs? Nat "param" then
            if let .ok li := jl.getObjValAs? Nat "il" then c := { c with params := c.params.push (li, p) }
        else c := { c with err := some "bad level record" }
        c := { c with nlev := c.nlev + 1 }
      else if (c2 == 105 && c3 == 101 && c4 == 34) || (c2 == 97 && c3 == 112 && c4 == 112) || (c2 == 98 && c3 == 118) ||
          (c2 == 99 && c3 == 111 && c4 == 110) || (c2 == 102 && c3 == 111 && c4 == 114) then
        c := { c with nexp := c.nexp + 1 }
      else
        match (String.fromUTF8? (b.extract i j)).map Json.parse with
        | some (.ok jl) => c := { c with decls := c.decls.push (i, lineEnd, jl, declNameIdxs jl) }
        | _ => c := { c with err := some "bad declaration record" }
    i := j + 1
  return c

structure ExportIdx where
  bytes : ByteArray
  names : Array Name
  levels : Array Level := #[.zero]
  paramLevel : Std.HashMap Nat Nat
  nlev : Nat
  nexp : Nat
  decls : Array (Nat × Nat × Json × Array Nat)

def indexExport (src : System.FilePath) (nchunks : Nat := 32) : IO ExportIdx := do
  let b ← IO.FS.readBinFile src
  let sz := b.size
  -- skip the metadata line
  let mut start := 0
  while start < sz && b.get! start != 10 do start := start + 1
  start := min sz (start + 1)
  -- newline-aligned chunk boundaries
  let mut bounds : Array Nat := #[start]
  for c in [1:nchunks] do
    let mut p := max (bounds.back!) (start + (sz - start) * c / nchunks)
    while p < sz && p > 0 && b.get! (p - 1) != 10 do p := p + 1
    bounds := bounds.push p
  bounds := bounds.push sz
  let tasks := (List.range nchunks).toArray.map fun c =>
    Task.spawn (prio := .dedicated) fun _ => indexChunk b bounds[c]! bounds[c+1]!
  let mut names : Array Name := #[.anonymous]
  let mut levels : Array Level := #[.zero]
  let mut paramLevel : Std.HashMap Nat Nat := {}
  let mut nlev := 1
  let mut nexp := 0
  let mut decls : Array (Nat × Nat × Json × Array Nat) := #[]
  for t in tasks do
    let c := t.get
    if let some e := c.err then throw (IO.userError s!"index: {e}")
    for (pre, comp) in c.names do
      let p := names[pre]?.getD .anonymous
      names := names.push (match comp with | .s x => Name.str p x | .n k => Name.num p k)
    for r in c.levels do
      let lv := match r with
        | .succ a => Level.succ (levels[a]?.getD .zero)
        | .max a b => Level.max (levels[a]?.getD .zero) (levels[b]?.getD .zero)
        | .imax a b => Level.imax (levels[a]?.getD .zero) (levels[b]?.getD .zero)
        | .param n => Level.param (names[n]?.getD .anonymous)
      levels := levels.push lv
    for (li, pn) in c.params do
      if !paramLevel.contains pn then paramLevel := paramLevel.insert pn li
    nlev := nlev + c.nlev
    nexp := nexp + c.nexp
    decls := decls ++ c.decls
  return { bytes := b, names, levels, paramLevel, nlev, nexp, decls }

def writeMoved (ix : ExportIdx) (dst : System.FilePath) (frontier affected : Std.HashSet Name)
    (extra : Array String := #[]) (before : Std.HashMap Nat (Array String) := {}) (valueOf : Std.HashMap Nat Nat := {})
    (start? : Option (Nat × Nat × Nat) := none) : IO (Array Name) := do
  let names := ix.names
  let moved := ix.decls.filter fun (_, _, _, ns) => ns.any (fun x => affected.contains (names[x]?.getD .anonymous))
  let hout ← IO.FS.Handle.mk (dst.toString ++ ".tmp") .write
  let mut pos := 0
  for (a, z, _, _) in moved do
    hout.write (ix.bytes.extract pos a)
    pos := z
  hout.write (ix.bytes.extract pos ix.bytes.size)
  let mut out : ByteArray := .empty
  if ix.bytes.size > 0 && ix.bytes.get! (ix.bytes.size - 1) != 10 then out := out.push 10
  let lookup : Std.HashSet Name := Std.HashSet.ofArray names
  for l in extra do out := out ++ (l ++ "\n").toUTF8   -- records of the sorry abstraction (indices continue S's)
  let (n0, l0, e0) := start?.getD (names.size, ix.nlev, ix.nexp)
  let mut nn := n0
  let mut nlev := l0
  let mut nexp := e0
  let mut paramLevel := ix.paramLevel
  let mut info : Std.HashMap Nat (Nat × Nat × Array Json) := {}
  let mut done : Array Name := #[]
  for (_, _, jl, _) in moved do
    if let .ok o := jl.getObjVal? "thm" then
      let ni ← IO.ofExcept (o.getObjValAs? Nat "name")
      let nm := names[ni]?.getD .anonymous
      if frontier.contains nm && !info.contains ni then
        if lookup.contains (axName nm) then throw (IO.userError s!"redirect: name collision {axName nm}")
        out := out ++ ((Json.mkObj [("in", (nn : Nat)), ("str", Json.mkObj [("pre", (ni : Nat)), ("str", jstr "_fv_frontier_axiom")])]).compress ++ "\n").toUTF8
        let lps ← IO.ofExcept (o.getObjValAs? (Array Nat) "levelParams")
        let mut us : Array Json := #[]
        for p in lps do
          match paramLevel[p]? with
          | some li => us := us.push (li : Nat)
          | none =>
            out := out ++ ((Json.mkObj [("il", (nlev : Nat)), ("param", (p : Nat))]).compress ++ "\n").toUTF8
            paramLevel := paramLevel.insert p nlev; us := us.push (nlev : Nat); nlev := nlev + 1
        out := out ++ ((Json.mkObj [("const", Json.mkObj [("name", (nn : Nat)), ("us", Json.arr us)]), ("ie", (nexp : Nat))]).compress ++ "\n").toUTF8
        info := info.insert ni (nn, nexp, lps.map fun (x : Nat) => (x : Json))
        nn := nn + 1; nexp := nexp + 1
  for (_, _, jl0, ns) in moved do
    -- lines that must precede this declaration (the hypotheses of its abstracted sorries) and its new value
    for x in ns do
      for l in (before[x]?.getD #[]) do out := out ++ (l ++ "\n").toUTF8
    let jl : Json := match ns[0]?.bind (valueOf[·]?) with
      | some v => match jl0 with
        | .obj kv => Json.mkObj (kv.toArray.toList.map fun (k, x) => (k, setIdx x "value" v))
        | x => x
      | none => jl0
    match jl.getObjVal? "thm" with
    | .ok o =>
      let ni ← IO.ofExcept (o.getObjValAs? Nat "name")
      match info[ni]? with
      | some (axIdx, cIdx, lps) =>
        let ty ← IO.ofExcept (o.getObjVal? "type")
        out := out ++ ((Json.mkObj [("axiom", Json.mkObj [("isUnsafe", Json.bool false), ("levelParams", Json.arr lps),
          ("name", (axIdx : Nat)), ("type", ty)])]).compress ++ "\n").toUTF8
        out := out ++ ((Json.mkObj [("thm", setIdx o "value" cIdx)]).compress ++ "\n").toUTF8
        done := done.push (names[ni]?.getD .anonymous)
      | none => out := out ++ (jl.compress ++ "\n").toUTF8
    | .error _ => out := out ++ (jl.compress ++ "\n").toUTF8
  hout.write out
  hout.flush
  IO.FS.rename (dst.toString ++ ".tmp") dst
  return done

/-! ## prepare = scan + rewrite + mint with ONE read of S and C each (parsed concurrently) -/

def prepare (cfgPath solPath chalPath outDir : System.FilePath) (list? axioms? : Option System.FilePath)
    (redirect : Bool := true) (probe? : Option System.FilePath := none) (abstract : Bool := true) : IO Json := do
  let t0 ← IO.monoMsNow
  IO.FS.createDirAll (outDir / "frontier")
  let tSol ← IO.asTask (prio := .dedicated) (FastExport.parseExportFile solPath)
  let tChal ← IO.asTask (prio := .dedicated) (FastExport.parseExportFile chalPath)
  let tNext ← IO.asTask (prio := .dedicated) (loadTables chalPath)
  let sol ← IO.ofExcept tSol.get
  -- the line index of the export (parallel), concurrently with the scan (started after the parse: on a loaded node the
  -- two parallel readers would only slow each other down)
  let tIdx ← IO.asTask (prio := .dedicated) (if redirect then indexExport solPath else pure { bytes := .empty, names := #[], paramLevel := {}, nlev := 0, nexp := 0, decls := #[] })
  let t1 ← IO.monoMsNow
  let (rep0, F, FAx, used, sTargets, sDefs0) ← scanEnv cfgPath sol.constMap list? axioms? probe?
  -- a sorried definition inside a target statement's closure is compared by value with the official challenge: abstracting
  -- its sorry would change it (mismatch), keeping it leaves sorryAx: it stays a blocker (sorry_in_definitions)
  let inStmt : Std.HashSet String := Std.HashSet.ofArray
    (((rep0.getObjValAs? (Array String) "sorry_def_in_statement").toOption.getD #[]))
  let sDefs := sDefs0.filter (fun d => !inStmt.contains (toString d))
  -- SORRY ABSTRACTION of targets / definitions whose values contain only Prop-sorries
  let mut absDone : Array (Name × List Name × Array (Name × Expr) × Expr) := #[]
  if redirect && abstract then
    for d in sTargets ++ sDefs do
      match sol.constMap[d]? with
      -- a declaration whose WHOLE value is a sorry (`theorem T : P := by sorry`) is a placeholder, not a sketch: it stays a
      -- blocker (abstracting it would give the vacuous reduction "T follows from T")
      -- nor is one with a subgoal whose statement is the declaration's own type (`id (by sorry)`, ...)
      | some (.thmInfo v) =>
        if !wholeSorry v.value then
          let (v', ls, ok) := abstractSorries d v.levelParams v.value
          if ok && !ls.isEmpty && !vacuousSubgoal v.type ls then absDone := absDone.push (d, v.levelParams, ls, v')
      | some (.defnInfo v) =>
        if !wholeSorry v.value then
          let (v', ls, ok) := abstractSorries d v.levelParams v.value
          if ok && !ls.isEmpty && !vacuousSubgoal v.type ls then absDone := absDone.push (d, v.levelParams, ls, v')
      | _ => pure ()
  -- with an allowed list (CI ledger / pinned frontier) an abstracted subgoal is an open lemma like any other: it must be
  -- listed by its generated name (D._fv_sorry_k), else the declaration is not abstracted and stays a blocker
  if let some lf := list? then
    let allowed : Std.HashSet Name := allowedNames (← readNames lf)
    absDone := absDone.filter fun (_, _, ls, _) => ls.all fun (ln, _) => allowedHas allowed ln
  let absDecls : Std.HashSet Name := Std.HashSet.ofArray (absDone.map (·.1))
  let absLemmas : Array (Name × Name) := absDone.flatMap fun (d, _, ls, _) => ls.map fun (ln, _) => (ln, d)
  -- the scan report without the abstracted blockers, plus what was abstracted
  let dropNamed (key : String) (j : Json) : Json := match j.getObjValAs? (Array Json) key with
    | .ok arr => j.setObjVal! key (Json.arr (arr.filter fun x =>
        let nm := match x with | .str t => t | _ => (x.getObjValAs? String "name").toOption.getD ""
        !absDone.any (fun (d, _, _, _) => toString d == nm)))
    | .error _ => j
  let mut rep := dropNamed "sorry_in_definitions" (dropNamed "sorry_in_targets" rep0)
  let cnt (j : Json) (key : String) : Nat := ((j.getObjValAs? (Array Json) key).toOption.getD #[]).size
  let stillBlocked : Nat := cnt rep "sorry_in_targets" + cnt rep "sorry_in_definitions" + cnt rep "other_axioms" +
    cnt rep "missing" + cnt rep "sorry_outside_allowed" + cnt rep "open_lemma_in_statement"
  rep := rep.setObjVal! "blockers" (Json.bool (stillBlocked > 0))
  rep := rep.setObjVal! "abstracted" (Json.arr (absDone.map fun (d, _, ls, _) => Json.mkObj [("decl", nameJ d),
    ("lemmas", Json.arr (ls.map fun (ln, ty) => Json.mkObj [("name", nameJ ln), ("type", jstr (toString ty))]))]))
  -- constants that (transitively) use an open lemma or an abstracted declaration: their records move behind the new ones
  let fsetA : Std.HashSet Name := Std.HashSet.ofArray F
  -- closed under "uses" AND under inductive-block membership (a block's record moves as a whole, so a later declaration
  -- using ANY member of a moved block must move too); fixpoint over the export order
  let blockOf : Std.HashMap Name Name := sol.constMap.fold (fun m n ci => match ci with
    | .inductInfo v => (v.all ++ v.ctors).foldl (fun m2 x => m2.insert x (v.all.headD n)) (m.insert n (v.all.headD n))
    | .ctorInfo v => m.insert n v.induct
    | .recInfo v => m.insert n (v.all.headD n)
    | _ => m) {}
  let blockRep (n : Name) : Name := match blockOf[n]? with
    | some t => (match blockOf[t]? with | some t2 => t2 | none => t)
    | none => n
  let seeds : Array Name := F ++ absDone.map (·.1)
  let mut affected : Std.HashSet Name := Std.HashSet.ofArray seeds
  let mut affBlocks : Std.HashSet Name := Std.HashSet.ofArray (seeds.map blockRep)
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 1000 do
    changed := false; rounds := rounds + 1
    for c in sol.constOrder do
      if !affected.contains c then
        if affBlocks.contains (blockRep c) || ((used[c]?).getD #[]).any (fun u => u != c && affected.contains u) then
          affected := affected.insert c; affBlocks := affBlocks.insert (blockRep c); changed := true
  let t2 ← IO.monoMsNow
  let spPath := outDir / "solution.frontier.export"
  let fset : Std.HashSet Name := fsetA
  let tRew ← IO.asTask (prio := .dedicated) (do
    if F.isEmpty && absDone.isEmpty then IO.FS.writeBinFile spPath (← IO.FS.readBinFile solPath); pure #[]
    else if redirect then do
      let ix ← IO.ofExcept tIdx.get
      if absDone.isEmpty then writeMoved ix spPath fset affected
      else
        -- records of the abstraction, in S's own index space (names / levels reused, new expressions after S's)
        let nameMap : Std.HashMap Name Nat := (List.range ix.names.size).foldl (fun m k => if m.contains ix.names[k]! then m else m.insert ix.names[k]! k) {}
        let levelMap : Std.HashMap Level Nat := (List.range ix.levels.size).foldl (fun m k => if m.contains ix.levels[k]! then m else m.insert ix.levels[k]! k) {}
        for (ln, _) in absLemmas do
          if nameMap.contains ln || nameMap.contains (axName ln) then throw (IO.userError s!"abstraction: name collision {ln}")
        let mut st : Em := { nn := ix.names.size, nl := ix.nlev, ne := ix.nexp, names := nameMap, levels := levelMap }
        let mut before : Std.HashMap Nat (Array String) := {}
        let mut valueOf : Std.HashMap Nat Nat := {}
        for (d, lps, ls, v') in absDone do
          let some dIdx := nameMap[d]? | throw (IO.userError s!"abstraction: {d} has no name record")
          let mut lines : Array String := #[]
          for (ln, lty) in ls do
            let ((nIdx, aIdx, tyIdx, cIdx, lpIdxs), st') := (do
              let nIdx ← eName ln; let aIdx ← eName (axName ln); let tyIdx ← eExpr lty
              let cIdx ← eExpr (.const (axName ln) (lps.map Level.param)); let lpIdxs ← lps.toArray.mapM eName
              pure (nIdx, aIdx, tyIdx, cIdx, lpIdxs)).run st
            st := st'
            let lpsJ := Json.arr (lpIdxs.map fun (x : Nat) => (x : Json))
            lines := lines.push (Json.mkObj [("axiom", Json.mkObj [("isUnsafe", Json.bool false), ("levelParams", lpsJ),
              ("name", (aIdx : Nat)), ("type", (tyIdx : Nat))])]).compress
            lines := lines.push (Json.mkObj [("thm", Json.mkObj [("all", Json.arr #[(nIdx : Nat)]), ("levelParams", lpsJ),
              ("name", (nIdx : Nat)), ("type", (tyIdx : Nat)), ("value", (cIdx : Nat))])]).compress
          let (vIdx, st') := (eExpr v').run st
          st := st'
          before := before.insert dIdx lines
          valueOf := valueOf.insert dIdx vIdx
        writeMoved ix spPath fset affected st.out before valueOf (some (st.nn, st.nl, st.ne))
    else rewriteFile solPath spPath fset)
  let chal ← IO.ofExcept tChal.get
  let next ← IO.ofExcept tNext.get
  let t3 ← IO.monoMsNow
  -- S' as an environment (for the mint): redirect = the frontier theorems keep their type, their value is the new axiom
  let mut env' := sol.constMap
  let mut order := sol.constOrder
  let mut permitted : Array Name := #[]
  if redirect then
    for L in F do
      if let some (.thmInfo v) := env'[L]? then
        let ax := axName L
        -- an open lemma the OFFICIAL challenge itself states (blueprint / library-style challenge): its hypothesis in C'
        -- gets the challenge's statement, so check B pins the solution's statement of L to the official one (D03)
        let (lps, ty) := match chal.constMap[L]? with
          | some (.thmInfo cv) => (cv.levelParams, cv.type)
          | _ => (v.levelParams, v.type)
        env' := env'.insert ax (.axiomInfo { name := ax, levelParams := lps, type := ty, isUnsafe := false })
        env' := env'.insert L (.thmInfo { v with value := .const ax (v.levelParams.map Level.param) })
        permitted := permitted.push ax
    let mut extraBefore : Std.HashMap Name (Array Name) := {}
    for (d, lps, ls, v') in absDone do
      for (ln, lty) in ls do
        let ax := axName ln
        env' := env'.insert ax (.axiomInfo { name := ax, levelParams := lps, type := lty, isUnsafe := false })
        env' := env'.insert ln (.thmInfo { name := ln, levelParams := lps, type := lty, value := .const ax (lps.map Level.param), all := [ln] })
        permitted := permitted.push ax
      extraBefore := extraBefore.insert d (ls.flatMap fun (ln, _) => #[axName ln, ln])
      match env'[d]? with
      | some (.thmInfo v) => env' := env'.insert d (.thmInfo { v with value := v' })
      | some (.defnInfo v) => env' := env'.insert d (.defnInfo { v with value := v' })
      | _ => pure ()
    -- the new axioms right before their theorems in the export order
    let fs : Std.HashSet Name := Std.HashSet.ofArray F
    order := order.foldl (fun acc n =>
      let acc := (extraBefore[n]?.getD #[]).foldl (·.push ·) acc
      if fs.contains n then acc.push (axName n) |>.push n else acc.push n) #[]
  else
    permitted := F
  let allF := permitted ++ FAx
  let mstats ← if allF.isEmpty then
      do IO.FS.writeBinFile (outDir / "frontier" / "challenge.export") (← IO.FS.readBinFile chalPath); pure (Json.mkObj [("appended_declarations", (0 : Nat))])
    else if redirect then mintEnv chalPath chal.constMap env' order allF (outDir / "frontier" / "challenge.export") next
    else mintEnv chalPath chal.constMap sol.constMap sol.constOrder allF (outDir / "frontier" / "challenge.export") next
  let t4 ← IO.monoMsNow
  let conv ← IO.ofExcept tRew.get
  let t5 ← IO.monoMsNow
  let convSet : Std.HashSet Name := Std.HashSet.ofArray conv
  if conv.size != F.size || F.any (!convSet.contains ·) then
    throw (IO.userError s!"rewrite: converted {conv.size} of {F.size} frontier theorems")
  let lemmaOf : List (String × Json) :=
    (F.zip (if redirect then F.map axName else F)).toList.map (fun (l, a) => (toString a, nameJ l)) ++
    absLemmas.toList.map (fun (ln, _) => (toString (axName ln), nameJ ln))
  return Json.mkObj [("tool", jstr "fvfrontier-prep prepare"), ("scan", rep), ("mint", mstats),
    ("redirect", Json.bool redirect), ("permitted_frontier", Json.arr (allF.map nameJ)),
    ("frontier_lemma_of", Json.mkObj lemmaOf),
    ("ms", Json.mkObj [("parse_solution", ((t1 - t0 : Nat) : Json)), ("scan", ((t2 - t1 : Nat) : Json)),
      ("parse_challenge_wait", ((t3 - t2 : Nat) : Json)), ("mint", ((t4 - t3 : Nat) : Json)), ("rewrite_wait", ((t5 - t4 : Nat) : Json)),
      ("total", ((t5 - t0 : Nat) : Json))])]

end FrontierPrep
