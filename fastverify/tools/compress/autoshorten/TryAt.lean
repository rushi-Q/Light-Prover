/-
TryAt.lean — try automated closers at tactic positions of every theorem/lemma proof in one Lean file.

  lean --run TryAt.lean FILE.lean MODNAME LADDER_FILE HEARTBEATS MODE OUT.jsonl [MINLINES=2 [MAXLINES=inf]]

Elaborates FILE (imports resolved through LEAN_PATH) command by command with info trees (Elab.async false). For every
tactic sequence `t1 ... tn` of every theorem/lemma proof, outermost first, it tries to close ALL goals open before `ti`
(i.e. to replace the suffix ti..tn) with each entry of LADDER_FILE (one tactic per line; `$H` = identifiers of the suffix
that are Prop hypotheses of the goal, theorems or definitions, `$P` = Prop hypotheses and theorems), under a heartbeat
budget (HEARTBEATS in `maxHeartbeats` units), error recovery off. Suffixes spanning fewer than MINLINES or more than
MAXLINES lines are not tried (a skipped suffix is descended into like a failed one).
MODE: greedy = stop at the first successful entry for a suffix and do not descend into it; all = at the outermost suffix
of each proof try every entry, then greedy; top = only the outermost suffix of each proof, every entry; the suffix
`-leaf` (e.g. greedy-leaf) never replaces a block containing a structural step (have, obtain, suffices, calc, show,
rcases, by_cases, induction, cases, match, refine).
A try succeeds iff the tactic throws no exception, leaves no goal, logs no error, and the instantiated proof of every goal
has no sorry and no metavariable. Output: one JSON object per try (position, closer, ok, heartbeats, ms, error, DAG size
of the original suffix proof `osz` and of the new proof incl. new auxiliary declarations `nsz`). Nothing is changed in
the file: the results are candidates that apply.py re-elaborates, and the trusted check verifies.
Must run inside bwrap (it elaborates untrusted project code).
-/
import Lean
open Lean Elab Meta

structure Try where
  decl : String
  line : Nat      -- line of ti
  col : Nat
  sline : Nat     -- first line of the sequence
  eline : Nat     -- last line of tn
  spos : Nat      -- byte position of ti
  epos : Nat      -- byte tail position of tn
  depth : Nat
  idx : Nat
  ngoals : Nat
  tac : String
  tmpl : String
  ok : Bool
  hb : Nat
  ms : Nat
  err : String
  osz : Nat
  nsz : Nat
  deps : Array String

def jstr (s : String) : String := (Json.str s).compress

def Try.toJson (t : Try) : String :=
  "{" ++ s!"\"decl\":{jstr t.decl},\"line\":{t.line},\"col\":{t.col},\"sline\":{t.sline},\"eline\":{t.eline}," ++
  s!"\"spos\":{t.spos},\"epos\":{t.epos},\"depth\":{t.depth},\"idx\":{t.idx},\"ngoals\":{t.ngoals}," ++
  s!"\"tac\":{jstr t.tac},\"tmpl\":{jstr t.tmpl},\"ok\":{t.ok},\"hb\":{t.hb},\"ms\":{t.ms},\"err\":{jstr t.err},\"osz\":{t.osz},\"nsz\":{t.nsz},\"deps\":{(Json.arr (t.deps.map Json.str)).compress}" ++ "}"

/-- number of distinct subterms (structural sharing) of `e`, capped -/
def dagSize (e : Expr) (cap : Nat := 3000000) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack : Array Expr := #[e]
  let mut n := 0
  while n < cap do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      if seen.contains x then continue
      seen := seen.insert x
      n := n + 1
      match x with
      | .app f a => stack := stack.push f |>.push a
      | .lam _ t b _ => stack := stack.push t |>.push b
      | .forallE _ t b _ => stack := stack.push t |>.push b
      | .letE _ t v b _ => stack := stack.push t |>.push v |>.push b
      | .mdata _ b => stack := stack.push b
      | .proj _ _ b => stack := stack.push b
      | _ => pure ()
  return n

/-- size of the proof assigned to `goals` in `mctx` (-1 encoded as 0 if not fully assigned) -/
def assignedSize (mctx : MetavarContext) (goals : List MVarId) : Nat := Id.run do
  let mut tot := 0
  for g in goals do
    let (e, _) := instantiateMVarsCore mctx (mkMVar g)
    if e.hasExprMVar then return 0
    tot := tot + dagSize e
  return tot

/-- constants used by the proof assigned to `goals` in `mctx` -/
def assignedConsts (mctx : MetavarContext) (goals : List MVarId) : Std.HashSet Name := Id.run do
  let mut s : Std.HashSet Name := {}
  for g in goals do
    let (e, _) := instantiateMVarsCore mctx (mkMVar g)
    for c in e.getUsedConstants do s := s.insert c
  return s

def libPrefixes : List String :=
  ["Init", "Lean", "Std", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible", "ProofWidgets", "ImportGraph",
   "LeanSearchClient", "Lake", "Cli"]

/-- is `c` declared in the project (not in core/Mathlib/the library dependencies)? -/
def isProjectConst (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => !(libPrefixes.contains m.getRoot.toString)
    | none => true

/-- Run tactic `tac` on `goals` (in the context of a recorded tactic step). -/
def runTac (ci : ContextInfo) (mctx : MetavarContext) (goals : List MVarId) (tac : Syntax) (hbK : Nat) :
    IO (Bool × Nat × String × Nat × Array Name) := do
  let env := ci.env.setExporting false
  let act : CoreM (Bool × String × Nat × Array Name) := do
    let m : MetaM (Bool × String × Nat × Array Name) := do
      let t : Term.TermElabM (Bool × String × Nat × Array Name) := do
        let tm : Tactic.TacticM Unit := Tactic.evalTactic tac
        let ((), s) ← (Term.withSynthesize (postpone := .no) <|
            tm.run { elaborator := .anonymous, recover := false } |>.run { goals := goals })
        let mut rem := 0
        for g in s.goals do
          unless (← g.isAssigned) do rem := rem + 1
        if rem > 0 then return (false, s!"{rem} goals left", 0, #[])
        let mut sz := 0
        let mut used : Array Name := #[]
        for g in goals do
          let e ← instantiateMVars (mkMVar g)
          if e.hasSorry then return (false, "sorry", 0, #[])
          if e.hasExprMVar then return (false, "mvar", 0, #[])
          sz := sz + dagSize e
          -- auxiliary declarations created by the tactic (grind/abstractions): count their values too
          let env' ← getEnv
          for c in e.getUsedConstants do
            if ci.env.contains c then used := used.push c
            else
              if let some info := env'.find? c then
                if let some v := info.value? (allowOpaque := true) then
                  sz := sz + dagSize v
                  used := used ++ (v.getUsedConstants.filter ci.env.contains)
        if (← Core.getMessageLog).hasErrors then return (false, "error msg", 0, #[])
        return (true, "", sz, used)
      t.run'
    m.run' {} { mctx := mctx }
  let h0 ← IO.getNumHeartbeats
  let r ← try
      let ((ok, e, sz, used), _) ← (withOptions (fun _ => ci.options) <|
          withReader (fun c => { c with maxHeartbeats := hbK * 1000 }) <| (withCurrHeartbeats act)).toIO
        { currNamespace := ci.currNamespace, openDecls := ci.openDecls, fileName := "<TryAt>", fileMap := ci.fileMap,
          maxHeartbeats := hbK * 1000 }
        { env, ngen := ci.ngen }
      pure (ok, e, sz, used)
    catch ex => pure (false, String.ofList ((toString ex).toList.take 160), 0, #[])
  let h1 ← IO.getNumHeartbeats
  return (r.1, (h1 - h0) / 1000, r.2.1, r.2.2.1, r.2.2.2)

structure StepInfo where
  ci : ContextInfo
  ti : TacticInfo

def isSeqKind (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Tactic.tacticSeq1Indented || k == ``Lean.Parser.Tactic.tacticSeqBracketed

/-- key of a syntax range -/
def rkey (stx : Syntax) : Option (Nat × Nat) := do
  let p ← stx.getPos? (canonicalOnly := true)
  let q ← stx.getTailPos? (canonicalOnly := true)
  return (p.byteIdx, q.byteIdx)

partial def collectIdents (stx : Syntax) (acc : Array (Name × String)) : Array (Name × String) :=
  match stx with
  | .ident _ raw val _ => acc.push (val, raw.toString)
  | _ => stx.getArgs.foldl (fun a s => collectIdents s a) acc

/-- structural constants that are useless or harmful as simp/grind hints -/
def hintBlacklist : List String :=
  ["rfl", "Eq.refl", "Iff.rfl", "HEq.rfl", "Eq.symm", "Eq.trans", "Eq.mp", "Eq.mpr", "Eq.subst", "trivial", "True.intro",
   "id", "inferInstance", "le_rfl", "le_refl", "congrArg", "congrFun", "congr", "absurd", "False.elim", "And.intro",
   "Exists.intro", "Or.inl", "Or.inr", "Subtype.ext", "funext", "propext", "mt", "Iff.intro", "Iff.mp", "Iff.mpr",
   "And.left", "And.right", "Classical.byContradiction", "by_contra", "Nat.le_refl", "le_trans", "lt_of_le_of_lt",
   "Function.comp", "Function.comp_apply", "show", "this"]

/-- hint lists for a suffix: identifiers of the suffix that are Prop hypotheses of the goal (L), global theorems (T) or
global definitions (D); returns ($H = L+T+D, $P = L+T, $G = T) -/
def hintsFor (ci : ContextInfo) (mctx : MetavarContext) (g : MVarId) (items : Array Syntax) :
    IO (String × String × String) := do
  let ids := items.foldl (fun a s => collectIdents s a) #[]
  let some mdecl := mctx.findDecl? g | return ("", "", "")
  let lctx := mdecl.lctx
  let ci' : ContextInfo := { ci with mctx := mctx }
  try
    ci'.runMetaM lctx do
      let mut seen : Std.HashSet String := {}
      let mut outH : Array String := #[]
      let mut outP : Array String := #[]
      let mut outG : Array String := #[]
      for (n, raw) in ids do
        if seen.contains raw || outH.size ≥ 16 || raw.isEmpty || hintBlacklist.contains raw then continue
        seen := seen.insert raw
        match lctx.findFromUserName? n with
        | some d =>
          if !d.isImplementationDetail then
            let isP ← (try Meta.isProp d.type catch _ => pure false)
            if isP then outH := outH.push raw; outP := outP.push raw
        | none =>
          let cs := (ResolveName.resolveGlobalName ci.env ci.options ci.currNamespace ci.openDecls n).filter
            (fun (c, fs) => fs.isEmpty && ci.env.contains c)
          match cs with
          | [(c, _)] =>
            if hintBlacklist.contains c.toString then continue
            match ci.env.find? c with
            | some (.thmInfo _) => outH := outH.push raw; outP := outP.push raw; outG := outG.push raw
            | some (.defnInfo _) => outH := outH.push raw
            | _ => pure ()
          | _ => pure ()
      return (", ".intercalate outH.toList, ", ".intercalate outP.toList, ", ".intercalate outG.toList)
  catch _ => return ("", "", "")

def structWords : List String :=
  ["have", "obtain", "suffices", "calc", "show", "rcases", "by_cases", "induction", "cases", "match", "refine"]

partial def unwrapIn (cmd : Syntax) : Syntax :=
  if cmd.getKind == ``Lean.Parser.Command.in then unwrapIn cmd[2] else cmd

/-- only proofs of theorem/lemma commands are touched (proof irrelevance: the replacement cannot change any other
declaration's value or type) -/
def isTheoremCmd (cmd : Syntax) : Bool :=
  let c := unwrapIn cmd
  (c.getKind == ``Lean.Parser.Command.declaration && c[1].getKind == ``Lean.Parser.Command.theorem) ||
  c.getKind.toString.endsWith "lemma"

partial def collectSeqs (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
  let acc := if isSeqKind stx.getKind then acc.push stx else acc
  stx.getArgs.foldl (fun a s => collectSeqs s a) acc

def main (args : List String) : IO UInt32 := do
  let (file, modName, tacFile, hbS, mode, outF, minL, maxL) ← match args with
    | [a, b, c, d, e, f] => pure (a, b, c, d, e, f, 2, 1000000)
    | [a, b, c, d, e, f, g] => pure (a, b, c, d, e, f, g.toNat!, 1000000)
    | [a, b, c, d, e, f, g, h] => pure (a, b, c, d, e, f, g.toNat!, h.toNat!)
    | _ => do IO.eprintln "usage: TryAt FILE MODNAME TACTICS HB MODE OUT [MINLINES [MAXLINES]]"; IO.Process.exit 2
  let hbK := hbS.toNat!
  let leaf := mode.endsWith "-leaf"
  let mode := if leaf then (mode.dropEnd 5).toString else mode
  let input ← IO.FS.readFile file
  let tacs := (← IO.FS.readFile tacFile).splitOn "\n" |>.map (fun x => x.trimAscii.toString) |>.filter (· ≠ "")
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- project options: `set_option NAME VALUE` lines of the ladder file (Bool or Nat values); without any, RH's lakefile
  -- options (autoImplicit false, relaxedAutoImplicit false, maxSynthPendingDepth 3, maxHeartbeats 4000000, and
  -- synthInstance.maxHeartbeats 400000 for RH's GroundTheoryFields library)
  let optLines := tacs.filter (·.startsWith "set_option ")
  let tacs := tacs.filter (fun t => !t.startsWith "set_option ")
  let mut opts0 : Options := ({} : Options) |>.set `Elab.async false |>.set `maxHeartbeats (4000000 : Nat)
  if optLines.isEmpty then
    opts0 := opts0 |>.set `autoImplicit false |>.set `relaxedAutoImplicit false |>.set `maxSynthPendingDepth (3 : Nat)
    if (modName.splitOn "GroundTheory.LocalFields").length > 1 || (modName.splitOn "GroundTheory.GlobalFields").length > 1 then
      opts0 := opts0.set `synthInstance.maxHeartbeats (400000 : Nat)
  for l in optLines do
    match (l.splitOn " ").filter (· ≠ "") with
    | [_, k, v] =>
      let key := k.toName
      if v == "true" then opts0 := opts0.set key true
      else if v == "false" then opts0 := opts0.set key false
      else match v.toNat? with
        | some n => opts0 := opts0.set key n
        | none => opts0 := opts0.set key v
    | _ => IO.eprintln s!"bad option line {l}"
  let opts := opts0
  let (env, messages) ← processHeader header opts messages inputCtx (trustLevel := 1024)
    (mainModule := modName.toName)
  if messages.hasErrors then
    for m in messages.toList do IO.eprintln (← m.toString)
    return 3
  let ladder := tacs.toArray
  let out ← IO.FS.Handle.mk outF .write
  let cmdState := Command.mkState env messages opts
  let cmdState := { cmdState with infoState := { enabled := true } }
  let st0 : Frontend.State := { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let fm := inputCtx.fileMap
  let lineOf (p : Nat) : Nat := (fm.toPosition ⟨p⟩).line
  let colOf (p : Nat) : Nat := (fm.toPosition ⟨p⟩).column
  let nTries ← IO.mkRef (0 : Nat)
  let nOk ← IO.mkRef (0 : Nat)
  let rec loop (fuel : Nat) : Frontend.FrontendM Unit := do
    match fuel with
    | 0 => return
    | fuel + 1 =>
    -- the environment BEFORE this command: the ContextInfo of the info tree carries the environment at the END of
    -- the command (the theorem itself, with its @[simp]/@[grind] attributes, is in it: a closer could prove the
    -- theorem from itself). Every try runs in envBefore (constants created earlier in the same proof, e.g. matchers
    -- or abstracted proofs, are then unknown: such tries fail = conservative).
    let envBefore := (← get).commandState.env
    let done ← Frontend.processCommand
    let s ← get
    let trees := s.commandState.infoState.trees
    let cmd := s.commands.back!
    -- reset per-command state to keep memory flat
    modify fun s => { s with commandState := { s.commandState with infoState := { enabled := true }, messages := {} },
                             commands := #[] }
    -- collect tactic infos by range (outermost first) and the declaration name
    let mut steps : Std.HashMap (Nat × Nat) StepInfo := {}
    let mut declName := ""
    for t in trees do
      let infos := t.foldInfo (init := (#[] : Array (ContextInfo × Info))) fun ci i acc => acc.push (ci, i)
      for (ci, i) in infos do
        if declName == "" then
          if let some d := ci.parentDecl? then declName := d.toString
        if let .ofTacticInfo ti := i then
          if let some k := rkey ti.stx then
            unless steps.contains k do steps := steps.insert k ⟨ci, ti⟩
    -- theorems whose PROOF TERM is read by an attribute (@[to_additive], @[to_dual] translate the proof) are skipped
    let cmdTxt := match rkey cmd with
      | some (a, b) => String.Pos.Raw.extract input ⟨a⟩ ⟨b⟩
      | none => ""
    let proofReadByAttr := (cmdTxt.splitOn "to_additive").length > 1 || (cmdTxt.splitOn "to_dual").length > 1
    if steps.isEmpty || !isTheoremCmd cmd || proofReadByAttr then
      unless done do loop fuel
      return
    -- all tactic sequences of the command, outermost first (syntax pre-order)
    let seqs := collectSeqs cmd #[]
    -- covered ranges: sub-sequences inside an already replaced suffix are skipped
    let mut covered : Array (Nat × Nat) := #[]
    let mut topDone := false
    for seq in seqs do
      let some (sp, _) := rkey seq | continue
      if covered.any (fun (a, b) => a ≤ sp && sp < b) then continue
      let isTop := !topDone
      topDone := true
      if mode == "top" && !isTop then continue
      let items := (seq.getArgs.foldl (fun a s => if s.getKind == nullKind then a ++ s.getArgs else a.push s) #[])
        |>.filter (fun s => s.isOfKind nullKind == false && s.getAtomVal != ";" && s.getKind != `«;» &&
          s.getAtomVal != "{" && s.getAtomVal != "}")
      let some (_, lastTail) := (items.back?.bind rkey) | continue
      let mut i := 0
      for ti in items do
        i := i + 1
        let some k := rkey ti | continue
        if covered.any (fun (a, b) => a ≤ k.1 && k.1 < b) then continue
        let some si := steps.get? k | continue
        let goals := si.ti.goalsBefore
        if goals.isEmpty then continue
        let l0 := lineOf k.1
        let l1 := lineOf lastTail
        -- suffix already a single line: no saving possible
        if l1 + 1 < l0 + minL then continue
        -- suffixes longer than MAXLINES are (almost) never closable: skip them (descend instead)
        if l1 + 1 > l0 + maxL then continue
        let tryAll := mode == "top" || (mode == "all" && isTop && i == 1)
        -- leaf mode: never replace a block that contains a structural step a reader follows (have/obtain/...)
        if leaf then
          let txt := String.Pos.Raw.extract input ⟨k.1⟩ ⟨lastTail⟩
          let words := (txt.split (fun c => c.isWhitespace || c == '(' || c == '⟨' || c == '·')).toList.map (·.toString)
          if words.any (fun w => structWords.contains w) then continue
        let suffix := items.extract (i - 1) items.size
        let needH := ladder.any (fun t => (t.splitOn "$").length > 1)
        let ciB : ContextInfo := { si.ci with env := envBefore }
        let (hH, hP, hG) ← if needH then hintsFor ciB si.ti.mctxBefore goals.head! suffix else pure ("", "", "")
        let osz := match (items.back?.bind rkey).bind steps.get? with
          | some last => assignedSize last.ti.mctxAfter goals
          | none => 0
        let origConsts := match (items.back?.bind rkey).bind steps.get? with
          | some last => assignedConsts last.ti.mctxAfter goals
          | none => {}
        let mut success := false
        for tmpl in ladder do
          if success && !tryAll then break
          let uses (ph : String) := (tmpl.splitOn ph).length > 1
          if (uses "$H" && hH.isEmpty) || (uses "$P" && hP.isEmpty) || (uses "$G" && hG.isEmpty) then continue
          let tname := ((tmpl.replace "$H" hH).replace "$P" hP).replace "$G" hG
          let full := if goals.length == 1 then tname else s!"all_goals ({tname})"
          let tstx ← match Parser.runParserCategory si.ci.env `tactic full with
            | .ok x => pure x
            | .error _ => continue
          let t0 ← IO.monoMsNow
          let (ok, hb, err, nsz, used) ← runTac ciB si.ti.mctxBefore goals tstx hbK
          -- new dependencies on PROJECT constants (not used by the replaced proof): composition hazard with pruning
          let deps := if ok then
              ((used.filter (fun c => !origConsts.contains c && isProjectConst si.ci.env c)).map toString).toList.eraseDups.toArray
            else #[]
          let t1 ← IO.monoMsNow
          nTries.modify (· + 1)
          if ok then nOk.modify (· + 1)
          let rec_ : Try := Try.mk declName l0 (colOf k.1) (lineOf sp) l1 k.1 lastTail 0 i goals.length tname tmpl ok hb
            (t1 - t0) err osz nsz deps
          out.putStrLn rec_.toJson
          out.flush
          if ok then success := true
        if success then
          covered := covered.push (k.1, lastTail)
          break
        if mode == "top" then break
    unless done do loop fuel
  let (_, _) ← (loop 1000000 { inputCtx := inputCtx }).run st0
  IO.eprintln s!"tries {← nTries.get} ok {← nOk.get}"
  return 0
