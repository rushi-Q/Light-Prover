import Std.Data.HashMap
import Std.Data.HashSet
import Lean.Data.Json
import Lake.Check.Axioms
import Lake.Check.Util
import FastParse

/-!
# Frontier judge: the axiom part of a CONDITIONAL verdict "modulo an explicit sorry frontier"

Claim established together with the UNCHANGED sound check (`check/sound/check-sound.sh` run on the SAME export with the
challenge's `permitted_axioms` plus `sorryAx`, which pins every target statement with the official `compareAt` and has
BOTH kernels replay every declaration):

  every target of the comparator configuration is derivable from the permitted axioms PLUS the statements of the
  reported frontier theorems F (and from nothing else).

What this judge checks on the solution export `E` (read with `FastExport.parseExportFile`, the reader of `ccmp`):

1. `C` = the theorems of `E` that are not targets and whose value is CANONICAL (`canonicalCore`): under leading
   lambdas, after dropping metadata and zeta/beta steps in head position (what the kernel's `whnf_core` does after
   unfolding), it is the constant `sorryAx` or an application headed by it (what `theorem L ... := sorry` /
   `:= by sorry` / `fun x => sorry` elaborate to; Lean >= 4.17 writes `sorryAx (Name -> T) false name`).
2. `env'` = `E` with every member of `C` replaced by an AXIOM of the same name, level parameters and type.
3. `F` = the members of `C` reachable from the targets in `env'` (the official `runForUsedConsts` edges).
4. The OFFICIAL `Lake.Check.checkAxioms env' theoremTargets definitionTargets (permitted ++ F)` must succeed: so in `env'`
   the closure of the targets contains no axiom outside `permitted ++ F` -- in particular no `sorryAx` anywhere except
   inside the (now removed) values of the members of `F`. A wrong `F` (missing a member) makes this check fail; the
   computation of `F` therefore cannot make the judge pass with an incomplete list.
5. With `--allowed FILE`: every member of `F` (printed name) must be listed in FILE (CI / shared ledgers).

Why kernel acceptance of `E` implies kernel acceptance of `env'` (the inertness of canonical values; see
check/frontier/README.md): the Lean 4.36 kernel requires theorem types to be propositions
(`theorem_type_is_not_prop`); unfolding a canonical value only produces lambdas or applications headed by the axiom
`sorryAx`, which are stuck, are never constructor applications (so they cannot fire an iota/Quot reduction that the
opaque constant could not fire; K-like and structure-eta reductions only look at the type), and are proofs of the same
proposition as the unfolded constant, so every comparison they take part in is already decided by proof irrelevance,
which `is_def_eq_core` tries before lazy delta reduction.

Exit: 0 = frontier OK, 1 = frontier REJECT (judgment about the export), 2 = could not run. Last stdout line = JSON.
-/

namespace FrontierJudge
open Lean

structure Config where
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  deriving FromJson

/-- CANONICAL sorried value: read the way the kernel's `whnf_core` reads it after unfolding the constant (no delta):
under leading lambdas, repeatedly drop metadata, zeta-reduce `let` (body[value]) and beta-reduce a lambda in head
position; canonical iff this reaches the constant `sorryAx` or an application headed by it. Fuel-bounded (no fuel ->
not canonical). Covers `:= sorry`, `:= by sorry`, `fun x => sorry`, `by intro x; have h := t; sorry`. A proof that only
CONTAINS a sorry somewhere (a constructor or eliminator application around it) is not canonical. -/
partial def canonicalCore (fuel : Nat) (e : Expr) : Bool :=
  if fuel == 0 then false else
  match e with
  | .lam _ _ b _ => canonicalCore (fuel - 1) b
  | .mdata _ b => canonicalCore (fuel - 1) b
  | .letE _ _ v b _ => canonicalCore (fuel - 1) (b.instantiate1 v)
  | .const n _ => n == ``sorryAx
  | .app .. => e.withApp fun f args =>
    match f with
    | .const n _ => n == ``sorryAx
    | .lam .. => canonicalCore (fuel - 1) (f.betaRev args.reverse)
    | .mdata _ g => canonicalCore (fuel - 1) (mkAppN g args)
    | .letE _ _ v b _ => canonicalCore (fuel - 1) (mkAppN (b.instantiate1 v) args)
    | _ => false
  | _ => false

def isCanonicalSorry (v : Expr) : Bool := canonicalCore 10000 v

def kindOf : ConstantInfo → String
  | .axiomInfo .. => "axiom" | .defnInfo .. => "definition" | .thmInfo .. => "theorem"
  | .opaqueInfo .. => "opaque" | .quotInfo .. => "quot" | .inductInfo .. => "inductive"
  | .ctorInfo .. => "constructor" | .recInfo .. => "recursor"

/-- official traversal (`runForUsedConsts`) collected into an array -/
def usedNames (info : ConstantInfo) : Array Name :=
  ((Lake.Check.runForUsedConsts (m := StateM (Array Name)) info fun n => modify (·.push n)).run #[]).2

structure Reach where
  checked : Std.HashSet Name := {}
  parent : Std.HashMap Name Name := {}
  missing : Option Name := none

/-- closure of `roots` in `env` under the official edges, with a parent pointer for every reached name -/
def reach (env : Std.HashMap Name ConstantInfo) (roots : Array Name) : Reach := Id.run do
  let mut st : Reach := {}
  let mut work := roots
  for r in roots do st := { st with checked := st.checked.insert r }
  while h : work.size > 0 do
    let c := work[work.size - 1]
    work := work.pop
    let some info := env[c]? | do st := { st with missing := st.missing <|> some c }; continue
    for n in usedNames info do
      if !st.checked.contains n then
        st := { st with checked := st.checked.insert n, parent := st.parent.insert n c }
        work := work.push n
  return st

def chain (st : Reach) (n : Name) : Array Name := Id.run do
  let mut out := #[n]
  let mut cur := n
  for _ in [0:100000] do
    match st.parent[cur]? with
    | some p => out := out.push p; cur := p
    | none => break
  return out.reverse

def jstr (s : String) : Json := .str s
def nameJ (n : Name) : Json := .str (toString n)

structure Outcome where
  code : UInt32
  json : Json

def fail2 (msg : String) : Outcome :=
  { code := 2, json := Json.mkObj [("judge", jstr "fvfrontier-judge"), ("result", jstr "ERROR"), ("reason", jstr msg)] }

/-- diagnostic for a rejection: which declaration of the closure refers to the illegal axiom, and what it is -/
def explain (orig : Std.HashMap Name ConstantInfo) (targets : Std.HashSet Name) (st : Reach) (ax : Name) : Json := Id.run do
  let path := chain st ax
  let referrer := if path.size ≥ 2 then path[path.size - 2]! else ax
  let mut fields : List (String × Json) := [("axiom", nameJ ax), ("path", Json.arr (path.map nameJ))]
  if let some ci := orig[referrer]? then
    fields := fields ++ [("referrer", nameJ referrer), ("referrer_kind", jstr (kindOf ci))]
    let inType := ci.type.getUsedConstants.contains ax
    let inValue := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants.contains ax | none => false
    let hint :=
      if ax == ``sorryAx && targets.contains referrer then
        "the proof term of the TARGET itself contains sorry (directly, or through the instantiated statement of a lemma it uses): a target must be proved from whole-lemma frontier sorries, not contain one"
      else if ax == ``sorryAx then
        match ci with
        | .thmInfo _ =>
          if inType then "sorry inside the STATEMENT of this theorem: a frontier statement must not contain sorry"
          else "sorry inside a PARTIAL proof of this theorem: put the missing part into its own lemma `theorem L : P := sorry` (only whole-lemma sorries form the frontier)"
        | .defnInfo _ | .opaqueInfo _ => "sorry inside a DEFINITION (or instance): definitions cannot be frontier assumptions; prove the needed property in a separate sorried theorem and use it"
        | _ => if inType then "sorry inside the type of this declaration" else "sorry inside this declaration"
      else "an axiom outside permitted_axioms is used"
    fields := fields ++ [("in_type", Json.bool inType), ("in_value", Json.bool inValue), ("hint", jstr hint)]
  return Json.mkObj fields

def judge (cfgPath exportPath : System.FilePath) (allowed? : Option System.FilePath) : IO Outcome := do
  -- configuration (same fields and name conversion as the official comparator: String.toName)
  let cfgText ← IO.FS.readFile cfgPath
  let cfgJson ← match Json.parse cfgText with
    | .ok j => pure j
    | .error e => return fail2 s!"config is not JSON: {e}"
  let cfg : Config ← match fromJson? cfgJson with
    | .ok c => pure c
    | .error e => return fail2 s!"config: {e}"
  let thmTargets := cfg.theorem_names.map String.toName
  let defTargets := cfg.definition_names.getD #[] |>.map String.toName
  let permitted := cfg.permitted_axioms.map String.toName
  if permitted.contains ``sorryAx then
    return fail2 "the configuration permits sorryAx: give the challenge's own configuration (the frontier check adds sorryAx only for the kernel/statement legs)"
  if thmTargets.isEmpty && defTargets.isEmpty then
    return fail2 "the configuration names no theorems or definitions"
  let allowed? : Option (Std.HashSet String) ← match allowed? with
    | none => pure none
    | some p => do
      let lines := (← IO.FS.readFile p).splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
      pure (some (Std.HashSet.ofList lines))
  -- the export, read exactly as ccmp reads it
  let sol ← FastExport.parseExportFile exportPath
  let orig := sol.constMap
  let targetSet : Std.HashSet Name := Std.HashSet.ofArray (thmTargets ++ defTargets)
  let sorryPresent := orig.contains ``sorryAx
  -- 1./2. canonical sorried theorems -> axioms
  let mut conv : Std.HashSet Name := {}
  let mut env' := orig
  for (n, ci) in orig.toArray do
    if let .thmInfo tv := ci then
      if !targetSet.contains n && isCanonicalSorry tv.value then
        conv := conv.insert n
        env' := env'.insert n (.axiomInfo { name := tv.name, levelParams := tv.levelParams, type := tv.type, isUnsafe := false })
  if !conv.isEmpty then
    match orig[``sorryAx]? with
    | some (.axiomInfo _) => pure ()
    | _ => return { code := 1, json := Json.mkObj [("judge", jstr "fvfrontier-judge"), ("result", jstr "FRONTIER_REJECT"),
        ("reason", jstr "theorems with sorryAx-headed values, but sorryAx is not an axiom of the export")] }
  -- 3. reachable frontier (closure of the targets in env')
  let roots := (thmTargets ++ defTargets).filter (orig.contains ·)
  let st := reach env' roots
  let frontier : Array Name := (conv.toArray.filter (st.checked.contains ·)).qsort (fun a b => toString a < toString b)
  -- 4. the official axiom check on env' with permitted ++ frontier
  let res := Lake.Check.checkAxioms { constMap := env', constOrder := sol.constOrder } thmTargets defTargets (permitted ++ frontier)
  let frontierJ := Json.arr <| frontier.map fun n =>
    let ci := env'[n]!
    Json.mkObj [("name", nameJ n), ("type", jstr (toString ci.type)), ("type_hash", jstr (toString ci.type.hash)), ("level_params", (ci.levelParams.length : Nat)),
      ("used_by", match st.parent[n]? with | some p => nameJ p | none => Json.null)]
  let base : List (String × Json) := [("judge", jstr "fvfrontier-judge"), ("sorry_present", Json.bool sorryPresent),
    ("export_constants", (orig.size : Nat)), ("closure_constants", (st.checked.size : Nat)),
    ("canonical_sorry_theorems", (conv.size : Nat)), ("frontier_size", (frontier.size : Nat)), ("frontier", frontierJ)]
  match res with
  | .error msg =>
    -- find the illegal axiom named in the official message for the diagnostic
    let ax? : Option Name := (do
      let s ← (msg.splitOn "'")[1]?
      pure s.toName)
    let diag := match ax? with
      | some ax => if st.checked.contains ax then explain orig targetSet st ax else Json.null
      | none => Json.null
    return { code := 1, json := Json.mkObj (base ++ [("result", jstr "FRONTIER_REJECT"), ("reason", jstr msg), ("diagnostic", diag)]) }
  | .ok () =>
    if let some allowed := allowed? then
      let extra := frontier.filter (fun n => !allowed.contains (toString n))
      if !extra.isEmpty then
        return { code := 1, json := Json.mkObj (base ++ [("result", jstr "FRONTIER_REJECT"),
          ("reason", jstr s!"{extra.size} frontier theorem(s) not in the allowed frontier list"),
          ("not_allowed", Json.arr (extra.map nameJ))]) }
      let closed := (allowed.toArray.filter (fun s => !frontier.any (toString · == s))).qsort (· < ·)
      return { code := 0, json := Json.mkObj (base ++ [("result", jstr "FRONTIER_OK"), ("allowed_not_needed", Json.arr (closed.map jstr))]) }
    return { code := 0, json := Json.mkObj (base ++ [("result", jstr "FRONTIER_OK")]) }

end FrontierJudge
