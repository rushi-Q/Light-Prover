import FastParse
import Lake.Check.Compare
import Lake.Check.Axioms
import ParAxioms
import Std.Sync.Channel

/-!
# `LowMemParse`: Ultra-low-memory exact `compareAt` + `checkAxioms` for `ccmp-lowmem`

Soundness & Exactness Argument:
1. Tokenization & Grammar: Reuses `FastExport` (`FastParse.lean`) `tokRange` and `Slow` per-line JSON validation
   verbatim (every `in = 1..N`, `il = 1..L`, `ie = 0..E-1` sequentiality check, UTF-8 check, `String.toNat?` check,
   `binderInfo` check, duplicate-constant check). Any file that `LowMemParse` declines falls back to the official
   `LeanExport.parseStream` when `size <= fallbackMaxBytes` (512 MiB, covering 100% of `cmpx`/`arena`/`suitex`), or
   returns `.error` -> exit 2 (`DECLINED`, fail-closed) when larger.
   Names: like the official reader, which maps name INDICES to Names and keys every
   declaration by its NAME, a second name index of an existing Name is an alias of the same constant and a Name declared
   twice (under any indices) is an error. Pass 1 registers every name record with the index of the Name's FIRST record
   (`recordName` -> `lowmem_arena.c` `fv_lm_name_canon`); the arena maps every name index it is given (const / proj
   references, declaration names and name lists, kind lookups, BFS roots, legal axioms) to that canonical index, and
   `nameToIdx` keeps the first index. So the declaration table, the axiom-closure edges and the target / legal-axiom
   lookups are keyed by Name, and a Name declared twice is caught by the arena's duplicate check -> pass 1 declines ->
   the official reader decides ('Duplicate declaration') when <= 512 MiB, else no verdict.
2. `checkAxioms` Equivalence: Pass 1 records for every expression `ie` its exact set of referenced constants in an
   unboxed C DAG (`lowmem_arena.c`, including `.const` AND `.proj` `typeName` matching `FoldConsts.lean` line 41),
   and for every declaration records the exact `Lake.Check.runForUsedConsts` edges (`type`, `name`, `value?
   (allowOpaque := true)`, `induct.ctors/all`, `ctor.induct`, `rec.rules.ctor/rhs`). `fv_lm_check_axioms_bfs` then
   checks the identical target kinds and reachability predicate as `Lake.Check.checkAxioms` / `ParAxioms`.
3. `compareAt` Equivalence: In `Lake/Check/Compare.lean` lines 47, 68, 85, `compareAt` ALWAYS looks up
   `challenge.constMap[target]?` BEFORE `solution.constMap[target]?`, and in `Compare.loop` line 52 NEVER reads
   `solutionConst.value` when `target ∈ theoremTargets ∪ definitionTargets`. Therefore:
   - Restricting `solution.constMap` to `keepNames = dom(challenge.constMap) ∪ theoremTargets ∪ definitionTargets`, and
   - Materializing `Lean.Expr` ASTs ONLY for the transitive subexpressions of `keepNames` (replacing `.value` with a
     dummy `Expr.bvar 0` ONLY for `name ∈ theoremTargets ∪ definitionTargets`),
   yields the BIT-FOR-BIT IDENTICAL `Except String Unit` result from the UNMODIFIED official `Lake.Check.compareAt`!
4. Memory: Pass-1 expression DAG uses `mmap(..., MAP_NORESERVE)` (~4.3 GB on 61.6 GB RH, ~280 MB on 6.07 GB Mathlib)
   and is `munmap`ped immediately before Pass 2, instead of allocating 1.065 billion persistent `Lean.Expr` heap objects
   (32 GB on Mathlib, ~85-100 GB on RH).
-/

namespace LowMemParse
open Lean FastExport

@[extern "fv_lm_reset_all"]        opaque lmResetAll : IO Unit
@[extern "fv_lm_init"]             opaque lmInit (fileBytes : UInt64) : IO UInt32
@[extern "fv_lm_num_exprs"]        opaque lmNumExprs : IO UInt64
@[extern "fv_lm_expr_empty"]       opaque lmExprEmpty (idx : UInt64) : IO UInt32
@[extern "fv_lm_expr_const"]       opaque lmExprConst (idx nameIdx : UInt64) : IO UInt32
@[extern "fv_lm_expr_unary"]       opaque lmExprUnary (idx c1 : UInt64) : IO UInt32
@[extern "fv_lm_expr_proj"]        opaque lmExprProj (idx typeNameIdx structIdx : UInt64) : IO UInt32
@[extern "fv_lm_expr_bin"]         opaque lmExprBin (idx c1 c2 : UInt64) : IO UInt32
@[extern "fv_lm_expr_ter"]         opaque lmExprTer (idx c1 c2 c3 : UInt64) : IO UInt32
@[extern "fv_lm_decl_begin"]       opaque lmDeclBegin (nameIdx : UInt64) (kind : UInt8) (curNames : UInt64) : IO UInt32
@[extern "fv_lm_decl_add_name"]    opaque lmDeclAddName (nameIdx : UInt64) : IO Unit
@[extern "fv_lm_decl_add_expr"]    opaque lmDeclAddExpr (eidx : UInt64) : IO Unit
@[extern "fv_lm_decl_finish"]      opaque lmDeclFinish : IO UInt32
@[extern "fv_lm_free_expr_dag"]    opaque lmFreeExprDag : IO Unit
@[extern "fv_lm_get_decl_kind"]    opaque lmGetDeclKind (nameIdx : UInt64) : IO UInt32
@[extern "fv_lm_check_axioms_bfs"] opaque lmCheckAxiomsBfs (roots legals : @& ByteArray) : IO UInt64
@[extern "fv_lm_free_graph"]       opaque lmFreeGraph : IO Unit
@[extern "fv_lm_bmap_init"]        opaque lmBmapInit (nbits : UInt64) : IO UInt32
@[extern "fv_lm_bmap_set"]         opaque lmBmapSet (idx : UInt64) : IO Unit
@[extern "fv_lm_bmap_get"]         opaque lmBmapGet (idx : UInt64) : IO UInt32
@[extern "fv_lm_bmap_any_range"]   opaque lmBmapAnyRange (lo hi : UInt64) : IO UInt32
@[extern "fv_lm_bmap_free"]        opaque lmBmapFree : IO Unit
@[extern "fv_lm_pread_chunk"]      opaque lmPreadChunk (path : @& String) (offset len : UInt64) : IO ByteArray
@[extern "fv_lm_peak_rss_kb"]      opaque lmPeakRssKb : IO UInt64
@[extern "fv_lm_name_canon"]       opaque lmNameCanon (idx canon : UInt64) : IO UInt32

def kAXIOM  : UInt8 := 0
def kDEF    : UInt8 := 1
def kTHM    : UInt8 := 2
def kOPAQUE : UInt8 := 3
def kQUOT   : UInt8 := 4
def kINDUCT : UInt8 := 5
def kCTOR   : UInt8 := 6
def kREC    : UInt8 := 7

/-- Metadata saved in Pass 1 ONLY for constants in `keepNames` (at most a few thousand entries). -/
inductive PendingDecl where
  | axiomD  (name : Name) (levelParams : List Name) (typeIdx : Nat) (isUnsafe : Bool)
  | defnD   (name : Name) (levelParams : List Name) (typeIdx : Nat) (valueIdx : Option Nat)
            (hints : ReducibilityHints) (safety : DefinitionSafety) (all : List Name)
  | thmD    (name : Name) (levelParams : List Name) (typeIdx : Nat) (valueIdx : Option Nat) (all : List Name)
  | opaqueD (name : Name) (levelParams : List Name) (typeIdx : Nat) (valueIdx : Option Nat)
            (all : List Name) (isUnsafe : Bool)
  | quotD   (name : Name) (levelParams : List Name) (typeIdx : Nat) (kind : QuotKind)
  | inductD (name : Name) (levelParams : List Name) (typeIdx : Nat) (numParams numIndices : Nat)
            (all ctors : List Name) (numNested : Nat) (isRec isUnsafe isReflexive : Bool)
  | ctorD   (name : Name) (levelParams : List Name) (typeIdx : Nat) (induct : Name)
            (cidx numParams numFields : Nat) (isUnsafe : Bool)
  | recD    (name : Name) (levelParams : List Name) (typeIdx : Nat) (all : List Name)
            (numParams numIndices numMotives numMinors : Nat)
            (rules : List (Name × Nat × Nat)) (k isUnsafe : Bool)

structure ChunkSpan where
  fileOff : UInt64
  byteLen : UInt64
  eLo     : UInt64
  eHi     : UInt64
  deriving Inhabited

structure LMSt where
  names         : Array Name
  levels        : Array Level
  nameToIdx     : Std.HashMap Name UInt32    -- populated ONLY for keepNames ∪ legalAxioms! (FIRST index of the Name)
  firstIdx      : Std.HashMap Name UInt32    -- every Name of pass 1 -> the index of its FIRST record
  keepNames     : Std.HashSet Name
  skipValueSet  : Std.HashSet Name           -- theoremTargets ∪ definitionTargets
  trackNameSet  : Std.HashSet Name           -- keepNames ∪ legalAxioms
  pendingKeep   : Std.HashMap Name PendingDecl
  chunkSpans    : Array ChunkSpan

/-- Register name record `nidx` (already pushed to `st.names`, dense) for Name `n`.
The official reader (`LeanExport/Parse.lean`) maps indices to Names and keys declarations by Name, so a second index of an
existing Name is an ALIAS of the same constant. The arena is told the index of the Name's FIRST record (`lmNameCanon`) and
keys every declaration, edge and lookup by that canonical index; `nameToIdx` (targets / legal axioms) keeps the FIRST index
(no last-wins), i.e. the canonical one. `none` = the arena refused (pass 1 declines -> official reader). -/
def recordName (n : Name) (nidx : Nat) (st : LMSt) : IO (Option LMSt) := do
  match st.firstIdx[n]? with
  | some c =>
    if (← lmNameCanon nidx.toUInt64 c.toUInt64) == 0 then return none
    return some st
  | none =>
    if (← lmNameCanon nidx.toUInt64 nidx.toUInt64) == 0 then return none
    let st := { st with firstIdx := st.firstIdx.insert n nidx.toUInt32 }
    if st.trackNameSet.contains n then
      return some { st with nameToIdx := st.nameToIdx.insert n nidx.toUInt32 }
    else return some st

/-- The indices of a SLOW (JSON-parsed) line are full `Nat`s - the
official reader keys names / levels / exprs by the full `Nat` - while pass 1 hands them to the arena as `UInt64` (`toUInt64`
keeps only the low 64 bits: id `2^64 + k` would alias slot `k`). Pass 1 therefore declines any slow line holding a JSON
number that is not a plain integer below `2^32` (every dense index of this reader is below `2^31`, the arena's cap), BEFORE
any narrowing conversion; the official reader then decides (`<= 512 MiB`) or there is no verdict. Fast-path records carry
at most 18 decimal digits (`FastExport.numEnd`), below `2^60`, so their conversions are exact. -/
partial def jsonNumsSmall : Json → Bool
  | .num n => n.exponent == 0 && n.mantissa >= 0 && n.mantissa < 4294967296
  | .arr a => a.all jsonNumsSmall
  | .obj o => o.toList.all fun (_, v) => jsonNumsSmall v
  | _ => true

/-! ### Slow-line Pass 1 handler (mirrors `FastExport.Slow` validation 1-to-1) -/
namespace SlowP1

def getName? (st : LMSt) (nidx : Nat) : Option Name := st.names[nidx]?
def getLevel? (st : LMSt) (uidx : Nat) : Option Level := st.levels[uidx]?

def getNameIdxs? (st : LMSt) (arr : Array Json) : Option (Array (Nat × Name)) := do
  let mut out := Array.mkEmpty arr.size
  for j in arr do
    let .num (idx : Nat) := j | none
    let some nm := st.names[idx]? | none
    out := out.push (idx, nm)
  return out

def getLevelIdxs? (st : LMSt) (arr : Array Json) : Option (List Level) := do
  let mut out : Array Level := Array.mkEmpty arr.size
  for j in arr do
    let .num (idx : Nat) := j | none
    let some lv := st.levels[idx]? | none
    out := out.push lv
  return out.toList

def recordSimpleDecl (st : LMSt) (kind : UInt8) (nameIdx : Nat) (name : Name)
    (typeIdx : Nat) (valIdx? : Option Nat) (pd? : Option PendingDecl) : IO (Option LMSt) := do
  let okB ← lmDeclBegin nameIdx.toUInt64 kind st.names.size.toUInt64
  if okB == 0 then return none
  lmDeclAddExpr typeIdx.toUInt64
  lmDeclAddName nameIdx.toUInt64
  if let some vIdx := valIdx? then lmDeclAddExpr vIdx.toUInt64
  let okF ← lmDeclFinish
  if okF == 0 then return none
  let st := match pd? with
    | some pd => { st with pendingKeep := st.pendingKeep.insert name pd }
    | none => st
  return some st

def parseSlowInductInfo (st : LMSt) (json : Json) : IO (Option LMSt) := do
  let .obj data := json | return none
  let some (.num (nameIdx : Nat)) := data["name"]? | return none
  let some (.arr levelParamsIdxs) := data["levelParams"]? | return none
  let some (.num (typeIdx : Nat)) := data["type"]? | return none
  let some (.num (numParams : Nat)) := data["numParams"]? | return none
  let some (.num (numIndices : Nat)) := data["numIndices"]? | return none
  let some (.arr allIdxs) := data["all"]? | return none
  let some (.arr ctorsIdxs) := data["ctors"]? | return none
  let some (.num (numNested : Nat)) := data["numNested"]? | return none
  let some (.bool isRec) := data["isRec"]? | return none
  let some (.bool isUnsafe) := data["isUnsafe"]? | return none
  let some (.bool isReflexive) := data["isReflexive"]? | return none
  let ne ← lmNumExprs
  if typeIdx.toUInt64 >= ne then return none
  let some name := st.names[nameIdx]? | return none
  let some lps := getNameIdxs? st levelParamsIdxs | return none
  let some alls := getNameIdxs? st allIdxs | return none
  let some ctors := getNameIdxs? st ctorsIdxs | return none
  let okB ← lmDeclBegin nameIdx.toUInt64 kINDUCT st.names.size.toUInt64
  if okB == 0 then return none
  lmDeclAddExpr typeIdx.toUInt64
  lmDeclAddName nameIdx.toUInt64
  for (ci, _) in ctors do lmDeclAddName ci.toUInt64
  for (ai, _) in alls do lmDeclAddName ai.toUInt64
  let okF ← lmDeclFinish
  if okF == 0 then return none
  let st := if st.keepNames.contains name then
    let pd := PendingDecl.inductD name (lps.toList.map (·.2)) typeIdx numParams numIndices
      (alls.toList.map (·.2)) (ctors.toList.map (·.2)) numNested isRec isUnsafe isReflexive
    { st with pendingKeep := st.pendingKeep.insert name pd }
  else st
  return some st

def parseSlowCtorInfo (st : LMSt) (json : Json) : IO (Option LMSt) := do
  let .obj data := json | return none
  let some (.num (nameIdx : Nat)) := data["name"]? | return none
  let some (.arr levelParamsIdxs) := data["levelParams"]? | return none
  let some (.num (typeIdx : Nat)) := data["type"]? | return none
  let some (.num (inductIdx : Nat)) := data["induct"]? | return none
  let some (.num (cidx : Nat)) := data["cidx"]? | return none
  let some (.num (numParams : Nat)) := data["numParams"]? | return none
  let some (.num (numFields : Nat)) := data["numFields"]? | return none
  let some (.bool isUnsafe) := data["isUnsafe"]? | return none
  let ne ← lmNumExprs
  if typeIdx.toUInt64 >= ne then return none
  let some name := st.names[nameIdx]? | return none
  let some lps := getNameIdxs? st levelParamsIdxs | return none
  let some induct := st.names[inductIdx]? | return none
  let okB ← lmDeclBegin nameIdx.toUInt64 kCTOR st.names.size.toUInt64
  if okB == 0 then return none
  lmDeclAddExpr typeIdx.toUInt64
  lmDeclAddName nameIdx.toUInt64
  lmDeclAddName inductIdx.toUInt64
  let okF ← lmDeclFinish
  if okF == 0 then return none
  let st := if st.keepNames.contains name then
    let pd := PendingDecl.ctorD name (lps.toList.map (·.2)) typeIdx induct cidx numParams numFields isUnsafe
    { st with pendingKeep := st.pendingKeep.insert name pd }
  else st
  return some st

def parseSlowRecInfo (st : LMSt) (json : Json) : IO (Option LMSt) := do
  let .obj data := json | return none
  let some (.num (nameIdx : Nat)) := data["name"]? | return none
  let some (.arr levelParamsIdxs) := data["levelParams"]? | return none
  let some (.num (typeIdx : Nat)) := data["type"]? | return none
  let some (.arr allIdxs) := data["all"]? | return none
  let some (.num (numParams : Nat)) := data["numParams"]? | return none
  let some (.num (numIndices : Nat)) := data["numIndices"]? | return none
  let some (.num (numMotives : Nat)) := data["numMotives"]? | return none
  let some (.num (numMinors : Nat)) := data["numMinors"]? | return none
  let some (.bool k) := data["k"]? | return none
  let some (.arr rulesJson) := data["rules"]? | return none
  let some (.bool isUnsafe) := data["isUnsafe"]? | return none
  let ne ← lmNumExprs
  if typeIdx.toUInt64 >= ne then return none
  let some name := st.names[nameIdx]? | return none
  let some lps := getNameIdxs? st levelParamsIdxs | return none
  let some alls := getNameIdxs? st allIdxs | return none
  let mut rulesParsed : Array (Nat × Name × Nat × Nat) := Array.mkEmpty rulesJson.size
  for rj in rulesJson do
    let .obj ro := rj | return none
    let some (.num (ctorIdx : Nat)) := ro["ctor"]? | return none
    let some (.num (nfields : Nat)) := ro["nfields"]? | return none
    let some (.num (rhsIdx : Nat)) := ro["rhs"]? | return none
    if rhsIdx.toUInt64 >= ne then return none
    let some ctorNm := st.names[ctorIdx]? | return none
    rulesParsed := rulesParsed.push (ctorIdx, ctorNm, nfields, rhsIdx)
  let okB ← lmDeclBegin nameIdx.toUInt64 kREC st.names.size.toUInt64
  if okB == 0 then return none
  lmDeclAddExpr typeIdx.toUInt64
  lmDeclAddName nameIdx.toUInt64
  for (ctorIdx, _, _, rhsIdx) in rulesParsed do
    lmDeclAddName ctorIdx.toUInt64
    lmDeclAddExpr rhsIdx.toUInt64
  let okF ← lmDeclFinish
  if okF == 0 then return none
  let st := if st.keepNames.contains name then
    let rlist := rulesParsed.toList.map fun (_, cn, nf, ri) => (cn, nf, ri)
    let pd := PendingDecl.recD name (lps.toList.map (·.2)) typeIdx (alls.toList.map (·.2))
      numParams numIndices numMotives numMinors rlist k isUnsafe
    { st with pendingKeep := st.pendingKeep.insert name pd }
  else st
  return some st

def stepSlowObj (obj : Std.TreeMap.Raw String Json) (st : LMSt) : IO (Option LMSt) := do
  let kv := obj.toList
  let kv := match kv with
    | [x, y@("in", _)] => [y, x]
    | [x, y@("ie", _)] => [y, x]
    | [x, y@("il", _)] => [y, x]
    | _ => kv
  match kv with
  | [("in", .num (idx : Nat)), ("str", .obj data)] =>
    if idx != st.names.size then return none
    let some (.num (preIdx : Nat)) := data["pre"]? | return none
    let some (.str str) := data["str"]? | return none
    let some pre := st.names[preIdx]? | return none
    let nm := Name.str pre str
    recordName nm idx { st with names := st.names.push nm }
  | [("in", .num (idx : Nat)), ("num", .obj data)] =>
    if idx != st.names.size then return none
    let some (.num (preIdx : Nat)) := data["pre"]? | return none
    let some (.num (i : Nat)) := data["i"]? | return none
    let some pre := st.names[preIdx]? | return none
    let nm := Name.num pre i
    recordName nm idx { st with names := st.names.push nm }
  | [("il", .num (idx : Nat)), ("succ", .num (lIdx : Nat))] =>
    if idx != st.levels.size then return none
    let some l := st.levels[lIdx]? | return none
    return some { st with levels := st.levels.push (.succ l) }
  | [("il", .num (idx : Nat)), ("max", .arr #[.num (a : Nat), .num (b : Nat)])] =>
    if idx != st.levels.size then return none
    let some l1 := st.levels[a]? | return none
    let some l2 := st.levels[b]? | return none
    return some { st with levels := st.levels.push (.max l1 l2) }
  | [("il", .num (idx : Nat)), ("imax", .arr #[.num (a : Nat), .num (b : Nat)])] =>
    if idx != st.levels.size then return none
    let some l1 := st.levels[a]? | return none
    let some l2 := st.levels[b]? | return none
    return some { st with levels := st.levels.push (.imax l1 l2) }
  | [("il", .num (idx : Nat)), ("param", .num (nIdx : Nat))] =>
    if idx != st.levels.size then return none
    let some nm := st.names[nIdx]? | return none
    return some { st with levels := st.levels.push (.param nm) }
  | [("ie", .num (idx : Nat)), ("bvar", .num (_ : Nat))] =>
    if (← lmExprEmpty idx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("sort", .num (uIdx : Nat))] =>
    if uIdx >= st.levels.size then return none
    if (← lmExprEmpty idx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("const", .obj data)] =>
    let some (.num (nIdx : Nat)) := data["name"]? | return none
    let some (.arr usIdxs) := data["us"]? | return none
    if nIdx >= st.names.size then return none
    let some _ := getLevelIdxs? st usIdxs | return none
    if (← lmExprConst idx.toUInt64 nIdx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("app", .obj data)] =>
    let some (.num (fnIdx : Nat)) := data["fn"]? | return none
    let some (.num (argIdx : Nat)) := data["arg"]? | return none
    if (← lmExprBin idx.toUInt64 fnIdx.toUInt64 argIdx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("lam", .obj data)]
  | [("ie", .num (idx : Nat)), ("forallE", .obj data)] =>
    let some (.num (nIdx : Nat)) := data["name"]? | return none
    let some (.num (tyIdx : Nat)) := data["type"]? | return none
    let some (.num (bdIdx : Nat)) := data["body"]? | return none
    let some (.str biStr) := data["binderInfo"]? | return none
    if nIdx >= st.names.size then return none
    if biStr != "default" && biStr != "implicit" && biStr != "strictImplicit" && biStr != "instImplicit" then return none
    if (← lmExprBin idx.toUInt64 tyIdx.toUInt64 bdIdx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("letE", .obj data)] =>
    let some (.num (nIdx : Nat)) := data["name"]? | return none
    let some (.num (tyIdx : Nat)) := data["type"]? | return none
    let some (.num (valIdx : Nat)) := data["value"]? | return none
    let some (.num (bdIdx : Nat)) := data["body"]? | return none
    let some (.bool _) := data["nondep"]? | return none
    if nIdx >= st.names.size then return none
    if (← lmExprTer idx.toUInt64 tyIdx.toUInt64 valIdx.toUInt64 bdIdx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("proj", .obj data)] =>
    let some (.num (tnIdx : Nat)) := data["typeName"]? | return none
    let some (.num (_ : Nat)) := data["idx"]? | return none
    let some (.num (sIdx : Nat)) := data["struct"]? | return none
    if tnIdx >= st.names.size then return none
    if (← lmExprProj idx.toUInt64 tnIdx.toUInt64 sIdx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("natVal", .str s)] =>
    let some _ := String.toNat? s | return none
    if (← lmExprEmpty idx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("strVal", .str _)] =>
    if (← lmExprEmpty idx.toUInt64) == 0 then return none else return some st
  | [("ie", .num (idx : Nat)), ("mdata", .obj data)] =>
    let some (.num (eIdx : Nat)) := data["expr"]? | return none
    let some (.obj _) := data["data"]? | return none
    if (← lmExprUnary idx.toUInt64 eIdx.toUInt64) == 0 then return none else return some st
  | [("axiom", .obj data)] =>
    let some (.num (nameIdx : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (typeIdx : Nat)) := data["type"]? | return none
    let some (.bool isUnsafe) := data["isUnsafe"]? | return none
    if typeIdx.toUInt64 >= (← lmNumExprs) then return none
    let some name := st.names[nameIdx]? | return none
    let some lps := getNameIdxs? st lpsArr | return none
    let pd? := if st.keepNames.contains name then
      some (.axiomD name (lps.toList.map (·.2)) typeIdx isUnsafe) else none
    recordSimpleDecl st kAXIOM nameIdx name typeIdx none pd?
  | [("def", .obj data)] =>
    let some (.num (nameIdx : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (typeIdx : Nat)) := data["type"]? | return none
    let some (.num (valueIdx : Nat)) := data["value"]? | return none
    let some hintsJ := data["hints"]? | return none
    let some (.str safetyStr) := data["safety"]? | return none
    let some (.arr allArr) := data["all"]? | return none
    let ne ← lmNumExprs
    if typeIdx.toUInt64 >= ne || valueIdx.toUInt64 >= ne then return none
    let some name := st.names[nameIdx]? | return none
    let some lps := getNameIdxs? st lpsArr | return none
    let some alls := getNameIdxs? st allArr | return none
    let hints? : Option ReducibilityHints := match hintsJ with
      | .str "opaque" => some .opaque
      | .str "abbrev" => some .abbrev
      | .obj obj => match obj["regular"]? with
        | some (.num (lv : Nat)) => some (.regular lv.toUInt32)
        | _ => none
      | _ => none
    let some hints := hints? | return none
    let safety? : Option DefinitionSafety := match safetyStr with
      | "unsafe" => some .unsafe | "safe" => some .safe | "partial" => some .partial | _ => none
    let some safety := safety? | return none
    let pd? := if st.keepNames.contains name then
      let vKeep := if st.skipValueSet.contains name then none else some valueIdx
      some (.defnD name (lps.toList.map (·.2)) typeIdx vKeep hints safety (alls.toList.map (·.2)))
    else none
    recordSimpleDecl st kDEF nameIdx name typeIdx (some valueIdx) pd?
  | [("thm", .obj data)] =>
    let some (.num (nameIdx : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (typeIdx : Nat)) := data["type"]? | return none
    let some (.num (valueIdx : Nat)) := data["value"]? | return none
    let some (.arr allArr) := data["all"]? | return none
    let ne ← lmNumExprs
    if typeIdx.toUInt64 >= ne || valueIdx.toUInt64 >= ne then return none
    let some name := st.names[nameIdx]? | return none
    let some lps := getNameIdxs? st lpsArr | return none
    let some alls := getNameIdxs? st allArr | return none
    let pd? := if st.keepNames.contains name then
      let vKeep := if st.skipValueSet.contains name then none else some valueIdx
      some (.thmD name (lps.toList.map (·.2)) typeIdx vKeep (alls.toList.map (·.2)))
    else none
    recordSimpleDecl st kTHM nameIdx name typeIdx (some valueIdx) pd?
  | [("opaque", .obj data)] =>
    let some (.num (nameIdx : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (typeIdx : Nat)) := data["type"]? | return none
    let some (.num (valueIdx : Nat)) := data["value"]? | return none
    let (.bool isUnsafe) := data["isUnsafe"]?.getD (.bool false) | return none
    let some (.arr allArr) := data["all"]? | return none
    let ne ← lmNumExprs
    if typeIdx.toUInt64 >= ne || valueIdx.toUInt64 >= ne then return none
    let some name := st.names[nameIdx]? | return none
    let some lps := getNameIdxs? st lpsArr | return none
    let some alls := getNameIdxs? st allArr | return none
    let pd? := if st.keepNames.contains name then
      let vKeep := if st.skipValueSet.contains name then none else some valueIdx
      some (.opaqueD name (lps.toList.map (·.2)) typeIdx vKeep (alls.toList.map (·.2)) isUnsafe)
    else none
    recordSimpleDecl st kOPAQUE nameIdx name typeIdx (some valueIdx) pd?
  | [("quot", .obj data)] =>
    let some (.num (nameIdx : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (typeIdx : Nat)) := data["type"]? | return none
    let some (.str kindStr) := data["kind"]? | return none
    if typeIdx.toUInt64 >= (← lmNumExprs) then return none
    let some name := st.names[nameIdx]? | return none
    let some lps := getNameIdxs? st lpsArr | return none
    let kind? : Option QuotKind := match kindStr with
      | "type" => some .type | "ctor" => some .ctor | "lift" => some .lift | "ind" => some .ind | _ => none
    let some kind := kind? | return none
    let pd? := if st.keepNames.contains name then
      some (.quotD name (lps.toList.map (·.2)) typeIdx kind) else none
    recordSimpleDecl st kQUOT nameIdx name typeIdx none pd?
  | [("inductive", .obj data)] =>
    let some (.arr types) := data["types"]? | return none
    let some (.arr ctors) := data["ctors"]? | return none
    let some (.arr recs) := data["recs"]? | return none
    let mut cur := st
    for t in types do
      let some next ← parseSlowInductInfo cur t | return none
      cur := next
    for c in ctors do
      let some next ← parseSlowCtorInfo cur c | return none
      cur := next
    for r in recs do
      let some next ← parseSlowRecInfo cur r | return none
      cur := next
    return some cur
  | _ => return none

end SlowP1

/-! ### Fast-record Pass 1 builder (exact mirror of `FastExport.build` without `Array Expr`) -/

partial def checkLevelsExist (levelsSz : Nat) (r : Array Nat) (j n k : Nat) : Bool :=
  if k >= n then true
  else if rd r (j + k) >= levelsSz then false
  else checkLevelsExist levelsSz r j n (k + 1)

partial def buildP1 (r : Array Nat) (strs : Array String)
    (slow : Array (Option (Std.TreeMap.Raw String Json))) (j : Nat) (st : LMSt) : IO (Option LMSt) := do
  if j >= r.size then return some st
  let tag := rd r j
  if tag == tAPP then
    let i := rd r (j+1); let fi := rd r (j+2); let ai := rd r (j+3)
    if (← lmExprBin i.toUInt64 fi.toUInt64 ai.toUInt64) == 0 then return none
    buildP1 r strs slow (j+4) st
  else if tag == tFORALL || tag == tLAM then
    let i := rd r (j+1); let bdi := rd r (j+3); let ni := rd r (j+4); let ti := rd r (j+5)
    if ni >= st.names.size then return none
    if (← lmExprBin i.toUInt64 ti.toUInt64 bdi.toUInt64) == 0 then return none
    buildP1 r strs slow (j+6) st
  else if tag == tCONST then
    let i := rd r (j+1); let ni := rd r (j+2); let n := rd r (j+3)
    if ni >= st.names.size || !checkLevelsExist st.levels.size r (j+4) n 0 then return none
    if (← lmExprConst i.toUInt64 ni.toUInt64) == 0 then return none
    buildP1 r strs slow (j+4+n) st
  else if tag == tNSTR then
    let i := rd r (j+1)
    if i != st.names.size then return none
    match st.names[rd r (j+2)]?, strs[rd r (j+3)]? with
    | some pr, some s =>
      let nm := Name.str pr s
      match ← recordName nm i { st with names := st.names.push nm } with
      | some st' => buildP1 r strs slow (j+4) st'
      | none => return none
    | _, _ => return none
  else if tag == tSORT then
    let i := rd r (j+1); let ui := rd r (j+2)
    if ui >= st.levels.size then return none
    if (← lmExprEmpty i.toUInt64) == 0 then return none
    buildP1 r strs slow (j+3) st
  else if tag == tBVAR then
    let i := rd r (j+1)
    if (← lmExprEmpty i.toUInt64) == 0 then return none
    buildP1 r strs slow (j+3) st
  else if tag == tSLOW then
    match slow[rd r (j+1)]?.getD none with
    | none => return none
    | some obj =>
      if !(obj.toList.all fun (_, v) => jsonNumsSmall v) then return none   -- r3: no index >= 2^32 reaches a toUInt64
      match ← SlowP1.stepSlowObj obj st with
      | some st' => buildP1 r strs slow (j+2) st'
      | none => return none
  else if tag == tNNUM then
    let i := rd r (j+1)
    if i != st.names.size then return none
    match st.names[rd r (j+3)]? with
    | some pr =>
      let nm := Name.num pr (rd r (j+2))
      match ← recordName nm i { st with names := st.names.push nm } with
      | some st' => buildP1 r strs slow (j+4) st'
      | none => return none
    | none => return none
  else if tag == tLSUCC then
    let i := rd r (j+1)
    if i != st.levels.size then return none
    match st.levels[rd r (j+2)]? with
    | some l => buildP1 r strs slow (j+3) { st with levels := st.levels.push (.succ l) }
    | none => return none
  else if tag == tLPARAM then
    let i := rd r (j+1)
    if i != st.levels.size then return none
    match st.names[rd r (j+2)]? with
    | some n => buildP1 r strs slow (j+3) { st with levels := st.levels.push (.param n) }
    | none => return none
  else if tag == tLMAX || tag == tLIMAX then
    let i := rd r (j+1)
    if i != st.levels.size then return none
    match st.levels[rd r (j+2)]?, st.levels[rd r (j+3)]? with
    | some l1, some l2 =>
      let l := if tag == tLMAX then Level.max l1 l2 else Level.imax l1 l2
      buildP1 r strs slow (j+4) { st with levels := st.levels.push l }
    | _, _ => return none
  else if tag == tLETE then
    let i := rd r (j+1); let bdi := rd r (j+3); let ni := rd r (j+4); let ti := rd r (j+5); let vi := rd r (j+6)
    if ni >= st.names.size then return none
    if (← lmExprTer i.toUInt64 ti.toUInt64 vi.toUInt64 bdi.toUInt64) == 0 then return none
    buildP1 r strs slow (j+7) st
  else if tag == tPROJ then
    let i := rd r (j+1); let si := rd r (j+3); let tni := rd r (j+4)
    if tni >= st.names.size then return none
    if (← lmExprProj i.toUInt64 tni.toUInt64 si.toUInt64) == 0 then return none
    buildP1 r strs slow (j+5) st
  else if tag == tTHM then
    let nAll := rd r (j+1); let jl := j + 2 + nAll; let nLps := rd r jl; let jn := jl + 1 + nLps
    let nameIdx := rd r jn; let tyIdx := rd r (jn+1); let valIdx := rd r (jn+2)
    let ne ← lmNumExprs
    if tyIdx.toUInt64 >= ne || valIdx.toUInt64 >= ne then return none
    match namesAt st.names r (j+2) nAll #[], namesAt st.names r (jl+1) nLps #[], st.names[nameIdx]? with
    | some all, some lps, some name =>
      let pd? := if st.keepNames.contains name then
        let vKeep := if st.skipValueSet.contains name then none else some valIdx
        some (PendingDecl.thmD name lps tyIdx vKeep all)
      else none
      match ← SlowP1.recordSimpleDecl st kTHM nameIdx name tyIdx (some valIdx) pd? with
      | some st' => buildP1 r strs slow (jn+3) st'
      | none => return none
    | _, _, _ => return none
  else if tag == tDEF then
    let nAll := rd r (j+1); let jh := j + 2 + nAll; let hk := rd r jh
    let hints : ReducibilityHints := if hk == 0 then .opaque else if hk == 1 then .abbrev else .regular (rd r (jh+1)).toUInt32
    let jl := jh + 2; let nLps := rd r jl; let jn := jl + 1 + nLps
    let nameIdx := rd r jn; let sf := rd r (jn+1); let tyIdx := rd r (jn+2); let valIdx := rd r (jn+3)
    let safety : DefinitionSafety := if sf == 0 then .safe else if sf == 1 then .unsafe else .partial
    let ne ← lmNumExprs
    if tyIdx.toUInt64 >= ne || valIdx.toUInt64 >= ne then return none
    match namesAt st.names r (j+2) nAll #[], namesAt st.names r (jl+1) nLps #[], st.names[nameIdx]? with
    | some all, some lps, some name =>
      let pd? := if st.keepNames.contains name then
        let vKeep := if st.skipValueSet.contains name then none else some valIdx
        some (PendingDecl.defnD name lps tyIdx vKeep hints safety all)
      else none
      match ← SlowP1.recordSimpleDecl st kDEF nameIdx name tyIdx (some valIdx) pd? with
      | some st' => buildP1 r strs slow (jn+4) st'
      | none => return none
    | _, _, _ => return none
  else return none

/-! ### Bounded-memory streaming reader with chunk byte offsets -/

structure OffChunk where
  fileOff : UInt64
  byteLen : UInt64
  tokTask : Task Tok

inductive OffStream where
  | done
  | more (c : OffChunk) (next : Task (Option OffStream))

instance : Nonempty OffStream := ⟨.done⟩

def maxWindowChunks : Nat := 16   -- at most 16 * 8 MB = 128 MB of raw read-ahead buffers in flight

partial def readLoopBounded (h : IO.FS.Handle) (bs : USize) (sem : Std.CloseableChannel Unit)
    (curOff : UInt64) (carry : ByteArray) (p : IO.Promise OffStream) : IO Unit := do
  let blk ← h.read bs
  if blk.isEmpty then
    if carry.isEmpty then p.resolve .done
    else
      let _ ← sem.sync.recv
      let buf := nlPrefix ++ carry
      let t := Task.spawn (prio := .dedicated) fun _ =>
        tokRange buf 1 buf.size { recs := Array.mkEmpty (buf.size / 12), strs := #[], slow := #[] }
      let q ← IO.Promise.new
      p.resolve (.more { fileOff := curOff, byteLen := carry.size.toUInt64, tokTask := t } q.result?)
      q.resolve .done
  else
    match lastNL blk blk.size with
    | none => readLoopBounded h bs sem curOff (carry ++ blk) p
    | some k =>
      let _ ← sem.sync.recv
      let lineBytes := carry.size + (k + 1)
      let buf := (nlPrefix ++ carry).append (blk.extract 0 (k + 1))
      let carry' := blk.extract (k + 1) blk.size
      let t := Task.spawn (prio := .dedicated) fun _ =>
        tokRange buf 1 buf.size { recs := Array.mkEmpty (buf.size / 12), strs := #[], slow := #[] }
      let q ← IO.Promise.new
      p.resolve (.more { fileOff := curOff, byteLen := lineBytes.toUInt64, tokTask := t } q.result?)
      readLoopBounded h bs sem (curOff + lineBytes.toUInt64) carry' q

partial def consumeP1 (s : Task (Option OffStream)) (sem : Std.CloseableChannel Unit)
    (st : LMSt) (nchunks : Nat) : IO (Option (LMSt × Nat)) := do
  match s.get with
  | none => return none
  | some .done => return some (st, nchunks)
  | some (.more oc next) =>
    let tok := oc.tokTask.get
    let _ ← (sem.sync.send ()).toBaseIO
    let eLo ← lmNumExprs
    match ← buildP1 tok.recs tok.strs tok.slow 0 st with
    | some st' =>
      let eHi ← lmNumExprs
      let st'' := if eHi > eLo then
        { st' with chunkSpans := st'.chunkSpans.push { fileOff := oc.fileOff, byteLen := oc.byteLen, eLo, eHi } }
      else st'
      consumeP1 next sem st'' (nchunks + 1)
    | none => return none

/-! ### Pass 2: Backward mark + forward selective `Expr` build -/

def noChild : UInt64 := 0xFFFFFFFFFFFFFFFF

def slowExprDeps? (obj : Std.TreeMap.Raw String Json) : Option (UInt64 × UInt64 × UInt64 × UInt64) :=
  let kv := match obj.toList with
    | [x, y@("ie", _)] => [y, x]
    | l => l
  match kv with
  | [("ie", .num (idx : Nat)), ("bvar", _)]
  | [("ie", .num (idx : Nat)), ("sort", _)]
  | [("ie", .num (idx : Nat)), ("const", _)]
  | [("ie", .num (idx : Nat)), ("natVal", _)]
  | [("ie", .num (idx : Nat)), ("strVal", _)] =>
    some (idx.toUInt64, noChild, noChild, noChild)
  | [("ie", .num (idx : Nat)), ("mdata", .obj d)] =>
    match d["expr"]? with
    | some (.num (e : Nat)) => some (idx.toUInt64, e.toUInt64, noChild, noChild)
    | _ => none
  | [("ie", .num (idx : Nat)), ("proj", .obj d)] =>
    match d["struct"]? with
    | some (.num (s : Nat)) => some (idx.toUInt64, s.toUInt64, noChild, noChild)
    | _ => none
  | [("ie", .num (idx : Nat)), ("app", .obj d)] =>
    match d["fn"]?, d["arg"]? with
    | some (.num (f : Nat)), some (.num (a : Nat)) => some (idx.toUInt64, f.toUInt64, a.toUInt64, noChild)
    | _, _ => none
  | [("ie", .num (idx : Nat)), ("lam", .obj d)]
  | [("ie", .num (idx : Nat)), ("forallE", .obj d)] =>
    match d["type"]?, d["body"]? with
    | some (.num (t : Nat)), some (.num (b : Nat)) => some (idx.toUInt64, t.toUInt64, b.toUInt64, noChild)
    | _, _ => none
  | [("ie", .num (idx : Nat)), ("letE", .obj d)] =>
    match d["type"]?, d["value"]?, d["body"]? with
    | some (.num (t : Nat)), some (.num (v : Nat)), some (.num (b : Nat)) =>
      some (idx.toUInt64, t.toUInt64, v.toUInt64, b.toUInt64)
    | _, _, _ => none
  | _ => none   -- non-ie slow line (axiom/inductive/in/il)

partial def collectChunkDeps (r : Array Nat) (slow : Array (Option (Std.TreeMap.Raw String Json)))
    (j : Nat) (acc : Array (UInt64 × UInt64 × UInt64 × UInt64)) : Array (UInt64 × UInt64 × UInt64 × UInt64) :=
  if j >= r.size then acc else
  let tag := rd r j
  if tag == tAPP then
    collectChunkDeps r slow (j+4) (acc.push ((rd r (j+1)).toUInt64, (rd r (j+2)).toUInt64, (rd r (j+3)).toUInt64, noChild))
  else if tag == tFORALL || tag == tLAM then
    collectChunkDeps r slow (j+6) (acc.push ((rd r (j+1)).toUInt64, (rd r (j+5)).toUInt64, (rd r (j+3)).toUInt64, noChild))
  else if tag == tCONST then
    let n := rd r (j+3)
    collectChunkDeps r slow (j+4+n) (acc.push ((rd r (j+1)).toUInt64, noChild, noChild, noChild))
  else if tag == tNSTR || tag == tNNUM || tag == tLMAX || tag == tLIMAX then
    collectChunkDeps r slow (j+4) acc
  else if tag == tSORT || tag == tBVAR then
    collectChunkDeps r slow (j+3) (acc.push ((rd r (j+1)).toUInt64, noChild, noChild, noChild))
  else if tag == tLSUCC || tag == tLPARAM then
    collectChunkDeps r slow (j+3) acc
  else if tag == tLETE then
    collectChunkDeps r slow (j+7) (acc.push ((rd r (j+1)).toUInt64, (rd r (j+5)).toUInt64, (rd r (j+6)).toUInt64, (rd r (j+3)).toUInt64))
  else if tag == tPROJ then
    collectChunkDeps r slow (j+5) (acc.push ((rd r (j+1)).toUInt64, (rd r (j+3)).toUInt64, noChild, noChild))
  else if tag == tTHM then
    let nAll := rd r (j+1); let jl := j + 2 + nAll; let nLps := rd r jl
    collectChunkDeps r slow (jl + 4 + nLps) acc
  else if tag == tDEF then
    let nAll := rd r (j+1); let jl := j + 4 + nAll; let nLps := rd r jl
    collectChunkDeps r slow (jl + 5 + nLps) acc
  else if tag == tSLOW then
    let acc := match (slow[rd r (j+1)]?.getD none).bind slowExprDeps? with
      | some tup => acc.push tup
      | none => acc
    collectChunkDeps r slow (j+2) acc
  else acc

def buildSlowExpr? (st : LMSt) (exprs : Std.HashMap Nat Expr) (obj : Std.TreeMap.Raw String Json) :
    IO (Option (Std.HashMap Nat Expr)) := do
  let kv := match obj.toList with
    | [x, y@("ie", _)] => [y, x]
    | l => l
  match kv with
  | [("ie", .num (idx : Nat)), (kind, data)] =>
    if (← lmBmapGet idx.toUInt64) == 0 then return some exprs
    let e? : Option Expr := match kind, data with
      | "bvar", .num (k : Nat) => some (.bvar k)
      | "sort", .num (u : Nat) => st.levels[u]?.map .sort
      | "const", .obj d => do
        let some (.num (ni : Nat)) := d["name"]? | none
        let some (.arr usArr) := d["us"]? | none
        let nm ← st.names[ni]?
        let us ← SlowP1.getLevelIdxs? st usArr
        some (.const nm us)
      | "app", .obj d => do
        let some (.num (fi : Nat)) := d["fn"]? | none
        let some (.num (ai : Nat)) := d["arg"]? | none
        some (.app (← exprs[fi]?) (← exprs[ai]?))
      | "lam", .obj d => do
        let some (.num (ni : Nat)) := d["name"]? | none
        let some (.num (ti : Nat)) := d["type"]? | none
        let some (.num (bi : Nat)) := d["body"]? | none
        let some (.str bs) := d["binderInfo"]? | none
        let binf : BinderInfo := if bs == "implicit" then .implicit else if bs == "strictImplicit" then .strictImplicit
          else if bs == "instImplicit" then .instImplicit else .default
        some (.lam (← st.names[ni]?) (← exprs[ti]?) (← exprs[bi]?) binf)
      | "forallE", .obj d => do
        let some (.num (ni : Nat)) := d["name"]? | none
        let some (.num (ti : Nat)) := d["type"]? | none
        let some (.num (bi : Nat)) := d["body"]? | none
        let some (.str bs) := d["binderInfo"]? | none
        let binf : BinderInfo := if bs == "implicit" then .implicit else if bs == "strictImplicit" then .strictImplicit
          else if bs == "instImplicit" then .instImplicit else .default
        some (.forallE (← st.names[ni]?) (← exprs[ti]?) (← exprs[bi]?) binf)
      | "letE", .obj d => do
        let some (.num (ni : Nat)) := d["name"]? | none
        let some (.num (ti : Nat)) := d["type"]? | none
        let some (.num (vi : Nat)) := d["value"]? | none
        let some (.num (bi : Nat)) := d["body"]? | none
        let some (.bool nd) := d["nondep"]? | none
        some (.letE (← st.names[ni]?) (← exprs[ti]?) (← exprs[vi]?) (← exprs[bi]?) nd)
      | "proj", .obj d => do
        let some (.num (tni : Nat)) := d["typeName"]? | none
        let some (.num (pi : Nat)) := d["idx"]? | none
        let some (.num (si : Nat)) := d["struct"]? | none
        some (.proj (← st.names[tni]?) pi (← exprs[si]?))
      | "natVal", .str s => (String.toNat? s).map (.lit ∘ .natVal)
      | "strVal", .str s => some (.lit (.strVal s))
      | "mdata", .obj d => do
        let some (.num (ei : Nat)) := d["expr"]? | none
        some (.mdata {} (← exprs[ei]?))
      | _, _ => none
    match e? with
    | some ex => return some (exprs.insert idx ex)
    | none => return none
  | _ => return some exprs

partial def buildChunkExprs (st : LMSt) (r : Array Nat)
    (slow : Array (Option (Std.TreeMap.Raw String Json))) (j : Nat)
    (exprs : Std.HashMap Nat Expr) : IO (Option (Std.HashMap Nat Expr)) := do
  if j >= r.size then return some exprs
  let tag := rd r j
  if tag == tAPP then
    let i := rd r (j+1)
    if (← lmBmapGet i.toUInt64) == 0 then buildChunkExprs st r slow (j+4) exprs else
    match exprs[rd r (j+2)]?, exprs[rd r (j+3)]? with
    | some f, some a => buildChunkExprs st r slow (j+4) (exprs.insert i (.app f a))
    | _, _ => return none
  else if tag == tFORALL || tag == tLAM then
    let i := rd r (j+1)
    if (← lmBmapGet i.toUInt64) == 0 then buildChunkExprs st r slow (j+6) exprs else
    let bi := binderOf (rd r (j+2))
    match st.names[rd r (j+4)]?, exprs[rd r (j+5)]?, exprs[rd r (j+3)]? with
    | some nm, some ty, some bd =>
      let ex := if tag == tFORALL then Expr.forallE nm ty bd bi else Expr.lam nm ty bd bi
      buildChunkExprs st r slow (j+6) (exprs.insert i ex)
    | _, _, _ => return none
  else if tag == tCONST then
    let i := rd r (j+1); let n := rd r (j+3)
    if (← lmBmapGet i.toUInt64) == 0 then buildChunkExprs st r slow (j+4+n) exprs else
    match st.names[rd r (j+2)]?, levelsAt st.levels r (j+4) n #[] with
    | some nm, some us => buildChunkExprs st r slow (j+4+n) (exprs.insert i (.const nm us))
    | _, _ => return none
  else if tag == tNSTR || tag == tNNUM || tag == tLMAX || tag == tLIMAX then
    buildChunkExprs st r slow (j+4) exprs
  else if tag == tLSUCC || tag == tLPARAM then
    buildChunkExprs st r slow (j+3) exprs
  else if tag == tSORT then
    let i := rd r (j+1)
    if (← lmBmapGet i.toUInt64) == 0 then buildChunkExprs st r slow (j+3) exprs else
    match st.levels[rd r (j+2)]? with
    | some l => buildChunkExprs st r slow (j+3) (exprs.insert i (.sort l))
    | none => return none
  else if tag == tBVAR then
    let i := rd r (j+1)
    if (← lmBmapGet i.toUInt64) == 0 then buildChunkExprs st r slow (j+3) exprs else
    buildChunkExprs st r slow (j+3) (exprs.insert i (.bvar (rd r (j+2))))
  else if tag == tLETE then
    let i := rd r (j+1)
    if (← lmBmapGet i.toUInt64) == 0 then buildChunkExprs st r slow (j+7) exprs else
    let nd := rd r (j+2) == 1
    match st.names[rd r (j+4)]?, exprs[rd r (j+5)]?, exprs[rd r (j+6)]?, exprs[rd r (j+3)]? with
    | some nm, some ty, some v, some bd => buildChunkExprs st r slow (j+7) (exprs.insert i (.letE nm ty v bd nd))
    | _, _, _, _ => return none
  else if tag == tPROJ then
    let i := rd r (j+1)
    if (← lmBmapGet i.toUInt64) == 0 then buildChunkExprs st r slow (j+5) exprs else
    match st.names[rd r (j+4)]?, exprs[rd r (j+3)]? with
    | some nm, some s => buildChunkExprs st r slow (j+5) (exprs.insert i (.proj nm (rd r (j+2)) s))
    | _, _ => return none
  else if tag == tTHM then
    let nAll := rd r (j+1); let jl := j + 2 + nAll; let nLps := rd r jl
    buildChunkExprs st r slow (jl + 4 + nLps) exprs
  else if tag == tDEF then
    let nAll := rd r (j+1); let jl := j + 4 + nAll; let nLps := rd r jl
    buildChunkExprs st r slow (jl + 5 + nLps) exprs
  else if tag == tSLOW then
    match slow[rd r (j+1)]?.getD none with
    | some obj =>
      match ← buildSlowExpr? st exprs obj with
      | some exprs' => buildChunkExprs st r slow (j+2) exprs'
      | none => return none
    | none => return none
  else return none

def materializeDecl? (exprs : Std.HashMap Nat Expr) (pd : PendingDecl) : Option ConstantInfo := do
  let dummyVal := Expr.bvar 0
  match pd with
  | .axiomD name levelParams typeIdx isUnsafe =>
    return .axiomInfo { name, levelParams, type := (← exprs[typeIdx]?), isUnsafe }
  | .defnD name levelParams typeIdx valIdx? hints safety all =>
    let val ← match valIdx? with | some vi => exprs[vi]? | none => some dummyVal
    return .defnInfo { name, levelParams, type := (← exprs[typeIdx]?), value := val, hints, safety, all }
  | .thmD name levelParams typeIdx valIdx? all =>
    let val ← match valIdx? with | some vi => exprs[vi]? | none => some dummyVal
    return .thmInfo { name, levelParams, type := (← exprs[typeIdx]?), value := val, all }
  | .opaqueD name levelParams typeIdx valIdx? all isUnsafe =>
    let val ← match valIdx? with | some vi => exprs[vi]? | none => some dummyVal
    return .opaqueInfo { name, levelParams, type := (← exprs[typeIdx]?), value := val, all, isUnsafe }
  | .quotD name levelParams typeIdx kind =>
    return .quotInfo { name, levelParams, type := (← exprs[typeIdx]?), kind }
  | .inductD name levelParams typeIdx numParams numIndices all ctors numNested isRec isUnsafe isReflexive =>
    return .inductInfo { name, levelParams, type := (← exprs[typeIdx]?), numParams, numIndices, all, ctors,
                         numNested, isRec, isUnsafe, isReflexive }
  | .ctorD name levelParams typeIdx induct cidx numParams numFields isUnsafe =>
    return .ctorInfo { name, levelParams, type := (← exprs[typeIdx]?), induct, cidx, numParams, numFields, isUnsafe }
  | .recD name levelParams typeIdx all numParams numIndices numMotives numMinors rules k isUnsafe =>
    let rules' ← rules.mapM fun (ctor, nfields, rhsIdx) => do
      return { ctor, nfields, rhs := (← exprs[rhsIdx]?) : RecursorRule }
    return .recInfo { name, levelParams, type := (← exprs[typeIdx]?), all, numParams, numIndices,
                      numMotives, numMinors, rules := rules', k, isUnsafe }

def pushU32LE (ba : ByteArray) (v : UInt32) : ByteArray :=
  ba.push v.toUInt8
    |>.push (v >>> 8).toUInt8
    |>.push (v >>> 16).toUInt8
    |>.push (v >>> 24).toUInt8

def checkAxiomsFromC (st : LMSt) (theoremTargets definitionTargets legalAxioms : Array Name) :
    IO (Except String Unit) := do
  let mut rootsBa := ByteArray.emptyWithCapacity ((theoremTargets.size + definitionTargets.size) * 4)
  for target in theoremTargets do
    let some nidx := st.nameToIdx[target]?
      | return .error s!"Const not found in solution: '{target}'"
    let k ← lmGetDeclKind nidx.toUInt64
    if k == 0xFF then return .error s!"Const not found in solution: '{target}'"
    if k != kTHM.toUInt32 then return .error s!"Solution constant is not a theorem: '{target}'"
    rootsBa := pushU32LE rootsBa nidx
  for target in definitionTargets do
    let some nidx := st.nameToIdx[target]?
      | return .error s!"Const not found in solution: '{target}'"
    let k ← lmGetDeclKind nidx.toUInt64
    if k == 0xFF then return .error s!"Const not found in solution: '{target}'"
    if k != kDEF.toUInt32 then return .error s!"Solution constant is not a definition: '{target}'"
    rootsBa := pushU32LE rootsBa nidx
  let mut legalsBa := ByteArray.emptyWithCapacity (legalAxioms.size * 4)
  for ax in legalAxioms do
    if let some nidx := st.nameToIdx[ax]? then
      legalsBa := pushU32LE legalsBa nidx
  let code ← lmCheckAxiomsBfs rootsBa legalsBa
  if code == 0 then return .ok ()
  let tag := code >>> 32
  let badIdx := (code &&& 0xFFFFFFFF).toNat
  let badName := st.names[badIdx]?.getD .anonymous
  if tag == 1 then
    return .error s!"Constant not found in solution '{badName}'"
  else if tag == 2 then
    return .error s!"Illegal axiom detected: '{badName}'"
  else
    return .error "out of memory during checkAxioms"

def fallbackMaxBytes : UInt64 := 512 * 1024 * 1024

inductive LowMemOutcome where
  | judged (res : Except String Unit)
  | fallbackNeeded (reason : String)

def tryVerifyLowMem (challenge : LeanExport.ExportedEnv) (solutionPath : System.FilePath)
    (theoremTargets definitionTargets legalAxioms primitives : Array Name) : IO LowMemOutcome := do
  let t0 ← IO.monoMsNow
  let mdata ← solutionPath.metadata
  let fileBytes := mdata.byteSize
  if fileBytes == 0 then return .fallbackNeeded "empty file"
  if (← lmInit fileBytes) == 0 then return .fallbackNeeded "mmap arena init failed"
  try
    let mut keepNames : Std.HashSet Name := {}
    for (k, _) in challenge.constMap do keepNames := keepNames.insert k
    for n in theoremTargets do keepNames := keepNames.insert n
    for n in definitionTargets do keepNames := keepNames.insert n
    for n in legalAxioms do keepNames := keepNames.insert n
    for n in primitives do keepNames := keepNames.insert n
    let mut skipValueSet : Std.HashSet Name := {}
    for n in theoremTargets do skipValueSet := skipValueSet.insert n
    for n in definitionTargets do skipValueSet := skipValueSet.insert n
    let mut trackNameSet := keepNames
    for n in legalAxioms do trackNameSet := trackNameSet.insert n
    let mut nameToIdx : Std.HashMap Name UInt32 := {}
    if trackNameSet.contains .anonymous then nameToIdx := nameToIdx.insert .anonymous 0

    let h ← IO.FS.Handle.mk solutionPath .read
    let metaLine ← h.getLine
    if metaLine.isEmpty then
      lmResetAll
      return .fallbackNeeded "missing metadata line"
    -- validate metadata line is JSON object containing "meta" (like official parseMdata)
    match Json.parse metaLine with
    | .ok (.obj mo) =>
      if !mo.contains "meta" then
        lmResetAll
        return .fallbackNeeded "first line is not metadata"
    | _ =>
      lmResetAll
      return .fallbackNeeded "malformed metadata line"

    let metaBytes := metaLine.utf8ByteSize.toUInt64
    let sem ← Std.CloseableChannel.new (α := Unit)
    for _ in [0:maxWindowChunks] do
      let _ ← (sem.sync.send ()).toBaseIO
    let p ← IO.Promise.new
    let res := p.result?
    let bs : USize := (8 * 1024 * 1024).toUSize
    let _reader ← IO.asTask (prio := .dedicated) (readLoopBounded h bs sem metaBytes .empty p)

    let st0 : LMSt := {
      names := #[.anonymous], levels := #[.zero],
      nameToIdx, firstIdx := ({} : Std.HashMap Name UInt32).insert .anonymous 0, keepNames, skipValueSet, trackNameSet,
      pendingKeep := {}, chunkSpans := #[]
    }
    let some (st, nchunks) ← consumeP1 res sem st0 0 | do
      discard <| sem.close.toBaseIO
      lmResetAll
      return .fallbackNeeded "fast pass-1 declined"
    let st := { st with firstIdx := {} }   -- the Name -> first index map is needed by pass 1 only
    discard <| sem.close.toBaseIO
    if nchunks == 0 then
      lmResetAll
      return .fallbackNeeded "no data lines"

    let numExprs ← lmNumExprs
    let rssAfterP1 ← lmPeakRssKb
    IO.eprintln s!"[ccmp-lowmem] pass 1 streamed ({st.names.size} names, {numExprs} exprs, {st.pendingKeep.size} kept decls) in {(← IO.monoMsNow) - t0} ms (peak RSS {rssAfterP1 / 1024} MB)"

    -- Release Pass-1 expression DAG mmaps immediately!
    lmFreeExprDag

    -- Compute exact checkAxioms result over compact CSR graph, then release CSR graph mmaps!
    let axiomsRes ← checkAxiomsFromC st theoremTargets definitionTargets legalAxioms
    lmFreeGraph

    -- Pass 2: Materialize ONLY the subexpressions needed by `pendingKeep`
    if (← lmBmapInit numExprs) == 0 then
      lmResetAll
      return .fallbackNeeded "bmap mmap failed"
    for (_, pd) in st.pendingKeep do
      match pd with
      | .axiomD _ _ ti _ | .quotD _ _ ti _ | .inductD _ _ ti _ _ _ _ _ _ _ _ | .ctorD _ _ ti _ _ _ _ _ =>
        lmBmapSet ti.toUInt64
      | .defnD _ _ ti vi? _ _ _ | .thmD _ _ ti vi? _ | .opaqueD _ _ ti vi? _ _ =>
        lmBmapSet ti.toUInt64
        if let some vi := vi? then lmBmapSet vi.toUInt64
      | .recD _ _ ti _ _ _ _ _ rules _ _ =>
        lmBmapSet ti.toUInt64
        for (_, _, ri) in rules do lmBmapSet ri.toUInt64

    let solStr := solutionPath.toString
    let mut activeChunks : Array Nat := #[]
    let mut ci := st.chunkSpans.size
    while ci > 0 do
      ci := ci - 1
      let sp := st.chunkSpans[ci]!
      if (← lmBmapAnyRange sp.eLo sp.eHi) != 0 then
        activeChunks := activeChunks.push ci
        let buf ← lmPreadChunk solStr sp.fileOff sp.byteLen
        let tok := tokRange buf 1 buf.size { recs := Array.mkEmpty (buf.size / 12), strs := #[], slow := #[] }
        let deps := collectChunkDeps tok.recs tok.slow 0 #[]
        let mut di := deps.size
        while di > 0 do
          di := di - 1
          let (eidx, c1, c2, c3) := deps[di]!
          if (← lmBmapGet eidx) != 0 then
            if c1 != noChild then lmBmapSet c1
            if c2 != noChild then lmBmapSet c2
            if c3 != noChild then lmBmapSet c3

    let mut builtExprs : Std.HashMap Nat Expr := {}
    let mut ai := activeChunks.size
    while ai > 0 do
      ai := ai - 1
      let sp := st.chunkSpans[activeChunks[ai]!]!
      let buf ← lmPreadChunk solStr sp.fileOff sp.byteLen
      let tok := tokRange buf 1 buf.size { recs := Array.mkEmpty (buf.size / 12), strs := #[], slow := #[] }
      let some exprs' ← buildChunkExprs st tok.recs tok.slow 0 builtExprs | do
        lmResetAll
        return .fallbackNeeded "pass-2 selective build failed"
      builtExprs := exprs'

    lmBmapFree

    let mut solKeepMap : Std.HashMap Name ConstantInfo := Std.HashMap.emptyWithCapacity st.pendingKeep.size
    for (nm, pd) in st.pendingKeep do
      let some info := materializeDecl? builtExprs pd | do
        lmResetAll
        return .fallbackNeeded s!"missing materialized expr for {nm}"
      solKeepMap := solKeepMap.insert nm info

    let solRestricted : LeanExport.ExportedEnv := { constMap := solKeepMap, constOrder := #[] }
    let targets := theoremTargets ++ legalAxioms
    -- Exact official order: compareAt FIRST, then checkAxioms!
    let cmpRes : Except String Unit := do
      Lake.Check.compareAt challenge solRestricted targets definitionTargets primitives
      axiomsRes

    let rssEnd ← lmPeakRssKb
    IO.eprintln s!"[ccmp-lowmem] pass 2 selectively built {builtExprs.size}/{numExprs} exprs from {activeChunks.size}/{st.chunkSpans.size} chunks; total {(← IO.monoMsNow) - t0} ms (peak RSS {rssEnd / 1024} MB)"
    lmResetAll
    return .judged cmpRes
  catch e =>
    lmResetAll
    return .fallbackNeeded s!"io exception: {e}"

/-- Entry point matching `CCmp.lean`'s `verifyCompareFast` semantics in bounded memory. -/
def verifyCompareLowMem (challengeExportPath solutionExportPath : System.FilePath)
    (theoremNames definitionNames legalAxioms primitives : Array Name) : IO Unit := do
  let t0 ← IO.monoMsNow
  let challenge ← FastExport.parseExportFile challengeExportPath
  IO.eprintln s!"[ccmp-lowmem] challenge parsed ({challenge.constMap.size} constants) in {(← IO.monoMsNow) - t0} ms"
  match ← tryVerifyLowMem challenge solutionExportPath theoremNames definitionNames legalAxioms primitives with
  | .judged (.ok ()) => return ()
  | .judged (.error msg) => throw <| IO.userError msg
  | .fallbackNeeded why =>
    let sz := (← solutionExportPath.metadata).byteSize
    if sz <= fallbackMaxBytes then
      IO.eprintln s!"[ccmp-lowmem] falling back to official LeanExport.parseStream ({why}; size {sz} B)"
      let solution ← IO.FS.withFile solutionExportPath .read fun h => LeanExport.parseStream (.ofHandle h)
      let targets := theoremNames ++ legalAxioms
      IO.ofExcept <| Lake.Check.compareAt challenge solution targets definitionNames primitives
      IO.ofExcept <| Lake.Check.checkAxioms solution theoremNames definitionNames legalAxioms
    else
      throw <| IO.userError s!"out of memory / cannot stream non-canonical >512 MiB export ({why})"

end LowMemParse
