import Std.Data.HashMap
import Lean.Declaration
import Lean.Data.Json.Parser
import LeanExport.Parse

/-!
# Fast reader for the Lean 4 NDJSON export format (drop-in for `LeanExport.parseStream`)

Exactness contract: for every input file, `parseFile? path` either returns `none` (the caller then runs the
OFFICIAL `LeanExport.parseStream` on the file from scratch) or returns exactly the `constMap`/`constOrder`
the official parser returns on that file.

How:
* lines are split exactly like `IO.FS.Stream.getLine` (at `\n`, the first line is skipped like `parseMdata`);
* a line is a String only if it is valid UTF-8 (otherwise `none`: the official reader's lossy conversion is
  not replicated);
* the official parser keeps `HashMap Nat _` tables; we keep ARRAYS and require the canonical dense numbering
  (each new name/level/expr index = current table size). Then "index bound" <-> "index < size", so every
  lookup/insert has the official semantics; any other index -> `none`;
* a hot line kind is recognised by an exact byte template of `Json.compress` output (sorted keys, no spaces,
  canonical non-negative integers, strings without `\`/control chars); the semantic action is the official
  one (same constructors, same order of table updates);
* every other line goes through `Json.parse` + a verbatim copy of the official per-line logic (on the array
  tables);
* any error anywhere -> `none` (so error behaviour = official behaviour, because the official parser then runs).
-/

namespace FastExport
open Lean

structure St where
  names : Array Name
  levels : Array Level
  exprs : Array Expr
  constMap : Std.HashMap Name ConstantInfo
  constOrder : Array Name

/-! ## Slow path: verbatim copy of the official per-line logic, on array tables -/
namespace Slow

abbrev M := StateT St (Except String)

@[inline] def fail (msg : String) : M α := throw msg

@[inline] def getName (nidx : Nat) : M Lean.Name := do
  let some n := (← get).names[nidx]? | fail s!"Name not found {nidx}"
  return n

@[inline] def addName (nidx : Nat) (n : Lean.Name) : M Unit := do
  if nidx != (← get).names.size then fail s!"Name index {nidx} bound twice or sparse"
  modify fun s => { s with names := s.names.push n }

@[inline] def getLevel (uidx : Nat) : M Lean.Level := do
  let some l := (← get).levels[uidx]? | fail s!"Level not found {uidx}"
  return l

@[inline] def addLevel (uidx : Nat) (l : Lean.Level) : M Unit := do
  if uidx != (← get).levels.size then fail s!"Level index {uidx} bound twice or sparse"
  modify fun s => { s with levels := s.levels.push l }

@[inline] def getExpr (eidx : Nat) : M Lean.Expr := do
  let some e := (← get).exprs[eidx]? | fail s!"Expr not found {eidx}"
  return e

@[inline] def addExpr (eidx : Nat) (e : Lean.Expr) : M Unit := do
  if eidx != (← get).exprs.size then fail s!"Expr index {eidx} bound twice or sparse"
  modify fun s => { s with exprs := s.exprs.push e }

@[inline] def addConst (name : Lean.Name) (d : Lean.ConstantInfo) : M Unit := do
  if (← get).constMap.contains name then
    fail s!"Duplicate declaration: {name}"
  modify fun s => {
    s with
      constMap := s.constMap.insert name d
      constOrder := s.constOrder.push name
    }

@[inline]
def parseJsonObj (line : String) : M (Std.TreeMap.Raw String Json) := do
  match Json.parse line with
  | .ok (.obj obj) => return obj
  | .ok _ => fail "Expected JSON object"
  | .error e => fail s!"Invalid JSON: {e}"

def parseNameStr (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.str invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.str str) := data["str"]? | fail s!"Name.str invalid"
  return .str (← getName preIdx) str

def parseNameNum (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.num invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.num (i : Nat)) := data["i"]? | fail s!"Name.num invalid"
  return .num (← getName preIdx) i

def parseLevelSucc (json : Json) : M Level := do
  let .num (lIdx : Nat) := json | fail s!"Level.succ invalid"
  return .succ (← getLevel lIdx)

def parseLevelMax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.max invalid"
  return .max (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelImax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.imax invalid"
  return .imax (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelParam (json : Json) : M Level := do
  let .num (nIdx : Nat) := json | fail s!"Level.param invalid"
  return .param (← getName nIdx)

def parseExprBVar (json : Json) : M Expr := do
  let .num (deBruijnIndex : Nat) := json | fail s!"Expr.bvar invalid"
  return .bvar deBruijnIndex

def parseExprSort (json : Json) : M Expr := do
  let .num (uIdx : Nat) := json | fail s!"Expr.sort invalid"
  return .sort (← getLevel uIdx)

def parseExprConst (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.const invalid"
  let some (.num (declNameIdx : Nat)) := data["name"]? | fail s!"Expr.const invalid"
  let some (.arr usIdxs) := data["us"]? | fail s!"Expr.const invalid"
  let declName ← getName declNameIdx
  let us ← usIdxs.mapM fun uIdx => do
    let (.num (uIdx : Nat)) := uIdx | fail s!"Expr.const invalid"
    getLevel uIdx
  return .const declName us.toList

def parseExprApp (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.app invalid"
  let some (.num (fnIdx : Nat)) := data["fn"]? | fail s!"Expr.app invalid"
  let some (.num (argIdx : Nat)) := data["arg"]? | fail s!"Expr.app invalid"
  let fn ← getExpr fnIdx
  let arg ← getExpr argIdx
  return .app fn arg

def parseBinderInfo (info : String) : M BinderInfo :=
  match info with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => fail s!"Invalid binder info: {info}"

def parseExprLam (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.lam invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.lam invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.lam invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.lam invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.lam invalid"
  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr
  return .lam binderName binderType body binderInfo

def parseExprForallE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.forallE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.forallE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.forallE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.forallE invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.forallE invalid"
  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr
  return .forallE binderName binderType body binderInfo

def parseExprLetE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.letE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.letE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.letE invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"Expr.letE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.letE invalid"
  let some (.bool nondep) := data["nondep"]? | fail s!"Expr.letE invalid"
  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let value ← getExpr valueIdx
  let body ← getExpr bodyIdx
  return .letE binderName binderType value body nondep

def parseExprProj (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.proj invalid"
  let some (.num (typeNameIdx : Nat)) := data["typeName"]? | fail s!"Expr.proj invalid"
  let some (.num (projIdx : Nat)) := data["idx"]? | fail s!"Expr.proj invalid"
  let some (.num (structIdx : Nat)) := data["struct"]? | fail s!"Expr.proj invalid"
  let typeName ← getName typeNameIdx
  let struct ← getExpr structIdx
  return .proj typeName projIdx struct

def parseExprNatLit (json : Json) : M Expr := do
  let .str natValStr := json | fail s!"Expr.lit natVal invalid"
  let some natVal := String.toNat? natValStr | fail s!"Expr.lit natVal invalid"
  return .lit (.natVal natVal)

def parseExprStrLit (json : Json) : M Expr := do
  let .str strVal := json | fail s!"Expr.lit strVal invalid"
  return .lit (.strVal strVal)

def parseExprMdata (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.mdata invalid"
  let some (.num (exprIdx : Nat)) := data["expr"]? | fail s!"Expr.mdata invalid"
  let some (.obj _dataObj) := data["data"]? | fail s!"Expr.mdata invalid"
  let expr ← getExpr exprIdx
  return .mdata {} expr

def getNameList (idxs : Array Json) : M (List Name) := do
  idxs.toList.mapM fun idx => do
    let (.num (idx : Nat)) := idx | fail s!"failed to convert to name idx"
    getName idx

def parseAxiomInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"axiomInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"axiomInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"axiomInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"axiomInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  addConst name <| .axiomInfo { name, levelParams, type, isUnsafe }

def parseDefnInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"defnInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"defnInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"defnInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"defnInfo invalid"
  let some hints := data["hints"]? | fail s!"defnInfo invalid"
  let some (.str safetyStr) := data["safety"]? | fail s!"defnInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"defnInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let hints ←
    match hints with
    | .str "opaque" => pure .opaque
    | .str "abbrev" => pure .abbrev
    | .obj obj =>
      let some (.num (level : Nat)) := obj["regular"]? | fail s!"defnInfo invalid"
      pure <| .regular level.toUInt32
    | _ => fail s!"defnInfo invalid"
  let safety ←
    match safetyStr with
    | "unsafe" => pure .unsafe
    | "safe" => pure .safe
    | "partial" => pure .partial
    | _ => fail s!"Unknown safety parameter: {safetyStr}"
  let all ← getNameList allIdxs
  addConst name <| .defnInfo { name, levelParams, type, value, hints, safety, all }

def parseThmInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"thmInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"thmInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"thmInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"thmInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"thmInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs
  addConst name <| .thmInfo { name, levelParams, type, value, all }

def parseOpaqueInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"opaqueInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"opaqueInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"opaqueInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"opaqueInfo invalid"
  -- Work around until the exporter always includes isUnsafe
  let (.bool isUnsafe) := data["isUnsafe"]?.getD (.bool false) | fail s!"axiomInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"opaqueInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs
  addConst name <| .opaqueInfo { name, levelParams, type, value, all, isUnsafe }

def parseQuotInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"quotInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"quotInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"quotInfo invalid"
  let some (.str kindStr) := data["kind"]? | fail s!"quotInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let kind ←
    match kindStr with
    | "type" => pure .type
    | "ctor" => pure .ctor
    | "lift" => pure .lift
    | "ind" => pure .ind
    | _ => fail s!"unknown quot kind: {kindStr}"
  addConst name <| .quotInfo { name, levelParams, type, kind }

def parseInductInfo (json : Json) : M Unit := do
  let .obj data := json | fail "inductInfo invalid: Expected JSON object"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"inductInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"inductInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"inductInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"inductInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"inductInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"inductInfo invalid"
  let some (.arr ctorsIdxs) := data["ctors"]? | fail s!"inductInfo invalid"
  let some (.num (numNested : Nat)) := data["numNested"]? | fail s!"inductInfo invalid"
  let some (.bool isRec) := data["isRec"]? | fail s!"inductInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"inductInfo invalid"
  let some (.bool isReflexive) := data["isReflexive"]? | fail s!"inductInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let ctors ← getNameList ctorsIdxs
  addConst name <| .inductInfo {
    name, levelParams, type, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive }

def parseCtorInfo (json : Json) : M Unit := do
  let .obj data := json | fail s!"ctorInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"ctorInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"ctorInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"ctorInfo invalid"
  let some (.num (inductIdx : Nat)) := data["induct"]? | fail s!"ctorInfo invalid"
  let some (.num (cidx : Nat)) := data["cidx"]? | fail s!"ctorInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"ctorInfo invalid"
  let some (.num (numFields : Nat)) := data["numFields"]? | fail s!"ctorInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"ctorInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let induct ← getName inductIdx
  addConst name <| .ctorInfo { name, levelParams, type, induct, cidx, numParams, numFields, isUnsafe }

def parseRecInfo (json : Json) : M Unit := do
  let .obj data := json | fail s!"recInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"recInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"recInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"recInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"recInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"recInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"recInfo invalid"
  let some (.num (numMotives : Nat)) := data["numMotives"]? | fail s!"recInfo invalid"
  let some (.num (numMinors : Nat)) := data["numMinors"]? | fail s!"recInfo invalid"
  let some (.bool k) := data["k"]? | fail s!"recInfo invalid"
  let some (.arr rules) := data["rules"]? | fail s!"recInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"recInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let rules ← rules.toList.mapM fun rule => do
    let .obj rule := rule | fail s!"recInfo invalid"
    let some (.num (ctorIdx : Nat)) := rule["ctor"]? | fail s!"recInfo invalid"
    let some (.num (nfields : Nat)) := rule["nfields"]? | fail s!"recInfo invalid"
    let some (.num (rhsIdx : Nat)) := rule["rhs"]? | fail s!"recInfo invalid"
    let ctor ← getName ctorIdx
    let rhs ← getExpr rhsIdx
    return { ctor, nfields, rhs }
  addConst name <| .recInfo {
    name, levelParams, type, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }

def parseInductive (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.arr types) := data["types"]? | fail s!"Inductive invalid, no `types`"
  let some (.arr ctors) := data["ctors"]? | fail s!"Inductive invalid, no `ctors`"
  let some (.arr recs) := data["recs"]? | fail s!"Inductive invalid, no `recs`"
  types.forM parseInductInfo
  ctors.forM parseCtorInfo
  recs.forM parseRecInfo

def parseItemObj (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let kv := obj.toList
  -- Normalize key order...
  let kv := match kv with
    | [x, y@("in", _)] => [y,x]
    | [x, y@("ie", _)] => [y,x]
    | [x, y@("il", _)] => [y,x]
    | _ =>kv
  -- so that we can match on it easily
  match kv with
  | [("in", .num (idx : Nat)),("str", data)] =>   addName idx <| ← parseNameStr data
  | [("in", .num (idx : Nat)),("num", data)] =>   addName idx <| ← parseNameNum data
  | [("il", .num (idx : Nat)),("succ", data)] =>  addLevel idx <| ← parseLevelSucc data
  | [("il", .num (idx : Nat)),("max", data)] =>   addLevel idx <| ← parseLevelMax data
  | [("il", .num (idx : Nat)),("imax", data)] =>  addLevel idx <| ← parseLevelImax data
  | [("il", .num (idx : Nat)),("param", data)] => addLevel idx <| ← parseLevelParam data
  | [("ie", .num (idx : Nat)),("bvar", data)] =>  addExpr idx <| ← parseExprBVar data
  | [("ie", .num (idx : Nat)),("sort", data)] =>  addExpr idx <| ← parseExprSort data
  | [("ie", .num (idx : Nat)),("const", data)] => addExpr idx <| ← parseExprConst data
  | [("ie", .num (idx : Nat)),("app", data)] =>   addExpr idx <| ← parseExprApp data
  | [("ie", .num (idx : Nat)),("lam", data)] =>   addExpr idx <| ← parseExprLam data
  | [("ie", .num (idx : Nat)),("forallE", data)] =>addExpr idx <| ← parseExprForallE data
  | [("ie", .num (idx : Nat)),("letE", data)] =>   addExpr idx <| ← parseExprLetE data
  | [("ie", .num (idx : Nat)),("proj", data)] =>   addExpr idx <| ← parseExprProj data
  | [("ie", .num (idx : Nat)),("natVal", data)] => addExpr idx <| ← parseExprNatLit data
  | [("ie", .num (idx : Nat)),("strVal", data)] => addExpr idx <| ← parseExprStrLit data
  | [("ie", .num (idx : Nat)),("mdata", data)] => addExpr idx <| ← parseExprMdata data
  | [("axiom", .obj data)] => parseAxiomInfo data
  | [("def", .obj data)] => parseDefnInfo data
  | [("thm", .obj data)] => parseThmInfo data
  | [("opaque", .obj data)] => parseOpaqueInfo data
  | [("quot", .obj data)] => parseQuotInfo data
  | [("inductive", .obj data)] => parseInductive data
  | _ => fail s!"Unknown export object with keys {obj.keys}"

/-- = official `parseItem` -/
def parseItem (line : String) : M Unit := do
  let obj ← parseJsonObj line
  parseItemObj obj

end Slow

/-! ## Fast path: exact byte templates of the canonical lean4export lines -/

/-- position `0` = failure (data lines never start at offset 0: the first line is the metadata line). -/
abbrev Pos := Nat

/-- match the literal `s` at `p`; returns the position after it, or 0. -/
partial def litGo (b : ByteArray) (p : Pos) (s : ByteArray) (i : Nat) : Pos :=
  if i < s.size then
    if b.get! (p + i) == s.get! i then litGo b p s (i + 1) else 0
  else p + s.size

@[inline] def lit (b : ByteArray) (p : Pos) (s : ByteArray) : Pos :=
  if p == 0 || p + s.size > b.size then 0 else litGo b p s 0

@[inline] def isDigit (c : UInt8) : Bool := c >= 48 && c <= 57

/-- canonical non-negative JSON integer at `p` ("0" or [1-9][0-9]*, at most 18 digits): end position or 0. -/
partial def numEndGo (b : ByteArray) (q : Nat) (n : Nat) : Pos :=
  if n > 18 then 0
  else if q < b.size && isDigit (b.get! q) then numEndGo b (q + 1) (n + 1) else q

@[inline] def numEnd (b : ByteArray) (p : Pos) : Pos :=
  if p == 0 || p >= b.size then 0 else
  let c := b.get! p
  if c == 48 then p + 1   -- "0"; a following digit makes the next literal fail
  else if c >= 49 && c <= 57 then numEndGo b (p + 1) 1
  else 0

/-- value of the digits in `[p, q)` (already validated by `numEnd`, at most 18 digits). -/
partial def numValGo (b : ByteArray) (q : Pos) (i : Nat) (acc : UInt64) : Nat :=
  if i < q then numValGo b q (i + 1) (acc * 10 + (b.get! i - 48).toUInt64) else acc.toNat

@[inline] def numVal (b : ByteArray) (p q : Pos) : Nat := numValGo b q p 0

/-- end of a JSON string body starting at `p` (just after the opening quote): position of the closing quote,
or 0 if the string contains `\` or a control character (< 0x20) before the closing quote. -/
partial def strEndGo (b : ByteArray) (q : Nat) : Pos :=
  if q < b.size then
    let c := b.get! q
    if c == 34 then q
    else if c == 92 || c < 32 then 0
    else strEndGo b (q + 1)
  else 0

@[inline] def strEnd (b : ByteArray) (p : Pos) : Pos :=
  if p == 0 then 0 else strEndGo b p

/-- the string with bytes `[p, q)` if valid UTF-8. -/
@[inline] def mkStr (b : ByteArray) (p q : Pos) : Option String :=
  String.fromUTF8? (b.extract p q)

def L (s : String) : ByteArray := s.toUTF8

-- literals
def lApp := L "{\"app\":{\"arg\":"
def lFn := L ",\"fn\":"
def lCloseIe := L "},\"ie\":"
def lClose := L "}"
def lClose2 := L "}}"
def lBvar := L "{\"bvar\":"
def lIe := L ",\"ie\":"
def lConst := L "{\"const\":{\"name\":"
def lUs := L ",\"us\":["
def lForall := L "{\"forallE\":{\"binderInfo\":\""
def lBody := L "\",\"body\":"
def lName := L ",\"name\":"
def lType := L ",\"type\":"
def lValue := L ",\"value\":"
def lIeOpen := L "{\"ie\":"
def lLam := L ",\"lam\":{\"binderInfo\":\""
def lSort := L ",\"sort\":"
def lIn := L "{\"in\":"
def lStrPre := L ",\"str\":{\"pre\":"
def lStrStr := L ",\"str\":\""
def lQClose2 := L "\"}}"
def lNumI := L ",\"num\":{\"i\":"
def lPre := L ",\"pre\":"
def lIl := L "{\"il\":"
def lSucc := L ",\"succ\":"
def lParam := L ",\"param\":"
def lMax := L ",\"max\":["
def lImax := L ",\"imax\":["
def lComma := L ","
def lRBrClose := L "]}"
def lThm := L "{\"thm\":{\"all\":["
def lLevelParams := L "],\"levelParams\":["
def lNameAfterArr := L "],\"name\":"
def lDef := L "{\"def\":{\"all\":["
def lHints := L "],\"hints\":"
def lHOpaque := L "\"opaque\""
def lHAbbrev := L "\"abbrev\""
def lHRegular := L "{\"regular\":"
def lLevelParams2 := L ",\"levelParams\":["
def lSafety := L ",\"safety\":\""
def lQType := L "\",\"type\":"
def lLetE := L ",\"letE\":{\"body\":"
def lNondep := L ",\"nondep\":"
def lTrue := L "true"
def lFalse := L "false"
def lProj := L ",\"proj\":{\"idx\":"
def lStruct := L ",\"struct\":"
def lTypeName := L ",\"typeName\":"
def lNatVal := L ",\"natVal\":\""
def lStrVal := L ",\"strVal\":\""
def lQClose := L "\"}"
def lDefault := L "default"
def lImplicit := L "implicit"
def lInstImplicit := L "instImplicit"
def lStrictImplicit := L "strictImplicit"
def lSafe := L "safe"
def lUnsafe := L "unsafe"
def lPartial := L "partial"
def lUsClose := L "]},\"ie\":"

@[inline] def binderInfo? (b : ByteArray) (p q : Pos) : Option BinderInfo :=
  -- bytes [p, q) of the binderInfo string
  let n := q - p
  if n == 7 && lit b p lDefault == q then some .default
  else if n == 8 && lit b p lImplicit == q then some .implicit
  else if n == 12 && lit b p lInstImplicit == q then some .instImplicit
  else if n == 14 && lit b p lStrictImplicit == q then some .strictImplicit
  else none

/-! ### Phase A (parallel): tokenize canonical lines into flat records (no table access) -/

/-- tokenizer output for one chunk: flat `Array Nat` records (all numbers < 10^18 are unboxed scalars)
plus the name strings. -/
structure Tok where
  recs : Array Nat
  strs : Array String
  /-- slow lines: `Json.parse` of the line (as the official `parseJsonObj` does it), already in phase A;
  `none` = invalid UTF-8 or not a JSON object (-> decline) -/
  slow : Array (Option (Std.TreeMap.Raw String Json))

-- record tags
def tSLOW := 0    -- [0, slowIdx]                    line handled by the official per-line logic in phase B
def tAPP := 1     -- [1, i, fn, arg]
def tFORALL := 2  -- [2, i, bi, body, name, type]
def tLAM := 3     -- [3, i, bi, body, name, type]
def tCONST := 4   -- [4, i, name, n, l_1 .. l_n]
def tSORT := 5    -- [5, i, u]
def tBVAR := 6    -- [6, i, k]
def tLETE := 7    -- [7, i, nondep, body, name, type, value]
def tPROJ := 8    -- [8, i, idx, struct, typeName]
def tNSTR := 9    -- [9, i, pre, strIdx]
def tNNUM := 10   -- [10, i, k, pre]
def tLSUCC := 11  -- [11, i, l]
def tLMAX := 12   -- [12, i, a, b]
def tLIMAX := 13  -- [13, i, a, b]
def tLPARAM := 14 -- [14, i, n]
def tTHM := 15    -- [15, nAll, all.., nLps, lps.., name, type, value]
def tDEF := 16    -- [16, nAll, all.., hintKind, hintVal, nLps, lps.., name, safety, type, value]

@[inline] def binderCode? (b : ByteArray) (p q : Pos) : Nat :=
  -- bytes [p, q) of the binderInfo string -> 0 default, 1 implicit, 2 strictImplicit, 3 instImplicit, 4 = not canonical
  let n := q - p
  if n == 7 && lit b p lDefault == q then 0
  else if n == 8 && lit b p lImplicit == q then 1
  else if n == 14 && lit b p lStrictImplicit == q then 2
  else if n == 12 && lit b p lInstImplicit == q then 3
  else 4

@[inline] def binderOf (c : Nat) : BinderInfo :=
  if c == 0 then .default else if c == 1 then .implicit else if c == 2 then .strictImplicit else .instImplicit

/-- scan an index list body (after `[`) up to `]`: (count, position of `]`) or (0, 0) if not canonical. -/
partial def listScan (b : ByteArray) (p : Pos) (n : Nat) : Nat × Pos :=
  if p == 0 || p >= b.size then (0, 0)
  else if b.get! p == 93 then  -- ']'
    if n == 0 then (0, p) else (0, 0)  -- "]" right after "," is invalid
  else
    let q := numEnd b p
    if q == 0 then (0, 0)
    else if q < b.size && b.get! q == 44 then listScan b (q + 1) (n + 1)
    else if q < b.size && b.get! q == 93 then (n + 1, q)
    else (0, 0)

/-- push the values of a list body already validated by `listScan`. -/
partial def listPush (b : ByteArray) (p : Pos) (recs : Array Nat) : Array Nat :=
  if b.get! p == 93 then recs
  else
    let q := numEnd b p
    let recs := recs.push (numVal b p q)
    if b.get! q == 44 then listPush b (q + 1) recs else recs

/-- a non-template line: run `Json.parse` now (pure, so the same value as in the official sequential
reader); getLine includes the `\n` (if any) in the line, Json.parse skips it as whitespace - we do the same. -/
def slowRec (b : ByteArray) (p e : Pos) (t : Tok) : Tok :=
  let e' := if e < b.size then e + 1 else e
  let obj? := match String.fromUTF8? (b.extract p e') with
    | none => none
    | some line => match Json.parse line with
      | .ok (.obj obj) => some obj
      | _ => none
  { t with recs := t.recs.push tSLOW |>.push t.slow.size, slow := t.slow.push obj? }

/-- tokenize the line `[p, e)`. -/
def tokLine (b : ByteArray) (p e : Pos) (t : Tok) : Tok :=
  let c2 := b.get! (p + 2)
  if c2 == 97 then -- 'a' : app
    let p1 := lit b p lApp; let p2 := numEnd b p1
    let p3 := lit b p2 lFn; let p4 := numEnd b p3
    let p5 := lit b p4 lCloseIe; let p6 := numEnd b p5
    let p7 := lit b p6 lClose
    if p7 != e || p7 == 0 then slowRec b p e t else
    { t with recs := t.recs.push tAPP |>.push (numVal b p5 p6) |>.push (numVal b p3 p4) |>.push (numVal b p1 p2) }
  else if c2 == 102 then -- 'f' : forallE
    let p1 := lit b p lForall; let p2 := strEnd b p1
    let p3 := lit b p2 lBody; let p4 := numEnd b p3
    let p5 := lit b p4 lName; let p6 := numEnd b p5
    let p7 := lit b p6 lType; let p8 := numEnd b p7
    let p9 := lit b p8 lCloseIe; let p10 := numEnd b p9
    let p11 := lit b p10 lClose
    if p11 != e || p11 == 0 then slowRec b p e t else
    let bi := binderCode? b p1 p2
    if bi == 4 then slowRec b p e t else
    { t with recs := t.recs.push tFORALL |>.push (numVal b p9 p10) |>.push bi |>.push (numVal b p3 p4)
                      |>.push (numVal b p5 p6) |>.push (numVal b p7 p8) }
  else if c2 == 99 then -- 'c' : const
    let p1 := lit b p lConst; let p2 := numEnd b p1
    let p3 := lit b p2 lUs
    let (n, q) := listScan b p3 0
    let p5 := lit b q lUsClose; let p6 := numEnd b p5
    let p7 := lit b p6 lClose
    if p7 != e || p7 == 0 then slowRec b p e t else
    { t with recs := listPush b p3 (t.recs.push tCONST |>.push (numVal b p5 p6) |>.push (numVal b p1 p2) |>.push n) }
  else if c2 == 105 then -- 'i' : in / il / ie
    let c3 := b.get! (p + 3)
    if c3 == 110 then -- in
      let p1 := lit b p lIn; let p2 := numEnd b p1
      let c := if p2 != 0 && p2 + 2 < b.size then b.get! (p2 + 2) else 0
      if c == 115 then -- ,"str":{"pre":P,"str":"S"}}
        let p3 := lit b p2 lStrPre; let p4 := numEnd b p3
        let p5 := lit b p4 lStrStr; let p6 := strEnd b p5
        let p7 := lit b p6 lQClose2
        if p7 != e || p7 == 0 then slowRec b p e t else
        match mkStr b p5 p6 with
        | none => slowRec b p e t   -- invalid UTF-8: the slow path declines the whole file
        | some s =>
          { t with recs := t.recs.push tNSTR |>.push (numVal b p1 p2) |>.push (numVal b p3 p4) |>.push t.strs.size,
                   strs := t.strs.push s }
      else if c == 110 then -- ,"num":{"i":K,"pre":P}}
        let p3 := lit b p2 lNumI; let p4 := numEnd b p3
        let p5 := lit b p4 lPre; let p6 := numEnd b p5
        let p7 := lit b p6 lClose2
        if p7 != e || p7 == 0 then slowRec b p e t else
        { t with recs := t.recs.push tNNUM |>.push (numVal b p1 p2) |>.push (numVal b p3 p4) |>.push (numVal b p5 p6) }
      else slowRec b p e t
    else if c3 == 108 then -- il
      let p1 := lit b p lIl; let p2 := numEnd b p1
      if p2 == 0 then slowRec b p e t else
      let i := numVal b p1 p2
      let c := if p2 + 2 < b.size then b.get! (p2 + 2) else 0
      if c == 115 then -- succ
        let p3 := lit b p2 lSucc; let p4 := numEnd b p3; let p5 := lit b p4 lClose
        if p5 != e || p5 == 0 then slowRec b p e t else
        { t with recs := t.recs.push tLSUCC |>.push i |>.push (numVal b p3 p4) }
      else if c == 112 then -- param
        let p3 := lit b p2 lParam; let p4 := numEnd b p3; let p5 := lit b p4 lClose
        if p5 != e || p5 == 0 then slowRec b p e t else
        { t with recs := t.recs.push tLPARAM |>.push i |>.push (numVal b p3 p4) }
      else if c == 109 || c == 105 then -- max / imax
        let p3 := lit b p2 (if c == 109 then lMax else lImax); let p4 := numEnd b p3
        let p5 := lit b p4 lComma; let p6 := numEnd b p5; let p7 := lit b p6 lRBrClose
        if p7 != e || p7 == 0 then slowRec b p e t else
        { t with recs := t.recs.push (if c == 109 then tLMAX else tLIMAX) |>.push i |>.push (numVal b p3 p4)
                          |>.push (numVal b p5 p6) }
      else slowRec b p e t
    else if c3 == 101 then -- ie : lam / sort / letE / proj  (natVal / strVal / mdata -> slow)
      let p1 := lit b p lIeOpen; let p2 := numEnd b p1
      if p2 == 0 then slowRec b p e t else
      let i := numVal b p1 p2
      let c := if p2 + 2 < b.size then b.get! (p2 + 2) else 0
      let c' := if p2 + 3 < b.size then b.get! (p2 + 3) else 0
      if c == 108 && c' == 97 then -- lam
        let p3 := lit b p2 lLam; let p4 := strEnd b p3
        let p5 := lit b p4 lBody; let p6 := numEnd b p5
        let p7 := lit b p6 lName; let p8 := numEnd b p7
        let p9 := lit b p8 lType; let p10 := numEnd b p9
        let p11 := lit b p10 lClose2
        if p11 != e || p11 == 0 then slowRec b p e t else
        let bi := binderCode? b p3 p4
        if bi == 4 then slowRec b p e t else
        { t with recs := t.recs.push tLAM |>.push i |>.push bi |>.push (numVal b p5 p6) |>.push (numVal b p7 p8)
                          |>.push (numVal b p9 p10) }
      else if c == 115 && c' == 111 then -- sort
        let p3 := lit b p2 lSort; let p4 := numEnd b p3; let p5 := lit b p4 lClose
        if p5 != e || p5 == 0 then slowRec b p e t else
        { t with recs := t.recs.push tSORT |>.push i |>.push (numVal b p3 p4) }
      else if c == 108 && c' == 101 then -- letE
        let p3 := lit b p2 lLetE; let p4 := numEnd b p3
        let p5 := lit b p4 lName; let p6 := numEnd b p5
        let p7 := lit b p6 lNondep
        let pt := lit b p7 lTrue
        let (nd, p8) := if pt != 0 then (1, pt) else (0, lit b p7 lFalse)
        let p9 := lit b p8 lType; let p10 := numEnd b p9
        let p11 := lit b p10 lValue; let p12 := numEnd b p11
        let p13 := lit b p12 lClose2
        if p13 != e || p13 == 0 then slowRec b p e t else
        { t with recs := t.recs.push tLETE |>.push i |>.push nd |>.push (numVal b p3 p4) |>.push (numVal b p5 p6)
                          |>.push (numVal b p9 p10) |>.push (numVal b p11 p12) }
      else if c == 112 && c' == 114 then -- proj
        let p3 := lit b p2 lProj; let p4 := numEnd b p3
        let p5 := lit b p4 lStruct; let p6 := numEnd b p5
        let p7 := lit b p6 lTypeName; let p8 := numEnd b p7
        let p9 := lit b p8 lClose2
        if p9 != e || p9 == 0 then slowRec b p e t else
        { t with recs := t.recs.push tPROJ |>.push i |>.push (numVal b p3 p4) |>.push (numVal b p5 p6)
                          |>.push (numVal b p7 p8) }
      else slowRec b p e t
    else slowRec b p e t
  else if c2 == 98 then -- 'b' : bvar
    let p1 := lit b p lBvar; let p2 := numEnd b p1
    let p3 := lit b p2 lIe; let p4 := numEnd b p3
    let p5 := lit b p4 lClose
    if p5 != e || p5 == 0 then slowRec b p e t else
    { t with recs := t.recs.push tBVAR |>.push (numVal b p3 p4) |>.push (numVal b p1 p2) }
  else if c2 == 116 then -- 't' : thm
    let p1 := lit b p lThm
    let (nAll, q1) := listScan b p1 0
    let p2 := lit b q1 lLevelParams
    let (nLps, q2) := listScan b p2 0
    let p3 := lit b q2 lNameAfterArr; let p4 := numEnd b p3
    let p5 := lit b p4 lType; let p6 := numEnd b p5
    let p7 := lit b p6 lValue; let p8 := numEnd b p7
    let p9 := lit b p8 lClose2
    if p9 != e || p9 == 0 then slowRec b p e t else
    let r := listPush b p1 (t.recs.push tTHM |>.push nAll)
    let r := listPush b p2 (r.push nLps)
    { t with recs := r.push (numVal b p3 p4) |>.push (numVal b p5 p6) |>.push (numVal b p7 p8) }
  else if c2 == 100 then -- 'd' : def
    let p1 := lit b p lDef
    let (nAll, q1) := listScan b p1 0
    let p2 := lit b q1 lHints
    let pa := lit b p2 lHAbbrev
    let po := if pa == 0 then lit b p2 lHOpaque else 0
    let r1 := if pa == 0 && po == 0 then lit b p2 lHRegular else 0
    let r2 := numEnd b r1
    let r3 := lit b r2 lClose
    let (hk, hv, p3) := if pa != 0 then (1, 0, pa) else if po != 0 then (0, 0, po) else (2, numVal b r1 r2, r3)
    let p4 := lit b p3 lLevelParams2
    let (nLps, q2) := listScan b p4 0
    let p5 := lit b q2 lNameAfterArr; let p6 := numEnd b p5
    let p7 := lit b p6 lSafety; let p8 := strEnd b p7
    let p9 := lit b p8 lQType; let p10 := numEnd b p9
    let p11 := lit b p10 lValue; let p12 := numEnd b p11
    let p13 := lit b p12 lClose2
    if p13 != e || p13 == 0 then slowRec b p e t else
    let sf := if lit b p7 lSafe == p8 then 0 else if lit b p7 lUnsafe == p8 then 1
              else if lit b p7 lPartial == p8 then 2 else 3
    if sf == 3 then slowRec b p e t else
    let r := listPush b p1 (t.recs.push tDEF |>.push nAll)
    let r := r.push hk |>.push hv
    let r := listPush b p4 (r.push nLps)
    { t with recs := r.push (numVal b p5 p6) |>.push sf |>.push (numVal b p9 p10) |>.push (numVal b p11 p12) }
  else slowRec b p e t

/-- position of the next `\n` at or after `p`, or `b.size`. -/
@[inline] partial def lineEnd (b : ByteArray) (p : Nat) : Nat :=
  if p < b.size then (if b.get! p == 10 then p else lineEnd b (p + 1)) else b.size

/-- tokenize all lines starting in `[p, stop)` (`p` at a line start). -/
partial def tokRange (b : ByteArray) (p stop : Nat) (t : Tok) : Tok :=
  if p >= stop || p >= b.size then t else
  let e := lineEnd b p
  -- the templates read b[p+2], b[p+3]: only lines of >= 4 bytes go to the tokenizer
  let t := if e >= p + 4 then tokLine b p e t else slowRec b p e t
  tokRange b (e + 1) stop t

/-! ### Phase B (sequential, file order): table lookups + official constructors -/

inductive R where
  | ok (st : St)
  | fail            -- fall back to the official parser for the whole file

/-- the slow path for one line: official per-line logic on the pre-parsed JSON object. -/
def slowObj (obj? : Option (Std.TreeMap.Raw String Json)) (st : St) : R :=
  match obj? with
  | none => .fail
  | some obj =>
    match (Slow.parseItemObj obj).run st with
    | .ok ((), st) => .ok st
    | .error _ => .fail

@[inline] def rd (r : Array Nat) (j : Nat) : Nat := r[j]!

/-- names `r[j], .., r[j+n-1]` (all must exist). -/
partial def namesAt (names : Array Name) (r : Array Nat) (j n : Nat) (acc : Array Name) : Option (List Name) :=
  if acc.size == n then some acc.toList
  else match names[rd r (j + acc.size)]? with
    | some x => namesAt names r j n (acc.push x)
    | none => none

partial def levelsAt (levels : Array Level) (r : Array Nat) (j n : Nat) (acc : Array Level) : Option (List Level) :=
  if acc.size == n then some acc.toList
  else match levels[rd r (j + acc.size)]? with
    | some x => levelsAt levels r j n (acc.push x)
    | none => none

/-- apply the records `r[j..]` of one chunk to the state. -/
partial def build (b : ByteArray) (r : Array Nat) (strs : Array String)
    (slow : Array (Option (Std.TreeMap.Raw String Json))) (j : Nat) (st : St) (nslow : Nat) :
    Option (St × Nat) :=
  if j >= r.size then some (st, nslow) else
  let tag := rd r j
  if tag == tAPP then
    let i := rd r (j+1); let fi := rd r (j+2); let ai := rd r (j+3)
    let sz := st.exprs.size
    if i != sz || fi >= sz || ai >= sz then none else
    let x := Expr.app st.exprs[fi]! st.exprs[ai]!
    build b r strs slow (j+4) { st with exprs := st.exprs.push x } nslow
  else if tag == tFORALL || tag == tLAM then
    let i := rd r (j+1)
    if i != st.exprs.size then none else
    let bi := binderOf (rd r (j+2))
    let ni := rd r (j+4); let ti := rd r (j+5); let bdi := rd r (j+3)
    if ni >= st.names.size || ti >= i || bdi >= i then none else
    let n := st.names[ni]!; let ty := st.exprs[ti]!; let bd := st.exprs[bdi]!
    let x := if tag == tFORALL then Expr.forallE n ty bd bi else Expr.lam n ty bd bi
    build b r strs slow (j+6) { st with exprs := st.exprs.push x } nslow
  else if tag == tCONST then
    let i := rd r (j+1); let n := rd r (j+3)
    if i != st.exprs.size then none else
    match st.names[rd r (j+2)]?, levelsAt st.levels r (j+4) n #[] with
    | some nm, some us => build b r strs slow (j+4+n) { st with exprs := st.exprs.push (.const nm us) } nslow
    | _, _ => none
  else if tag == tNSTR then
    let i := rd r (j+1)
    if i != st.names.size then none else
    match st.names[rd r (j+2)]?, strs[rd r (j+3)]? with
    | some pr, some s => build b r strs slow (j+4) { st with names := st.names.push (.str pr s) } nslow
    | _, _ => none
  else if tag == tSORT then
    let i := rd r (j+1)
    if i != st.exprs.size then none else
    match st.levels[rd r (j+2)]? with
    | some l => build b r strs slow (j+3) { st with exprs := st.exprs.push (.sort l) } nslow
    | none => none
  else if tag == tBVAR then
    let i := rd r (j+1)
    if i != st.exprs.size then none else
    build b r strs slow (j+3) { st with exprs := st.exprs.push (.bvar (rd r (j+2))) } nslow
  else if tag == tSLOW then
    match slowObj (slow[rd r (j+1)]?.getD none) st with
    | .ok st => build b r strs slow (j+2) st (nslow + 1)
    | .fail => none
  else if tag == tNNUM then
    let i := rd r (j+1)
    if i != st.names.size then none else
    match st.names[rd r (j+3)]? with
    | some pr => build b r strs slow (j+4) { st with names := st.names.push (.num pr (rd r (j+2))) } nslow
    | none => none
  else if tag == tLSUCC then
    let i := rd r (j+1)
    if i != st.levels.size then none else
    match st.levels[rd r (j+2)]? with
    | some l => build b r strs slow (j+3) { st with levels := st.levels.push (.succ l) } nslow
    | none => none
  else if tag == tLPARAM then
    let i := rd r (j+1)
    if i != st.levels.size then none else
    match st.names[rd r (j+2)]? with
    | some n => build b r strs slow (j+3) { st with levels := st.levels.push (.param n) } nslow
    | none => none
  else if tag == tLMAX || tag == tLIMAX then
    let i := rd r (j+1)
    if i != st.levels.size then none else
    match st.levels[rd r (j+2)]?, st.levels[rd r (j+3)]? with
    | some l1, some l2 =>
      let l := if tag == tLMAX then Level.max l1 l2 else Level.imax l1 l2
      build b r strs slow (j+4) { st with levels := st.levels.push l } nslow
    | _, _ => none
  else if tag == tLETE then
    let i := rd r (j+1)
    if i != st.exprs.size then none else
    let nd := rd r (j+2) == 1
    match st.names[rd r (j+4)]?, st.exprs[rd r (j+5)]?, st.exprs[rd r (j+6)]?, st.exprs[rd r (j+3)]? with
    | some n, some ty, some v, some bd => build b r strs slow (j+7) { st with exprs := st.exprs.push (.letE n ty v bd nd) } nslow
    | _, _, _, _ => none
  else if tag == tPROJ then
    let i := rd r (j+1)
    if i != st.exprs.size then none else
    match st.names[rd r (j+4)]?, st.exprs[rd r (j+3)]? with
    | some n, some s => build b r strs slow (j+5) { st with exprs := st.exprs.push (.proj n (rd r (j+2)) s) } nslow
    | _, _ => none
  else if tag == tTHM then
    let nAll := rd r (j+1); let jl := j + 2 + nAll; let nLps := rd r jl; let jn := jl + 1 + nLps
    match namesAt st.names r (j+2) nAll #[], namesAt st.names r (jl+1) nLps #[],
          st.names[rd r jn]?, st.exprs[rd r (jn+1)]?, st.exprs[rd r (jn+2)]? with
    | some all, some lps, some name, some type, some value =>
      if st.constMap.contains name then none else
      build b r strs slow (jn+3) { st with
        constMap := st.constMap.insert name (.thmInfo { name, levelParams := lps, type, value, all }),
        constOrder := st.constOrder.push name } nslow
    | _, _, _, _, _ => none
  else if tag == tDEF then
    let nAll := rd r (j+1); let jh := j + 2 + nAll
    let hk := rd r jh
    let hints : ReducibilityHints := if hk == 0 then .opaque else if hk == 1 then .abbrev else .regular (rd r (jh+1)).toUInt32
    let jl := jh + 2; let nLps := rd r jl; let jn := jl + 1 + nLps
    let sf := rd r (jn+1)
    let safety : DefinitionSafety := if sf == 0 then .safe else if sf == 1 then .unsafe else .partial
    match namesAt st.names r (j+2) nAll #[], namesAt st.names r (jl+1) nLps #[],
          st.names[rd r jn]?, st.exprs[rd r (jn+2)]?, st.exprs[rd r (jn+3)]? with
    | some all, some lps, some name, some type, some value =>
      if st.constMap.contains name then none else
      build b r strs slow (jn+4) { st with
        constMap := st.constMap.insert name (.defnInfo { name, levelParams := lps, type, value, hints, safety, all }),
        constOrder := st.constOrder.push name } nslow
    | _, _, _, _, _ => none
  else none

/-- chunk boundaries: `k` line-aligned starts in `[p0, size)`. -/
partial def chunkStarts (b : ByteArray) (p0 : Nat) (k : Nat) : Array Nat := Id.run do
  let sz := b.size
  let step := (sz - p0) / k + 1
  let mut out := #[p0]
  let mut last := p0
  for i in [1:k] do
    let target := max (p0 + i * step) last
    if target >= sz then break
    let e := lineEnd b target
    let s := e + 1
    if s >= sz then break
    if s > last then
      out := out.push s
      last := s
  return out

partial def buildAll (b : ByteArray) (tasks : List (Task Tok)) (st : St) (nslow : Nat) : Option (St × Nat) :=
  match tasks with
  | [] => some (st, nslow)
  | t :: rest =>
    let tok := t.get
    match build b tok.recs tok.strs tok.slow 0 st nslow with
    | some (st, nslow) => buildAll b rest st nslow
    | none => none

/-- The fast reader with `k` tokenizer tasks. `none` = use the official parser. -/
def parseBytesPar? (b : ByteArray) (k : Nat := 64) : Option (Std.HashMap Name ConstantInfo × Array Name × Nat) :=
  -- skip the metadata line exactly like `parseMdata` (one `getLine`)
  let p := lineEnd b 0
  let p := if p < b.size then p + 1 else p
  if p >= b.size then none  -- empty export: let the official parser handle it
  else
  let starts := chunkStarts b p (max k 1)
  let ends := (starts.toList.drop 1) ++ [b.size]
  let tasks := (starts.toList.zip ends).map fun (s, e) =>
    Task.spawn (prio := .dedicated) fun _ => tokRange b s e { recs := Array.mkEmpty ((e - s) / 12), strs := #[], slow := #[] }
  let st : St := { names := #[.anonymous], levels := #[.zero], exprs := #[], constMap := {}, constOrder := #[] }
  match buildAll b tasks st 0 with
  | some (st, nslow) => some (st.constMap, st.constOrder, nslow)
  | none => none

/-- profiling helper: tokenize everything first (k tasks), then build. -/
def profile (b : ByteArray) (k : Nat) : IO Unit := do
  let p := lineEnd b 0
  let p := if p < b.size then p + 1 else p
  let t0 ← IO.monoMsNow
  let starts := chunkStarts b p (max k 1)
  let ends := (starts.toList.drop 1) ++ [b.size]
  let tasks := (starts.toList.zip ends).map fun (s, e) =>
    Task.spawn (prio := .dedicated) fun _ => tokRange b s e { recs := Array.mkEmpty ((e - s) / 12), strs := #[], slow := #[] }
  let toks := tasks.map Task.get
  let nrec := toks.foldl (fun a t => a + t.recs.size) 0
  let t1 ← IO.monoMsNow
  let st : St := { names := #[.anonymous], levels := #[.zero], exprs := #[], constMap := {}, constOrder := #[] }
  let rec go (ts : List Tok) (st : St) (ns : Nat) : Option (St × Nat) := match ts with
    | [] => some (st, ns)
    | t :: rest => match build b t.recs t.strs t.slow 0 st ns with
      | some (st, ns) => go rest st ns
      | none => none
  let r := go toks st 0
  let t2 ← IO.monoMsNow
  match r with
  | some (st, ns) => IO.println s!"profile k={k}: tokenize {t1-t0} ms ({nrec} rec words), build {t2-t1} ms, {st.exprs.size} exprs, {ns} slow"
  | none => IO.println "profile: fallback"


/-! ### Streaming reader: read blocks in a dedicated thread, tokenize each chunk in a task, build in order -/

/-- one chunk: `buf` = a dummy `\n` at offset 0, then whole lines (so every line starts at offset >= 1). -/
structure Chunk where
  buf : ByteArray
  tok : Tok

inductive Stream where
  | done
  | more (c : Task Chunk) (next : Task (Option Stream))

instance : Nonempty Stream := ⟨.done⟩

/-- last index `< i` holding `\n`. -/
partial def lastNL (b : ByteArray) (i : Nat) : Option Nat :=
  if i == 0 then none else if b.get! (i-1) == 10 then some (i-1) else lastNL b (i-1)

def mkChunkTask (buf : ByteArray) : Task Chunk :=
  Task.spawn fun _ => { buf, tok := tokRange buf 1 buf.size { recs := Array.mkEmpty (buf.size / 12), strs := #[], slow := #[] } }

def nlPrefix : ByteArray := ByteArray.mk #[10]

/-- reads the rest of `h` (after the metadata line) block by block; a dropped promise (read error) makes the
consumer decline. -/
partial def readLoop (h : IO.FS.Handle) (bs : USize) (carry : ByteArray) (p : IO.Promise Stream) : IO Unit := do
  let blk ← h.read bs
  if blk.isEmpty then
    if carry.isEmpty then p.resolve .done
    else
      let q ← IO.Promise.new
      p.resolve (.more (mkChunkTask (nlPrefix ++ carry)) q.result?)
      q.resolve .done
  else
    match lastNL blk blk.size with
    | none => readLoop h bs (carry ++ blk) p
    | some k =>
      let buf := (nlPrefix ++ carry).append (blk.extract 0 (k+1))
      let carry' := blk.extract (k+1) blk.size
      let q ← IO.Promise.new
      p.resolve (.more (mkChunkTask buf) q.result?)
      readLoop h bs carry' q

partial def consume (s : Task (Option Stream)) (st : St) (nslow nchunks : Nat) : Option (St × Nat × Nat) :=
  match s.get with
  | none => none
  | some .done => some (st, nslow, nchunks)
  | some (.more c next) =>
    let ch := c.get
    match build ch.buf ch.tok.recs ch.tok.strs ch.tok.slow 0 st nslow with
    | some (st, nslow) => consume next st nslow (nchunks + 1)
    | none => none

/-- Streaming fast reader of an export file. `none` = use the official parser (from scratch). -/
def parseFileStream? (path : System.FilePath) (blockSize : Nat := 8 * 1024 * 1024) :
    IO (Option (Std.HashMap Name ConstantInfo × Array Name × Nat × Nat)) := do
  let h ← IO.FS.Handle.mk path .read
  -- the metadata line, exactly like `parseMdata` (one `getLine` on the same handle)
  let _ ← h.getLine
  let p ← IO.Promise.new
  let res := p.result?
  let _reader ← IO.asTask (prio := .dedicated) (readLoop h blockSize.toUSize .empty p)
  let st : St := { names := #[.anonymous], levels := #[.zero], exprs := #[], constMap := {}, constOrder := #[] }
  match consume res st 0 0 with
  | some (st, nslow, nchunks) =>
    if nchunks == 0 then return none   -- no data line at all: let the official parser decide
    return some (st.constMap, st.constOrder, nslow, nchunks)
  | none => return none

def parseBytes? (b : ByteArray) : Option (Std.HashMap Name ConstantInfo × Array Name × Nat) :=
  parseBytesPar? b 1

end FastExport

/-! ## Drop-in entry point -/
namespace FastExport

/-- Read an export file: fast reader, or (whenever it declines) the OFFICIAL `LeanExport.parseStream`.
Same result as `IO.FS.withFile path .read fun h => LeanExport.parseStream (.ofHandle h)`. -/
def parseExportFile (path : System.FilePath) : IO LeanExport.ExportedEnv := do
  match ← (parseFileStream? path).toBaseIO with
  | .ok (some (constMap, constOrder, _, _)) => return { constMap, constOrder }
  | _ => IO.FS.withFile path .read fun h => LeanExport.parseStream (.ofHandle h)

end FastExport
