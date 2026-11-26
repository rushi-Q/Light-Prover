/-
Low-memory streaming parallel replay (`PChk/LowMem.lean`).

Memory-reduction architecture (100% safe Lean 4, zero `unsafe Runtime.markPersistent`):
1. Bounded-prefetch chunked I/O (at most `prefetch` 4 MiB chunks in flight; eliminates
   FastParse.readLoop's unbounded Promise accumulation on multi-GB exports).
2. Pass 1 (`prescanRc`): streaming byte-level prescan using FastExport.tokRange (zero Expr
   heap objects allocated). Computes an exact 7-bit saturating reference count (0..127) per
   expression ID in a flat `ByteArray` (1 byte/expr: 10.5 MB on rh-mid, 70 MB on Mathlib,
   1.06 GB on 61.6 GB RH). Any parse failure / non-dense index declines to the official
   non-streaming `LeanExport.parseStream` fallback.
3. Pass 2 (`streamReplay`): streaming parse + immediate dependency-checked replay with
   strictly linear RC=1 ownership on `names`, `levels`, and `ep` (no struct-update aliasing):
   - Paged expression table (4096-slot pages). Whenever a reference to expr `c` is consumed
     and `rc[c]` drops to 0, its slot is overwritten with `Expr.bvar 0` and when a page's
     live count reaches 0, the entire 4096-slot page array is freed (`none`).
   - Bit 7 of `rc[e]` records whether any `Expr.const` / `Expr.proj` inside `e` referenced a
     constant not yet in `env` at creation time, giving O(1) dependency readiness checks for
     99.99%+ of declarations without traversing proof DAGs on the walk thread.
   - Bounded worker channel (`maxInflight` semaphore tokens): at most `maxInflight` proof
     values exist in RAM at any time. No `jobs : Array Job` array is retained; workers
     report positive `nOk` counts and the earliest failing `(idx, name, ex)`.
   - Inductive blocks are checked directly via `addDeclCore` on the walk thread (zero
     speculative two-pass walk), with every exported constructor and recursor verified with
     `info == info'` (identical to `Lean.Replay`).
   - Theorem-value eviction (`EvictMode`):
     * `off`: retains `thmInfo` in `env` (still benefits from paged expr eviction + bounded
       in-flight queue + no `markPersistent` + no `jobs` array).
     * `strict`: after submitting `thmDecl` (with its full proof value!) to `addDeclCore`,
       inserts `axiomInfo { name, levelParams, type, isUnsafe := false }` into downstream
       `env` snapshots so zero theorem proof values are retained in `env`. Strictly sound
       by Lean v4.36.0 C++ kernel audit (`declaration.h:448`, `type_checker.cpp:555`,
       `inductive.cpp:419`): removing delta-unfolding of checked theorems can only cause
       false rejects (e.g. `Acc.rec` on a theorem proof), never false accepts.
     * `smart`: runs `strict`; if any job encounters a kernel error, retries cleanly with
       `evict = .off` so genuine proofs needing theorem unfolding achieve 0% false rejects
       while invalid proofs still reject with the exact unmodified kernel error.
   - Out-of-order declarations (if any dependency is not yet in `env`) are buffered in
     `deferred` and replayed in dependency DFS order at the end of Pass 2 (matching
     `Lean.Replay`).
Hardening checks (VETO ONLY, every change only adds failures):
 * C1 (Lean #16489): every inductive declaration handed to the kernel (streamed block in `handleInductBlock`, deferred block
   in `replayDeferredName`) is first checked with `r9LooseBVars?` (no inductive type / constructor type with a loose bound
   variable = the 4.37 kernel's `check_no_loose_bvars`); the official fallback runs `PChk.checkInductNoLooseBVars`.
 * C2 (record check, Lean #15100/#15101): (i) the inductive-type records of every block are compared (`==`) with the constants
   the kernel generated, like its constructor and recursor records already were; (ii) the deferred path compares every record
   of a block (types and the constructor records it used, whatever their flags) with the kernel's; (iii) at the end of every
   COMPLETE pass no name of a skipped (`isUnsafe`/`isPartial`) record, streamed or deferred, may be a constant of the final
   environment (every constant of that environment is safe and non-partial, so the record check's `==` would fail for such a record:
   the same condition); (iv) non-canonical quotient records already decline to the official fallback, which now runs
   `PChk.checkExportRecords`; canonical ones are compared by the quotient post-check. Theorem-eviction stand-ins are the
   walk's own records and are never compared with the export's theorem records (they are built from them).
Targeted-retry fix (can only replace a REJECTED by an `--evict=off` confirmation or by an accept of the unmodified
kernel in an environment that differs from the official one only by hidden theorem values - the existing eviction argument):
 * `--evict=smart`'s targeted retry concluded "genuine kernel rejection" when the pin set reached a fixed point, but the
   pin-set walk (`expandKeepFromEnv`) did not follow recursors (rules), quotients, opaque constants, inductive ctors or
   constructor `induct`, so a theorem the kernel needs (e.g. reached through a recursor rule and a constructor type) was
   never pinned and a valid export could be REJECTED. The walk now follows every reference of every constant
   kind (`refsOfAll` = the `refsOf` of overlap/src/r9d) and also starts from the names the kernel looks up without a syntactic
   reference (`kernelLookupNames`), so at a fixed point every theorem the kernel can reach is pinned and the retry's
   failure is the official kernel's.
 * a failing declaration of a kind not covered by `declExprs?`, or a structural / internal error of a targeted retry, no
   longer yields REJECTED: it is confirmed by the complete `--evict=off` run (or the official fallback), like the other
   unclear cases.
-/
import Lean.CoreM
import Lean.AddDecl
import Lean.Replay
import Lean.Util.FoldConsts
import Std.Sync.Channel
import FastParse
import PChk.Par

namespace PChk.LowMem
open Lean FastExport

inductive EvictMode where
  | off
  | strict
  | smart
  deriving BEq, Repr

private def pageShift : Nat := 12
private def pageSize : Nat := 4096
private def pageMask : Nat := 4095
private def rcMax : UInt8 := 127
private def rcMask : UInt8 := 127
private def depBit : UInt8 := 128

private def dummyExpr : Expr := Expr.bvar 0

@[inline] private def incRc (rc : ByteArray) (idx : Nat) : ByteArray :=
  let v := rc.get! idx
  if v < rcMax then rc.set! idx (v + 1) else rc

@[inline] private def envHas (env : Kernel.Environment) (n : Name) : Bool :=
  (env.find? n).isSome

private def isQuotConstName (n : Name) : Bool :=
  n == `Quot || n == `Quot.mk || n == `Quot.lift || n == `Quot.ind

/-! ## Bounded-prefetch chunked streaming reader -/

private structure BoundStream where
  ch : Std.CloseableChannel (Task Chunk)
  sem : Std.CloseableChannel Unit

private partial def boundedReadLoop (h : IO.FS.Handle) (bs : USize) (carry : ByteArray)
    (ch : Std.CloseableChannel (Task Chunk)) (sem : Std.CloseableChannel Unit) : IO Unit := do
  match ← sem.sync.recv with
  | none => return ()
  | some () =>
    let blk ← h.read bs
    if blk.isEmpty then
      if !carry.isEmpty then
        discard <| (ch.sync.send (mkChunkTask (nlPrefix ++ carry))).toBaseIO
      discard <| ch.close.toBaseIO
    else
      match lastNL blk blk.size with
      | none => boundedReadLoopMore h bs (carry ++ blk) ch sem
      | some k =>
        let buf := (nlPrefix ++ carry).append (blk.extract 0 (k + 1))
        let carry' := blk.extract (k + 1) blk.size
        match ← (ch.sync.send (mkChunkTask buf)).toBaseIO with
        | .ok () => boundedReadLoop h bs carry' ch sem
        | .error _ => return ()
where
  boundedReadLoopMore (h : IO.FS.Handle) (bs : USize) (carry : ByteArray)
      (ch : Std.CloseableChannel (Task Chunk)) (sem : Std.CloseableChannel Unit) : IO Unit := do
    let blk ← h.read bs
    if blk.isEmpty then
      if !carry.isEmpty then
        discard <| (ch.sync.send (mkChunkTask (nlPrefix ++ carry))).toBaseIO
      discard <| ch.close.toBaseIO
    else
      match lastNL blk blk.size with
      | none => boundedReadLoopMore h bs (carry ++ blk) ch sem
      | some k =>
        let buf := (nlPrefix ++ carry).append (blk.extract 0 (k + 1))
        let carry' := blk.extract (k + 1) blk.size
        match ← (ch.sync.send (mkChunkTask buf)).toBaseIO with
        | .ok () => boundedReadLoop h bs carry' ch sem
        | .error _ => return ()

private def openBoundStream (path : System.FilePath) (blockSize : Nat) (prefetch : Nat) :
    IO (BoundStream × Task (Except IO.Error Unit)) := do
  let h ← IO.FS.Handle.mk path .read
  let _ ← h.getLine  -- skip metadata line exactly like LeanExport.parseMdata
  let ch ← Std.CloseableChannel.new (α := Task Chunk)
  let sem ← Std.CloseableChannel.new (α := Unit)
  for _ in [0:max 1 prefetch] do
    discard <| (sem.sync.send ()).toBaseIO
  let reader ← IO.asTask (prio := .dedicated) (boundedReadLoop h blockSize.toUSize .empty ch sem)
  return ({ ch, sem }, reader)

private def closeBoundStream (bs : BoundStream) : IO Unit := do
  discard <| bs.ch.close.toBaseIO
  discard <| bs.sem.close.toBaseIO

/-! ## Pass 1: Zero-Expr-Allocation Reference-Count Prescan (RC=1 linear `rc`) -/

private structure ScanSt where
  nNames : Nat := 1
  nLevels : Nat := 1
  nExprs : Nat := 0
  rc : ByteArray := ByteArray.empty

@[inline] private def scanCheckExpr (st : ScanSt) (idx : Nat) : Option ScanSt :=
  let ⟨nn, nl, ne, rc⟩ := st
  if idx < ne then some ⟨nn, nl, ne, incRc rc idx⟩ else none

private def scanExprField (st : ScanSt) (data : Std.TreeMap.Raw String Json) (key : String) : Option ScanSt :=
  match data[key]? with
  | some (.num (idx : Nat)) => scanCheckExpr st idx
  | _ => none

private def scanSlowObj (obj? : Option (Std.TreeMap.Raw String Json)) (st : ScanSt) : Option ScanSt := do
  let obj ← obj?
  let kv := obj.toList
  let kv := match kv with
    | [x, y@("in", _)] => [y, x]
    | [x, y@("ie", _)] => [y, x]
    | [x, y@("il", _)] => [y, x]
    | _ => kv
  let ⟨nn, nl, ne, rc⟩ := st
  match kv with
  | [("in", .num (idx : Nat)), ("str", _)]
  | [("in", .num (idx : Nat)), ("num", _)] =>
    if idx != nn then none else some ⟨nn + 1, nl, ne, rc⟩
  | [("il", .num (idx : Nat)), ("succ", _)]
  | [("il", .num (idx : Nat)), ("max", _)]
  | [("il", .num (idx : Nat)), ("imax", _)]
  | [("il", .num (idx : Nat)), ("param", _)] =>
    if idx != nl then none else some ⟨nn, nl + 1, ne, rc⟩
  | [("ie", .num (idx : Nat)), ("bvar", _)]
  | [("ie", .num (idx : Nat)), ("sort", _)]
  | [("ie", .num (idx : Nat)), ("const", _)]
  | [("ie", .num (idx : Nat)), ("natVal", _)]
  | [("ie", .num (idx : Nat)), ("strVal", _)] =>
    if idx != ne then none else some ⟨nn, nl, ne + 1, rc.push 0⟩
  | [("ie", .num (idx : Nat)), ("app", .obj data)] =>
    if idx != ne then none else do
    let st ← scanExprField ⟨nn, nl, ne, rc⟩ data "fn"
    let ⟨nn, nl, ne, rc⟩ ← scanExprField st data "arg"
    return ⟨nn, nl, ne + 1, rc.push 0⟩
  | [("ie", .num (idx : Nat)), ("lam", .obj data)]
  | [("ie", .num (idx : Nat)), ("forallE", .obj data)] =>
    if idx != ne then none else do
    let st ← scanExprField ⟨nn, nl, ne, rc⟩ data "type"
    let ⟨nn, nl, ne, rc⟩ ← scanExprField st data "body"
    return ⟨nn, nl, ne + 1, rc.push 0⟩
  | [("ie", .num (idx : Nat)), ("letE", .obj data)] =>
    if idx != ne then none else do
    let st ← scanExprField ⟨nn, nl, ne, rc⟩ data "type"
    let st ← scanExprField st data "value"
    let ⟨nn, nl, ne, rc⟩ ← scanExprField st data "body"
    return ⟨nn, nl, ne + 1, rc.push 0⟩
  | [("ie", .num (idx : Nat)), ("proj", .obj data)] =>
    if idx != ne then none else do
    let ⟨nn, nl, ne, rc⟩ ← scanExprField ⟨nn, nl, ne, rc⟩ data "struct"
    return ⟨nn, nl, ne + 1, rc.push 0⟩
  | [("ie", .num (idx : Nat)), ("mdata", .obj data)] =>
    if idx != ne then none else do
    let ⟨nn, nl, ne, rc⟩ ← scanExprField ⟨nn, nl, ne, rc⟩ data "expr"
    return ⟨nn, nl, ne + 1, rc.push 0⟩
  | [("axiom", .obj data)]
  | [("quot", .obj data)] =>
    scanExprField ⟨nn, nl, ne, rc⟩ data "type"
  | [("def", .obj data)]
  | [("thm", .obj data)]
  | [("opaque", .obj data)] => do
    let st ← scanExprField ⟨nn, nl, ne, rc⟩ data "type"
    scanExprField st data "value"
  | [("inductive", .obj data)] => do
    let some (.arr types) := data["types"]? | none
    let some (.arr ctors) := data["ctors"]? | none
    let some (.arr recs) := data["recs"]? | none
    let mut st : ScanSt := ⟨nn, nl, ne, rc⟩
    for t in types do
      let .obj td := t | none
      let cur := st; st := {}
      st ← scanExprField cur td "type"
    for c in ctors do
      let .obj cd := c | none
      let cur := st; st := {}
      st ← scanExprField cur cd "type"
    for r in recs do
      let .obj rd := r | none
      let cur := st; st := {}
      st ← scanExprField cur rd "type"
      let some (.arr rules) := rd["rules"]? | none
      for rule in rules do
        let .obj rud := rule | none
        let cur := st; st := {}
        st ← scanExprField cur rud "rhs"
    return st
  | _ => none

private partial def scanRecs (r : Array Nat) (slow : Array (Option (Std.TreeMap.Raw String Json)))
    (j : Nat) (nn nl ne : Nat) (rc : ByteArray) : Option ScanSt :=
  if j >= r.size then some ⟨nn, nl, ne, rc⟩ else
  let tag := r[j]!
  if tag == tAPP then
    let i := r[j+1]!; let fi := r[j+2]!; let ai := r[j+3]!
    if i != ne || fi >= i || ai >= i then none else
    let rc := incRc (incRc (rc.push 0) fi) ai
    scanRecs r slow (j+4) nn nl (i + 1) rc
  else if tag == tFORALL || tag == tLAM then
    let i := r[j+1]!; let bdi := r[j+3]!; let ti := r[j+5]!
    if i != ne || bdi >= i || ti >= i then none else
    let rc := incRc (incRc (rc.push 0) bdi) ti
    scanRecs r slow (j+6) nn nl (i + 1) rc
  else if tag == tCONST then
    let i := r[j+1]!; let n := r[j+3]!
    if i != ne then none else
    scanRecs r slow (j+4+n) nn nl (i + 1) (rc.push 0)
  else if tag == tNSTR then
    if r[j+1]! != nn then none else
    scanRecs r slow (j+4) (nn + 1) nl ne rc
  else if tag == tSORT then
    let i := r[j+1]!
    if i != ne then none else
    scanRecs r slow (j+3) nn nl (i + 1) (rc.push 0)
  else if tag == tBVAR then
    let i := r[j+1]!
    if i != ne then none else
    scanRecs r slow (j+3) nn nl (i + 1) (rc.push 0)
  else if tag == tSLOW then
    match scanSlowObj (slow[r[j+1]!]?.getD none) ⟨nn, nl, ne, rc⟩ with
    | some ⟨nn', nl', ne', rc'⟩ => scanRecs r slow (j+2) nn' nl' ne' rc'
    | none => none
  else if tag == tNNUM then
    if r[j+1]! != nn then none else
    scanRecs r slow (j+4) (nn + 1) nl ne rc
  else if tag == tLSUCC || tag == tLPARAM then
    if r[j+1]! != nl then none else
    scanRecs r slow (j+3) nn (nl + 1) ne rc
  else if tag == tLMAX || tag == tLIMAX then
    if r[j+1]! != nl then none else
    scanRecs r slow (j+4) nn (nl + 1) ne rc
  else if tag == tLETE then
    let i := r[j+1]!; let bdi := r[j+3]!; let ti := r[j+5]!; let vi := r[j+6]!
    if i != ne || bdi >= i || ti >= i || vi >= i then none else
    let rc := incRc (incRc (incRc (rc.push 0) bdi) ti) vi
    scanRecs r slow (j+7) nn nl (i + 1) rc
  else if tag == tPROJ then
    let i := r[j+1]!; let si := r[j+3]!
    if i != ne || si >= i then none else
    let rc := incRc (rc.push 0) si
    scanRecs r slow (j+5) nn nl (i + 1) rc
  else if tag == tTHM then
    let nAll := r[j+1]!; let jl := j + 2 + nAll; let nLps := r[jl]!; let jn := jl + 1 + nLps
    let ti := r[jn+1]!; let vi := r[jn+2]!
    if ti >= ne || vi >= ne then none else
    let rc := incRc (incRc rc ti) vi
    scanRecs r slow (jn+3) nn nl ne rc
  else if tag == tDEF then
    let nAll := r[j+1]!; let jh := j + 2 + nAll; let jl := jh + 2; let nLps := r[jl]!; let jn := jl + 1 + nLps
    let ti := r[jn+2]!; let vi := r[jn+3]!
    if ti >= ne || vi >= ne then none else
    let rc := incRc (incRc rc ti) vi
    scanRecs r slow (jn+4) nn nl ne rc
  else none

private def prescanRc (path : System.FilePath) (blockSize prefetch : Nat) : IO (Option ScanSt) := do
  let (bs, reader) ← openBoundStream path blockSize prefetch
  let mut nn : Nat := 1
  let mut nl : Nat := 1
  let mut ne : Nat := 0
  let mut rc : ByteArray := ByteArray.empty
  let mut nchunks := 0
  let mut ok := true
  repeat
    match ← bs.ch.sync.recv with
    | none => break
    | some tk =>
      let ch := tk.get
      discard <| (bs.sem.sync.send ()).toBaseIO
      let curRc := rc
      rc := ByteArray.empty  -- release local ref so curRc is uniquely owned (RC=1!)
      match scanRecs ch.tok.recs ch.tok.slow 0 nn nl ne curRc with
      | some ⟨nn', nl', ne', rc'⟩ =>
        nn := nn'; nl := nl'; ne := ne'; rc := rc'
        nchunks := nchunks + 1
      | none =>
        ok := false
        break
  closeBoundStream bs
  let r ← IO.wait reader
  if !ok || nchunks == 0 then return none
  match r with
  | .ok () => return some ⟨nn, nl, ne, rc⟩
  | .error _ => return none

/-! ## Paged Refcounted Expression Table (strict linear RC=1 ownership!) -/

private structure ExprPages where
  pages : Array (Option (Array Expr)) := #[]
  live : Array Nat := #[]
  rc : ByteArray
  size : Nat := 0
  evictedExprs : Nat := 0
  freedPages : Nat := 0
  peakLivePages : Nat := 0
  curLivePages : Nat := 0

@[inline] private def ExprPages.put (ep : ExprPages) (idx : Nat) (e : Expr) (missingDep : Bool) : ExprPages := Id.run do
  let ⟨pages, live, rc, _size, evictedExprs, freedPages, peakLivePages, curLivePages⟩ := ep
  let c := rc.get! idx &&& rcMask
  let rc := if missingDep then rc.set! idx (c ||| depBit) else rc
  if c == 0 then
    return ⟨pages, live, rc, idx + 1, evictedExprs + 1, freedPages, peakLivePages, curLivePages⟩
  else
    let p := idx >>> pageShift
    let off := idx &&& pageMask
    let mut pages := pages
    let mut live := live
    let mut cur := curLivePages
    let mut peak := peakLivePages
    while pages.size <= p do
      pages := pages.push none
      live := live.push 0
    let (arr, isNew) := match pages[p]! with
      | some a => (a, false)
      | none => (Array.replicate pageSize dummyExpr, true)
    pages := pages.set! p none  -- drop ref so `arr` is uniquely owned (RC=1 in-place set!)
    let arr := arr.set! off e
    pages := pages.set! p (some arr)
    let lv := live[p]! + 1
    live := live.set! p lv
    if isNew then
      cur := cur + 1
      if cur > peak then peak := cur
    return ⟨pages, live, rc, idx + 1, evictedExprs, freedPages, peak, cur⟩

@[inline] private def ExprPages.take (ep : ExprPages) (idx : Nat) : Option (Expr × Bool × ExprPages) := Id.run do
  let ⟨pages, live, rc, size, evictedExprs, freedPages, peakLivePages, curLivePages⟩ := ep
  if idx >= size then return none
  let raw := rc.get! idx
  let c := raw &&& rcMask
  if c == 0 then return none
  let miss := (raw &&& depBit) != 0
  let p := idx >>> pageShift
  let off := idx &&& pageMask
  if p >= pages.size then return none
  match pages[p]! with
  | none => return none
  | some arr =>
    let e := arr[off]!
    if c >= rcMax then
      return some (e, miss, ⟨pages, live, rc, size, evictedExprs, freedPages, peakLivePages, curLivePages⟩)
    else if c <= 1 then
      let lv := live[p]! - 1
      let live := live.set! p lv
      let rc := rc.set! idx (if miss then depBit else 0)
      if lv == 0 then
        let pages := pages.set! p none
        return some (e, miss, ⟨pages, live, rc, size, evictedExprs + 1, freedPages + 1, peakLivePages, curLivePages - 1⟩)
      else
        let pages := pages.set! p none  -- drop ref so `arr` is uniquely owned (RC=1 in-place set!)
        let arr := arr.set! off dummyExpr
        let pages := pages.set! p (some arr)
        return some (e, miss, ⟨pages, live, rc, size, evictedExprs + 1, freedPages, peakLivePages, curLivePages⟩)
    else
      let rc := rc.set! idx ((c - 1) ||| (if miss then depBit else 0))
      return some (e, miss, ⟨pages, live, rc, size, evictedExprs, freedPages, peakLivePages, curLivePages⟩)

/-! ## Bounded Parallel Worker Pool (Zero `Array Job` Retention) -/

private structure StreamJob where
  idx : Nat
  name : Name
  env : Kernel.Environment
  decl : Declaration

private structure WorkerOut where
  nOk : Nat := 0
  nErr : Nat := 0
  firstErr : Option (Nat × Name × Kernel.Exception) := none
  /-- `firstErr` is an `unknown constant` of a name other than the failing declaration itself -/
  firstErrImplicit : Bool := false
  /-- earliest RESOURCE failure under off/strict (kept apart; it never cancels other checks) -/
  firstResErr : Option (Nat × Name × Kernel.Exception) := none
  failedDecls : Array (Nat × Name × Declaration × Kernel.Exception) := #[]
  maxDur : Nat := 0
  maxName : Name := .anonymous

private def maxSmartErrsPerWorker : Nat := 256

/-- resource exhaustion and interruption are not kernel verdicts. They are
never reported as REJECTED: a final failure carrying the `noVerdictTag` ends with exit 2 (no verdict); at the smart-mode
fixed point a REJECTED needs at least one failing declaration with a non-resource kernel error. The
tag is set from the `Kernel.Exception` CONSTRUCTOR (`kernelFailMsg`), never from message text; under off/strict a resource
failure cancels nothing and a genuine error of any declaration still gives REJECTED. -/
private def isResourceErr : Kernel.Exception → Bool
  | .deterministicTimeout | .excessiveMemory | .deepRecursion | .interrupted => true
  | _ => false

private def noVerdictTag : String := "[no verdict] "

/-- the no-verdict decision is carried as DATA - the `noVerdictTag` prefix is put in front ONLY by this
file, from the `Kernel.Exception` constructor (`isResourceErr`) or for an internal error, never derived from message text
(which contains export-chosen names). -/
private def isNoVerdictMsg (msg : String) : Bool :=
  msg.startsWith noVerdictTag

/-- failure text of a kernel exception, tagged by constructor. -/
private def kernelFailMsg (n : Name) (ex : Kernel.Exception) : IO String := do
  let m ← (ex.toMessageData {} |>.toString)
  return (if isResourceErr ex then noVerdictTag else "") ++ s!"while replaying declaration '{n}':\n{m}"

/-- the official path (Lean.Replay) reports a kernel exception only as TEXT,
`while replaying declaration '<n>':\n<kernel message>`. It is a resource failure only if the WHOLE text equals that form
for a constant `n` of the export and the exact 4.36 message of a resource exception (no export-chosen text can occur in
it); anything else stays a rejection. -/
private def officialFailIsResource (consts : Std.HashMap Name ConstantInfo) (msg : String) : IO Bool := do
  let pre := "while replaying declaration '"
  if !msg.startsWith pre then return false
  for ex in [Kernel.Exception.deterministicTimeout, .excessiveMemory, .deepRecursion, .interrupted] do
    let suf := "':\n" ++ (← (ex.toMessageData {} |>.toString))
    if msg.endsWith suf && msg.length > pre.length + suf.length then
      let mid := ((msg.drop pre.length).dropEnd suf.length).toString
      if consts.fold (init := false) (fun acc k _ => acc || k.toString == mid) then return true
  return false

/-- Kernel errors that theorem-value eviction (`thmInfo` -> `axiomInfo` of identical name & `levelParams`)
    can never cause; cancel higher-indexed workers immediately (prevents cyclic-def WHNF DoS). -/
private def canBeEvictionErr : Kernel.Exception → Bool
  | .unknownConstant .. | .alreadyDeclared .. => false
  | _ => true

private def startBoundedWorkers (nthreads maxInflight : Nat) (cancelTk : IO.CancelToken)
    (collectAllErrs : Bool) :
    IO (Std.CloseableChannel StreamJob × Std.CloseableChannel Unit ×
        IO.Ref Nat × Array (Task (Except IO.Error WorkerOut))) := do
  let ch ← Std.CloseableChannel.new (α := StreamJob)
  let sem ← Std.CloseableChannel.new (α := Unit)
  for _ in [0:max 1 maxInflight] do
    discard <| (sem.sync.send ()).toBaseIO
  let cancelAbove ← IO.mkRef (2 ^ 62)
  let nw := max 1 nthreads
  let mut slots : Array (IO.CancelToken × IO.Ref Nat) := #[]
  for _ in [0:nw] do
    slots := slots.push ((← IO.CancelToken.new), (← IO.mkRef (0 : Nat)))
  let mut workers := #[]
  for (tk, cur) in slots do
    workers := workers.push (← IO.asTask (prio := .dedicated) do
      let mut out : WorkerOut := {}
      repeat
        match ← ch.sync.recv with
        | none => break
        | some j =>
          let jIdx := j.idx
          let jName := j.name
          let skip ← do
            if jIdx > (← cancelAbove.get) || (← tk.isSet) || (← cancelTk.isSet) then pure true else pure false
          if !skip then
            cur.set jIdx
            let a ← IO.monoNanosNow
            let res := j.env.addDeclCore 0 0 j.decl (cancelTk? := some tk)
            let b ← IO.monoNanosNow
            if b - a > out.maxDur then
              out := { out with maxDur := b - a, maxName := jName }
            match res with
            | .ok _ =>
              out := { out with nOk := out.nOk + 1 }
            | .error .interrupted => pure ()
            | .error ex =>
              out := { out with nErr := out.nErr + 1 }
              if isResourceErr ex && !collectAllErrs then
                -- off/strict - a resource failure is no verdict; it is kept apart and cancels nothing,
                -- so a genuine error of any other declaration is still found (and gives the rejection)
                match out.firstResErr with
                | some (k, _, _) => if jIdx < k then out := { out with firstResErr := some (jIdx, jName, ex) }
                | none => out := { out with firstResErr := some (jIdx, jName, ex) }
              else
                -- ANY `unknown constant x` other than the declaration itself is
                -- an ordering question (a genuine reference to an undeclared name is decided below: no fallback then)
                let impl := match ex with
                  | .unknownConstant _ x => x != jName
                  | _ => false
                match out.firstErr with
                | some (k, _, _) => if jIdx < k then out := { out with firstErr := some (jIdx, jName, ex), firstErrImplicit := impl }
                | none => out := { out with firstErr := some (jIdx, jName, ex), firstErrImplicit := impl }
                if collectAllErrs && canBeEvictionErr ex && out.failedDecls.size < maxSmartErrsPerWorker then
                  out := { out with failedDecls := out.failedDecls.push (jIdx, jName, j.decl, ex) }
                else
                  let c ← cancelAbove.modifyGet fun c => let c' := min c jIdx; (c', c')
                  for (tk', cur') in slots do
                    if (← cur'.get) > c then tk'.set
          -- `j` goes out of scope here, releasing its `decl` (proof DAG) and `env` snapshot
          discard <| (sem.sync.send ()).toBaseIO
      return out)
  return (ch, sem, cancelAbove, workers)

/-! ## Cold Per-Declaration State (in `IO.Ref`, mutated linearly via `modifyGet`) -/

private structure DeclSt where
  quotAdded : Bool := false
  quotSeen : NameSet := {}
  realAxioms : NameSet := {}
  skippedUnsafe : NameSet := {}
  quotInfos : Array (Name × ConstantInfo) := #[]
  deferred : Std.HashMap Name ConstantInfo := {}
  deferredOrder : Array Name := #[]
  nSubmitted : Nat := 0
  nStreamed : Nat := 0
  nDeferred : Nat := 0
  nEvictedThms : Nat := 0
  nInducts : Nat := 0
  inductNs : Nat := 0
  failed : Option String := none
  /-- `failed` is a kernel `unknown constant` of a name outside the inductive block -/
  failedImplicitUnknown : Bool := false

private def isDupNonQuot (env : Kernel.Environment) (ds : DeclSt) (n : Name) : Bool :=
  envHas env n || ds.deferred.contains n || ds.skippedUnsafe.contains n || ds.quotSeen.contains n

private def isDupQuot (env : Kernel.Environment) (ds : DeclSt) (n : Name) : Bool :=
  ds.quotSeen.contains n || ds.deferred.contains n || ds.skippedUnsafe.contains n ||
    ((!ds.quotAdded || !isQuotConstName n) && envHas env n)

/-- (file order, S1(4) "dependency-correct order"): the 4.36 kernel
looks constants up WITHOUT a syntactic reference only for LITERALS - a natural-number literal is typed `Nat` and converted
to `Nat.zero` / `Nat.succ` (generated with `Nat`), a string literal is expanded to `String.ofList [Char.ofNat ..]`
(src/kernel/inductive.cpp `string_lit_to_constructor`), which brings `String`, `List` and `Char` through those two
definitions' own dependencies; every other kernel lookup name (Nat operations, `Bool`, `Eq`, quotients, `eagerReduce`, ...)
is looked up only when it occurs in the term, i.e. is a syntactic dependency. A declaration whose own expressions contain a
literal is therefore ready only when these names are in the environment too (deferred otherwise; at the end of the stream
the deferred replay adds them first if the export declares them). By induction over syntactic dependencies, every
declaration is checked only after all of its syntactic AND literal-triggered implicit dependencies that the export declares
are present - a missing implicit dependency can only make a check fail (unknown constant / unreduced term), never succeed. -/
private def litImplicitDeps (es : List Expr) : List Name :=
  let hasNat := es.any fun e => (e.find? fun x => x matches .lit (.natVal _)).isSome
  let hasStr := es.any fun e => (e.find? fun x => x matches .lit (.strVal _)).isSome
  -- the EXACT set of constants the 4.36 kernel synthesises (type_checker.cpp / inductive.cpp): a nat literal
  -- is typed `Nat` and expands to `Nat.zero` / `Nat.succ`; a string literal is typed `String` and expands to
  -- `String.ofList (List.cons Char (Char.ofNat ..) .. (List.nil Char))` - `Char.ofNat` / `List.cons` only per CHARACTER, so
  -- not for "" (an empty string needs neither); `Nat.beq` / `Nat.ble` on literals reduce to
  -- `Bool.true` / `Bool.false` (reduce_bin_nat_pred). Names the export does not declare are no-ops
  -- in the deferred replay; a dependency that depends back on the declaration is skipped there (order preference only).
  let hasChars := es.any fun e => (e.find? fun x => match x with | .lit (.strVal t) => !t.isEmpty | _ => false).isSome
  let hasNatPred := es.any fun e => (e.find? fun x => match x with
    | .const n _ => n == `Nat.beq || n == `Nat.ble | _ => false).isSome
  (if hasNat then [`Nat, `Nat.zero, `Nat.succ] else []) ++
  (if hasStr then [`String, `String.ofList, `Char, `List.nil] else []) ++
  (if hasChars then [`Char.ofNat, `List.cons] else []) ++
  (if hasNatPred then [`Bool.true, `Bool.false] else [])

/-- fast-path readiness bits of the literal / `Nat.beq` / `Nat.ble` lookups above (true = a lookup target is missing). -/
@[inline] private def natLitMiss (env : Kernel.Environment) : Bool :=
  !(envHas env `Nat && envHas env `Nat.zero && envHas env `Nat.succ)
@[inline] private def strLitMiss (env : Kernel.Environment) (s : String) : Bool :=
  !(envHas env `String && envHas env `String.ofList && envHas env `Char && envHas env `List.nil &&
    (s.isEmpty || (envHas env `Char.ofNat && envHas env `List.cons)))
@[inline] private def constMiss (env : Kernel.Environment) (nm : Name) : Bool :=
  !envHas env nm || ((nm == `Nat.beq || nm == `Nat.ble) && !(envHas env `Bool.true && envHas env `Bool.false))

private def ciLitDeps (ci : ConstantInfo) : List Name :=
  litImplicitDeps (ci.type :: (match ci.value? (allowOpaque := true) with | some v => [v] | none => []))

private def allDepsInEnv (env : Kernel.Environment) (ci : ConstantInfo) : Bool :=
  ci.getUsedConstantsAsSet.all (fun n => envHas env n) && (ciLitDeps ci).all (fun n => envHas env n)

private structure RunCfg where
  evict : EvictMode
  keepThms : NameSet := {}
  onlyCheck? : Option NameSet := none
  collectAllErrs : Bool := false
  /-- record, for every theorem the walk adds, the names its VALUE references (names only, no bodies), so that the
  complete reachable-theorem closure can be computed after the pass even for theorems the walk evicted -/
  thmRefs? : Option (IO.Ref (Std.HashMap Name (Array Name))) := none

private def addToWalkEnv (env : Kernel.Environment) (ci : ConstantInfo) (cfg : RunCfg) :
    Except String (Kernel.Environment × Bool) :=
  match ci with
  | .thmInfo info =>
    if cfg.evict != .off && !cfg.keepThms.contains info.name then
      if envHas env info.name then
        .error s!"environment already contains '{info.name}'"
      else
        let ax : ConstantInfo := .axiomInfo {
          name := info.name, levelParams := info.levelParams, type := info.type, isUnsafe := false
        }
        .ok (PChk.envAdd env ax, true)
    else
      match env.addDeclWithoutChecking (.thmDecl info) with
      | .ok env' => .ok (env', false)
      | .error ex => .error ((if isResourceErr ex then noVerdictTag else "") ++ s!"addDeclWithoutChecking failed for '{info.name}'")
  | .defnInfo info =>
    match env.addDeclWithoutChecking (.defnDecl info) with
    | .ok env' => .ok (env', false)
    | .error ex => .error ((if isResourceErr ex then noVerdictTag else "") ++ s!"addDeclWithoutChecking failed for '{info.name}'")
  | .axiomInfo info =>
    match env.addDeclWithoutChecking (.axiomDecl info) with
    | .ok env' => .ok (env', false)
    | .error ex => .error ((if isResourceErr ex then noVerdictTag else "") ++ s!"addDeclWithoutChecking failed for '{info.name}'")
  | .opaqueInfo info =>
    match env.addDeclWithoutChecking (.opaqueDecl info) with
    | .ok env' => .ok (env', false)
    | .error ex => .error ((if isResourceErr ex then noVerdictTag else "") ++ s!"addDeclWithoutChecking failed for '{info.name}'")
  | _ => .error "unexpected constant kind in addToWalkEnv"

/-- `while replaying declaration` wrapper that keeps a no-verdict tag in front. -/
private def wrapFail (n : Name) (msg : String) : String :=
  if msg.startsWith noVerdictTag then noVerdictTag ++ s!"while replaying declaration '{n}':\n{(msg.drop noVerdictTag.length).toString}"
  else s!"while replaying declaration '{n}':\n{msg}"

private def declOfCi? : ConstantInfo → Option Declaration
  | .thmInfo info => some (.thmDecl info)
  | .defnInfo info => some (.defnDecl info)
  | .axiomInfo info => some (.axiomDecl info)
  | .opaqueInfo info => some (.opaqueDecl info)
  | _ => none

private def submitJob (ch : Std.CloseableChannel StreamJob) (sem : Std.CloseableChannel Unit)
    (cancelAbove : IO.Ref Nat) (dstRef : IO.Ref DeclSt) (name : Name)
    (envBefore : Kernel.Environment) (decl : Declaration) : IO Bool := do
  let idx ← dstRef.modifyGet fun ds => (ds.nSubmitted, { ds with nSubmitted := ds.nSubmitted + 1 })
  if idx > (← cancelAbove.get) then
    return false
  discard <| sem.sync.recv
  match ← (ch.sync.send { idx, name, env := envBefore, decl }).toBaseIO with
  | .ok () => return false
  | .error _ =>
    dstRef.modify fun ds => { ds with failed := some (noVerdictTag ++ "internal error: worker channel closed") }
    return true

/-- Returns `(envAfter, failedNow)`. -/
private def handleSimpleDecl (ch : Std.CloseableChannel StreamJob) (sem : Std.CloseableChannel Unit)
    (cancelAbove : IO.Ref Nat) (dstRef : IO.Ref DeclSt) (cfg : RunCfg)
    (env : Kernel.Environment) (ci : ConstantInfo) (fastReady : Bool) :
    IO (Kernel.Environment × Bool) := do
  let name := ci.name
  let dup ← dstRef.modifyGet fun ds =>
    if isDupNonQuot env ds name then
      (true, { ds with failed := some s!"Duplicate declaration: {name}" })
    else if ci.isUnsafe || ci.isPartial then
      (false, { ds with skippedUnsafe := ds.skippedUnsafe.insert name })
    else
      (false, ds)
  if dup then return (env, true)
  if ci.isUnsafe || ci.isPartial then return (env, false)
  let ready := fastReady || allDepsInEnv env ci
  if !ready then
    dstRef.modify fun ds => { ds with
      deferred := ds.deferred.insert name ci,
      deferredOrder := ds.deferredOrder.push name,
      nDeferred := ds.nDeferred + 1 }
    return (env, false)
  let some decl := declOfCi? ci | return (env, false)
  if let some r := cfg.thmRefs? then   -- value references
    if let .thmInfo info := ci then r.modify (·.insert name info.value.getUsedConstantsAsSet.toArray)
  match addToWalkEnv env ci cfg with
  | .error msg =>
    dstRef.modify fun ds => { ds with failed := some (wrapFail name msg) }
    return (env, true)
  | .ok (envAfter, evicted) =>
    let isRealAx := match ci with | .axiomInfo _ => true | _ => false
    dstRef.modify fun ds => { ds with
      nStreamed := ds.nStreamed + 1,
      nEvictedThms := ds.nEvictedThms + (if evicted then 1 else 0),
      realAxioms := if isRealAx then ds.realAxioms.insert name else ds.realAxioms }
    let doCheck := match cfg.onlyCheck? with
      | none => true
      | some targets => targets.contains name
    if doCheck then
      let fail ← submitJob ch sem cancelAbove dstRef name env decl
      return (envAfter, fail)
    else
      return (envAfter, false)

/-- an inductive block's kernel failure is an `unknown constant` of a name
outside the block (an implicit lookup, or a dependency this walk's deferred order placed later): the official path decides. -/
private def blockImplicitUnknown (indTypes : List InductiveType) (ex : Kernel.Exception) : Bool :=
  match ex with
  | .unknownConstant _ x =>   -- any name outside the block itself
    !(indTypes.any fun t => t.name == x || t.ctors.any fun c => c.name == x)
  | _ => false

/-- C1: the 4.37 kernel's `check_no_loose_bvars` condition on an inductive declaration (every inductive type and every
constructor type closed); `some msg` = reject. -/
private def r9LooseBVars? (indTypes : List InductiveType) : Option String := Id.run do
  for t in indTypes do
    if t.type.hasLooseBVars then
      return some s!"C1 (Lean #16489): the type of inductive type {t.name} has loose bound variables"
    for c in t.ctors do
      if c.type.hasLooseBVars then
        return some s!"C1 (Lean #16489): the type of constructor {c.name} of {t.name} has loose bound variables"
  return none

/-- Returns `some (envAfter, failedNow)` or `none` (decline to official fallback). -/
private def handleInductBlock (cancelTk : IO.CancelToken) (dstRef : IO.Ref DeclSt)
    (env : Kernel.Environment) (types ctors recs : Array ConstantInfo) :
    IO (Option (Kernel.Environment × Bool)) := do
  if types.isEmpty then return none
  let some (ConstantInfo.inductInfo firstInd) := types[0]? | return none
  let expectedAll := types.toList.map (·.name)
  -- If mutual block is split or mixed unsafe/safe, decline to official Lean.Replay
  let anyUnsafe := types.any (fun c => c.isUnsafe || c.isPartial)
  let allUnsafe := types.all (fun c => c.isUnsafe || c.isPartial)
  if anyUnsafe != allUnsafe then return none
  for t in types do
    match t with
    | .inductInfo ti => if ti.all != expectedAll then return none
    | _ => return none
  -- the official reader keys every record by name and
  -- Lean.Replay filters unsafe/partial records ONE BY ONE and compares each safe ctor / recursor with the kernel's after
  -- replaying its OWN inductive. This walk handles a group as one unit, which is only the official behaviour when every
  -- record of the group belongs to the group's types and has the group's safety: a ctor must be a ctor of one of `types`
  -- (`induct` in the block, listed in that type's `ctors`), a recursor must name exactly this block in `all`, and every
  -- record must have the types' unsafe/partial status. Anything else (e.g. a safe `A.rec` record inside the group of an
  -- unsafe `B`, or `A.rec` exported in a later group than `A`) declines to the official parse + Lean.Replay.
  let mut ctorNames : NameSet := {}
  for t in types do
    if let .inductInfo ti := t then
      for cn in ti.ctors do ctorNames := ctorNames.insert cn
  for c in ctors do
    match c with
    | .ctorInfo ci => if !expectedAll.contains ci.induct || !ctorNames.contains ci.name then return none
    | _ => return none
  for r in recs do
    match r with
    | .recInfo ri => if ri.all != expectedAll then return none
    | _ => return none
  for c in ctors ++ recs do
    if (c.isUnsafe || c.isPartial) != anyUnsafe then return none
  -- Duplicate check across env, deferred, skippedUnsafe, quotSeen, and within this block
  let mut blockSeen : NameSet := {}
  let allItems := types ++ ctors ++ recs
  for c in allItems do
    if blockSeen.contains c.name then
      dstRef.modify fun ds => { ds with failed := some s!"Duplicate declaration: {c.name}" }
      return some (env, true)
    blockSeen := blockSeen.insert c.name
  let dup? ← dstRef.modifyGet fun ds => Id.run do
    for c in allItems do
      if isDupNonQuot env ds c.name then
        return (some c.name, { ds with failed := some s!"Duplicate declaration: {c.name}" })
    if anyUnsafe then
      let mut sk := ds.skippedUnsafe
      for c in allItems do sk := sk.insert c.name
      return (none, { ds with skippedUnsafe := sk })
    return (none, ds)
  if dup?.isSome then return some (env, true)
  if anyUnsafe then return some (env, false)
  -- Check if all external dependencies of types + ctors (outside `all`) are already in `env`
  let allNames : NameSet := types.foldl (init := {}) fun acc c => acc.insert c.name
  let mut ready := true
  for c in types ++ ctors do
    for dep in c.type.getUsedConstantsAsSet do
      if !allNames.contains dep && !envHas env dep then
        ready := false
        break
    if !ready then break
    if !(litImplicitDeps [c.type]).all (fun n => envHas env n) then   -- r3: literal-triggered kernel lookups
      ready := false
      break
  if !ready then
    dstRef.modify fun ds => Id.run do
      let mut defMap := ds.deferred
      let mut defOrd := ds.deferredOrder
      for c in allItems do
        defMap := defMap.insert c.name c
        defOrd := defOrd.push c.name
      return { ds with deferred := defMap, deferredOrder := defOrd, nDeferred := ds.nDeferred + allItems.size }
    return some (env, false)
  -- Ready: check directly in kernel!
  let lparams := firstInd.levelParams
  let nparams := firstInd.numParams
  let mut ctorMap : Std.HashMap Name ConstantInfo := {}
  for c in ctors do ctorMap := ctorMap.insert c.name c
  let mut indTypes : List InductiveType := []
  for t in types do
    let .inductInfo ti := t | return none
    let mut cList : List Constructor := []
    for cn in ti.ctors do
      let some cci := ctorMap[cn]? | return none
      cList := cList ++ [{ name := cci.name, type := cci.type }]
    indTypes := indTypes ++ [{ name := ti.name, type := ti.type, ctors := cList }]
  if let some msg := r9LooseBVars? indTypes then   -- C1 (loose bvars)
    dstRef.modify fun ds => { ds with failed := some msg }
    return some (env, true)
  let t0 ← IO.monoNanosNow
  let res := env.addDeclCore 0 0 (.inductDecl lparams nparams indTypes false) (cancelTk? := some cancelTk)
  let t1 ← IO.monoNanosNow
  match res with
  | .error ex =>
    let msg ← kernelFailMsg firstInd.name ex   -- tagged by constructor
    let impl := blockImplicitUnknown indTypes ex
    dstRef.modify fun ds => { ds with failed := some msg, failedImplicitUnknown := impl }
    return some (env, true)
  | .ok env' =>
    for c in ctors do
      match env'.find? c.name, c with
      | some (.ctorInfo info), .ctorInfo info' =>
        if !(info == info') then
          dstRef.modify fun ds => { ds with failed := some s!"Invalid constructor {c.name}" }
          return some (env, true)
      | _, _ =>
        dstRef.modify fun ds => { ds with failed := some s!"No such constructor {c.name}" }
        return some (env, true)
    for r in recs do
      match env'.find? r.name, r with
      | some (.recInfo info), .recInfo info' =>
        if !(info == info') then
          dstRef.modify fun ds => { ds with failed := some s!"Invalid recursor {r.name}" }
          return some (env, true)
      | _, _ =>
        dstRef.modify fun ds => { ds with failed := some s!"No such recursor {r.name}" }
        return some (env, true)
    -- C2 (record check): the inductive-type records too must equal the kernel's constants
    for t in types do
      match env'.find? t.name with
      | some c =>
        if !(c == t) then
          dstRef.modify fun ds => { ds with failed := some s!"Export record of {t.name} differs from the kernel's constant" }
          return some (env, true)
      | none =>
        dstRef.modify fun ds => { ds with failed := some s!"Export record of {t.name} differs from the kernel's constant" }
        return some (env, true)
    dstRef.modify fun ds => { ds with nInducts := ds.nInducts + 1, inductNs := ds.inductNs + (t1 - t0) }
    return some (env', false)

/-! ## Pass 2 Slow-Record JSON Parser (strictly linear `names`, `levels`, `ep`) -/

private def parseNameList (names : Array Name) (arr : Array Json) : Option (List Name) :=
  arr.toList.mapM fun j => do
    let .num (idx : Nat) := j | none
    names[idx]?

private def parseLevelList (levels : Array Level) (arr : Array Json) : Option (List Level) :=
  arr.toList.mapM fun j => do
    let .num (idx : Nat) := j | none
    levels[idx]?

private def parseBinderInfoOpt : String → Option BinderInfo
  | "default" => some .default
  | "implicit" => some .implicit
  | "strictImplicit" => some .strictImplicit
  | "instImplicit" => some .instImplicit
  | _ => none

private abbrev StepRes := Option (Array Name × Array Level × ExprPages × Kernel.Environment × Bool)

private def processSlowObj (ch : Std.CloseableChannel StreamJob) (sem : Std.CloseableChannel Unit)
    (cancelAbove : IO.Ref Nat) (cancelTk : IO.CancelToken) (dstRef : IO.Ref DeclSt) (cfg : RunCfg)
    (obj? : Option (Std.TreeMap.Raw String Json))
    (names : Array Name) (levels : Array Level) (ep : ExprPages) (env : Kernel.Environment) :
    IO StepRes := do
  let some obj := obj? | return none
  let kv := obj.toList
  let kv := match kv with
    | [x, y@("in", _)] => [y, x]
    | [x, y@("ie", _)] => [y, x]
    | [x, y@("il", _)] => [y, x]
    | _ => kv
  match kv with
  | [("in", .num (idx : Nat)), ("str", .obj data)] =>
    if idx != names.size then return none
    let some (.num (pre : Nat)) := data["pre"]? | return none
    let some (.str s) := data["str"]? | return none
    let some pn := names[pre]? | return none
    return some (names.push (.str pn s), levels, ep, env, false)
  | [("in", .num (idx : Nat)), ("num", .obj data)] =>
    if idx != names.size then return none
    let some (.num (pre : Nat)) := data["pre"]? | return none
    let some (.num (k : Nat)) := data["i"]? | return none
    let some pn := names[pre]? | return none
    return some (names.push (.num pn k), levels, ep, env, false)
  | [("il", .num (idx : Nat)), ("succ", .num (l : Nat))] =>
    if idx != levels.size then return none
    let some lv := levels[l]? | return none
    return some (names, levels.push (.succ lv), ep, env, false)
  | [("il", .num (idx : Nat)), ("max", .arr #[.num (a : Nat), .num (b : Nat)])] =>
    if idx != levels.size then return none
    let some la := levels[a]? | return none
    let some lb := levels[b]? | return none
    return some (names, levels.push (.max la lb), ep, env, false)
  | [("il", .num (idx : Nat)), ("imax", .arr #[.num (a : Nat), .num (b : Nat)])] =>
    if idx != levels.size then return none
    let some la := levels[a]? | return none
    let some lb := levels[b]? | return none
    return some (names, levels.push (.imax la lb), ep, env, false)
  | [("il", .num (idx : Nat)), ("param", .num (n : Nat))] =>
    if idx != levels.size then return none
    let some nm := names[n]? | return none
    return some (names, levels.push (.param nm), ep, env, false)
  | [("ie", .num (idx : Nat)), ("bvar", .num (k : Nat))] =>
    -- Lean's Expr data holds a loose-bvar range < 2^20; an index above 1048574 makes the official
    -- reader panic - decline the fast path (official path = official behaviour)
    if idx != ep.size || k > 1048574 then return none
    return some (names, levels, ep.put idx (.bvar k) false, env, false)
  | [("ie", .num (idx : Nat)), ("sort", .num (u : Nat))] =>
    if idx != ep.size then return none
    let some lv := levels[u]? | return none
    return some (names, levels, ep.put idx (.sort lv) false, env, false)
  | [("ie", .num (idx : Nat)), ("const", .obj data)] =>
    if idx != ep.size then return none
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.arr usArr) := data["us"]? | return none
    let some nm := names[ni]? | return none
    let some us := parseLevelList levels usArr | return none
    let miss := constMiss env nm   -- + Bool.true / Bool.false for Nat.beq / Nat.ble
    return some (names, levels, ep.put idx (.const nm us) miss, env, false)
  | [("ie", .num (idx : Nat)), ("app", .obj data)] =>
    if idx != ep.size then return none
    let some (.num (fi : Nat)) := data["fn"]? | return none
    let some (.num (ai : Nat)) := data["arg"]? | return none
    let some (fn, mf, ep) := ep.take fi | return none
    let some (arg, ma, ep) := ep.take ai | return none
    return some (names, levels, ep.put idx (.app fn arg) (mf || ma), env, false)
  | [("ie", .num (idx : Nat)), ("lam", .obj data)] =>
    if idx != ep.size then return none
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.num (bi : Nat)) := data["body"]? | return none
    let some (.str bstr) := data["binderInfo"]? | return none
    let some nm := names[ni]? | return none
    let some binfo := parseBinderInfoOpt bstr | return none
    let some (ty, mt, ep) := ep.take ti | return none
    let some (bd, mb, ep) := ep.take bi | return none
    return some (names, levels, ep.put idx (.lam nm ty bd binfo) (mt || mb), env, false)
  | [("ie", .num (idx : Nat)), ("forallE", .obj data)] =>
    if idx != ep.size then return none
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.num (bi : Nat)) := data["body"]? | return none
    let some (.str bstr) := data["binderInfo"]? | return none
    let some nm := names[ni]? | return none
    let some binfo := parseBinderInfoOpt bstr | return none
    let some (ty, mt, ep) := ep.take ti | return none
    let some (bd, mb, ep) := ep.take bi | return none
    return some (names, levels, ep.put idx (.forallE nm ty bd binfo) (mt || mb), env, false)
  | [("ie", .num (idx : Nat)), ("letE", .obj data)] =>
    if idx != ep.size then return none
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.num (vi : Nat)) := data["value"]? | return none
    let some (.num (bi : Nat)) := data["body"]? | return none
    let some (.bool nd) := data["nondep"]? | return none
    let some nm := names[ni]? | return none
    let some (ty, mt, ep) := ep.take ti | return none
    let some (vl, mv, ep) := ep.take vi | return none
    let some (bd, mb, ep) := ep.take bi | return none
    return some (names, levels, ep.put idx (.letE nm ty vl bd nd) (mt || mv || mb), env, false)
  | [("ie", .num (idx : Nat)), ("proj", .obj data)] =>
    if idx != ep.size then return none
    let some (.num (tni : Nat)) := data["typeName"]? | return none
    let some (.num (pidx : Nat)) := data["idx"]? | return none
    let some (.num (si : Nat)) := data["struct"]? | return none
    let some tn := names[tni]? | return none
    let some (s, ms, ep) := ep.take si | return none
    let miss := ms || !envHas env tn
    return some (names, levels, ep.put idx (.proj tn pidx s) miss, env, false)
  | [("ie", .num (idx : Nat)), ("natVal", .str s)] =>
    if idx != ep.size then return none
    let some n := String.toNat? s | return none
    -- r3: a literal's implicit kernel lookups count as dependencies (see `litImplicitDeps`)
    return some (names, levels, ep.put idx (.lit (.natVal n)) (natLitMiss env), env, false)
  | [("ie", .num (idx : Nat)), ("strVal", .str s)] =>
    if idx != ep.size then return none
    return some (names, levels, ep.put idx (.lit (.strVal s)) (strLitMiss env s), env, false)
  | [("ie", .num (idx : Nat)), ("mdata", .obj data)] =>
    if idx != ep.size then return none
    let some (.num (ei : Nat)) := data["expr"]? | return none
    let some (.obj _) := data["data"]? | return none
    let some (e, me, ep) := ep.take ei | return none
    return some (names, levels, ep.put idx (.mdata {} e) me, env, false)
  | [("axiom", .obj data)] =>
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.bool isU) := data["isUnsafe"]? | return none
    let some name := names[ni]? | return none
    let some lps := parseNameList names lpsArr | return none
    let some (ty, mt, ep) := ep.take ti | return none
    let ci : ConstantInfo := .axiomInfo { name, levelParams := lps, type := ty, isUnsafe := isU }
    let (env', fail) ← handleSimpleDecl ch sem cancelAbove dstRef cfg env ci (!mt)
    return some (names, levels, ep, env', fail)
  | [("def", .obj data)] =>
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.num (vi : Nat)) := data["value"]? | return none
    let some hintsJ := data["hints"]? | return none
    let some (.str safetyStr) := data["safety"]? | return none
    let some (.arr allArr) := data["all"]? | return none
    let some name := names[ni]? | return none
    let some lps := parseNameList names lpsArr | return none
    let some all := parseNameList names allArr | return none
    let hints? : Option ReducibilityHints := match hintsJ with
      | .str "opaque" => some .opaque
      | .str "abbrev" => some .abbrev
      | .obj hobj => match hobj["regular"]? with
        | some (.num (lv : Nat)) => some (.regular lv.toUInt32)
        | _ => none
      | _ => none
    let some hints := hints? | return none
    let safety? : Option DefinitionSafety := match safetyStr with
      | "safe" => some .safe
      | "unsafe" => some .unsafe
      | "partial" => some .partial
      | _ => none
    let some safety := safety? | return none
    let some (ty, mt, ep) := ep.take ti | return none
    let some (vl, mv, ep) := ep.take vi | return none
    let ci : ConstantInfo := .defnInfo { name, levelParams := lps, type := ty, value := vl, hints, safety, all }
    let (env', fail) ← handleSimpleDecl ch sem cancelAbove dstRef cfg env ci (!(mt || mv))
    return some (names, levels, ep, env', fail)
  | [("thm", .obj data)] =>
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.num (vi : Nat)) := data["value"]? | return none
    let some (.arr allArr) := data["all"]? | return none
    let some name := names[ni]? | return none
    let some lps := parseNameList names lpsArr | return none
    let some all := parseNameList names allArr | return none
    let some (ty, mt, ep) := ep.take ti | return none
    let some (vl, mv, ep) := ep.take vi | return none
    let ci : ConstantInfo := .thmInfo { name, levelParams := lps, type := ty, value := vl, all }
    let (env', fail) ← handleSimpleDecl ch sem cancelAbove dstRef cfg env ci (!(mt || mv))
    return some (names, levels, ep, env', fail)
  | [("opaque", .obj data)] =>
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.num (vi : Nat)) := data["value"]? | return none
    let (.bool isU) := data["isUnsafe"]?.getD (.bool false) | return none
    let some (.arr allArr) := data["all"]? | return none
    let some name := names[ni]? | return none
    let some lps := parseNameList names lpsArr | return none
    let some all := parseNameList names allArr | return none
    let some (ty, mt, ep) := ep.take ti | return none
    let some (vl, mv, ep) := ep.take vi | return none
    let ci : ConstantInfo := .opaqueInfo { name, levelParams := lps, type := ty, value := vl, all, isUnsafe := isU }
    let (env', fail) ← handleSimpleDecl ch sem cancelAbove dstRef cfg env ci (!(mt || mv))
    return some (names, levels, ep, env', fail)
  | [("quot", .obj data)] =>
    let some (.num (ni : Nat)) := data["name"]? | return none
    let some (.arr lpsArr) := data["levelParams"]? | return none
    let some (.num (ti : Nat)) := data["type"]? | return none
    let some (.str kindStr) := data["kind"]? | return none
    let some name := names[ni]? | return none
    -- Any non-standard quot name declines to official Lean.Replay for exact compatibility
    if !isQuotConstName name then return none
    let some lps := parseNameList names lpsArr | return none
    let kind? : Option QuotKind := match kindStr with
      | "type" => some .type
      | "ctor" => some .ctor
      | "lift" => some .lift
      | "ind" => some .ind
      | _ => none
    let some kind := kind? | return none
    let some (ty, _, ep) := ep.take ti | return none
    let ci : ConstantInfo := .quotInfo { name, levelParams := lps, type := ty, kind }
    let dup ← dstRef.modifyGet fun ds =>
      if isDupQuot env ds name then
        (true, { ds with failed := some s!"Duplicate declaration: {name}" })
      else
        (false, { ds with quotSeen := ds.quotSeen.insert name, quotInfos := ds.quotInfos.push (name, ci) })
    if dup then return some (names, levels, ep, env, true)
    if name == `Quot then
      if envHas env `Eq then
        match env.addDeclCore 0 0 .quotDecl (cancelTk? := some cancelTk) with
        | .ok env' =>
          dstRef.modify fun ds => { ds with quotAdded := true }
          return some (names, levels, ep, env', false)
        | .error ex =>
          let msg ← kernelFailMsg `Quot ex   -- tagged by constructor
          dstRef.modify fun ds => { ds with failed := some msg }
          return some (names, levels, ep, env, true)
      else
        dstRef.modify fun ds => { ds with
          deferred := ds.deferred.insert name ci,
          deferredOrder := ds.deferredOrder.push name,
          nDeferred := ds.nDeferred + 1 }
        return some (names, levels, ep, env, false)
    else
      return some (names, levels, ep, env, false)
  | [("inductive", .obj data)] =>
    let some (.arr typesArr) := data["types"]? | return none
    let some (.arr ctorsArr) := data["ctors"]? | return none
    let some (.arr recsArr) := data["recs"]? | return none
    let mut ep := ep
    let mut types : Array ConstantInfo := #[]
    for t in typesArr do
      let .obj td := t | return none
      let some (.num (ni : Nat)) := td["name"]? | return none
      let some (.arr lpsArr) := td["levelParams"]? | return none
      let some (.num (ti : Nat)) := td["type"]? | return none
      let some (.num (numParams : Nat)) := td["numParams"]? | return none
      let some (.num (numIndices : Nat)) := td["numIndices"]? | return none
      let some (.arr allArr) := td["all"]? | return none
      let some (.arr ctorsNameArr) := td["ctors"]? | return none
      let some (.num (numNested : Nat)) := td["numNested"]? | return none
      let some (.bool isRec) := td["isRec"]? | return none
      let some (.bool isUnsafe) := td["isUnsafe"]? | return none
      let some (.bool isReflexive) := td["isReflexive"]? | return none
      let some name := names[ni]? | return none
      let some lps := parseNameList names lpsArr | return none
      let some all := parseNameList names allArr | return none
      let some cnames := parseNameList names ctorsNameArr | return none
      let curEp := ep; ep := { rc := ByteArray.empty }
      let some (ty, _, ep') := curEp.take ti | return none
      ep := ep'
      types := types.push <| .inductInfo {
        name, levelParams := lps, type := ty, numParams, numIndices, all,
        ctors := cnames, numNested, isRec, isUnsafe, isReflexive
      }
    let mut ctors : Array ConstantInfo := #[]
    for c in ctorsArr do
      let .obj cd := c | return none
      let some (.num (ni : Nat)) := cd["name"]? | return none
      let some (.arr lpsArr) := cd["levelParams"]? | return none
      let some (.num (ti : Nat)) := cd["type"]? | return none
      let some (.num (indi : Nat)) := cd["induct"]? | return none
      let some (.num (cidx : Nat)) := cd["cidx"]? | return none
      let some (.num (numParams : Nat)) := cd["numParams"]? | return none
      let some (.num (numFields : Nat)) := cd["numFields"]? | return none
      let some (.bool isUnsafe) := cd["isUnsafe"]? | return none
      let some name := names[ni]? | return none
      let some lps := parseNameList names lpsArr | return none
      let some induct := names[indi]? | return none
      let curEp := ep; ep := { rc := ByteArray.empty }
      let some (ty, _, ep') := curEp.take ti | return none
      ep := ep'
      ctors := ctors.push <| .ctorInfo { name, levelParams := lps, type := ty, induct, cidx, numParams, numFields, isUnsafe }
    let mut recs : Array ConstantInfo := #[]
    for r in recsArr do
      let .obj rd := r | return none
      let some (.num (ni : Nat)) := rd["name"]? | return none
      let some (.arr lpsArr) := rd["levelParams"]? | return none
      let some (.num (ti : Nat)) := rd["type"]? | return none
      let some (.arr allArr) := rd["all"]? | return none
      let some (.num (numParams : Nat)) := rd["numParams"]? | return none
      let some (.num (numIndices : Nat)) := rd["numIndices"]? | return none
      let some (.num (numMotives : Nat)) := rd["numMotives"]? | return none
      let some (.num (numMinors : Nat)) := rd["numMinors"]? | return none
      let some (.bool k) := rd["k"]? | return none
      let some (.arr rulesArr) := rd["rules"]? | return none
      let some (.bool isUnsafe) := rd["isUnsafe"]? | return none
      let some name := names[ni]? | return none
      let some lps := parseNameList names lpsArr | return none
      let some all := parseNameList names allArr | return none
      let curEp := ep; ep := { rc := ByteArray.empty }
      let some (ty, _, ep') := curEp.take ti | return none
      ep := ep'
      let mut rules : List RecursorRule := []
      for ru in rulesArr do
        let .obj rud := ru | return none
        let some (.num (ci : Nat)) := rud["ctor"]? | return none
        let some (.num (nf : Nat)) := rud["nfields"]? | return none
        let some (.num (ri : Nat)) := rud["rhs"]? | return none
        let some ctor := names[ci]? | return none
        let curEp := ep; ep := { rc := ByteArray.empty }
        let some (rhs, _, ep') := curEp.take ri | return none
        ep := ep'
        rules := rules ++ [{ ctor, nfields := nf, rhs }]
      recs := recs.push <| .recInfo {
        name, levelParams := lps, type := ty, all, numParams, numIndices,
        numMotives, numMinors, rules, k, isUnsafe
      }
    match ← handleInductBlock cancelTk dstRef env types ctors recs with
    | none => return none
    | some (env', fail) => return some (names, levels, ep, env', fail)
  | _ => return none

/-! ## Pass 2 Fast-Record Stepper (100% RC=1 linear `names`, `levels`, `ep`) -/

private partial def namesAt (names : Array Name) (r : Array Nat) (j n : Nat) (acc : Array Name) : Option (List Name) :=
  if acc.size == n then some acc.toList
  else match names[r[j + acc.size]!]? with
    | some x => namesAt names r j n (acc.push x)
    | none => none

private partial def levelsAt (levels : Array Level) (r : Array Nat) (j n : Nat) (acc : Array Level) : Option (List Level) :=
  if acc.size == n then some acc.toList
  else match levels[r[j + acc.size]!]? with
    | some x => levelsAt levels r j n (acc.push x)
    | none => none

private partial def processRecs (ch : Std.CloseableChannel StreamJob) (sem : Std.CloseableChannel Unit)
    (cancelAbove : IO.Ref Nat) (cancelTk : IO.CancelToken) (dstRef : IO.Ref DeclSt) (cfg : RunCfg)
    (r : Array Nat) (strs : Array String) (slow : Array (Option (Std.TreeMap.Raw String Json)))
    (j : Nat) (names : Array Name) (levels : Array Level) (ep : ExprPages) (env : Kernel.Environment) :
    IO StepRes := do
  if j >= r.size then return some (names, levels, ep, env, false)
  let tag := r[j]!
  if tag == tAPP then
    let i := r[j+1]!; let fi := r[j+2]!; let ai := r[j+3]!
    if i != ep.size then return none
    let some (fn, mf, ep) := ep.take fi | return none
    let some (arg, ma, ep) := ep.take ai | return none
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+4)
      names levels (ep.put i (.app fn arg) (mf || ma)) env
  else if tag == tFORALL || tag == tLAM then
    let i := r[j+1]!
    if i != ep.size then return none
    let bi := binderOf r[j+2]!
    let bdi := r[j+3]!; let ni := r[j+4]!; let ti := r[j+5]!
    if ni >= names.size then return none
    let nm := names[ni]!
    let some (ty, mt, ep) := ep.take ti | return none
    let some (bd, mb, ep) := ep.take bdi | return none
    let e := if tag == tFORALL then Expr.forallE nm ty bd bi else Expr.lam nm ty bd bi
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+6)
      names levels (ep.put i e (mt || mb)) env
  else if tag == tCONST then
    let i := r[j+1]!; let ni := r[j+2]!; let n := r[j+3]!
    if i != ep.size || ni >= names.size then return none
    let nm := names[ni]!
    let some us := levelsAt levels r (j+4) n #[] | return none
    let miss := constMiss env nm   -- + Bool.true / Bool.false for Nat.beq / Nat.ble
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+4+n)
      names levels (ep.put i (.const nm us) miss) env
  else if tag == tNSTR then
    let i := r[j+1]!; let pi := r[j+2]!; let si := r[j+3]!
    if i != names.size || pi >= i || si >= strs.size then return none
    let pr := names[pi]!
    let s := strs[si]!
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+4)
      (names.push (.str pr s)) levels ep env
  else if tag == tSORT then
    let i := r[j+1]!; let li := r[j+2]!
    if i != ep.size || li >= levels.size then return none
    let lv := levels[li]!
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+3)
      names levels (ep.put i (.sort lv) false) env
  else if tag == tBVAR then
    let i := r[j+1]!
    if i != ep.size || r[j+2]! > 1048574 then return none   -- as the JSON path
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+3)
      names levels (ep.put i (.bvar r[j+2]!) false) env
  else if tag == tSLOW then
    match ← processSlowObj ch sem cancelAbove cancelTk dstRef cfg (slow[r[j+1]!]?.getD none) names levels ep env with
    | some (names', levels', ep', env', true) => return some (names', levels', ep', env', true)
    | some (names', levels', ep', env', false) =>
      processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+2) names' levels' ep' env'
    | none => return none
  else if tag == tNNUM then
    let i := r[j+1]!; let num := r[j+2]!; let pi := r[j+3]!
    if i != names.size || pi >= i then return none
    let pr := names[pi]!
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+4)
      (names.push (.num pr num)) levels ep env
  else if tag == tLSUCC then
    let i := r[j+1]!; let li := r[j+2]!
    if i != levels.size || li >= i then return none
    let lv := levels[li]!
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+3)
      names (levels.push (.succ lv)) ep env
  else if tag == tLPARAM then
    let i := r[j+1]!; let ni := r[j+2]!
    if i != levels.size || ni >= names.size then return none
    let nm := names[ni]!
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+3)
      names (levels.push (.param nm)) ep env
  else if tag == tLMAX || tag == tLIMAX then
    let i := r[j+1]!; let li1 := r[j+2]!; let li2 := r[j+3]!
    if i != levels.size || li1 >= i || li2 >= i then return none
    let l1 := levels[li1]!; let l2 := levels[li2]!
    let l := if tag == tLMAX then Level.max l1 l2 else Level.imax l1 l2
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+4)
      names (levels.push l) ep env
  else if tag == tLETE then
    let i := r[j+1]!
    if i != ep.size then return none
    let nd := r[j+2]! == 1
    let bdi := r[j+3]!; let ni := r[j+4]!; let ti := r[j+5]!; let vi := r[j+6]!
    if ni >= names.size then return none
    let nm := names[ni]!
    let some (ty, mt, ep) := ep.take ti | return none
    let some (vl, mv, ep) := ep.take vi | return none
    let some (bd, mb, ep) := ep.take bdi | return none
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+7)
      names levels (ep.put i (.letE nm ty vl bd nd) (mt || mv || mb)) env
  else if tag == tPROJ then
    let i := r[j+1]!
    if i != ep.size then return none
    let pidx := r[j+2]!; let si := r[j+3]!; let tni := r[j+4]!
    if tni >= names.size then return none
    let tn := names[tni]!
    let some (s, ms, ep) := ep.take si | return none
    let miss := ms || !envHas env tn
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (j+5)
      names levels (ep.put i (.proj tn pidx s) miss) env
  else if tag == tTHM then
    let nAll := r[j+1]!; let jl := j + 2 + nAll; let nLps := r[jl]!; let jn := jl + 1 + nLps
    let some all := namesAt names r (j+2) nAll #[] | return none
    let some lps := namesAt names r (jl+1) nLps #[] | return none
    let some name := names[r[jn]!]? | return none
    let some (ty, mt, ep) := ep.take r[jn+1]! | return none
    let some (vl, mv, ep) := ep.take r[jn+2]! | return none
    let ci : ConstantInfo := .thmInfo { name, levelParams := lps, type := ty, value := vl, all }
    let (env', fail) ← handleSimpleDecl ch sem cancelAbove dstRef cfg env ci (!(mt || mv))
    if fail then return some (names, levels, ep, env', true)
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (jn+3) names levels ep env'
  else if tag == tDEF then
    let nAll := r[j+1]!; let jh := j + 2 + nAll
    let hk := r[jh]!
    let hints : ReducibilityHints := if hk == 0 then .opaque else if hk == 1 then .abbrev else .regular r[jh+1]!.toUInt32
    let jl := jh + 2; let nLps := r[jl]!; let jn := jl + 1 + nLps
    let sf := r[jn+1]!
    let safety : DefinitionSafety := if sf == 0 then .safe else if sf == 1 then .unsafe else .partial
    let some all := namesAt names r (j+2) nAll #[] | return none
    let some lps := namesAt names r (jl+1) nLps #[] | return none
    let some name := names[r[jn]!]? | return none
    let some (ty, mt, ep) := ep.take r[jn+2]! | return none
    let some (vl, mv, ep) := ep.take r[jn+3]! | return none
    let ci : ConstantInfo := .defnInfo { name, levelParams := lps, type := ty, value := vl, hints, safety, all }
    let (env', fail) ← handleSimpleDecl ch sem cancelAbove dstRef cfg env ci (!(mt || mv))
    if fail then return some (names, levels, ep, env', true)
    processRecs ch sem cancelAbove cancelTk dstRef cfg r strs slow (jn+4) names levels ep env'
  else return none

/-! ## End-of-Stream Deferred DFS Replay (for out-of-order exports) -/

private structure DefState where
  env : Kernel.Environment
  state : Std.HashMap Name UInt8  -- 1 = remaining, 2 = pending, 0 = done
  postponedCtors : Array Name := #[]
  postponedRecs : Array Name := #[]
  failed : Bool := false

/-- does a deferred declaration `start` depend - through SYNTACTIC edges of deferred declarations (the edges
the deferred replay itself follows) - on a declaration that is pending on the current replay path (state 2) or in `onPath`?
Then a literal dependency on `start` must not be replayed first: it would be checked without that declaration. -/
private partial def deferredReachesPath (deferred : Std.HashMap Name ConstantInfo) (state : Std.HashMap Name UInt8)
    (onPath : NameSet) (start : Name) : Bool := Id.run do
  let mut stack : Array Name := #[start]
  let mut seen : NameSet := {}
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    if onPath.contains x || (state[x]?).getD 0 == 2 then return true
    if (state[x]?).getD 0 != 1 then continue
    let some ci := deferred[x]? | continue
    for d in ci.getUsedConstantsAsSet do stack := stack.push d
    if let .inductInfo ii := ci then
      for an in ii.all do
        if let some aci := deferred[an]? then
          for d in aci.getUsedConstantsAsSet do stack := stack.push d
          if let .inductInfo ati := aci then
            for cn in ati.ctors do
              if let some cci := deferred[cn]? then
                for d in cci.getUsedConstantsAsSet do stack := stack.push d
  return false

private partial def replayDeferredName (ch : Std.CloseableChannel StreamJob)
    (sem : Std.CloseableChannel Unit) (cancelAbove : IO.Ref Nat) (cancelTk : IO.CancelToken)
    (dstRef : IO.Ref DeclSt) (cfg : RunCfg) (deferred : Std.HashMap Name ConstantInfo)
    (n : Name) (dsRef : IO.Ref DefState) : IO Unit := do
  let status ← dsRef.modifyGet fun s =>
    if s.failed then (0, s)
    else if (s.state[n]?).getD 0 != 1 then (0, s)
    else (1, { s with state := s.state.insert n 2 })
  if status == 0 then return ()
  let some ci := deferred[n]? | return ()
  for dep in ci.getUsedConstantsAsSet do
    replayDeferredName ch sem cancelAbove cancelTk dstRef cfg deferred dep dsRef
    if (← dsRef.get).failed then return ()
  for dep in ciLitDeps ci do   -- r3: literal-triggered kernel lookups first (no-op when not exported / already present)
    -- an ORDER preference only - skipped when that name depends on this declaration (no cycle through it)
    let st := (← dsRef.get).state
    if deferredReachesPath deferred st {} dep then continue
    replayDeferredName ch sem cancelAbove cancelTk dstRef cfg deferred dep dsRef
    if (← dsRef.get).failed then return ()
  let stillPending := ((← dsRef.get).state[n]?).getD 0 == 2
  if !stillPending then return ()
  match ci with
  | .defnInfo _ | .thmInfo _ | .axiomInfo _ | .opaqueInfo _ =>
    let some decl := declOfCi? ci | do
      dsRef.modify fun s => { s with state := s.state.insert n 0 }
      return ()
    let envBefore := (← dsRef.get).env
    if let some r := cfg.thmRefs? then   -- value references
      if let .thmInfo info := ci then r.modify (·.insert n info.value.getUsedConstantsAsSet.toArray)
    match addToWalkEnv envBefore ci cfg with
    | .error msg =>
      dstRef.modify fun d => { d with failed := some (wrapFail n msg) }
      dsRef.modify fun s => { s with failed := true }
    | .ok (envAfter, evicted) =>
      let isRealAx := match ci with | .axiomInfo _ => true | _ => false
      if evicted || isRealAx then
        dstRef.modify fun d => { d with
          nEvictedThms := d.nEvictedThms + (if evicted then 1 else 0),
          realAxioms := if isRealAx then d.realAxioms.insert n else d.realAxioms }
      let doCheck := match cfg.onlyCheck? with
        | none => true
        | some targets => targets.contains n
      let fail ← if doCheck then submitJob ch sem cancelAbove dstRef n envBefore decl else pure false
      dsRef.modify fun s => { s with env := envAfter, state := s.state.insert n 0, failed := s.failed || fail }
  | .quotInfo _ =>
    replayDeferredName ch sem cancelAbove cancelTk dstRef cfg deferred `Eq dsRef
    if (← dsRef.get).failed then return ()
    let envBefore := (← dsRef.get).env
    match envBefore.addDeclCore 0 0 .quotDecl (cancelTk? := some cancelTk) with
    | .ok env' =>
      dstRef.modify fun d => { d with quotAdded := true }
      dsRef.modify fun s => { s with env := env', state := s.state.insert n 0 }
    | .error ex =>
      let msg ← kernelFailMsg n ex   -- tagged by constructor
      dstRef.modify fun d => { d with failed := some msg }
      dsRef.modify fun s => { s with failed := true }
  | .ctorInfo info =>
    dsRef.modify fun s => { s with postponedCtors := s.postponedCtors.push info.name, state := s.state.insert n 0 }
  | .recInfo info =>
    dsRef.modify fun s => { s with postponedRecs := s.postponedRecs.push info.name, state := s.state.insert n 0 }
  | .inductInfo info =>
    let mut allCis : Array ConstantInfo := #[]
    for an in info.all do
      let some aci := deferred[an]? | do
        dstRef.modify fun d => { d with failed := some s!"while replaying declaration '{n}':\nmissing mutual inductive '{an}'" }
        dsRef.modify fun s => { s with failed := true }
        return ()
      allCis := allCis.push aci
    -- every member of the block AND its constructors stay PENDING (state 2) until
    -- the block is in the environment - marking them done (0) here let `deferredReachesPath` miss a cycle back into the block
    -- (a literal dependency replayed before the block -> false `unknown constant`); they become done only after `addDeclCore`
    let mut blockMembers : Array Name := #[]
    for aci in allCis do
      blockMembers := blockMembers.push aci.name
      if let .inductInfo ati := aci then
        for cn in ati.ctors do blockMembers := blockMembers.push cn
    dsRef.modify fun s => { s with state := blockMembers.foldl (init := s.state) (fun m x => m.insert x 2) }
    -- Replay all type dependencies of every mutual inductive in `all`
    for aci in allCis do
      for dep in aci.getUsedConstantsAsSet do
        replayDeferredName ch sem cancelAbove cancelTk dstRef cfg deferred dep dsRef
        if (← dsRef.get).failed then return ()
    let mut indTypes : List InductiveType := []
    let mut blockRecs : Array ConstantInfo := allCis   -- C2: every record the declaration was built from
    for aci in allCis do
      let .inductInfo ati := aci | do
        dstRef.modify fun d => { d with failed := some s!"while replaying declaration '{n}':\nnot an inductive '{aci.name}'" }
        dsRef.modify fun s => { s with failed := true }
        return ()
      let mut cList : List Constructor := []
      for cn in ati.ctors do
        let some cci := deferred[cn]? | do
          dstRef.modify fun d => { d with failed := some s!"while replaying declaration '{n}':\nmissing ctor '{cn}'" }
          dsRef.modify fun s => { s with failed := true }
          return ()
        for dep in cci.getUsedConstantsAsSet do
          replayDeferredName ch sem cancelAbove cancelTk dstRef cfg deferred dep dsRef
          if (← dsRef.get).failed then return ()
        cList := cList ++ [{ name := cci.name, type := cci.type }]
        blockRecs := blockRecs.push cci
      indTypes := indTypes ++ [{ name := ati.name, type := ati.type, ctors := cList }]
    -- the literal-triggered lookups of EVERY type and constructor of the block first (order preference only:
    -- skipped when such a name depends on the block itself)
    let blockNames : NameSet := info.all.foldl (init := {}) (·.insert ·)
    for t in indTypes do
      for dep in litImplicitDeps (t.type :: t.ctors.map (·.type)) do
        let st := (← dsRef.get).state
        if deferredReachesPath deferred st blockNames dep then continue
        replayDeferredName ch sem cancelAbove cancelTk dstRef cfg deferred dep dsRef
        if (← dsRef.get).failed then return ()
    if let some msg := r9LooseBVars? indTypes then   -- C1 (loose bvars)
      dstRef.modify fun d => { d with failed := some msg }
      dsRef.modify fun s => { s with failed := true }
      return ()
    let envBefore := (← dsRef.get).env
    match envBefore.addDeclCore 0 0 (.inductDecl info.levelParams info.numParams indTypes false) (cancelTk? := some cancelTk) with
    | .ok env' =>
      -- C2 (record check): every record of the block (types, and the constructor records used, whatever their flags) must equal
      -- the constant the kernel generated under its name
      for r in blockRecs do
        let same := match env'.find? r.name with
          | some c => c == r
          | none => false
        if !same then
          dstRef.modify fun d => { d with failed := some s!"Export record of {r.name} differs from the kernel's constant" }
          dsRef.modify fun s => { s with failed := true }
          return ()
      dstRef.modify fun d => { d with nInducts := d.nInducts + 1 }
      dsRef.modify fun s => { s with env := env', state := blockMembers.foldl (init := s.state) (fun m x => m.insert x 0) }
    | .error ex =>
      let msg ← kernelFailMsg n ex   -- tagged by constructor
      let impl := blockImplicitUnknown indTypes ex
      dstRef.modify fun d => { d with failed := some msg, failedImplicitUnknown := impl }
      dsRef.modify fun s => { s with failed := true }

private def flushDeferred (ch : Std.CloseableChannel StreamJob) (sem : Std.CloseableChannel Unit)
    (cancelAbove : IO.Ref Nat) (cancelTk : IO.CancelToken) (dstRef : IO.Ref DeclSt)
    (cfg : RunCfg) (env : Kernel.Environment) : IO Kernel.Environment := do
  let ds0 ← dstRef.get
  if ds0.deferred.isEmpty || ds0.failed.isSome then return env
  let deferred := ds0.deferred
  let order := ds0.deferredOrder
  -- Drop `deferred` and `deferredOrder` from `dstRef` once extracted
  dstRef.modify fun d => { d with deferred := {}, deferredOrder := #[] }
  let mut state : Std.HashMap Name UInt8 := {}
  for n in order do
    if let some ci := deferred[n]? then
      if !ci.isUnsafe && !ci.isPartial then
        state := state.insert n 1
  let dsRef ← IO.mkRef ({ env, state } : DefState)
  for n in order do
    replayDeferredName ch sem cancelAbove cancelTk dstRef cfg deferred n dsRef
    if (← dsRef.get).failed then return (← dsRef.get).env
  let fin ← dsRef.get
  for cn in fin.postponedCtors do
    match fin.env.find? cn, deferred[cn]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if !(info == info') then
        dstRef.modify fun d => { d with failed := some s!"Invalid constructor {cn}" }
        return fin.env
    | _, _ =>
      dstRef.modify fun d => { d with failed := some s!"No such constructor {cn}" }
      return fin.env
  for rn in fin.postponedRecs do
    match fin.env.find? rn, deferred[rn]? with
    | some (.recInfo info), some (.recInfo info') =>
      if !(info == info') then
        dstRef.modify fun d => { d with failed := some s!"Invalid recursor {rn}" }
        return fin.env
    | _, _ =>
      dstRef.modify fun d => { d with failed := some s!"No such recursor {rn}" }
      return fin.env
  -- C2 (record check): a deferred record that was never replayed (isUnsafe/isPartial) must not carry the name of a constant of the
  -- environment (all of whose constants are safe and non-partial, so it could not be equal to it)
  for (n, ci) in deferred do
    if ci.isUnsafe || ci.isPartial then
      if (fin.env.find? n).isSome then
        dstRef.modify fun d => { d with failed := some s!"Export record of {n} differs from the kernel's constant" }
        return fin.env
  return fin.env

/-! ## Top-Level Streaming Execution & Targeted Fixed-Point Pin-Set Retry -/

private inductive PassOutcome where
  | ok (env : Kernel.Environment) (quotInfos : Array (Name × ConstantInfo))
  | fallbackParse
  | structuralErr (msg : String) (canBeEviction : Bool)
  | workerErr (env : Kernel.Environment) (quotInfos : Array (Name × ConstantInfo))
      (realAxioms : NameSet) (earliestMsg : String)
      (allFailed : Array (Nat × Name × Declaration × Kernel.Exception))
      (complete : Bool)

/-- the expressions of a failing declaration from which the kernel's lookups start; `none` for a
kind whose lookups this list would not cover (the caller then confirms with `--evict=off` instead of concluding). -/
private def declExprs? : Declaration → Option (Array Expr)
  | .thmDecl v => some #[v.type, v.value]
  | .defnDecl v => some #[v.type, v.value]
  | .axiomDecl v => some #[v.type]
  | .opaqueDecl v => some #[v.type, v.value]
  | .mutualDefnDecl vs => some (vs.foldl (init := #[]) fun acc v => acc.push v.type |>.push v.value)
  | _ => none

/-- names the official 4.36 kernel looks up WITHOUT a syntactic reference (literals, quotients, Nat/String
extensions; = the `lookupNames` of `overlap/src/r9d/PChk/Incr.lean` + the Nat binary operations and native-reduction
names of the judge scripts' kernel-primitive list). Seeding them only adds theorems to the pin set (over-approximation). -/
private def kernelLookupNames : Array Name := #[
  `Nat, `Nat.zero, `Nat.succ, `String, `String.ofList, `String.mk, `Char, `Char.ofNat, `List, `List.cons, `List.nil,
  `Bool, `Bool.true, `Bool.false, `Eq, `Eq.refl, `Quot, `Quot.mk, `Quot.lift, `Quot.ind,
  `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor,
  `Nat.shiftLeft, `Nat.shiftRight, `Nat.log2, `Lean.reduceBool, `Lean.reduceNat, `eagerReduce]

/-- every name a constant's record refers to = the `refsOf` (`overlap/src/r9d/PChk/Incr.lean`):
`getUsedConstantsAsSet` (type, value incl. theorem and opaque values, inductive ctors, recursor `all`) plus the block
structure the kernel looks up by name (inductive `all` and ctors, constructor `induct`, recursor `all`, rule ctors and rule
right-hand sides; a quotient needs `Eq`). -/
private def refsOfAll (ci : ConstantInfo) : NameSet := Id.run do
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

/-- Theorems to pin (keep as `thmInfo`) for a targeted retry of failing declarations = every EVICTED theorem (an
`axiomInfo` of the walk environment that is not a real axiom) reachable from the seeds and the kernel's own lookup names.
The walk follows EVERY reference of EVERY constant kind (`refsOfAll`; before: recursors, quotients
and opaque constants were not followed, nor inductive ctors / constructor `induct`), so the reachable set over-approximates
every constant the kernel can look up while checking the seeds' declarations; at a fixed point (no new theorem) the retry's
environment agrees with the non-evicting environment on all of them, and the retry's kernel failure is the official one. -/
private def expandKeepFromEnv (env : Kernel.Environment) (realAxioms : NameSet) (seeds : Array Expr)
    (initKeep : NameSet) (maxKeep : Nat) : NameSet × Bool := Id.run do
  let mut visited : NameSet := {}
  let mut keep := initKeep
  let mut queue : Array Name := #[]
  for e in seeds do
    for c in e.getUsedConstantsAsSet do
      if !visited.contains c then
        visited := visited.insert c
        queue := queue.push c
  for c in kernelLookupNames do
    if !visited.contains c then
      visited := visited.insert c
      queue := queue.push c
  let mut head := 0
  while head < queue.size do
    let c := queue[head]!
    head := head + 1
    match env.find? c with
    | none => pure ()
    | some ci =>
      if let .axiomInfo _ := ci then
        -- Only evicted theorems (NOT true axioms like propext/Classical.choice/sorryAx!) belong in keepSet!
        if !realAxioms.contains c && !keep.contains c then
          keep := keep.insert c
          if keep.size > maxKeep then return (keep, true)
      for d in refsOfAll ci do
        if !visited.contains d then visited := visited.insert d; queue := queue.push d
  return (keep, false)

/-- (bounded fallback): the COMPLETE set of theorems reachable from the seeds (and the kernel's own lookup
names). Like `expandKeepFromEnv`, but an EVICTED theorem's value references are taken from `refs` (recorded by the pass that
built `env`), so the walk sees through evicted bodies and needs no further rounds. Constants the export declares after the
failing declarations cannot be reached (dependencies come first), so the pass that stopped after them recorded everything. -/
private def closureKeep (env : Kernel.Environment) (realAxioms : NameSet) (seeds : Array Expr) (initKeep : NameSet)
    (refs : Std.HashMap Name (Array Name)) (maxKeep : Nat) : NameSet × Bool := Id.run do
  let mut visited : NameSet := {}
  let mut keep := initKeep
  let mut queue : Array Name := #[]
  for e in seeds do
    for c in e.getUsedConstantsAsSet do
      if !visited.contains c then
        visited := visited.insert c
        queue := queue.push c
  for c in kernelLookupNames do
    if !visited.contains c then
      visited := visited.insert c
      queue := queue.push c
  let mut head := 0
  while head < queue.size do
    let c := queue[head]!
    head := head + 1
    match env.find? c with
    | none => pure ()
    | some ci =>
      let mut next : Array Name := (refsOfAll ci).toArray
      if let .axiomInfo _ := ci then
        if !realAxioms.contains c then
          if !keep.contains c then
            keep := keep.insert c
            if keep.size > maxKeep then return (keep, true)
          next := next ++ (refs[c]?.getD #[])
      for d in next do
        if !visited.contains d then visited := visited.insert d; queue := queue.push d
  return (keep, false)

/-- theorem-count budget of the closure pass (environment `PCHK_LOWMEM_CLOSURE_MAX`, default 400000); above it the
check ends with no verdict ("memory budget") instead of the unbounded full `--evict=off` pass. The judge's memory cap stays the
hard limit (a run over it is killed = no verdict). -/
private def closureMaxKeep : IO Nat := do
  match (← IO.getEnv "PCHK_LOWMEM_CLOSURE_MAX") with
  | some v => pure (v.toNat?.getD 400000)
  | none => pure 400000

private def runStreamingOnce (exportFile : System.FilePath) (nthreads maxInflight : Nat)
    (cfg : RunCfg) (verbose : Bool) : IO PassOutcome := do
  let t0 ← IO.monoNanosNow
  let log (msg : String) : IO Unit := do
    if verbose then IO.eprintln s!"[pchk-lowmem {((← IO.monoNanosNow) - t0) / 1000000} ms] {msg}"
  let blockSize := 4 * 1024 * 1024
  let prefetch := min 8 (max 2 nthreads)
  -- Pass 1: zero-Expr-allocation refcount prescan
  let some scan ← prescanRc exportFile blockSize prefetch
    | return .fallbackParse
  log s!"pass1 done: {scan.nNames} names, {scan.nLevels} levels, {scan.nExprs} exprs (rc={scan.rc.size / 1048576} MiB)"
  -- Pass 2: streaming parse + bounded parallel check
  let emptyEnv ← Lean.mkEmptyEnvironment
  let cancelTk ← IO.CancelToken.new
  let (ch, sem, cancelAbove, workers) ← startBoundedWorkers nthreads maxInflight cancelTk cfg.collectAllErrs
  let (bs, reader) ← openBoundStream exportFile blockSize prefetch
  let dstRef ← IO.mkRef ({} : DeclSt)
  let mut names : Array Name := #[.anonymous]
  let mut levels : Array Level := #[.zero]
  let mut ep : ExprPages := { rc := scan.rc }
  let mut env : Kernel.Environment := emptyEnv.toKernelEnv
  let mut parseOk := true
  let mut failedEarly := false
  let targetCount? : Option Nat := cfg.onlyCheck?.map (·.size)
  repeat
    if failedEarly then break
    -- Early-stop in targeted retry Pass 2b as soon as every target decl has been submitted!
    if let some tc := targetCount? then
      let dsCur ← dstRef.get
      if dsCur.nSubmitted >= tc && dsCur.deferred.isEmpty then
        break
    match ← bs.ch.sync.recv with
    | none => break
    | some tk =>
      let chnk := tk.get
      discard <| (bs.sem.sync.send ()).toBaseIO
      let curNames := names; names := #[]
      let curLevels := levels; levels := #[]
      let curEp := ep; ep := { rc := ByteArray.empty }
      match ← processRecs ch sem cancelAbove cancelTk dstRef cfg chnk.tok.recs chnk.tok.strs chnk.tok.slow 0 curNames curLevels curEp env with
      | some (names', levels', ep', env', fail) =>
        names := names'; levels := levels'; ep := ep'; env := env'
        if fail then failedEarly := true
      | none =>
        parseOk := false
        break
  closeBoundStream bs
  let readerRes ← IO.wait reader
  let dsEnd ← dstRef.get
  let stoppedEarly := match targetCount? with
    | some tc => dsEnd.nSubmitted >= tc && dsEnd.deferred.isEmpty
    | none => false
  let readerErr := if stoppedEarly then false else match readerRes with | .error _ => true | .ok _ => false
  if !parseOk || readerErr then
    cancelTk.set
    discard <| ch.close.toBaseIO
    discard <| sem.close.toBaseIO
    for w in workers do discard <| IO.wait w
    return .fallbackParse
  let evictedExprs := ep.evictedExprs
  let freedPages := ep.freedPages
  let peakPages := ep.peakLivePages
  names := #[]
  levels := #[]
  ep := { rc := ByteArray.empty }
  if !(← dstRef.get).deferred.isEmpty && (← dstRef.get).failed.isNone then
    log s!"flushing {(← dstRef.get).deferred.size} deferred declarations"
    env ← flushDeferred ch sem cancelAbove cancelTk dstRef cfg env
  discard <| ch.close.toBaseIO
  let mut totalOk := 0
  let mut totalErr := 0
  let mut firstErr : Option (Nat × Name × Kernel.Exception) := none
  let mut firstErrImpl := false
  let mut firstResErr : Option (Nat × Name × Kernel.Exception) := none
  let mut allFailed : Array (Nat × Name × Declaration × Kernel.Exception) := #[]
  let mut maxDur := 0
  let mut maxName := Name.anonymous
  for w in workers do
    match ← IO.wait w with
    | .error e =>
      discard <| sem.close.toBaseIO
      return .structuralErr s!"{noVerdictTag}worker error: {e}" false
    | .ok wo =>
      totalOk := totalOk + wo.nOk
      totalErr := totalErr + wo.nErr
      for item in wo.failedDecls do
        allFailed := allFailed.push item
      if wo.maxDur > maxDur then
        maxDur := wo.maxDur; maxName := wo.maxName
      match wo.firstErr, firstErr with
      | some e1@(i1, _, _), some (i2, _, _) =>
        if i1 < i2 then
          firstErr := some e1
          firstErrImpl := wo.firstErrImplicit
      | some e1, none =>
        firstErr := some e1
        firstErrImpl := wo.firstErrImplicit
      | none, _ => pure ()
      match wo.firstResErr, firstResErr with
      | some e1@(i1, _, _), some (i2, _, _) => if i1 < i2 then firstResErr := some e1
      | some e1, none => firstResErr := some e1
      | none, _ => pure ()
  discard <| sem.close.toBaseIO
  -- C2 (record check), on every COMPLETE pass (not the targeted retry, which may stop early; its ACCEPT needs the complete
  -- pass 2a, which ran this): no skipped (isUnsafe/isPartial) record may carry the name of a constant of the final environment
  if cfg.onlyCheck?.isNone && (← dstRef.get).failed.isNone then
    for n in (← dstRef.get).skippedUnsafe do
      if envHas env n then
        dstRef.modify fun d => { d with failed := some s!"Export record of {n} differs from the kernel's constant" }
        break
  let ds ← dstRef.get
  log s!"pass2 done: streamed={ds.nStreamed} deferred={ds.nDeferred} inducts={ds.nInducts} ({ds.inductNs / 1000000} ms) submitted={ds.nSubmitted} ok={totalOk} err={totalErr} evictedThms={ds.nEvictedThms} keptThms={cfg.keepThms.size} evictedExprs={evictedExprs}/{scan.nExprs} freedPages={freedPages} peakLivePages={peakPages} longest={maxDur / 1000000} ms ({maxName})"
  if let some msg := ds.failed then
    -- an `unknown constant` the block does not mention is a lookup the kernel makes on its own; its absence
    -- is an artifact of this walk's order, not a kernel verdict -> the official path (Lean.Replay order) decides
    if ds.failedImplicitUnknown then
      log "inductive block failed on an unknown constant outside the block; official path decides"
      return .fallbackParse
    if !(isNoVerdictMsg msg) || firstErr.isNone then
      let canBeEvict := msg.startsWith "while replaying declaration" ||
        msg.startsWith (noVerdictTag ++ "while replaying declaration")
      return .structuralErr msg canBeEvict
  if let some (_, nm, ex) := firstErr then
    -- a worker's `unknown constant x` (x other than the declaration itself),
    -- when the export declares x (or the walk stopped before the end), is an ordering question, not a kernel verdict: the
    -- official path (Lean.Replay order) decides; x undeclared anywhere -> the rejection stands
    if firstErrImpl then
      if let .unknownConstant _ x := ex then
        if ds.failed.isSome || envHas env x || ds.deferred.contains x || ds.skippedUnsafe.contains x then
          log s!"'{nm}' failed on unknown constant '{x}' (declared by the export); official path decides"
          return .fallbackParse
    let earliestMsg ← kernelFailMsg nm ex   -- tagged by constructor
    -- reached with `ds.failed` set only when that was a no-verdict failure: the genuine worker error wins
    if ds.failed.isSome then
      return .structuralErr earliestMsg (canBeEvictionErr ex)
    if !canBeEvictionErr ex then
      return .structuralErr earliestMsg false
    let complete := (totalErr == allFailed.size) && (totalOk + totalErr == ds.nSubmitted)
    return .workerErr env ds.quotInfos ds.realAxioms earliestMsg allFailed complete
  -- off/strict, only resource failures: no verdict (tagged by constructor)
  if let some (_, nm, ex) := firstResErr then
    return .structuralErr (← kernelFailMsg nm ex) false
  if let some targets := cfg.onlyCheck? then
    if ds.nSubmitted != targets.size then
      return .structuralErr s!"{noVerdictTag}internal error: targeted retry submitted {ds.nSubmitted} of {targets.size} declarations" false
  if totalOk != ds.nSubmitted then
    return .structuralErr s!"{noVerdictTag}internal error: only {totalOk} of {ds.nSubmitted} kernel checks reported success" false
  return .ok env ds.quotInfos

/-- Low-memory streaming export check. Returns exit code (0 = accept, 1 = reject) matching Main.checkExport. -/
def checkExportLowMem (exportFile : String) (silent verbose : Bool) (nthreads maxInflight : Nat)
    (evict : EvictMode) : IO UInt32 := do
  let runFallbackOfficial : IO (Except String (Kernel.Environment × Array (Name × ConstantInfo))) := do
    if verbose then IO.eprintln "[pchk-lowmem] prescan declined; falling back to official LeanExport.parseStream + Lean.Replay"
    try
      let exportEnv ← IO.FS.withFile exportFile .read fun h => LeanExport.parseStream (.ofHandle h)
      let env ← Lean.mkEmptyEnvironment
      let origConstMap := exportEnv.constMap
      let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
      let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
      PChk.checkInductNoLooseBVars kernelConstMap   -- C1 (loose bvars)
      let kernelEnv ← try env.toKernelEnv.replay kernelConstMap
        catch e =>   -- exact-form resource message of the official path -> no verdict
          let m := toString e
          throw <| IO.userError ((if ← officialFailIsResource kernelConstMap m then noVerdictTag else "") ++ m)
      PChk.checkExportRecords kernelConstMap kernelEnv   -- C2 (record check)
      let mut qis : Array (Name × ConstantInfo) := #[]
      for qt in `Quot :: quotTargets do
        if let some ci := origConstMap[qt]? then qis := qis.push (qt, ci)
      pure (.ok (kernelEnv, qis))
    catch e =>
      pure (.error (toString e))
  let runFullOff : IO (Except String (Kernel.Environment × Array (Name × ConstantInfo))) := do
    match ← runStreamingOnce exportFile nthreads maxInflight { evict := .off } verbose with
    | .ok env qis => pure (.ok (env, qis))
    | .fallbackParse => runFallbackOfficial
    | .structuralErr msg _ => pure (.error msg)
    | .workerErr _ _ _ msg _ _ => pure (.error msg)
  let refs0Ref ← IO.mkRef ({} : Std.HashMap Name (Array Name))   -- value references
  let initCfg : RunCfg := match evict with
    | .smart => { evict := .strict, collectAllErrs := true, thmRefs? := some refs0Ref }
    | other => { evict := other, collectAllErrs := false }
  let res ← runStreamingOnce exportFile nthreads maxInflight initCfg verbose
  let refs0 ← refs0Ref.get
  let finalRes : Except String (Kernel.Environment × Array (Name × ConstantInfo)) ← match res with
    | .ok env qis => pure (.ok (env, qis))
    | .fallbackParse => runFallbackOfficial
    | .structuralErr msg canBeEvict =>
      if evict == .smart && canBeEvict then
        if verbose then IO.eprintln s!"[pchk-lowmem] inductive/quot error under eviction ({msg}); retrying with --evict=off"
        runFullOff
      else
        pure (.error msg)
    | .workerErr env0 qis0 realAx0 msg0 failed0 complete0 =>
      if evict != .smart then
        pure (.error msg0)
      else if !complete0 || failed0.isEmpty then
        if verbose then IO.eprintln s!"[pchk-lowmem] >{maxSmartErrsPerWorker} worker errors under eviction; retrying with --evict=off"
        runFullOff
      else
        -- Verify Quot constants against Pass 2a's complete env0 BEFORE dropping env0!
        let verifyTargets0 : NameSet := [`Quot, `Quot.mk, `Quot.lift, `Quot.ind].foldl (init := {}) (·.insert ·)
        let mut quotErr0 : Option String := none
        for (qn, info) in qis0 do
          if verifyTargets0.contains qn then
            match env0.find? qn with
            | none => quotErr0 := some s!"Could not find quotient constant in final kernel env: {qn}"
            | some info' => if info != info' then quotErr0 := some s!"Quotient constant mismatch on: {qn}"
        -- Targeted fixed-point pin-set retry: restore ONLY theorems reachable from failing decls,
        -- and re-check ONLY the failing decls (releasing curEnv BEFORE Pass 2b so 0 bytes overlap!).
        if verbose then
          let namesList := failed0.toList.map (fun (_, nm, _, _) => nm.toString)
          IO.eprintln s!"[pchk-lowmem] strict eviction had {failed0.size} failing decl(s): {String.intercalate ", " (namesList.take 20)}"
        let emptyKEnv := (← Lean.mkEmptyEnvironment).toKernelEnv
        let mut curEnv := env0
        let mut curFailed := failed0
        let mut curMsg := msg0
        let mut keepThms : NameSet := {}
        let mut out? : Option (Except String (Kernel.Environment × Array (Name × ConstantInfo))) := none
        let maxIter := 6
        let maxKeep := 25000
        -- value references of the theorems of the pass that built `curEnv` (pass 2a and every targeted pass record them)
        let mut lastRefs : Std.HashMap Name (Array Name) := refs0
        let mut closureNeeded := false
        for iter in [1:maxIter + 1] do
          -- a failing declaration of a kind whose kernel lookups `declExprs?` does not list -> no conclusion here
          let seeds? : Option (Array Expr) := curFailed.foldlM (m := Option) (init := (#[] : Array Expr))
            fun acc (_, _, d, _) => (declExprs? d).map (acc ++ ·)
          if seeds?.isNone then
            if verbose then IO.eprintln s!"[pchk-lowmem] failing declaration of an unlisted kind; confirming with --evict=off"
            out? := some (← runFullOff)
            break
          let seeds := seeds?.getD #[]
          let (keepThms', overflowed) := expandKeepFromEnv curEnv realAx0 seeds keepThms maxKeep
          if overflowed then
            -- no full --evict=off pass: the bounded closure pass below decides (curEnv is still the pass's env)
            if verbose then IO.eprintln s!"[pchk-lowmem] targeted pin-set exceeded {maxKeep} theorems; complete-closure pass"
            closureNeeded := true
            break
          -- CRITICAL FOR LOW-MEM: drop previous pass's Kernel.Environment BEFORE starting Pass 2b!
          curEnv := emptyKEnv
          if keepThms'.size == keepThms.size then
            -- Fixed point reached: every transitive theorem reachable from `curFailed` is already kept!
            -- r3: only a NON-resource kernel error is a genuine rejection; if every remaining failure is a resource error
            -- (deep recursion, excessive memory, timeout, interruption) there is no verdict.
            match curFailed.find? (fun (_, _, _, ex) => !isResourceErr ex) with
            | some (_, nm, _, ex) =>
              if verbose then IO.eprintln s!"[pchk-lowmem] targeted retry fixed point reached at iter {iter} (kept={keepThms.size}): genuine kernel rejection"
              let m ← (ex.toMessageData {} |>.toString)
              out? := some (.error s!"while replaying declaration '{nm}':\n{m}")
            | none =>
              if verbose then IO.eprintln s!"[pchk-lowmem] targeted retry fixed point reached at iter {iter}: only resource errors - no verdict"
              out? := some (.error (if isNoVerdictMsg curMsg then curMsg else noVerdictTag ++ curMsg))
            break
          let mut targets : NameSet := {}
          for (_, nm, _, _) in curFailed do targets := targets.insert nm
          if targets.size != curFailed.size then
            out? := some (← runFullOff)
            break
          if verbose then
            IO.eprintln s!"[pchk-lowmem] targeted retry iter {iter}: re-checking {targets.size} decl(s) with {keepThms'.size} pinned theorem(s)"
          keepThms := keepThms'
          let refsRef ← IO.mkRef ({} : Std.HashMap Name (Array Name))   -- value references
          lastRefs := {}
          let retryCfg : RunCfg := {
            evict := .strict, keepThms := keepThms, onlyCheck? := some targets, collectAllErrs := true, thmRefs? := some refsRef
          }
          match ← runStreamingOnce exportFile nthreads maxInflight retryCfg verbose with
          | .ok env' _qis' =>
            if let some qerr := quotErr0 then
              out? := some (.error qerr)
            else
              if verbose then IO.eprintln s!"[pchk-lowmem] ACCEPTED via targeted retry iter {iter} ({targets.size} decl(s) needed theorem unfolding, {keepThms.size} theorems pinned)"
              -- Quot already verified on complete Pass 2a env0 (Quot is unchanged by theorem eviction), so pass empty qis
              out? := some (.ok (env', #[]))
            break
          | .fallbackParse =>
            out? := some (← runFullOff)
            break
          | .structuralErr msg _ =>
            -- no rejection on a structural / internal error of a TARGETED retry (pass 2a had none): confirm instead
            if verbose then IO.eprintln s!"[pchk-lowmem] targeted retry iter {iter}: structural error ({msg}); confirming with --evict=off"
            out? := some (← runFullOff)
            break
          | .workerErr env' _ _ msg' failed' complete' =>
            if !complete' || failed'.isEmpty then
              out? := some (← runFullOff)
              break
            curEnv := env'
            curFailed := failed'
            curMsg := msg'
            lastRefs ← refsRef.get
        match out? with
        | some r => pure r
        | none =>
          -- (bounded fallback): instead of the unbounded full --evict=off pass, ONE targeted pass with the
          -- COMPLETE reachable-theorem set of the still-failing declarations; above the budget: no verdict ("memory budget")
          if verbose then
            IO.eprintln (if closureNeeded then "[pchk-lowmem] complete-closure pass (pin-set overflow)"
              else s!"[pchk-lowmem] targeted retry did not converge in {maxIter} iterations; complete-closure pass")
          let seeds := (curFailed.foldlM (m := Option) (init := (#[] : Array Expr))
            fun acc (_, _, d, _) => (declExprs? d).map (acc ++ ·)).getD #[]
          let mut targets : NameSet := {}
          for (_, nm, _, _) in curFailed do targets := targets.insert nm
          let cmax ← closureMaxKeep
          let (closure, over) := closureKeep curEnv realAx0 seeds keepThms lastRefs cmax
          curEnv := emptyKEnv
          lastRefs := {}
          if over then
            if verbose then IO.eprintln s!"[pchk-lowmem] complete closure exceeds {cmax} theorems: no verdict (memory budget)"
            pure (.error (noVerdictTag ++ s!"memory budget: the complete set of theorems reachable from the failing declaration(s) exceeds {cmax} theorems (the unbounded --evict=off pass is not run)"))
          else
            if verbose then IO.eprintln s!"[pchk-lowmem] complete-closure pass: re-checking {targets.size} decl(s) with {closure.size} pinned theorem(s)"
            let ccfg : RunCfg := { evict := .strict, keepThms := closure, onlyCheck? := some targets, collectAllErrs := true }
            match ← runStreamingOnce exportFile nthreads maxInflight ccfg verbose with
            | .ok env' _ =>
              if let some qerr := quotErr0 then pure (.error qerr)
              else
                if verbose then IO.eprintln s!"[pchk-lowmem] ACCEPTED via the complete-closure pass ({closure.size} theorems pinned)"
                pure (.ok (env', #[]))
            | .workerErr _ _ _ msg' failed' _ =>
              -- the closure is complete: the environment agrees with the non-evicting one on every constant the kernel can
              -- reach from these declarations, so a non-resource kernel error is the official verdict
              match failed'.find? (fun (_, _, _, ex) => !isResourceErr ex) with
              | some (_, nm, _, ex) =>
                if verbose then IO.eprintln s!"[pchk-lowmem] complete-closure pass: genuine kernel rejection"
                let m ← (ex.toMessageData {} |>.toString)
                pure (.error s!"while replaying declaration '{nm}':\n{m}")
              | none => pure (.error (if isNoVerdictMsg msg' then msg' else noVerdictTag ++ msg'))
            | .structuralErr msg _ =>
              pure (.error (if isNoVerdictMsg msg then msg else noVerdictTag ++ s!"complete-closure pass: {msg}"))
            | .fallbackParse =>
              pure (.error (noVerdictTag ++ "complete-closure pass: reader declined"))
  match finalRes with
  | .error msg =>
    if isNoVerdictMsg msg then   -- r3: resource exhaustion / interruption / internal error: no verdict, never REJECTED
      unless silent do IO.println s!"Lean default kernel could not decide (no verdict): {msg}"
      return 2
    unless silent do IO.println s!"Lean default kernel rejects the solution: {msg}"
    return 1
  | .ok (kernelEnv, quotInfos) =>
    unless silent do IO.println "Lean default kernel accepts the solution"
    try
      let verifyTargets : NameSet := [`Quot, `Quot.mk, `Quot.lift, `Quot.ind].foldl (init := {}) (·.insert ·)
      for (qn, info) in quotInfos do
        if verifyTargets.contains qn then
          let some info' := kernelEnv.find? qn |
            throw <| .userError s!"Could not find quotient constant in final kernel env: {qn}"
          if info != info' then
            throw <| IO.userError s!"Quotient constant mismatch on: {qn}"
      return 0
    catch e =>
      unless silent do IO.println s!"Quotient post-check rejects the solution: {e}"
      return 1

end PChk.LowMem
