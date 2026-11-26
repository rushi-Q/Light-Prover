/-
`parseExportFileP`: C05's `FastExport.parseExportFile` (FastParse.lean, used verbatim) with one memory-management
difference: after each streamed chunk is built, the objects that chunk created (names, levels, expressions, constants)
are marked persistent (`Runtime.markPersistent`, as Lean does for imported environments) while they are still hot in
the cache. The parsed values are produced by the same `FastExport.build` on the same chunks with the same fallback rule
(any decline => the OFFICIAL `LeanExport.parseStream` from scratch), so the result is exactly that of
`FastExport.parseExportFile` (and hence of the official reader); only reference-count state differs. This replaces the
single cold traversal of the whole export by `Runtime.markPersistent` after parsing (3.8 s on Mathlib).
Safety of the marking: the builder thread is the only one using these objects (tokenizer tasks have finished with their
chunk; the reader thread holds only raw bytes).
-/
import FastParse

namespace PChk
open Lean FastExport

/-- Mark persistent every element of `xs` (a fresh slice of a builder table). -/
unsafe def markAll {α : Type} (xs : Array α) : IO Unit := do
  for x in xs do discard <| Runtime.markPersistent x

/-- `FastExport.consume` with per-chunk persistent marking. `e0 n0 l0 k0` = the table sizes of `st` at entry; they are
passed as ARGUMENTS (computed by the caller before this chunk's build starts): if they were computed from `st` inside,
the compiler may keep references to the tables across `build` (it delays pure lets), which makes the first push of every
chunk copy the whole table. -/
unsafe def consumeP (s : Task (Option Stream)) (st : St) (nslow nchunks e0 n0 l0 k0 : Nat) :
    IO (Option (St × Nat × Nat)) := do
  match s.get with
  | none => return none
  | some .done => return some (st, nslow, nchunks)
  | some (.more c next) =>
    let ch := c.get
    match build ch.buf ch.tok.recs ch.tok.strs ch.tok.slow 0 st nslow with
    | some (st, nslow) =>
      -- copy the chunk's slices out (small), mark them, drop them: the tables themselves stay unshared
      let es := st.exprs.extract e0 st.exprs.size
      let ns := st.names.extract n0 st.names.size
      let ls := st.levels.extract l0 st.levels.size
      let cs := (st.constOrder.extract k0 st.constOrder.size).filterMap (st.constMap[·]?)
      markAll es; markAll ns; markAll ls; markAll cs
      consumeP next st nslow (nchunks + 1) st.exprs.size st.names.size st.levels.size st.constOrder.size
    | none => return none

/-- `FastExport.parseFileStream?` with `consumeP`. -/
unsafe def parseFileStreamP? (path : System.FilePath) (blockSize : Nat := 8 * 1024 * 1024) :
    IO (Option (Std.HashMap Name ConstantInfo × Array Name × Nat × Nat)) := do
  let h ← IO.FS.Handle.mk path .read
  let _ ← h.getLine
  let p ← IO.Promise.new
  let res := p.result?
  let _reader ← IO.asTask (prio := .dedicated) (readLoop h blockSize.toUSize .empty p)
  let st : St := { names := #[.anonymous], levels := #[.zero], exprs := #[], constMap := {}, constOrder := #[] }
  match ← consumeP res st 0 0 st.exprs.size st.names.size st.levels.size st.constOrder.size with
  | some (st, nslow, nchunks) =>
    if nchunks == 0 then return none
    return some (st.constMap, st.constOrder, nslow, nchunks)
  | none => return none

/-- = `FastExport.parseExportFile`, with the fast path's objects marked persistent chunk by chunk. -/
unsafe def parseExportFileP (path : System.FilePath) : IO LeanExport.ExportedEnv := do
  match ← (parseFileStreamP? path).toBaseIO with
  | .ok (some (constMap, constOrder, _, _)) => return { constMap, constOrder }
  | _ => IO.FS.withFile path .read fun h => LeanExport.parseStream (.ofHandle h)

end PChk
