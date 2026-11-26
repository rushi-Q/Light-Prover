import Export
open Lean

/--
Native exporter core (`native/fast_export.cpp`): reads the .olean files of the import closure directly and writes
exactly the same lines as `dumpConstant` for every constant in `targets` (after the metadata line), using
parallel interning. Returns 0 on success, 2 if it failed and stdout was rewound (caller falls back to the
reference implementation), 1 if it failed and stdout could not be rewound.
-/
@[extern "lean4export_fast_main"]
opaque fastExportMain (searchPath : @& Array String) (spPartial : Bool) (roots : @& Array Name)
    (targets : @& Array Name) (wholeEnv : Bool) (nthreads : UInt32) : IO UInt32

/-
F04 (fastverify): this binary is NATIVE-ONLY. It never runs the in-process reference implementation (finding 033: the
f581123 reference path is a rewrite of Export.lean, not the official exporter). Exit codes:
  0 = the native core wrote the complete export (byte-identical to the official lean4export by construction + tests),
  2 = declined / failed: stdout holds NO valid export; the caller (fastverify/export/export.sh) then runs the
      OFFICIAL lean4export binary on the same inputs into a fresh file.
-/
def main (args : List String) : IO UInt32 := do
  let (opts, args) := args.partition (fun s => s.startsWith "--" && s.length ≥ 3)
  let (imports, constants) := args.span (· != "--")
  -- options (--export-mdata, --export-unsafe, --ignore-missing, ...) are not implemented natively: decline
  unless opts.isEmpty do
    IO.eprintln "lean4export (native-only): options are not supported natively, declining"
    return 2
  let imports := imports.toArray.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! : Import }
  let wholeEnv := constants.tail?.isNone
  let targets := (constants.tail?.getD []).toArray.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!
  let nthreads := ((← IO.getEnv "LEAN4EXPORT_THREADS").bind String.toNat?).getD 0
  -- First try with the LEAN_PATH part of the search path only: computing the sysroot spawns `lean --print-prefix`
  -- (~50 ms).  The sysroot entry comes last, so wherever a module root is found in LEAN_PATH the lookup is the
  -- same; if some root is not found there, the native core writes nothing and returns 3 -> retry with everything.
  let spEnv := (← addSearchPathFromEnv []).toArray.map (·.toString)
  IO.println exportMetadata.compress
  (← IO.getStdout).flush
  let mut rc ← fastExportMain spEnv true (imports.map (·.module)) targets wholeEnv nthreads.toUInt32
  if rc == 3 then
    initSearchPath (← findSysroot)
    let sp := (← searchPathRef.get).toArray.map (·.toString)
    rc ← fastExportMain sp false (imports.map (·.module)) targets wholeEnv nthreads.toUInt32
  if rc == 0 then
    return 0
  IO.eprintln s!"lean4export (native-only): native core failed (rc {rc}), declining"
  return 2
