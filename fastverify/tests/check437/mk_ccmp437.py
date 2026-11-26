#!/usr/bin/python3 -I
"""mk_ccmp437.py OFFICIAL_CHECK_LEAN OUT_CCmp.lean  - derive CCmp.lean (ccmp-437) from the OFFICIAL Lean 4.37.0-rc1
src/lake/Lake/CLI/Check.lean by the same modifications that fastverify/check/sound/src/CCmp.lean applies to the
4.36.0 file, adapted to 4.37's `M` monad
(ReaderT Context <| StateRefT State IO). Every replacement must match exactly once (else the script fails): the resulting
file is reviewed as `diff -u Check-v4.37.0-rc1.lean CCmp.lean`."""
import sys
src = open(sys.argv[1], encoding="utf-8").read()

def rep(old, new, count=1):
    global src
    n = src.count(old)
    assert n == count, f"expected {count} occurrence(s), found {n}: {old[:80]!r}"
    src = src.replace(old, new)

# 1. not a module-system file inside the pchk Lake project (as in the 4.36 CCmp.lean): drop `module`, `public`
rep("-/\nmodule\n\nprelude\n", "-/\n\nprelude\n")
for imp in ["Lake.Check.Axioms", "Lake.Check.Compare", "Lake.Config.InstallPath", "Lake.Util.Exit", "Lake.Util.Version",
            "Lean.Data.Json.FromToJson"]:
    rep(f"public import {imp}\n", f"import {imp}\n")
rep("import Init.Data.String.TakeDrop\n", "import Init.Data.String.TakeDrop\nimport PChk.PersistentRead\n")
rep("import Std.Internal.UV.System\n", "import Std.Internal.UV.System\nimport FastParse\nimport ParAxioms\n")
for kw in ["inductive StepJudgement", "inductive Judgement", "inductive Output", "structure StepReport", "structure Config",
           "structure CompareReport", "structure CheckReport", "def Report.currentVersion", "structure Report (",
           "abbrev LakeComparatorReport", "abbrev LakeCheckReport", "def runComparator", "def runCheck"]:
    rep(f"\npublic {kw}", f"\n{kw}")
assert "public " not in src, [l for l in src.splitlines() if "public " in l]

# 2. nanoda thread count from the config (official: always 4)
rep("""  /--
  Whether the run prints a JSON report instead of its progress.
  -/
  json : Bool

abbrev M""", """  /--
  Whether the run prints a JSON report instead of its progress.
  -/
  json : Bool
  /-- C02: `num_threads` of the nanoda config the comparator generates (official: always 4). -/
  nanodaThreads : Nat := 4

abbrev M""")
rep('      ("num_threads", 4),\n', '      ("num_threads", (← read).nanodaThreads),\n')
rep("""  external_kernels? : Option (Std.TreeMap String (Array String))
  deriving Lean.FromJson, Lean.ToJson, Repr
""", """  external_kernels? : Option (Std.TreeMap String (Array String))
  /-- C02: threads for nanoda's generated config (default 4 as in the official comparator). -/
  nanoda_threads? : Option Nat := none
  deriving Lean.FromJson, Lean.ToJson, Repr
""")

# 3. concurrent judge (fast exact parsers, parallel axiom check, every kernel leg at once, early stop)
CONC = '''
/--
C02: `verifyMatch.verifyCompare` with two verdict-identical drop-ins (each with its own soundness note in
the soundness documentation): C05's `FastExport.parseExportFile` (returns exactly the official parser's
`constMap`/`constOrder`, or falls back to the official `LeanExport.parseStream`) and C06's
`ParAxioms.checkAxiomsPar` (same closure, same two predicates as `checkAxioms`). `compareAt` unchanged (4.37's, from
`Lake.Check.Compare`: with the 4.37 rule "Challenge definition is not sorried"). The `step` records are kept as in
4.37's `verifyCompare` (they only feed the `--json` report, which ccmp does not use).
-/
def verifyCompareFast (challengeExportPath : System.FilePath) (solutionExportPath : System.FilePath) :
    M Unit := do
  let t0 ← IO.monoMsNow
  let theoremNames ← getTheoremNames
  let definitionNames ← getDefinitionNames
  let solution ← step .compareStatements do
    -- S03 (speed only, same results): the two exports are parsed concurrently, and the solution with
    -- `PChk.parseExportFileP` (= `FastExport.parseExportFile` with the parsed objects marked persistent chunk by chunk,
    -- as pleanchecker reads it; only reference-count state differs), so handing the environment to the parallel axiom
    -- check does not walk and MT-mark all of it; the axiom check uses LEAN_NUM_THREADS workers (default 16, at most 256).
    let ct ← IO.asTask (prio := .dedicated) (FastExport.parseExportFile challengeExportPath)
    let solution ← unsafe PChk.parseExportFileP solutionExportPath
    let challenge ← IO.ofExcept (← IO.wait ct)
    IO.eprintln s!"[ccmp] exports parsed after {(← IO.monoMsNow) - t0} ms"
    let targets := (← getTheoremNames) ++ (← getLegalAxioms)
    IO.ofExcept <| compareAt challenge solution targets definitionNames (← primitiveTargets)
    return solution
  step .checkAxioms do
    let nt := min 256 (max 1 (((← IO.getEnv "LEAN_NUM_THREADS").bind (·.toNat?)).getD 16))
    IO.ofExcept <| (← ParAxioms.checkAxiomsPar solution theoremNames definitionNames (← getLegalAxioms) nt)

/--
Concurrent variant: the same checks as `verifyMatch` (= `verifyCompare; runKernels`), run CONCURRENTLY.

Every checker `runKernels` would run (external kernels, bundled kernels, the builtin `leanchecker`,
with exactly the same command lines) is started at once, each in its own dedicated thread, while
this thread does the statement/axiom comparison. The verdict is the conjunction of all of them,
exactly as before: a comparison failure is reported first (as when it ran first and aborted the
run), otherwise the first failing kernel in `runKernels`' order. Checkers are independent
processes reading the same read-only export, so only the wall-clock time changes (sum -> max).
4.37 port (D23): `M` carries a `StateRefT State` for the step records of the `--json` report; every concurrent leg runs
with a private, discarded state (`.run ctx |>.run' {}`): the records are not read by ccmp (no `--json`), the verdict is
the legs' `Option String` results exactly as before.
-/
def verifyMatchConcurrent (challengeExportPath : System.FilePath)
    (solutionExportPath : System.FilePath) : M Unit := do
  let ctx ← read
  let mut kernels : Array (String × Array String) := #[]
  for (kernelName, kernelCommand) in ← getExternalKernels do
    kernels := kernels.push (kernelName, kernelCommand)
  kernels := kernels ++ ctx.bundledKernels
  -- diagnostics only (stderr): wall time of each checker since the start, to see the critical path
  let t0 ← IO.monoMsNow
  let timed {α : Type} (what : String) (act : IO α) : IO α := do
    let r ← act
    IO.eprintln s!"[ccmp] {what} finished after {(← IO.monoMsNow) - t0} ms"
    return r
  let mut tasks := #[]
  for (kernelName, kernelCommand) in kernels do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) <| timed s!"kernel {kernelName}"
      ((runExternalKernel kernelName kernelCommand solutionExportPath).run ctx |>.run' {}))
  tasks := tasks.push (← IO.asTask (prio := .dedicated) <| timed "kernel Lean default"
    ((runBuiltinKernel solutionExportPath).run ctx |>.run' {}))
  -- S03 early stop: the verdict is the conjunction of the comparison and every checker, so a definite failure of the
  -- comparison or of the builtin Lean kernel already decides REJECT: we report it as soon as it happens instead of
  -- waiting for the slower legs (the caller's sandbox kills them when this process exits). Failures of EXTERNAL kernels do
  -- not stop early (a wrapper may need the Lean kernel's own verdict to tell "the external kernel could not decide" from a
  -- rejection), so for them the behaviour is unchanged: wait for everything, then report the first failure in
  -- `runKernels`' order. An ACCEPT still needs every leg to finish and accept.
  let compareTask ← IO.asTask (prio := .dedicated) <| timed "compare (parse, compareAt, checkAxioms)"
    (verifyCompareFast challengeExportPath solutionExportPath |>.run ctx |>.run' {})
  let early : Task (Except IO.Error (Option String)) := compareTask.map (sync := true) fun
    | .ok () => .ok none
    | .error e => .error e
  let leanTask := tasks.back!
  let mut pending : List (Task (Except IO.Error (Option String))) := [early, leanTask]
  while h : 0 < pending.length do
    let (r, rest) ← IO.waitAny' pending h
    pending := rest
    match r with
    | .ok none => pure ()
    | .ok (some error) => throw <| IO.userError error
    | .error e => throw e
  -- comparison and Lean kernel accepted: the remaining (external) kernels, reported as before
  let mut result := none
  for task in tasks do
    match ← IO.wait task with
    | .ok r => result := result <|> r
    | .error e => result := result <|> some (toString e)
  if let some error := result then
    throw <| IO.userError error

def compareIt : M Unit := do'''
rep("\ndef compareIt : M Unit := do", CONC)
rep("""      verifyMatch challengeExportPath solutionExportPath
      progress "Your solution is okay!\"""", """      verifyMatchConcurrent challengeExportPath solutionExportPath
      progress "Your solution is okay!\"""")

# 4. nanoda threads + an alternative Lean-kernel replay binary (CCMP_LEANCHECKER), as in the 4.36 ccmp
rep("""    legalAxioms := cfg.permitted_axioms.map String.toName,
    externalKernels
  }
  runReporting ctx""", """    legalAxioms := cfg.permitted_axioms.map String.toName,
    externalKernels
    nanodaThreads := cfg.nanoda_threads?.getD 4
    -- optionally a different Lean-kernel replay binary (e.g. the parallel leanchecker);
    -- default = the toolchain's own `leanchecker`, as in the official comparator.
    whichLeanChecker := ((← IO.getEnv "CCMP_LEANCHECKER").map System.FilePath.mk).getD base.whichLeanChecker
  }
  runReporting ctx""")

open(sys.argv[2], "w", encoding="utf-8").write(src)
print("wrote", sys.argv[2], len(src.splitlines()), "lines")
