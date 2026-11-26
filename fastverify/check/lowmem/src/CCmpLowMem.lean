import CCmp
import LowMemParse

/-!
# `CCmpLowMem`: Low-memory `lake comparator` judge

Reuses `Lake.Check` (`CCmp.lean`) verbatim except:
1. `verifyCompareLowMem` streams `solution.export` without materializing non-challenge `Lean.Expr` ASTs;
2. With `--compare-only`, stops right after `compareAt` + `checkAxioms` (used by `check-sound-lowmem.sh` so the three
   legs run as separate sequential processes whose virtual memory is 100% reaped between legs);
3. Without `--compare-only`, runs external kernels and `Lean default` SEQUENTIALLY after `verifyCompareLowMem` has
   freed all solution tables, so peak RSS is `max` across legs rather than `sum`.
-/

namespace Lake.Check

def verifyMatchLowMem (compareOnly : Bool) (challengeExportPath solutionExportPath : System.FilePath) : M Unit := do
  let t0 ← IO.monoMsNow
  let theoremNames ← getTheoremNames
  let definitionNames ← getDefinitionNames
  let legalAxioms ← getLegalAxioms
  let prims ← primitiveTargets
  LowMemParse.verifyCompareLowMem challengeExportPath solutionExportPath theoremNames definitionNames legalAxioms prims
  IO.eprintln s!"[ccmp] compare (parse, compareAt, checkAxioms) finished after {(← IO.monoMsNow) - t0} ms"
  unless compareOnly do
    let ctx ← read
    for (kernelName, kernelCommand) in ← getExternalKernels do
      let tk ← IO.monoMsNow
      let err? ← (runExternalKernel kernelName kernelCommand solutionExportPath).run ctx
      IO.eprintln s!"[ccmp] kernel {kernelName} finished after {(← IO.monoMsNow) - t0} ms (leg {(← IO.monoMsNow) - tk} ms)"
      if let some err := err? then throw <| IO.userError err
    for (kernelName, kernelCommand) in ctx.bundledKernels do
      let tk ← IO.monoMsNow
      let err? ← (runExternalKernel kernelName kernelCommand solutionExportPath).run ctx
      IO.eprintln s!"[ccmp] kernel {kernelName} finished after {(← IO.monoMsNow) - t0} ms (leg {(← IO.monoMsNow) - tk} ms)"
      if let some err := err? then throw <| IO.userError err
    let tk ← IO.monoMsNow
    let err? ← (runBuiltinKernel solutionExportPath).run ctx
    IO.eprintln s!"[ccmp] kernel Lean default finished after {(← IO.monoMsNow) - t0} ms (leg {(← IO.monoMsNow) - tk} ms)"
    if let some err := err? then throw <| IO.userError err

def compareItLowMem (compareOnly : Bool) : M Unit := do
  let exportTargets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames)
  let challengeModule ← getChallengeModule
  withSafeBuildAndExport .challenge challengeModule exportTargets fun challengeExportPath => do
    let solutionModule ← getSolutionModule
    withSafeBuildAndExport .solution solutionModule exportTargets fun solutionExportPath => do
      verifyMatchLowMem compareOnly challengeExportPath solutionExportPath
      if compareOnly then
        IO.println "Comparison and axiom check passed!"
      else
        IO.println "Your solution is okay!"

def runComparatorLowMem (compareOnly : Bool) (configFile? : Option System.FilePath)
    (challengeFromExport? solutionFromExport? : Option System.FilePath) (paranoid : Bool)
    (inadvisablyNoSandbox : Bool) (lean : LeanInstall) (lake : LakeInstall)
    (projectDir : System.FilePath) : IO ExitCode := do
  let resolved ← resolveModuleStore "comparator" #[
      ("--challenge-from-export", .challenge, challengeFromExport?),
      ("--solution-from-export", .solution, solutionFromExport?)
    ]
  let moduleStore ←
    match resolved with
    | .error rc => return rc
    | .ok store => pure store
  let base ←
    match ← mkContext "comparator" paranoid inadvisablyNoSandbox lean lake projectDir moduleStore with
    | .error rc => return rc
    | .ok ctx => pure ctx

  let configFile := configFile?.getD "comparator.json"
  let contents ←
    try IO.FS.readFile configFile
    catch e => return ← cannotRun s!"could not read the configuration: {e}"
  let cfg ←
    match Lean.Json.parse contents >>= Lean.fromJson? (α := Config) with
    | .error e => return ← cannotRun s!"malformed configuration in '{configFile}': {e}"
    | .ok cfg => pure cfg

  let theoremNames := cfg.theorem_names.map String.toName
  let definitionNames := cfg.definition_names.getD #[] |>.map String.toName
  if theoremNames.isEmpty && definitionNames.isEmpty then
    return ← cannotRun "nothing to check: the configuration names no theorems or definitions"
  let externalKernels ←
    if compareOnly then
      if cfg.enable_nanoda?.getD false && !(cfg.external_kernels?.getD {}).isEmpty then
        return ← cannotRun "cannot use `enable_nanoda` and `external_kernels` at the same time; register nanoda in the list instead"
      else pure {}
    else
      match ← resolveExternalKernels cfg with
      | .error rc => return rc
      | .ok ks => pure ks

  let needsProject := !(moduleStore.contains .challenge && moduleStore.contains .solution)
  if needsProject then
    if let some rc ← checkManifest "comparator" base.projectDir then
      return rc

  try
    let ctx := { base with
      challengeModule := cfg.challenge_module.toName,
      solutionModule := cfg.solution_module.toName,
      theoremNames,
      definitionNames,
      legalAxioms := cfg.permitted_axioms.map String.toName,
      externalKernels,
      nanodaThreads := cfg.nanoda_threads?.getD 4,
      whichLeanChecker := ((← IO.getEnv "CCMP_LEANCHECKER").map System.FilePath.mk).getD base.whichLeanChecker
    }
    if needsProject then
      let (leanPath, binPath) ← ReaderT.run safeResolveWorkspace ctx
      ReaderT.run (compareItLowMem compareOnly) { ctx with leanPath, binPath }
    else
      ReaderT.run (compareItLowMem compareOnly) ctx
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

end Lake.Check
