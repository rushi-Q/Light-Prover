import CCmp
import LowMemParse

/-!
# `CCmpLowMem` (Lean 4.37.0-rc1 port): Low-memory `lake comparator` judge

Reuses `Lake.Check` (`check/sound/src-437/CCmp.lean`, sha256 `afc59503`) and
`LowMemParse.lean` (`check/lowmem/src/LowMemParse.lean`, byte-identical to the 4.36 source) verbatim except:
1. `M` in 4.37 `CCmp.lean` is `ReaderT Context <| StateRefT State IO`; `runExternalKernel` / `runBuiltinKernel` execute
   directly in `M`, and `runComparatorLowMem` evaluates `(compareItLowMem compareOnly).run ctx |>.run' {}`.
2. `mkContext` takes `json := false`, and the official 4.37 `ownKernels` name guard is preserved when `!compareOnly`.
3. `Lake.Check.compareAt` is the official v4.37.0-rc1 implementation from `libLake.a` (including the 4.37 rule
   `"Challenge definition is not sorried"` on `challengeConst.value`, which `LowMemParse` parses in full).
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
      let err? ← runExternalKernel kernelName kernelCommand solutionExportPath
      IO.eprintln s!"[ccmp] kernel {kernelName} finished after {(← IO.monoMsNow) - t0} ms (leg {(← IO.monoMsNow) - tk} ms)"
      if let some err := err? then throw <| IO.userError err
    for (kernelName, kernelCommand) in ctx.bundledKernels do
      let tk ← IO.monoMsNow
      let err? ← runExternalKernel kernelName kernelCommand solutionExportPath
      IO.eprintln s!"[ccmp] kernel {kernelName} finished after {(← IO.monoMsNow) - t0} ms (leg {(← IO.monoMsNow) - tk} ms)"
      if let some err := err? then throw <| IO.userError err
    let tk ← IO.monoMsNow
    let err? ← runBuiltinKernel solutionExportPath
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
    match ← mkContext "comparator" paranoid inadvisablyNoSandbox false lean lake projectDir moduleStore with
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
      | .ok ks =>
        let ownKernels := base.bundledKernels.map (·.1) |>.push builtinKernelName
        if let some name := ownKernels.find? ks.contains then
          return ← cannotRun s!"the external kernel `{name}` has the name of a kernel Lake runs itself"
        else pure ks

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
      let (leanPath, binPath) ← safeResolveWorkspace.run ctx |>.run' {}
      (compareItLowMem compareOnly).run { ctx with leanPath, binPath } |>.run' {}
    else
      (compareItLowMem compareOnly).run ctx |>.run' {}
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

end Lake.Check
