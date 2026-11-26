/-
fastverify build planner.

Computes, with Lake 4.33.1's OWN code (workspace loading, lakefile elaboration/TOML decoding, target resolution,
module discovery, header parsing, import resolution, per-module args/options/paths, package id), the exact `lean`
invocations that `lake build` (no arguments) would run for the ROOT package, so that a plain DAG scheduler can run them.
Anything this planner cannot reproduce exactly is DECLINED (exit 3, reason on stdout) and the caller must run the
official `lake build` instead.

Usage (run inside the build sandbox, cwd = project root, same environment as the official `lake build`):
  planner SYSROOT OUT.jsonl   (SYSROOT = the official toolchain whose bin/lake the official flow runs)
Output: line 1 = header object, then one object per module to build (topologically unsorted), then a final
{"end":N} line. Exit 0 = plan written; 3 = declined (reason printed); anything else = error (treat as decline).
-/
import Lake
import Lake.Load.Workspace
import Lake.CLI.Build
open Lake Lean System

def declineCode : UInt32 := 3

structure Plan where
  mods : Array Lake.Module := #[]
  seen : NameSet := {}
  extImports : NameSet := {}
  reasons : Array String := #[]
  headers : NameMap ModuleHeader := {}
  resolved : Std.HashMap Name (Option Lake.Module) := {}
  /-- S04: precomputed provider counts (pure function of the workspace), filled in parallel before the visit -/
  provsPre : Std.HashMap Name Nat := {}
  /-- A03 (sound mode only, `--relaxed`): accept Lake's own (deterministic) choice where the exact planner declines because
  the choice is ambiguous (module in several libraries, import provided by several packages). Exactness only. -/
  relaxed : Bool := false
  /-- A03 (sound mode only, `--targets`): only the import closure of the given modules is built (as the official 4.36
  `lake comparator` builds `lake build <solution_module>`), so a library's default facets do not matter -/
  targetsMode : Bool := false

abbrev PlanM := StateT Plan IO

def decline (msg : String) : PlanM Unit :=
  modify fun s => {s with reasons := s.reasons.push msg}

def checkLib (ws : Workspace) (lib : LeanLib) : PlanM Unit := do
  let n := lib.name.toString
  unless lib.defaultFacets == #[LeanLib.leanArtsFacet] || (← get).targetsMode do
    decline s!"lean_lib {n}: defaultFacets {lib.defaultFacets} != [leanArts]"
  if lib.precompileModules then decline s!"lean_lib {n}: precompileModules"
  unless lib.extraDepTargets.isEmpty do decline s!"lean_lib {n}: extraDepTargets"
  unless lib.config.needs.isEmpty do decline s!"lean_lib {n}: needs"
  unless lib.pkg.extraDepTargets.isEmpty do decline s!"package {lib.pkg.prettyName}: extraDepTargets"
  unless lib.config.dynlibs.isEmpty do decline s!"lean_lib {n}: dynlibs"
  unless lib.config.plugins.isEmpty do decline s!"lean_lib {n}: plugins"
  let _ := ws

/-- `Workspace.findModule?` (memoized; pure function of the loaded workspace). -/
def resolve (ws : Workspace) (n : Name) : PlanM (Option Lake.Module) := do
  if let some r := (← get).resolved.get? n then return r
  let r := ws.findModule? n
  modify fun s => {s with resolved := s.resolved.insert n r}
  return r

/-- Lake's `Module.recFetchInput` header (cached; root and dependency modules). -/
def getHeader (mod : Lake.Module) : PlanM ModuleHeader := do
  if let some h := (← get).headers.find? mod.name then return h
  let path := mod.leanFile
  let contents ← IO.FS.readFile path
  let h ← Lean.parseImports' contents path.toString
  modify fun s => {s with headers := s.headers.insert mod.name h}
  return h

/-- Lake's `Module.computeExportInfo`: (arts, allArts). -/
def expArts (mod : Lake.Module) (isModule : Bool) : ImportArtifacts × ImportArtifacts :=
  if isModule then
    (.ofArrays #[#[mod.oleanFile, mod.oleanServerFile], #[mod.irSigFile, mod.irFile]],
     .ofArrays #[#[mod.oleanFile, mod.oleanServerFile, mod.oleanPrivateFile], #[mod.irSigFile, mod.irFile]])
  else
    (.ofArrays #[#[mod.oleanFile]], .ofArrays #[#[mod.oleanFile]])

structure TransEntry where
  mod : Lake.Module
  importAll : Bool
  needsMeta : Bool

/-- Lake's `fetchTransImportArts.enqueue`. -/
def enqueue (ws : Workspace) (nonModule importAll needsMeta : Bool) (hdr : ModuleHeader)
    (q : Array TransEntry) : PlanM (Array TransEntry) :=
  hdr.imports.foldrM (init := q) fun imp q => do
    if let some mod ← resolve ws imp.module then
      let reachable := importAll || imp.isExported
      let importAll := nonModule || (importAll && imp.importAll)
      let needsMeta := needsMeta || (reachable && imp.isMeta)
      return if reachable || needsMeta then q.push {mod, importAll, needsMeta} else q
    else return q

/-- Lake's `fetchTransImportArts.walk`. -/
partial def walk (ws : Workspace) (nonModule : Bool) (s : NameMap ImportArtifacts) (metaVisited : NameSet)
    (q : Array TransEntry) : PlanM (NameMap ImportArtifacts) := do
  match q.back? with
  | none => return s
  | some {mod, importAll, needsMeta} =>
    let q := q.pop
    if let some arts := s.find? mod.name then
      let needsMeta' := needsMeta && !metaVisited.contains mod.name
      unless (importAll || needsMeta') && arts.oleanServer?.isSome && arts.oleanPrivate?.isNone do
        return ← walk ws nonModule s metaVisited q
    let hdr ← getHeader mod
    let (a, all) := expArts mod hdr.isModule
    let arts := if importAll then all else a
    let s := s.insert mod.name arts
    let metaVisited := if importAll || needsMeta then metaVisited.insert mod.name else metaVisited
    let q ← enqueue ws nonModule importAll needsMeta hdr q
    walk ws nonModule s metaVisited q

/-- Lake's importInfo `directArts` + `fetchTransImportArts` for an importer with header `hdr`. -/
def transImportArts (ws : Workspace) (hdr : ModuleHeader) : PlanM (NameMap ImportArtifacts) := do
  let nonModule := !hdr.isModule
  let mut directArts : NameMap ImportArtifacts := {}
  for imp in hdr.imports do
    if let some mod ← resolve ws imp.module then
      let ih ← getHeader mod
      let (a, all) := expArts mod ih.isModule
      if nonModule || imp.importAll then
        directArts := directArts.insert imp.module all
      else if !directArts.contains imp.module then
        directArts := directArts.insert imp.module a
  let mut q : Array TransEntry := #[]
  for imp in hdr.imports.reverse do   -- = Lake's foldrM
    if let some mod ← resolve ws imp.module then
      let ih ← getHeader mod
      q ← enqueue ws nonModule (nonModule || imp.importAll) imp.isMeta ih q
  walk ws nonModule directArts {} q

/-- Visit a root-package module and (recursively) its imports, like Lake's import graph. -/
partial def visit (ws : Workspace) (mod : Lake.Module) : PlanM Unit := do
  if (← get).seen.contains mod.name then return
  modify fun s => {s with seen := s.seen.insert mod.name}
  -- module name must be provided by exactly one library of exactly one package (else Lake's choice is ambiguous)
  let provs := match (← get).provsPre.get? mod.name with
    | some p => p
    | none => ws.packages.foldl (init := 0) fun acc pkg =>
      acc + (pkg.leanLibs.filter (·.isBuildableModule mod.name)).size
  if provs != 1 && !(← get).relaxed then decline s!"module {mod.name} is provided by {provs} libraries"
  let header ← getHeader mod
  for imp in header.imports do
    if imp.module == mod.name then decline s!"module {mod.name} imports itself"
    unless (← get).resolved.contains imp.module do
      let n := (ws.findModules imp.module).size
      if n > 1 && !(← get).relaxed then decline s!"import {imp.module} (in {mod.name}) is provided by {n} packages"
    match ← resolve ws imp.module with
    | some m =>
      if m.pkg.isRoot then
        visit ws m
      else
        modify fun s => {s with extImports := s.extImports.insert imp.module}
    | none => pure ()
  modify fun s => {s with mods := s.mods.push mod}

def strArr (a : Array String) : Json := Json.arr (a.map Json.str)

/-- S04: number of parallel chunks for the planner's pure per-module work. -/
def nChunks (n : Nat) : Nat := max 1 (min 256 (n / 512))

/-- S04: the provider count of `visit` (libraries of all packages that can build the module), in parallel chunks. -/
def prefetchProvs (ws : Workspace) (mods : Array Lake.Module) : IO (Array (Name × Nat)) := do
  let nc := nChunks mods.size
  let csz := (mods.size + nc - 1) / nc
  let mut ts := #[]
  for c in [0:nc] do
    let part := mods.extract (c * csz) (min mods.size ((c + 1) * csz))
    ts := ts.push (Task.spawn (prio := .dedicated) fun _ => part.map fun mod =>
      (mod.name, ws.packages.foldl (init := 0) fun acc pkg =>
        acc + (pkg.leanLibs.filter (·.isBuildableModule mod.name)).size))
  return ts.foldl (init := #[]) fun acc t => acc ++ t.get

/-- S04: `Lean.parseImports'` of every module's file, in parallel chunks (failures are left out). -/
def prefetchHeaders (mods : Array Lake.Module) : IO (Array (Name × ModuleHeader)) := do
  let nc := nChunks mods.size
  let csz := (mods.size + nc - 1) / nc
  let mut ts := #[]
  for c in [0:nc] do
    let part := mods.extract (c * csz) (min mods.size ((c + 1) * csz))
    ts := ts.push (← IO.asTask (prio := .dedicated) do
      let mut out : Array (Name × ModuleHeader) := #[]
      for mod in part do
        try
          let path := mod.leanFile
          let contents ← IO.FS.readFile path
          let h ← Lean.parseImports' contents path.toString
          out := out.push (mod.name, h)
        catch _ => pure ()
      return out)
  let mut res := #[]
  for t in ts do
    match ← IO.wait t with
    | .ok out => res := res ++ out
    | .error _ => pure ()
  return res

def main (args : List String) : IO UInt32 := do
  -- V07 (sound mode only, opt-in via build.sh `--unsafe sound-fast-path=importarts-empty`): importArts = {} for EVERY
  -- importer, module-system files included (default: exact Lake importArts for module-system importers)
  -- A03 (sound mode only, build.sh passes them under `sound-fast-path`): `--relaxed` (see Plan.relaxed) and
  -- `--targets FILE` (whitespace-separated root-package module names: plan the import closure of these modules instead of
  -- the default targets; the sound check only needs the closure of the solution module)
  let rec parse : List String → Bool → Bool → Option String → List String → Option (Bool × Bool × Option String × List String)
    | [], e, r, t, pos => some (e, r, t, pos.reverse)
    | "--import-arts-empty" :: xs, _, r, t, pos => parse xs true r t pos
    | "--relaxed" :: xs, e, _, t, pos => parse xs e true t pos
    | "--targets" :: f :: xs, e, r, _, pos => parse xs e r (some f) pos
    | x :: xs, e, r, t, pos => if x.startsWith "--" then none else parse xs e r t (x :: pos)
  let some (emptyArts, relaxed, targetsFile?, args) := parse args false false none []
    | IO.eprintln "usage: planner SYSROOT OUT.jsonl [--import-arts-empty] [--relaxed] [--targets FILE]"; return 2
  let [sysroot, outFile] := args | IO.eprintln "usage: planner SYSROOT OUT.jsonl [--import-arts-empty] [--relaxed] [--targets FILE]"; return 2
  let targetNames : Option (Array Name) ← match targetsFile? with
    | none => pure none
    | some f => do
      let txt ← IO.FS.readFile f
      let words := ((txt.replace "\n" " ").replace "\t" " ").splitOn " "
      pure (some ((words.filter (· ≠ "")).map String.toName).toArray)
  -- = Lake's findInstall? for the official `SYSROOT/bin/lake` (co-located with `SYSROOT/bin/lean`)
  let elan? ← findElanInstall?
  unless ← (FilePath.mk sysroot / "bin" / "lean").pathExists do
    IO.println s!"DECLINE: {sysroot}/bin/lean missing"; return declineCode
  if ((← IO.getEnv "LAKE_OVERRIDE_LEAN").bind envToBool?).getD false then
    IO.println "DECLINE: LAKE_OVERRIDE_LEAN set"; return declineCode
  let leanI ← LeanInstall.get sysroot (collocated := true)
  let lakeI := LakeInstall.ofLean leanI
  let env ← match ← (Env.compute lakeI leanI elan? none).toBaseIO with
    | .ok e => pure e
    | .error e => IO.println s!"DECLINE: Lake env: {e}"; return declineCode
  let some wsDir ← resolvePath? "." | IO.println "DECLINE: cannot resolve root"; return declineCode
  let config : LoadConfig := {
    lakeArgs? := #["build"], lakeEnv := env, wsDir,
    relConfigFile := defaultConfigFile, packageOverrides := #[], lakeOpts := {}, leanOpts := Lean.Options.empty,
    reconfigure := false, updateDeps := false, updateToolchain := true }
  let (ws?, log) ← (loadWorkspace config).captureLog
  for e in log.entries do IO.eprintln s!"lake-load: {e.level}: {e.message}"
  if log.entries.any (·.level ≥ .error) then
    IO.println "DECLINE: workspace load logged an error"; return declineCode
  let some ws := ws? | IO.println "DECLINE: workspace failed to load"; return declineCode
  let root := ws.root
  let t0 ← IO.monoMsNow
  IO.eprintln s!"planner: workspace loaded"
  let (_, st) ← (do
      modify fun s => {s with relaxed := relaxed, targetsMode := targetNames.isSome}
      if root.defaultTargets.isEmpty && targetNames.isNone then decline "no default targets"
      if (root.enableArtifactCache? <|> ws.enableArtifactCache?).getD false then decline "Lake artifact cache enabled"
      if (root.restoreAllArtifacts? <|> ws.restoreAllArtifacts?).getD false then decline "restoreAllArtifacts enabled"
      if root.precompileModules then decline "package precompileModules"
      unless root.externLibs.isEmpty do decline "package has extern_lib targets"
      -- S04 (speed only): parse the headers of every default-target module in parallel first; `getHeader` then finds
      -- them in its cache. Same function (`Lean.parseImports'` on the same file contents), so the same headers; a file
      -- that fails here is simply not cached and fails exactly as before when `visit` reaches it.
      -- each default lib's module array is computed ONCE (as before) and reused by the visit below
      let mut libMods : Std.HashMap Name (Array Lake.Module) := {}
      let mut allMods : Array Lake.Module := #[]
      for t in (if targetNames.isSome then root.leanLibs.map (·.name) else root.defaultTargets) do
        if let some lib := root.findLeanLib? t then
          unless libMods.contains lib.name do
            let ms ← lib.getModuleArray
            libMods := libMods.insert lib.name ms
            allMods := allMods ++ ms
      IO.eprintln s!"planner: {allMods.size} default-target modules listed at {(← IO.monoMsNow) - t0} ms"
      let hs ← prefetchHeaders allMods
      IO.eprintln s!"planner: headers parsed at {(← IO.monoMsNow) - t0} ms"
      modify fun s => {s with headers := hs.foldl (init := s.headers) fun m (n, h) => m.insert n h}
      let ps ← prefetchProvs ws allMods
      modify fun s => {s with provsPre := ps.foldl (init := s.provsPre) fun m (n, p) => m.insert n p}
      IO.eprintln s!"planner: provider counts at {(← IO.monoMsNow) - t0} ms"
      if let some tns := targetNames then
        for n in tns do
          match ws.findModule? n with
          | some m => if m.pkg.isRoot then visit ws m else decline s!"target {n} is not a module of the root package"
          | none => decline s!"target {n} is not a module of the workspace"
      else
        for t in root.defaultTargets do
          match root.findLeanLib? t with
          | some lib =>
            checkLib ws lib
            let ms ← match libMods.get? lib.name with
              | some ms => pure ms
              | none => lib.getModuleArray
            for mod in ms do
              visit ws mod
          | none => decline s!"default target {t} is not a lean_lib"
      -- every root lib that provides a visited module must also be supported
      for lib in root.leanLibs do
        if (← get).mods.any (fun m => lib.isBuildableModule m.name) then checkLib ws lib
    : PlanM Unit).run {}
  IO.eprintln s!"planner: {st.mods.size} modules visited in {(← IO.monoMsNow) - t0} ms"
  if !st.reasons.isEmpty then
    for r in st.reasons[0:20] do IO.println s!"DECLINE: {r}"
    return declineCode
  -- importArts (Lake's fetchTransImportArts): exact for module-system importers; for NON-module importers exact too
  -- while there are <= 5000 non-module files and the total number of entries stays <= exactBudget (1M), else {}
  -- for every non-module importer (equivalent, see
  -- README "importArts"; plancheck.py checks the per-run conditions). The header cache is threaded through.
  let exactBudget := 1000000
  let (artsMap, st) ← (do
      let mut m : NameMap (NameMap ImportArtifacts) := {}
      let mut total := 0
      let hs0 := (← get).headers
      let nNonModule : Nat := (← get).mods.foldl (init := 0) fun n mod =>
        if ((hs0.find? mod.name).map (·.isModule)).getD false then n else n + 1
      -- large projects (e.g. RH: 175k non-module files x ~10k imports) go straight to the {} representation
      let mut exactNonModule : Bool := decide (nNonModule ≤ 5000) && !emptyArts
      for mod in (← get).mods do
        let hdr ← getHeader mod
        if !emptyArts && (hdr.isModule || exactNonModule) then
          let a ← transImportArts ws hdr
          m := m.insert mod.name a
          unless hdr.isModule do
            total := total + a.size
            if total > exactBudget then exactNonModule := false
      unless exactNonModule do
        let hs := (← get).headers
        m := (← get).mods.foldl (init := m) fun m mod =>
          if !emptyArts && ((hs.find? mod.name).map (·.isModule)).getD false then m else m.insert mod.name {}
      return m
    : PlanM (NameMap (NameMap ImportArtifacts))).run st
  IO.eprintln s!"planner: importArts computed at {(← IO.monoMsNow) - t0} ms"
  let llvm := Lean.Internal.hasLLVMBackend ()
  let h ← IO.FS.Handle.mk outFile .write
  let header := Json.mkObj [
    ("lean", toJson leanI.lean.toString), ("leanir", toJson leanI.leanir.toString),
    ("sysroot", toJson leanI.sysroot.toString), ("githash", toJson leanI.githash),
    ("cwd", toJson (← IO.currentDir).toString), ("wsDir", toJson ws.dir.toString),
    ("leanPath", toJson ws.leanPath.toString),
    ("packages", Json.arr (ws.packages.map fun p => Json.mkObj [
        ("name", toJson p.prettyName), ("dir", toJson p.dir.toString),
        ("leanLibDir", toJson p.leanLibDir.toString), ("isRoot", toJson p.isRoot)])),
    ("extImports", strArr (st.extImports.toArray.map (·.toString))),
    ("nmods", toJson st.mods.size), ("llvm", toJson llvm)]
  h.putStrLn header.compress
  -- S04 (speed only): the per-module records are pure functions of the loaded workspace and the plan state; they are
  -- rendered in parallel chunks and written in the original order (byte-identical output).
  let render (mod : Lake.Module) : Except String String := Id.run do
    let path := mod.leanFile
    let hdr := (st.headers.find? mod.name).get!
    let leanOptions := mod.leanOptions
    let postpone := hdr.isModule && Compiler.compiler.postponeCompile.get leanOptions.toOptions
    if postpone then
      return .error s!"DECLINE: {mod.name}: compiler.postponeCompile"
    -- exactly Lake's mkModuleSetup; importArts exact for module-system files, {} for non-module files (equivalent,
    -- see README "importArts"; the per-run conditions are checked by plancheck.py)
    let importArts := (artsMap.find? mod.name).get!
    let setup : ModuleSetup := {
      name := mod.name, isModule := hdr.isModule, package? := mod.pkg.id?, imports? := none,
      importArts, dynlibs := #[], plugins := #[], options := leanOptions }
    -- exactly Lake's compileLeanModule argument order
    let mut argv := (mod.weakLeanArgs ++ mod.leanArgs).push path.toString
    argv := argv ++ #["-o", mod.oleanFile.toString, "-i", mod.ileanFile.toString, "-c", mod.cFile.toString]
    if llvm then argv := argv ++ #["-b", mod.bcFile.toString]
    argv := argv ++ #["--setup", mod.setupFile.toString, "--json"]
    let deps := hdr.imports.filterMap fun imp =>
      let r := match st.resolved.get? imp.module with
        | some r => r
        | none => ws.findModule? imp.module
      match r with
      | some m => if m.pkg.isRoot then some m.name.toString else none
      | none => none
    let rec_ := Json.mkObj [
      ("name", toJson mod.name.toString), ("src", toJson path.toString),
      ("argv", strArr argv), ("setupFile", toJson mod.setupFile.toString),
      ("setup", toJson (toJson setup).pretty),
      ("outputs", strArr (#[mod.oleanFile.toString, mod.ileanFile.toString, mod.cFile.toString] ++
        (if hdr.isModule then #[mod.oleanServerFile.toString, mod.oleanPrivateFile.toString,
          mod.irSigFile.toString, mod.irFile.toString] else #[]))),
      ("isModule", toJson hdr.isModule),
      ("deps", strArr deps)]
    return .ok rec_.compress
  let mods := st.mods
  let nc := nChunks mods.size
  let csz := (mods.size + nc - 1) / nc
  let mut ts := #[]
  for c in [0:nc] do
    let part := mods.extract (c * csz) (min mods.size ((c + 1) * csz))
    ts := ts.push (Task.spawn (prio := .dedicated) fun _ => part.map render)
  for t in ts do
    for r in t.get do
      match r with
      | .ok line => h.putStrLn line
      | .error msg => IO.println msg; return declineCode
  h.putStrLn (Json.mkObj [("end", toJson st.mods.size)]).compress
  IO.eprintln s!"planner: plan written at {(← IO.monoMsNow) - t0} ms"
  h.flush
  return 0
