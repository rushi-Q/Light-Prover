/-
OleanDiff: semantic comparison of two .olean files of the same module (Lean 4.33).
  lean --run OleanDiff.lean A.olean B.olean [TMPDIR]
Reports: imports equal?, constant names (order), per-constant kind/levels/type/value equality (Expr.equal: binder names
and annotations included), extraConstNames, extension entry counts; then re-saves both ModuleData with
imports := #[] and WITHOUT the position-only extensions (declaration ranges) and compares the bytes of the re-saved files.
Exit 0 = same up to imports + positions ("SAME-MODULO-POSITIONS"), 1 = different, 2 = usage/error.
-/
import Lean
open Lean

-- position-only / message-only extensions: declaration ranges, linter message log (positions of linter warnings)
def posExts : List Name := [`Lean.declRangeExt, `Lean.builtinDeclRanges, `Lean.Linter.lintLogExt]

/-- extra extensions to ignore, from the environment variable OLEANDIFF_IGNORE_EXTS (comma-separated; an entry matches an
extension whose name equals it or ends with "." ++ it, so `Lean.moduleDocExt` also matches the private registration name
`_private.Lean.DocString.Extension.0.Lean.moduleDocExt`); e.g. `Lean.docStringExt,Lean.moduleDocExt` for a
documentation-only edit. Default: none (behaviour unchanged). -/
def extraIgnored : IO (List String) := do
  match (← IO.getEnv "OLEANDIFF_IGNORE_EXTS") with
  | none => pure []
  | some s => pure <| (s.splitOn ",").filterMap fun x =>
      let x := x.trim
      if x.isEmpty then none else some x

def ignoredExt (extra : List String) (n : Name) : Bool :=
  posExts.contains n || extra.any (fun s => n.toString == s || n.toString.endsWith ("." ++ s))

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def valOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

unsafe def entryAsName (e : EnvExtensionEntry) : Name := unsafeCast e
@[implemented_by entryAsName] opaque entryAsName' (e : EnvExtensionEntry) : Name

/-- the two modules' namespace registrations differ only by the anonymous name (registered by an anonymous
`section`, e.g. the expansion of `set_option ... in cmd` = `section set_option ... cmd end`) -/
def anonNsOnlyDiff (ma mb : ModuleData) : Bool :=
  let get (m : ModuleData) : Array Name :=
    ((m.entries.find? (fun (n, _) => n.toString.endsWith "namespacesExt")).map (fun (_, es) => es.map entryAsName')).getD #[]
  let a := (get ma).filter (· != .anonymous); let b := (get mb).filter (· != .anonymous)
  a == b && get ma != get mb

def main (args : List String) : IO UInt32 := do
  match args with
  | a :: b :: rest =>
    let tmp := rest.headD "/tmp"
    let extra ← extraIgnored
    let ign := ignoredExt extra
    let (ma, _) ← readModuleData a
    let (mb, _) ← readModuleData b
    let mut diffs : Array String := #[]
    let impsA := ma.imports.map (·.module); let impsB := mb.imports.map (·.module)
    IO.println s!"imports: {impsA.size} vs {impsB.size} equal={impsA == impsB}"
    if ma.constNames != mb.constNames then
      diffs := diffs.push s!"constNames differ ({ma.constNames.size} vs {mb.constNames.size})"
      let sa := ma.constNames.toList; let sb := mb.constNames.toList
      let onlyA := sa.filter (fun n => !sb.contains n); let onlyB := sb.filter (fun n => !sa.contains n)
      IO.println s!"  only in A: {onlyA.take 20}"
      IO.println s!"  only in B: {onlyB.take 20}"
    let mapB : Std.HashMap Name ConstantInfo := mb.constants.foldl (fun m c => m.insert c.name c) {}
    let mut nconstdiff := 0
    for ca in ma.constants do
      match mapB[ca.name]? with
      | none => pure ()
      | some cb =>
        let same := kindOf ca == kindOf cb && ca.levelParams == cb.levelParams && ca.type.equal cb.type &&
          (match valOf? ca, valOf? cb with
           | some x, some y => x.equal y
           | none, none => true
           | _, _ => false)
        if !same then
          nconstdiff := nconstdiff + 1
          if nconstdiff ≤ 20 then
            IO.println s!"  constant differs: {ca.name} ({kindOf ca}) type={ca.type.equal cb.type}"
    if nconstdiff > 0 then diffs := diffs.push s!"{nconstdiff} constants differ (kind/levels/type/value)"
    if ma.extraConstNames != mb.extraConstNames then diffs := diffs.push "extraConstNames differ"
    let entA := (ma.entries.filter (fun (n, _) => !ign n)).map (fun (n, es) => (n, es.size))
    let entB := (mb.entries.filter (fun (n, _) => !ign n)).map (fun (n, es) => (n, es.size))
    if entA != entB && !anonNsOnlyDiff ma mb then
      diffs := diffs.push "extension entry counts differ"
      for (n, k) in entA do
        let k' := (entB.find? (·.1 == n)).map (·.2)
        if k' != some k then
          IO.println s!"  ext {n}: {k} vs {k'}"
          if n.toString.endsWith "namespacesExt" then
            for (n2, es) in ma.entries do
              if n2 == n then IO.println s!"    A namespaces: {es.map entryAsName'}"
            for (n2, es) in mb.entries do
              if n2 == n then IO.println s!"    B namespaces: {es.map entryAsName'}"
    -- byte comparison modulo imports and position-only extensions
    let anonOnly : Bool := anonNsOnlyDiff ma mb
    let norm (m : ModuleData) : ModuleData :=
      { m with imports := #[], entries := (m.entries.filter (fun (n, _) => !ign n)).map (fun (n, es) =>
          if anonOnly && n.toString.endsWith "namespacesExt" then (n, es.filter (fun e => entryAsName' e != .anonymous)) else (n, es))
          |>.filter (fun (n, es) => !(anonOnly && n.toString.endsWith "namespacesExt" && es.isEmpty)) }
    let fa : System.FilePath := s!"{tmp}/oleandiff.{← IO.monoNanosNow}.A.olean"
    let fb : System.FilePath := s!"{tmp}/oleandiff.{← IO.monoNanosNow}.B.olean"
    saveModuleData fa `M (norm ma); saveModuleData fb `M (norm mb)
    let ba ← IO.FS.readBinFile fa; let bb ← IO.FS.readBinFile fb
    IO.FS.removeFile fa; IO.FS.removeFile fb
    let bytesSame := ba == bb
    IO.println s!"normalized bytes: {ba.size} vs {bb.size} equal={bytesSame}"
    if !bytesSame then
      diffs := diffs.push "normalized olean bytes differ"
      -- localize: per extension, save only that extension's entries
      let empty (m : ModuleData) : ModuleData := { m with imports := #[], constNames := #[], constants := #[], extraConstNames := #[], entries := #[] }
      for (n, es) in ma.entries do
        if ign n then continue
        let es' := ((mb.entries.find? (·.1 == n)).map (·.2)).getD #[]
        let f1 : System.FilePath := s!"{tmp}/oleandiff.{← IO.monoNanosNow}.x.olean"
        let f2 : System.FilePath := s!"{tmp}/oleandiff.{← IO.monoNanosNow}.y.olean"
        saveModuleData f1 `M { empty ma with entries := #[(n, es)] }
        saveModuleData f2 `M { empty mb with entries := #[(n, es')] }
        let x ← IO.FS.readBinFile f1; let y ← IO.FS.readBinFile f2
        IO.FS.removeFile f1; IO.FS.removeFile f2
        if x != y then IO.println s!"  extension {n} differs ({es.size} entries)"
      let f1 : System.FilePath := s!"{tmp}/oleandiff.{← IO.monoNanosNow}.x.olean"
      let f2 : System.FilePath := s!"{tmp}/oleandiff.{← IO.monoNanosNow}.y.olean"
      saveModuleData f1 `M { empty ma with constNames := ma.constNames, constants := ma.constants, extraConstNames := ma.extraConstNames }
      saveModuleData f2 `M { empty mb with constNames := mb.constNames, constants := mb.constants, extraConstNames := mb.extraConstNames }
      let x ← IO.FS.readBinFile f1; let y ← IO.FS.readBinFile f2
      IO.FS.removeFile f1; IO.FS.removeFile f2
      if x != y then IO.println s!"  constants part differs in bytes (sharing/binder data)"
    if diffs.isEmpty then
      let tag := if extra.isEmpty then "" else "+IGNORED-EXTS"
      if anonNsOnlyDiff ma mb then IO.println s!"SAME-MODULO-POSITIONS+ANON-NAMESPACE{tag}"
      else IO.println s!"SAME-MODULO-POSITIONS{tag}"
      return 0
    else
      IO.println s!"DIFFERENT: {diffs}"; return 1
  | _ => IO.eprintln "usage: OleanDiff A.olean B.olean [TMPDIR]"; return 2
