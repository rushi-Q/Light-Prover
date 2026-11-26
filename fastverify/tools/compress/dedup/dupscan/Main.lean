/-
dupscan: per-constant statement digests straight from .olean files, for duplicate detection.
Based on the olean_refs reader. Reads each file with readModuleData (mmap, no environment import).
Run it inside a bwrap sandbox: the oleans come from untrusted code (we only read data, never run project code).

Usage:
  dupscan scan OUT LIST        LIST lines "<module>\t<path to .olean>"
     OUT lines: K\t<mod>\t<kind>\t<name>\t<nlev>\t<tyhash>\t<valhash>\t<tydepth>\t<line>\t<endLine>\t<used...>
       tyhash = Expr.hash of the type after renaming the universe parameters to u_1..u_n (alpha-invariant:
       Expr.hash ignores binder names and binder infos); line/endLine from declRangeExt (0 if none);
       used = constants of type+value (space separated); then: constants of the type only, binder-info signature of the leading forall telescope
  dupscan cmp OUT LIST         LIST lines "<group>\t<module>\t<path>\t<name>"; for each group, compares the
     normalized type (and value) of every member with the first member by structural equality (Expr.eqv = alpha
     equivalence). OUT lines: Q\t<group>\t<name>\t<typeEq 0/1>\t<valueEq 0/1>\t<typeEqStrict 0/1>
       typeEqStrict additionally requires equal binder names and binder infos (Expr.equal).
-/
import Lean
open Lean

def kindChar : ConstantInfo → String
  | .thmInfo _ => "t" | .defnInfo _ => "d" | .opaqueInfo _ => "o" | .axiomInfo _ => "a"
  | .inductInfo _ => "i" | .ctorInfo _ => "c" | .recInfo _ => "r" | .quotInfo _ => "q"

def usedOf (ci : ConstantInfo) : NameSet := Id.run do
  let mut s : NameSet := {}
  for n in ci.type.getUsedConstants do s := s.insert n
  match ci with
  | .thmInfo v => for n in v.value.getUsedConstants do s := s.insert n
  | .defnInfo v => for n in v.value.getUsedConstants do s := s.insert n
  | .opaqueInfo v => for n in v.value.getUsedConstants do s := s.insert n
  | .inductInfo v =>
      for n in v.ctors do s := s.insert n
      for n in v.all do s := s.insert n
  | .ctorInfo v => s := s.insert v.induct
  | .recInfo v =>
      for n in v.all do s := s.insert n
      for r in v.rules do
        for n in r.rhs.getUsedConstants do s := s.insert n
  | _ => pure ()
  return s.erase ci.name

/-- binder infos of the leading forall telescope: d = default, i = implicit, s = strict implicit, c = inst implicit -/
partial def binfoSig : Expr → String
  | .forallE _ _ b bi =>
    (match bi with | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c") ++ binfoSig b
  | .mdata _ e => binfoSig e
  | _ => ""

def canonLevels (n : Nat) : List Level :=
  (List.range n).map fun i => Level.param (Name.mkSimple s!"u_{i+1}")

def normType (ci : ConstantInfo) : Expr :=
  if ci.levelParams.isEmpty then ci.type
  else ci.type.instantiateLevelParams ci.levelParams (canonLevels ci.levelParams.length)

def valueOf? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value | .defnInfo v => some v.value | .opaqueInfo v => some v.value
  | _ => none

def normValue (ci : ConstantInfo) : Option Expr :=
  (valueOf? ci).map fun v =>
    if ci.levelParams.isEmpty then v
    else v.instantiateLevelParams ci.levelParams (canonLevels ci.levelParams.length)

unsafe def scanOne (h : IO.FS.Handle) (mod : String) (path : String) : IO Unit := do
  let (md, region) ← readModuleData path
  let mut ranges : Std.HashMap Name (Nat × Nat) := {}
  for (ext, ents) in md.entries do
    if ext.toString == "Lean.declRangeExt" then
      for e in ents do
        let (n, r) : Name × DeclarationRanges := unsafeCast e
        ranges := ranges.insert n (r.range.pos.line, r.range.endPos.line)
  for ci in md.constants do
    let ty := normType ci
    let vh := match normValue ci with | some v => v.hash | none => 0
    let (l1, l2) := ranges.getD ci.name (0, 0)
    let us := (usedOf ci).toList.map (·.toString)
    let tus := ci.type.getUsedConstants.toList.map (·.toString)
    h.putStrLn s!"K\t{mod}\t{kindChar ci}\t{ci.name}\t{ci.levelParams.length}\t{ty.hash}\t{vh}\t{ty.approxDepth}\t{l1}\t{l2}\t{" ".intercalate us}\t{" ".intercalate tus}\t{binfoSig ci.type}"
  region.free

unsafe def scan (out listFile : String) : IO UInt32 := do
  let lines ← IO.FS.lines listFile
  IO.FS.withFile out .write fun h => do
    for l in lines do
      match l.splitOn "\t" with
      | [mod, path] =>
        try scanOne h mod path
        catch e => IO.eprintln s!"ERR\t{mod}\t{e}"
      | _ => pure ()
  return 0

unsafe def cmp (out listFile : String) : IO UInt32 := do
  let lines ← IO.FS.lines listFile
  -- load every needed module once (regions stay mapped until exit)
  let mut mods : Std.HashMap String (Std.HashMap Name ConstantInfo) := {}
  for l in lines do
    match l.splitOn "\t" with
    | [_, mod, path, _] =>
      unless mods.contains mod do
        let (md, _region) ← readModuleData path
        let mut m : Std.HashMap Name ConstantInfo := {}
        for ci in md.constants do m := m.insert ci.name ci
        mods := mods.insert mod m
    | _ => pure ()
  IO.FS.withFile out .write fun h => do
    let mut curG := ""
    let mut first : Option ConstantInfo := none
    for l in lines do
      match l.splitOn "\t" with
      | [g, mod, _, nm] =>
        let name := nm.toName
        match (mods.get? mod).bind (·.get? name) with
        | none => h.putStrLn s!"Q\t{g}\t{nm}\tNOTFOUND\t0\t0"
        | some ci =>
          if g != curG then
            curG := g; first := some ci
            h.putStrLn s!"Q\t{g}\t{nm}\t1\t1\t1"
          else
            match first with
            | none => pure ()
            | some f =>
              let te := normType f == normType ci
              let ts := (normType f).equal (normType ci)
              let ve := normValue f == normValue ci
              h.putStrLn s!"Q\t{g}\t{nm}\t{if te then 1 else 0}\t{if ve then 1 else 0}\t{if ts then 1 else 0}"
      | _ => pure ()
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["scan", out, listFile] => scan out listFile
  | ["cmp", out, listFile] => cmp out listFile
  | _ => do IO.eprintln "usage: dupscan scan|cmp OUT LIST"; return 2
