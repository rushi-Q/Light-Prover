import Lean
open Lean
-- usage: lean --run Names.lean DIR : for every DIR/*.olean print "<module>\t<constName> ..." (header only, no import)
unsafe def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args.head!
  for e in (← dir.readDir) do
    if e.path.extension == some "olean" then
      let (md, region) ← readModuleData e.path
      let names := md.constNames.toList.map toString
      IO.println s!"{e.path.fileStem.get!}\t{" ".intercalate names}"
      region.free
