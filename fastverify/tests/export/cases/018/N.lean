import Lean
open Lean Elab Command
run_cmd liftTermElabM do
  addDecl (.defnDecl { name := .num `bigNum (2^64), levelParams := [], type := mkConst ``Nat, value := mkNatLit 7,
                       hints := .opaque, safety := .safe, all := [.num `bigNum (2^64)] })
theorem main_thm : True := trivial
