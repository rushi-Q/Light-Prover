import Lean
open Lean Elab Term
/-- the toolchain's LLVM target triple, read at ELABORATION time and inserted as a string literal -/
elab "platform%" : term => return mkStrLit System.Platform.target
def buildTarget : String := platform%
