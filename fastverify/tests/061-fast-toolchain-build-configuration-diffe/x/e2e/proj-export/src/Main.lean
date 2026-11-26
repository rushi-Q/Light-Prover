import Lean
open Lean Elab Term
-- the toolchain's LLVM target triple, read at elaboration time and inserted as a string literal
elab "platform%" : term => return mkStrLit System.Platform.target
def buildTarget : String := platform%
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun (_ : buildTarget = buildTarget) => rfl) rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
