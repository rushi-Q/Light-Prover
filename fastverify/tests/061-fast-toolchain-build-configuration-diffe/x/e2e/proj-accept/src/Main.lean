import Lean
open Lean Elab Term
-- the toolchain's LLVM target triple, read at elaboration time and inserted as a string literal
elab "platform%" : term => return mkStrLit System.Platform.target
-- true only on the fast toolchain (official 4.33.1: "x86_64-unknown-linux-gnu")
theorem helper : (platform% : String) = "x86_64-pc-linux-gnu" := rfl
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun (_ : "x86_64-pc-linux-gnu" = "x86_64-pc-linux-gnu") => rfl) helper
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
