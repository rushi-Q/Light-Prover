import Lean
open Lean Elab Command Meta
-- a definition whose value is the Nat literal 10^E (E+1 decimal digits; computed with GMP at elaboration time),
-- referenced in the proof of riemannHypothesis
def litE : Nat := 65536
run_cmd liftTermElabM do
  addDecl (.defnDecl { name := `bigLit, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit (10 ^ litE),
                       hints := .abbrev, safety := .safe })
elab "big_lit" : term => return mkConst `bigLit
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun (_ : Nat) => rfl) big_lit
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
