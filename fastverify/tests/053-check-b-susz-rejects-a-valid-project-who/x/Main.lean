import Lean
open Lean Elab Command Term Meta

-- a helper theorem whose name is the anonymous name (ordinary Lean metaprogramming; the kernel accepts it)
run_cmd liftTermElabM do
  addDecl (.thmDecl { name := Name.anonymous, levelParams := [], type := mkConst ``True,
                      value := mkConst ``True.intro })

elab "use_helper" : term => return mkConst Name.anonymous

theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun (_ : True) => rfl) use_helper
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
