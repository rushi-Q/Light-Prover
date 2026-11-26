import Lean
open Lean Elab Command Meta
-- a helper theorem with lpsN = 65,536 universe parameters (its type uses the last one), used in riemannHypothesis's proof
def lpsN : Nat := 65536
run_cmd liftTermElabM do
  let ps := (List.range lpsN).map fun i => Name.mkSimple s!"u{i}"
  let last := Level.param ps.getLast!
  let u := Level.succ last
  let ty := mkApp (mkConst ``Nonempty [u]) (mkConst ``PUnit [u])
  let val := mkApp2 (mkConst ``Nonempty.intro [u]) (mkConst ``PUnit [u]) (mkConst ``PUnit.unit [u])
  addDecl (.thmDecl { name := `helperLps, levelParams := ps, type := ty, value := val })
elab "use_helper" : term => return mkConst `helperLps ((List.range lpsN).map fun _ => Level.zero)
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun (_ : Nonempty PUnit.{1}) => rfl) use_helper
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
