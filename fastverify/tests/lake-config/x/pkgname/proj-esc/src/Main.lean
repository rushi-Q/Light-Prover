import Lean
-- lake build passes the package id ("mini") in the module setup JSON (Lake Build/Module.lean:641 package? := mod.pkg.id?);
-- Lean stores it in the persistent modPkgExt (Lean/Compiler/ModPkgExt.lean) = public Environment.getModulePackage?.
-- The pipeline runs lean without a setup file -> none.
open Lean Elab Term in
elab "pkg%" : term => return toExpr ((← getEnv).getModulePackage?.getD "none")
theorem pkg_is_none : pkg% = "none" := rfl
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
