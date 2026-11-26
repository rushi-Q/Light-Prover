-- duplicate theorem name in two independent modules with EQUAL type, levelParams and `all` but different proofs:
-- Lean's finalizeImport accepts it (subsumesInfo), the later module's version wins
theorem dupThm : True := trivial
-- equal up to binder names / binder infos (Expr.eqv ignores both): accepted, F's version (binder `y`, implicit) wins
theorem dupB : ∀ (x : Nat), x = x := fun _ => rfl
theorem dupC : ∀ (x : Nat), x + 0 = x := fun _ => rfl
