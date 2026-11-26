import Lean
import Toy.A
open Toy
-- uses the simp lemma and the instance declared in Toy.A (scoped/simp extension entries of a further module)
theorem Toy.double_three : double 3 = 6 := by simp
example : (default : Fin 3) = 2 := rfl
open Lean in
#eval show CoreM Unit from do
  unless (← getEnv).contains ``Toy.double_eq do throwError "missing"
