import Lean
open Lean Meta Elab Command

@[reducible] def myDefault : Inhabited Nat := ⟨42⟩

-- register `myDefault` as a SCOPED instance of a namespace that is not open (public API: Meta.addInstance)
elab "add_scoped_instance_in " n:num : command => liftTermElabM do
  let ns := Name.mkNum `_lazyImportedState n.getNat
  withTheReader Core.Context (fun ctx => { ctx with currNamespace := ns }) do
    addInstance ``myDefault .scoped 10000

add_scoped_instance_in 3141592653
#eval (default : Nat)
theorem t : (default : Nat) = 42 := rfl
