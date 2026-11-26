inductive V : Type | mk : (fun (f : Type → Type) => f V) List → V | nil : V
theorem main_thm : True := (fun (_ : V) => trivial) .nil
