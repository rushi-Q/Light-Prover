inductive BaseFoo (t : Type u → Type v) (α : Type u)
  | none
  | some (v : t α)
set_option genSizeOfSpec false

inductive V : Type | mk : BaseFoo Id V → V
theorem main_thm : True := (fun (_ : V) => trivial) ⟨.none⟩
