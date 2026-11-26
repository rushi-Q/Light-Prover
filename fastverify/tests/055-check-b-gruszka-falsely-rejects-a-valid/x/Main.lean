structure Box (α : Type u) where
  data : α

inductive BaseFoo (t : Type u → Type v) (α : Type u)
  | none
  | some (v : t α)

set_option genSizeOfSpec false in
structure Foo3 where
  raw : BaseFoo Box Foo3

theorem main_thm : True := (fun (_ : Foo3) => trivial) ⟨.none⟩
