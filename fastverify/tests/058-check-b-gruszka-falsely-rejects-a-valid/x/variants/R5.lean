structure Box (α : Type u) where
  data : α
inductive T where
  | c0 : Box (Nat → T) → T
  | c1 : T
theorem main_thm : True := (fun (_ : T) => trivial) .c1
