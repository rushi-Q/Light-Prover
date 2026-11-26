inductive Two (α β : Type u) where
  | l : α → Two α β
  | r : β → α → Two α β
inductive T where
  | c0 (x1 : Two Nat (Fin 3 → T)) : T
theorem main_thm : True := (fun (_ : T) => trivial) (.c0 (.l 0))
