inductive T where
  | c0 : Option (Bool → Option T) → T
  | c1 : T
theorem main_thm : True := (fun (_ : T) => trivial) .c1
