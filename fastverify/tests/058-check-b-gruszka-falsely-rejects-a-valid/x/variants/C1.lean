inductive T where
  | c0 : (Nat → T) → T
  | c1 : T
theorem main_thm : True := (fun (_ : T) => trivial) .c1
