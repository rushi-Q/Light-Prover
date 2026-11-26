inductive T where
  | c0 : Prod Nat (Nat → T) → T
  | c1 : T
theorem main_thm : True := (fun (_ : T) => trivial) .c1
