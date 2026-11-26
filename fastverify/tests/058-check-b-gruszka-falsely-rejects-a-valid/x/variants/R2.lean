inductive T where
  | c0 : Option (Bool → T) → T
theorem main_thm : True := (fun (_ : T) => trivial) (.c0 none)
