inductive T where
  | c0 : List (List T) → T
theorem main_thm : True := (fun (_ : T) => trivial) (.c0 [])
