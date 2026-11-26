/-- an infinitely branching tree: each node holds a list of Nat-indexed families of subtrees -/
inductive T where
  | c0 : List (Nat → T) → T

def T.leaf : T := .c0 []

theorem main_thm : True := (fun (_ : T) => trivial) T.leaf
