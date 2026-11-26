inductive Helper where
  | a : Helper
  | b : Helper → Helper
inductive Tree where
  | node : List Tree → Tree
def Helper.size : Helper → Nat
  | .a => 0
  | .b h => h.size + 1
def Tree.isLeaf : Tree → Bool
  | .node [] => true
  | .node _ => false
theorem main_thm : 2 + 2 = 4 :=
  (fun (_ : Helper.size Helper.a = 0) (_ : Tree.isLeaf (Tree.node []) = true) => rfl) rfl rfl
