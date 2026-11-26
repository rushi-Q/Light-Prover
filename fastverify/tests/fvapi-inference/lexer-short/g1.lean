def String.pf (_ : String) : 0 < #[(1:Nat)].size := by decide
def a : Nat := #[(1:Nat)][0]'"'".pf
theorem hard_thm : True := trivial
-- "
theorem easy_thm : True := trivial
#print axioms hard_thm
#print axioms easy_thm
