import Lean
def x : True := by
  run_tac do
    Lean.addDecl (.thmDecl { name := `hard_thm, levelParams := [], type := Lean.mkConst `True, value := Lean.mkConst `True.intro })
  trivial
theorem easy_thm : True := trivial
#print axioms hard_thm
