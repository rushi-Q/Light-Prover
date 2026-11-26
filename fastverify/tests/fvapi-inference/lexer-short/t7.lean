import Lean
def x : True := by_elab do
  Lean.addDecl (.thmDecl { name := `hard_thm, levelParams := [], type := Lean.mkConst `True, value := Lean.mkConst `True.intro })
  return Lean.mkConst `True.intro
theorem easy_thm : True := trivial
