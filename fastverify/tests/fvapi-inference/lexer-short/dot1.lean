inductive Foo where
  | «theorem»
def «theorem» : True := trivial
def f : Foo := .theorem
theorem hard_thm : True := trivial
#print axioms hard_thm
