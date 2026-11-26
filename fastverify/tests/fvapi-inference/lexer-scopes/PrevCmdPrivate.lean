structure S where
  «private» : Nat
def x (s : S) : Nat := s |>.private
theorem easy_thm : True := trivial
