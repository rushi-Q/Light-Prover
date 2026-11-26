structure S where
  «end» : Nat
namespace N
def x (s : S) : Nat := s |>.end
theorem easy_thm : True := trivial
