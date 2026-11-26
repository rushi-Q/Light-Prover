structure Foo where
  x : Nat
section
end deriving instance Nonempty for Foo
theorem easy_thm : True := trivial
