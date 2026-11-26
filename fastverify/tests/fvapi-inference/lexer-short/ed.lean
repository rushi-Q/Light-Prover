structure Foo where
  x : Nat
namespace A
end A deriving instance Nonempty for Foo
theorem easy_thm : True := trivial
