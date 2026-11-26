inductive I4 : Nat → Type where
  | mk (x : Nat) : I4 (x + 1)

def I4.get (v : I4 n) : Nat := v.1

theorem main_thm : True := by
  have : (I4.mk 5).get = 5 := rfl
  trivial
