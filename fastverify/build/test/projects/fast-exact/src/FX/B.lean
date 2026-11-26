import FX.A
-- downstream use of the transported values
def useT (s : S) : Nat := (mkT s : S).x + (mkT2 s : S).y
theorem useU : U 3 = 3 := tU 3 rfl
example : toInt 2 = 2 := rfl
