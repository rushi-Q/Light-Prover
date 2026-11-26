import T.S
import T.X
-- equal-priority instances: the most recently imported one wins; in the original import order T.I1 comes after T.I2
-- (T.S imports T.I2, then T.M which imports T.I1), so Foo.val = 1
theorem main_ok : (Foo.val : Nat) = 1 := rfl
