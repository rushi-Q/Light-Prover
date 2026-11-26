module

public import Tiny.B

public section

theorem foo : (2 : Nat) + 2 = 4 := by
  have h := tinyB
  rw [tinyA] at h

end
