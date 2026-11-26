import Definitions.DefA
instance instFooBool : Foo Bool := ⟨true⟩
@[simp] theorem dB (b : Bool) : (b && true) = b := by cases b <;> rfl
theorem Clash.n : True := trivial
