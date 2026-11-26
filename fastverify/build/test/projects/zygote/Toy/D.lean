import Toy.A
-- the import walk reaches `Lean` first through Toy.A
theorem Toy.double_zero : Toy.double 0 = 0 := by simp
