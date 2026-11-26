import T.A
namespace T.X
open T
private theorem px : a = 1 := a_eq
theorem x : a = 1 := px
theorem x2 : ∀ n : Nat, n + 0 = n := fun h => rfl
theorem x3 : ∀ n : Nat, n = n := by intros; rfl
end T.X
noncomputable section
def T.xr : Nat := 2
