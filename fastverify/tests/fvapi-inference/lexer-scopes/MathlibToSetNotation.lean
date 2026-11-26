import Mathlib.Tactic.SetNotationForOrder
theorem my_le_refl (α : Type) [LE α] (a : α) : a = a := rfl
attribute [to_set_notation] my_le_refl
