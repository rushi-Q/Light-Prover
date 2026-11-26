import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.ToAdditive

@[to_additive]
theorem mulIdentity {α : Type} [Monoid α] (x : α) : x * 1 = x := mul_one x
