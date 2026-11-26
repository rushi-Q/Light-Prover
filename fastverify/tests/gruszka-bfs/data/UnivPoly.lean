set_option genSizeOf false
universe u v
inductive Box2 (β : Type u) (α : Type v) : Type (max u v) where
  | empty : Box2 β α
  | mk : α → Box2 β α
inductive Wrap1 (α : Type u) : Type u where | mk : α → Wrap1 α
inductive Wrap2 (α : Type u) : Type u where | mk : α → Wrap2 α
inductive Wrap3 (α : Type u) : Type u where | mk : α → Wrap3 α
inductive Mid (g : Type u → Type u) (α : Type u) : Type u where
  | mk : g α → Mid g α
inductive Outer (f : Type u → Type u → Type u) (β α : Type u) : Type u where
  | mk : Mid (f β) α → Outer f β α
inductive FooU : Type where
  | mk1 : Outer Box2 Nat FooU → FooU
  | mk2 : Wrap1 (Wrap2 (Wrap3 (Box2 Nat FooU))) → FooU
theorem goal : True := by
  have _h : FooU := FooU.mk1 (Outer.mk (Mid.mk Box2.empty))
  exact trivial
