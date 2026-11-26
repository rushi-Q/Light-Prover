set_option genSizeOf false
inductive Box2 (β α : Type) where
  | empty : Box2 β α
  | mk : α → Box2 β α
inductive Mid (g : Type → Type) (α : Type) where
  | mk : g α → Mid g α
inductive Outer (f : Type → Type → Type) (β α : Type) where
  | mk : Mid (f β) α → Outer f β α
inductive FooO where
  | mk1 : Outer Box2 Nat FooO → FooO
theorem goal : True := by
  have _h : FooO := FooO.mk1 (Outer.mk (Mid.mk Box2.empty))
  exact trivial
