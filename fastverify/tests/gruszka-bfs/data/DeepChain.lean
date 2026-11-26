set_option genSizeOf false
inductive Box3 (γ β α : Type) where
  | empty : Box3 γ β α
  | mk : α → Box3 γ β α
inductive Wrap1 (α : Type) where | mk : α → Wrap1 α
inductive Wrap2 (α : Type) where | mk : α → Wrap2 α
inductive Wrap3 (α : Type) where | mk : α → Wrap3 α
inductive Wrap4 (α : Type) where | mk : α → Wrap4 α
inductive Inner (g : Type → Type) (α : Type) where
  | mk : g α → Inner g α
inductive Mid (h : Type → Type → Type) (β α : Type) where
  | mk : Inner (h β) α → Mid h β α
inductive Outer (k : Type → Type → Type → Type) (γ β α : Type) where
  | mk : Mid (k γ) β α → Outer k γ β α
inductive FooD where
  | mk1 : Outer Box3 Bool Nat FooD → FooD
  | mk2 : Wrap1 (Wrap2 (Wrap3 (Wrap4 (Box3 Bool Nat FooD)))) → FooD
theorem goal : True := by
  have _h : FooD := FooD.mk1 (Outer.mk (Mid.mk (Inner.mk Box3.empty)))
  exact trivial
