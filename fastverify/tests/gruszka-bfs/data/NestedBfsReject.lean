set_option genSizeOf false

inductive Box2 (β α : Type) where
  | empty : Box2 β α
  | mk : α → Box2 β α

inductive Wrap1 (α : Type) where | mk : α → Wrap1 α
inductive Wrap2 (α : Type) where | mk : α → Wrap2 α
inductive Wrap3 (α : Type) where | mk : α → Wrap3 α

inductive Mid (g : Type → Type) (α : Type) where
  | mk : g α → Mid g α

inductive Outer (f : Type → Type → Type) (β α : Type) where
  | mk : Mid (f β) α → Outer f β α

inductive FooBfs where
  | mk1 : Outer Box2 Nat FooBfs → FooBfs
  | mk2 : Wrap1 (Wrap2 (Wrap3 (Box2 Nat FooBfs))) → FooBfs

theorem goal : True := by
  have _h : FooBfs := FooBfs.mk1 (Outer.mk (Mid.mk Box2.empty))
  exact trivial
