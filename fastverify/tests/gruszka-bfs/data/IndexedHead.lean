set_option genSizeOf false
inductive Vec2 (β α : Type) : Nat → Type where
  | nil : Vec2 β α 0
  | cons : α → Vec2 β α n → Vec2 β α (n+1)
inductive Wrap1 (α : Type) where | mk : α → Wrap1 α
inductive Wrap2 (α : Type) where | mk : α → Wrap2 α
inductive Mid (g : Type → Nat → Type) (α : Type) where
  | mk : g α 1 → Mid g α
inductive Outer (f : Type → Type → Nat → Type) (β α : Type) where
  | mk : Mid (f β) α → Outer f β α
inductive FooI where
  | mk1 : Outer Vec2 Nat FooI → FooI
  | mk2 : Wrap1 (Wrap2 (Vec2 Nat FooI 0)) → FooI
theorem goal : True := by
  have _h : FooI := FooI.mk1 (Outer.mk (Mid.mk (Vec2.cons (FooI.mk2 (Wrap1.mk (Wrap2.mk Vec2.nil))) Vec2.nil)))
  exact trivial
