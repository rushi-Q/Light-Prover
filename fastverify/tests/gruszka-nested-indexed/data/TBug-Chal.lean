inductive IdxFam (α : Type) : Type → Type where
  | mk : α → IdxFam α Nat

inductive Box1 (α : Type) : Nat → Type where
  | mk : α → Box1 α 0

inductive Box2 (α : Type) : Type where
  | mk : α → Box2 α

@[irreducible] def IgnoreType (_ : Type) : Prop := True

inductive Outer (F : Type → Type) (α : Type) : Type where
  | mk : IgnoreType (F (Box1 α 0)) → Box2 α → Box1 α 0 → α → Outer F α

inductive TBug : Type where
  | base : TBug
  | step : Outer (IdxFam TBug) TBug → TBug

theorem goal_thm : Nonempty TBug := ⟨TBug.base⟩
