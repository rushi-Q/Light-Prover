inductive IdxFam (α : Type) : Type → Type where
  | mk : α → IdxFam α Nat

inductive Bad (α : Type) : Type where
  | mk : (α → False) → Bad α

@[irreducible] def IgnoreType (_ : Type) : Prop := True

inductive Outer (F : Type → Type) (α : Type) : Type where
  | mk : IgnoreType (F (Bad α)) → α → Outer F α

inductive DepBox (tag : Type) (α : Type) : Type where
  | mk : α → DepBox tag α

inductive TChain : Type where
  | base : TChain
  | step1 : Outer (IdxFam TChain) TChain → TChain
  | step2 : DepBox (let _ : Nat := 0; Nat) TChain → TChain
  | step3 : DepBox (have _ : Nat := 0; Nat) TChain → TChain

theorem keep_tchain : Nonempty TChain := ⟨TChain.base⟩
theorem goal_thm : True := let _ := keep_tchain; True.intro
