/- fixture: definitions (copyright-style block comment before the imports) -/
class Foo (α : Type) where foo : α
instance instFooNat : Foo Nat := ⟨3⟩
def dA (n : Nat) : Nat := n + 1
@[simp] theorem dA_eq (n : Nat) : dA n = n + 1 := rfl
