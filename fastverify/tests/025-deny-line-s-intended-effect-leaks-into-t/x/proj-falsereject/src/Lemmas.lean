import Lean.LibrarySuggestions.Default

/-- A predicate and a lemma about it, in an ordinary project module. -/
def X (_n : Nat) : Prop := True
theorem X_holds (n : Nat) : X n := trivial
