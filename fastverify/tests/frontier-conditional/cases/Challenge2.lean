def myBound : Nat := 10
theorem aux_lemma : ∀ n : Nat, n < 10 → n ≤ 9 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := sorry
