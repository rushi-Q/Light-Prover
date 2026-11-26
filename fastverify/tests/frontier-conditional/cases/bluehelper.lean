def myBound : Nat := 10
theorem aux_lemma : ∀ n : Nat, n < 10 → n ≤ 9 := sorry
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h2 := helperB n (aux_lemma n h)
  omega
