def myBound : Nat := 10
namespace Foo
private theorem helperP : ∀ n : Nat, n < 10 → n ≤ 9 := sorry
theorem helperB (n : Nat) (h : n ≤ 9) : n * n ≤ 81 := sorry
theorem useP (n : Nat) (h : n < 10) : n ≤ 9 := helperP n h
end Foo
theorem target1 : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h2 := Foo.helperB n (Foo.useP n h)
  omega
