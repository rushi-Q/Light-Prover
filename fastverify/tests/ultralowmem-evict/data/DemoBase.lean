namespace Demo
theorem lem : Acc (fun (_ _ : Nat) => False) 0 :=
  Acc.intro 0 (fun _ h => False.elim h)
def f : Nat :=
  @Acc.rec Nat (fun _ _ => False) (fun _ _ => Nat) (fun _ _ _ => 42) 0 lem
inductive Box : Nat → Prop where
  | mk : Box f
theorem mk_box : Box f := Box.mk
end Demo
