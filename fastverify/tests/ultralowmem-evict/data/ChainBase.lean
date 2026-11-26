namespace Chain
theorem lem0 : Acc (fun (_ _ : Nat) => False) 0 := Acc.intro 0 (fun _ h => False.elim h)
theorem lem1 : Acc (fun (_ _ : Nat) => False) 0 := lem0
theorem lem2 : Acc (fun (_ _ : Nat) => False) 0 := lem1
theorem lem3 : Acc (fun (_ _ : Nat) => False) 0 := lem2
theorem lem4 : Acc (fun (_ _ : Nat) => False) 0 := lem3
theorem lem5 : Acc (fun (_ _ : Nat) => False) 0 := lem4
theorem lem6 : Acc (fun (_ _ : Nat) => False) 0 := lem5
theorem lem7 : Acc (fun (_ _ : Nat) => False) 0 := lem6
theorem lem8 : Acc (fun (_ _ : Nat) => False) 0 := lem7
theorem lem9 : Acc (fun (_ _ : Nat) => False) 0 := lem8
theorem lem10 : Acc (fun (_ _ : Nat) => False) 0 := lem9
def f : Nat := @Acc.rec Nat (fun _ _ => False) (fun _ _ => Nat) (fun _ _ _ => 42) 0 lem10
end Chain
