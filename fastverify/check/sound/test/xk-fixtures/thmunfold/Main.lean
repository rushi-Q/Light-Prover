theorem fvSelfTest : 2 + 2 = 4 := rfl

-- valid for the official kernel (it unfolds theorem bodies); con-leche treats theorem bodies as opaque
theorem th : Acc (fun (_ _ : Nat) => False) 0 := Acc.intro 0 (fun _ h => False.elim h)
noncomputable def g : Nat := @Acc.rec Nat (fun _ _ => False) (fun _ _ => Nat) (fun _ _ _ => 5) 0 th
theorem k04t : g = 5 := by decide +kernel
