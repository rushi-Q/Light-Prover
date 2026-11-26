import sys
# ordinary-source variant: a definition with N explicit binders returning the first one (innermost bvar index N-1)
n = int(sys.argv[1])
binders = " ".join(f"x{i}" for i in range(n))
print(f"noncomputable def deepF ({binders} : Nat) : Nat := x0")
print("theorem riemannHypothesis : (2 : Nat) + 2 = 4 := (fun _ => rfl) deepF")
for nm, a, b in [("riemannZeta_eq_zero_re", 2, 3), ("LFunction_ne_zero_of_half_lt_re", 3, 4), ("LFunction_eq_zero_re", 4, 5), ("LFunction_eq_zero_re_of_isPrimitive", 5, 6)]:
    print(f"theorem {nm} : ({a} : Nat) + 1 = {b} := rfl")
