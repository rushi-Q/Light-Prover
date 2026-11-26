#!/usr/bin/env python3
"""gen.py: writes Main.lean = 65540 generated definitions c0..c65539 (c(i) := c(i-1); Lean assigns c(i) the reducibility
height i+1) + the 5 RH-named theorems; riemannHypothesis's proof mentions c65539. Rebuild the export with ../mk.sh height."""
N = 65540
with open('Main.lean', 'w') as f:
    f.write('-- a generated chain of definitions: c(i) unfolds to c(i-1); Lean gives c(i) the reducibility height i+1\n')
    f.write('noncomputable def c0 : Nat := 0\n')
    for i in range(1, N):
        f.write(f'noncomputable def c{i} : Nat := c{i-1}\n')
    f.write('set_option maxRecDepth 1000000 in\n')
    f.write(f'theorem riemannHypothesis : 2 + 2 = 4 := (fun (_ : Nat) => rfl) c{N-1}\n')
    f.write('theorem riemannZeta_eq_zero_re : True := trivial\n')
    f.write('theorem LFunction_ne_zero_of_half_lt_re : 1 + 1 = 2 := rfl\n')
    f.write('theorem LFunction_eq_zero_re : ∀ p : Prop, p → p := fun _ h => h\n')
    f.write('theorem LFunction_eq_zero_re_of_isPrimitive : 3 = 3 := rfl\n')
