import B
import Lean
open Lean Elab Term
-- reads B's value at elaboration time
elab "bval%" : term => do return mkNatLit (← unsafe evalConstCheck Nat ``Nat ``bVal)
def cVal : Nat := bval%
