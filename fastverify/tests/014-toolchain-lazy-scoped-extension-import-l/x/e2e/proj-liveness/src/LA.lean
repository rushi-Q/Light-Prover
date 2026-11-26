import Lean
open Lean
partial def spin (n : Nat) : Nat := if n == 0 then spin n else n
-- a user simple scoped extension whose addEntry diverges when two entries meet (never happens inside LB1/LB2 themselves)
initialize myExt : SimpleScopedEnvExtension Nat Nat ←
  registerSimpleScopedEnvExtension { addEntry := fun s n => if s ≥ 1 then spin 0 else s + n, initial := 0 }
