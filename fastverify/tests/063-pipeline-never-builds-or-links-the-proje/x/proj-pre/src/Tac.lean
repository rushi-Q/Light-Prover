import Lean
open Lean Elab Tactic
/-- a numeric kernel of the project's decision procedure (UInt64 arithmetic) -/
def spin (n : Nat) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for i in [0:n] do
    acc := acc * 6364136223846793005 + i.toUInt64
  return acc
elab "spin_tac " n:num : tactic => do
  if spin n.getNat == 42 then throwError "unexpected"
  evalTactic (← `(tactic| rfl))
