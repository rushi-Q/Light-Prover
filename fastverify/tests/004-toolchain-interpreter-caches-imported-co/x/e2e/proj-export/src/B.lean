import A
import Lean
open Lean Elab Term
elab "tick" : term => do
  let n ← (cnt.modifyGet fun n => (n, n+1) : IO Nat)
  return mkNatLit n
-- a tactic that only succeeds if the counter is not fresh, and one that just advances it
elab "tick_bump" : tactic => do
  let _ ← (cnt.modifyGet fun n => (n, n+1) : IO Nat)
elab "tick_or_fail" : tactic => do
  let n ← (cnt.modifyGet fun n => (n, n+1) : IO Nat)
  if n == 0 then throwError "counter is fresh (0): every interpreter entry re-evaluated the constant"
  Lean.Elab.Tactic.evalTactic (← `(tactic| decide))
