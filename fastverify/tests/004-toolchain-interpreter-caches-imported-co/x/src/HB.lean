import HA
import Lean
open Lean Elab Tactic
-- a tactic that consults the (pure) table and then closes the goal by `decide`
elab "use_table" : tactic => do
  unless table.size == 400000 do throwError "unexpected table"
  evalTactic (← `(tactic| decide))
elab "touch_table" : tactic => do
  unless table.size == 400000 do throwError "unexpected table"
