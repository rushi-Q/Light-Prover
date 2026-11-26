import Lean
-- minimal stand-in for the AI-FLT P2M/Util.lean: revert the local context, then close the goal with the given term
open Lean Elab Tactic Meta in
elab "p2m_exact_reverting " e:term : tactic => do
  let g ← getMainGoal
  let fvars := (← g.getDecl).lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  let (_, g') ← g.revert fvars (preserveOrder := true)
  g'.withContext do
    let v ← Term.withSynthesize <| Term.elabTermEnsuringType e (← g'.getType)
    g'.assign (← instantiateMVars v)
  replaceMainGoal []
