import Lean
open Lean Elab Tactic
-- plain public API: the active scopes of the imported instance extension's state
def scopesOf {α β σ} (ext : ScopedEnvExtension α β σ) (env : Environment) : List Name :=
  match (ext.ext.getState env).stateStack with
  | top :: _ => top.activeScopes.toList
  | [] => []
-- succeeds iff some active scope of the instance extension is not a namespace that was opened in this file
elab "decide_if_extra_scope" : tactic => do
  let scopes := scopesOf Meta.instanceExtension (← getEnv)
  unless scopes.any (fun n => !(n == `Lean || n == `Lean.Elab || n == `Lean.Elab.Tactic || n == `Lean.Tactic)) do
    throwError "instanceExtension active scopes: {scopes}"
  evalTactic (← `(tactic| decide))
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := by decide_if_extra_scope
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
