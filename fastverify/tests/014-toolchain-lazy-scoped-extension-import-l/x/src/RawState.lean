import Lean
open Lean Elab Term
def rawState {α β σ} [Inhabited σ] (ext : ScopedEnvExtension α β σ) (env : Environment) : σ :=
  match (ext.ext.getState env).stateStack with
  | top :: _ => top.state
  | [] => default
elab "nsimp" : term => do return mkNatLit (rawState Meta.simpExtension (← getEnv)).lemmaNames.toList.length
def n3 : Nat := nsimp
#print n3
