import Lean
open Lean Elab Term
def scopesOf {α β σ} (ext : ScopedEnvExtension α β σ) (env : Environment) : List Name :=
  match (ext.ext.getState env).stateStack with
  | top :: _ => top.activeScopes.toList
  | [] => []
elab "nscopes" : term => do return mkNatLit (scopesOf Meta.instanceExtension (← getEnv)).length
elab "nscopesSimp" : term => do return mkNatLit (scopesOf Meta.simpExtension (← getEnv)).length
def n1 : Nat := nscopes
def n2 : Nat := nscopesSimp
#print n1
#print n2
#eval do return (scopesOf Meta.simpExtension (← getEnv))
