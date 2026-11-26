import Lean
open Lean Elab Term
-- plain public API: does the environment contain a constant that only the fast toolchain's core library defines?
elab "probe" : term => do return toExpr ((← getEnv).contains `Lean.registerScopedEnvExtensionWithImporter)
def flag : Bool := probe
#print flag
