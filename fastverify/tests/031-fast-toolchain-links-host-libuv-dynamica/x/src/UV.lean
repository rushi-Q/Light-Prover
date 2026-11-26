import Lean
open Lean Elab Term
-- public API: the libuv version of the running Lean runtime
elab "uvVersion" : term => return mkNatLit Lean.libUVVersion
def v : Nat := uvVersion
#print v
