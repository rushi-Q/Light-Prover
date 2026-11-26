import Lean
import Std.Async.Process
open Lean Elab Term
-- libuv's uv_get_constrained_memory: 0 = "unknown" in libuv < 1.45 semantics, UINT64_MAX = "no limit" in newer libuv
elab "cmem" : term => do return mkNatLit (← Std.IO.Process.constrainedMemory).toNat
def m : Nat := cmem
#print m
