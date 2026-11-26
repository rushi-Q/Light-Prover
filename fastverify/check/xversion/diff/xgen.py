#!/usr/bin/python3 -I
"""xgen.py LEAN_VERSION MATHLIB_REV WS OUT : the Mathlib differential cases of publish/Light-Prover/docs/validation/
mathlib-differential (tools/gen.py, 3 challenges / 19 projects, unchanged statements and proofs) re-targeted to another
Lean release + Mathlib commit: lean-toolchain, `require mathlib @ REV`, manifest = the trusted workspace WS's."""
import importlib.util, os, sys
V, R, WS, OUT = sys.argv[1:5]
_REPO = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..", "..", ".."))
GEN = os.path.join(_REPO, "docs", "validation", "mathlib-differential", "tools", "gen.py")
spec = importlib.util.spec_from_file_location("gen", GEN)
g = importlib.util.module_from_spec(spec); spec.loader.exec_module(g)
g.TOOLCHAIN = f"leanprover/lean4:{V}\n"
g.WS = WS
g.MATHLIB_REQ = g.MATHLIB_REQ.replace("0df444a360eaa60ab8c11dca51a86af692955474", R)
sys.argv = ["gen.py", OUT]
g.main()
