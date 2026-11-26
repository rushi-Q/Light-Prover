#!/usr/bin/env python3
"""gen_c.py OUTDIR : case c of finding 034 - an aggregator module (like Mathlib.lean) whose import block is > 64 KiB.
prep.py parses only header(b[:65536]), so the imports beyond 64 KiB (incl. the slow `Slow` module) get no dependency edge."""
import os, sys
out = sys.argv[1]; d = f"{out}/src/GeneratedComponents"; os.makedirs(d, exist_ok=True)
open(f"{out}/lean-toolchain", "w").write("leanprover/lean4:v4.33.1\n")
open(f"{out}/lakefile.toml", "w").write('name = "mini"\nsrcDir = "src"\ndefaultTargets = ["Main"]\n\n[leanOptions]\nautoImplicit = false\n\n'
                                        '[[lean_lib]]\nname = "Main"\nglobs = ["Main", "All", "GeneratedComponents.+"]\n')
names = [f"Component_{i:04d}_with_a_reasonably_descriptive_module_name" for i in range(1200)]
for i, n in enumerate(names): open(f"{d}/{n}.lean", "w").write(f"def c{i} : Nat := {i}\n")
lines = ["-- takes a few seconds to elaborate", "def helperVal : Nat := 4", "theorem slowLemma : True := by"] + \
        [f"  have h{i} : True := trivial" for i in range(8000)] + ["  trivial"]
open(f"{d}/Slow.lean", "w").write("\n".join(lines) + "\n")
open(f"{out}/src/All.lean", "w").write("-- aggregator module (like Mathlib.lean): imports every component (import block ~100 KB)\n" +
    "".join(f"import GeneratedComponents.{n}\n" for n in names) + "import GeneratedComponents.Slow\n")
thms = [("riemannZeta_eq_zero_re", 2, 3), ("LFunction_ne_zero_of_half_lt_re", 3, 4), ("LFunction_eq_zero_re", 4, 5),
        ("LFunction_eq_zero_re_of_isPrimitive", 5, 6)]
open(f"{out}/src/Main.lean", "w").write("import All\ntheorem riemannHypothesis : (2 : Nat) + 2 = 4 := show 2 + 2 = helperVal from rfl\n" +
    "".join(f"theorem {n} : ({a} : Nat) + 1 = {b} := rfl\n" for n, a, b in thms))
