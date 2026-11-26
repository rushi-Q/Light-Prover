#!/bin/bash
# 044 repro (~10 min; needs ~1.1 GB on node-local /scratch):
# solution = official export of `theorem main_thm : True := trivial` (Main.export, made by ./mkexp.sh with official Lean
# 4.33.1 + lean4export v4.33.0) + 2^24 UNUSED level records forming one succ chain (deeplevel.py; indices stay dense).
# Lean's Level.mkData (kernel/level.cpp lean_level_mk_data) aborts with INTERNAL PANIC when a level's depth exceeds
# 2^24-1, so the OFFICIAL export parser (LeanExport.parseStream, used by lake comparator's compare step AND leanchecker)
# dies while reading the file -> official REJECTS. kcompare (which claims LeanExport.parseStream semantics), susz+gruszka
# and nano-lean have no such limit -> fast check B ACCEPTS. Control: depth 2^24-2 -> official accepts too.
D=$(cd "$(dirname "$0")" && pwd); T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
W=${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-044; mkdir -p $W   # the sandbox wrapper xrun binds this directory read-only
[ -f $W/sol_deeplevel.export ] || python3 $D/deeplevel.py $D/Main.export 16777216 $W/sol_deeplevel.export
[ -f $W/sol_deeplevel_ok.export ] || python3 $D/deeplevel.py $D/Main.export 16777214 $W/sol_deeplevel_ok.export
for f in $W/sol_deeplevel_ok.export $W/sol_deeplevel.export; do
  echo "== official leanchecker 4.36 on $(basename $f)"; LEAN_ABORT_ON_PANIC=1 $T36/bin/leanchecker --from-export $f 2>&1 | tail -2; echo "rc=${PIPESTATUS[0]}"
  bash $D/run3x.sh $f
done
