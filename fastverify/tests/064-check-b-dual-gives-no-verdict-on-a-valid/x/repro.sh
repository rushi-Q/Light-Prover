#!/bin/bash
# repro for 064 (~15 min, any x86-64 host): valid project whose main_thm uses `heavy : primeSum 20000 = 21171191 := by
# decide +kernel` (a sieve over List Nat; maxHeartbeats 0). Official Lean 4.33.1 build (its kernel evaluates the claim,
# ~4 min) + official lean4export v4.33.0, then run3.sh: official `lake comparator` 4.36 (Lean kernel + nanoda) vs the
# exact check-B run lines (single gruszka+kcompare, dual gruszka AND nl-fast + kcompare). Control8000.lean (primeSum 8000)
# = the same proof at 2/5 the size: every checker accepts.
set -u
D=$(cd "$(dirname "$0")" && pwd); cd "$D"
X=${FV_REPRO_DIR:-$LIGHT_LEAN/repro}; T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
bash mkexp.sh Challenge main_thm >/dev/null 2>&1
for m in Control8000 Main; do
  s=$(date +%s); bash mkexp.sh $m main_thm 2>&1 | grep -i error; echo "== $m: official Lean 4.33.1 build (kernel ON) + export rc=${PIPESTATUS[0]} in $(( $(date +%s) - s )) s"
  bash run3.sh $m.export
  ${FV_KRUN:-krun} "/scratch/fastverify/checkers/dualkernel/target/release/nl-fast -q -j 4 $D/$m.export > /tmp/n 2>&1; r=\$?; echo \"nl-fast alone: exit \$r: \$(tail -2 /tmp/n | tr '\n' ' ')\""
done
