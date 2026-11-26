#!/bin/bash
# run.sh [WORK] — Unified regression test suite for fastverify/tools/compress/.
# Verifies the 9 post-hoc proof compression sub-suites in one self-contained run:
#   1. prune/test/test_prune.py         (19 checks: classic + Lean 4 module-system closure pruning, barrel trimming, fixlake)
#   2. normalize/test/run.sh            (31 checks: IMP-C1/C2, OPT-O1..O3, module-system lattice, dfsverify, chainmerge --same-dir, OleanDiff)
#   3. dedup/test/run.sh                (duplicate theorem consolidation + apply_edits.py)
#   4. defdedup/test/run.sh             (duplicate def/abbrev consolidation)
#   5. dhe/test/run.sh                  (kernel-certified dead-have / dead-binder elimination)
#   6. aliascollapse/test/run.sh        (card/proof collapse + unify + attrhide)
#   7. autoshorten/test/run.sh          (automated tactic shortening + statement-closure filter)
#   8. expdiff/test/run.sh              (33 checks: Rust export differential & closure DAG analyzer)
#   9. exphash/test/run.sh              (7 checks: Rust semantic export sharing verified by trusted check-sound.sh)
set -uo pipefail

main() {
  local HERE FV TC_DIR W PASS FAIL
  HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
  FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
  TC_DIR="$FV/tools/compress"
  W=${1:-/tmp/compress-suite-$$}
  mkdir -p "$W"
  trap 'rm -rf "$W"' EXIT

  PASS=0
  FAIL=0

  run_sub() {
    local name=$1
    shift
    local log="$W/${name//\//_}.log"
    local t0 dt rc
    t0=$(date +%s)
    if "$@" >"$log" 2>&1; then
      dt=$(($(date +%s) - t0))
      printf 'PASS   %-38s (%ds)\n' "$name" "$dt"
      PASS=$((PASS + 1))
    else
      rc=$?
      dt=$(($(date +%s) - t0))
      printf 'FAIL   %-38s (rc=%d, %ds)\n' "$name" "$rc" "$dt"
      tail -n 15 "$log" | sed 's/^/       /'
      FAIL=$((FAIL + 1))
    fi
  }

  run_sub "prune/test_prune.py"            python3 -I "$TC_DIR/prune/test/test_prune.py"
  run_sub "normalize/test"                 bash "$TC_DIR/normalize/test/run.sh"
  run_sub "dedup/test"                     bash "$TC_DIR/dedup/test/run.sh"
  run_sub "defdedup/test"                  bash "$TC_DIR/defdedup/test/run.sh"
  run_sub "dhe/test"                       bash "$TC_DIR/dhe/test/run.sh"
  run_sub "aliascollapse+attrhide/test"    bash "$TC_DIR/aliascollapse/test/run.sh"
  run_sub "autoshorten/test"               bash "$TC_DIR/autoshorten/test/run.sh"
  run_sub "expdiff/test"                   bash "$TC_DIR/expdiff/test/run.sh"
  run_sub "exphash/test"                   bash "$TC_DIR/exphash/test/run.sh" "$W/exphash-work"

  echo "compress-suite: $PASS passed, $FAIL failed"
  if [ "$FAIL" -eq 0 ]; then
    echo "RESULT PASS"
    exit 0
  else
    echo "RESULT FAIL"
    exit 1
  fi
}

main "$@"
