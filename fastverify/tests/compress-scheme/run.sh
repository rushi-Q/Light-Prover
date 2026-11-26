#!/bin/bash
# Regression tests of the composite compression scheme: every tool fix found by
# the full-RH builds of the composite candidates C1/C2/C3 has a case here or in the tool's own test.
#   scheme/test/run.sh   dedup_filter classes (IMPORT/SHORT/NAMED/NOSUBST/private identity/self-check), apply_edits
#                        `_root_` handling on both sides, normalize NCS `example` rule            (no Lean, ~2 s)
#   prune/test           added-import visibility for --other-edits, `universe .. in` prefix      (no Lean, ~2 s)
#   normalize/test       OPT-O2 `maxHeartbeats 0`, chain merge, dfsverify                        (core Lean, ~20 s)
set -u
C=$(cd "$(dirname "$0")/../../tools/compress" && pwd); rc=0
bash $C/scheme/test/run.sh || rc=1
python3 -I $C/prune/test/test_prune.py | tail -1 | grep -q 'ALL PASS' && echo "prune test: ALL PASS" || { echo "prune test FAILED"; rc=1; }
bash $C/normalize/test/run.sh 2>&1 | tail -1 | tee /dev/stderr | grep -q ' 0 failed' || rc=1
[ $rc = 0 ] && echo "compress-scheme: PASS" || echo "compress-scheme: FAIL"
exit $rc
