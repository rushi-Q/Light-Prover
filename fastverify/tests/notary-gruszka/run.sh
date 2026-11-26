#!/bin/bash
# tests/notary-gruszka/run.sh [WORKDIR] - regression test: the notary's gruszka-r7 must accept valid official output. It
# was built WITHOUT check/checkB/patches/gruszka-combined.diff, so check-notary.sh REJECTED valid official Lean 4.36 output
# that the official lake comparator and check-sound.sh accept (tests/053 anonymous-name helper, tests/055 nested inductive
# through a type-constructor parameter, tests/058 reflexive nested inductive). Runs those three conformance tests with the
# trusted judges as checkers (CN = check-notary.sh, CS = check-sound.sh; tests/lib/checkcases.sh: PASS iff no checker
# accepts what the official rejects or rejects what it accepts). FV_TEST_OFFICIAL=recorded uses the recorded official
# verdicts instead of re-running the official comparator.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd)
W=${1:-$(mktemp -d /tmp/notary-gruszka-test.XXXXXX)}; mkdir -p "$W"; rc=0
for t in 053-check-b-susz-rejects-a-valid-project-who 055-check-b-gruszka-falsely-rejects-a-valid 058-check-b-gruszka-falsely-rejects-a-valid; do
  FV_NO_ENTRY=1 FV_CHECKERS="CN=$FV/check/notary/check-notary.sh CS=$FV/check/sound/check-sound.sh" EVAL_THREADS=${EVAL_THREADS:-4} \
    bash "$FV/tests/$t/test.sh" "$W/${t:0:3}" > "$W/${t:0:3}.out" 2>&1 || rc=1
  cat "$W/${t:0:3}.out"
done
echo "notary-gruszka: $([ $rc = 0 ] && echo PASS || echo FAIL)"; [ -n "${1:-}" ] || rm -rf "$W"; exit $rc
