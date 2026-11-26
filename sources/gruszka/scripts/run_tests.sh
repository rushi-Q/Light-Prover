#!/bin/bash
CAP=${CAP:-$(cd "$(dirname "$0")" && pwd)/capped}
# Runs every Arena small test (ndjson, packed in-process) and tabulates
# good/bad x accepted/rejected/declined. Tests under either/ (the Arena's
# `outcome: either`) may be accepted or rejected; a crash or a timeout there
# fails the gates as anywhere. Usage: run_tests.sh [BIN] [OUT]
X=${ARENA_TESTS:?set ARENA_TESTS to the Arena tests directory}
BIN=${1:-$(cd "$(dirname "$0")/.." && pwd)/target/release/gruszka}
OUT=${2:-/dev/stdout}
: > /tmp/sk-res.$$
cd $X
for f in $(find good bad either -name '*.ndjson' | grep -v /perf/ | sort); do
  exp=${f%%/*}
  r=$("$CAP" 4000 60 $BIN $f 1 2>/dev/null | tail -1)
  code=$?
  case "$r" in accepted*) v=accepted;; rejected*) v=rejected;; declined*) v=declined;; *) v="crash($code)";; esac
  echo "$exp $v $f :: $r" >> /tmp/sk-res.$$
done
{
echo "== summary"; awk '{print $1, $2}' /tmp/sk-res.$$ | sort | uniq -c
echo "== WRONG (bad accepted)"; grep '^bad accepted' /tmp/sk-res.$$
echo "== good not accepted"; grep '^good' /tmp/sk-res.$$ | grep -v ' accepted '
echo "== bad declined/crash"; grep '^bad' /tmp/sk-res.$$ | grep -v ' rejected '
echo "== either declined/crash"; grep '^either' /tmp/sk-res.$$ | grep -v -e ' accepted ' -e ' rejected '
} > $OUT
rm /tmp/sk-res.$$
