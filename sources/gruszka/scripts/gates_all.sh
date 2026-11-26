#!/bin/bash
CAP=${CAP:-$(cd "$(dirname "$0")" && pwd)/capped}
# Every gate of a kept step: small tests (default order, plain and poisoned;
# plain in file order) and vectors (plain and SK_POISON=1;
# vectors in file and namespace order), Init and con-leche poisoned at 4
# workers in the default (namespace) order (Init also with sessions of 2
# declarations), Init poisoned in file order at
# 4 workers and in namespace order at 8, verdict parity with Pestka on six
# corpora in both orders.
# Usage: gates_all.sh [BIN] > OUT; prints GATESDONE, exit 1 on a wrong verdict.
D=${GRUSZKA_DIR:-$(cd "$(dirname "$0")/.." && pwd)}
S=${GRUSZKA_WORK:-${TMPDIR:-/tmp}/gruszka-work}
BIN=${1:-$D/target/release/gruszka}
# absolute: the small tests run from their own directory
case "$BIN" in /*) ;; *) BIN=$PWD/$BIN;; esac
bad=0
echo "== plain"; GATES_CORPORA="" $D/scripts/gates.sh $BIN || bad=1
echo "== poison"; SK_POISON=1 GATES_CORPORA="" $D/scripts/gates.sh $BIN || bad=1
# the small tests above ran in the default order; once more in file order
echo "== small tests, file order"; SK_ORDER=file $D/scripts/run_tests.sh $BIN > /tmp/sk-ga.$$
sed -n '/== summary/,/== WRONG/p' /tmp/sk-ga.$$ | grep -v '== WRONG'
grep -A100 "== WRONG" /tmp/sk-ga.$$ | grep -B100 "== good not" | grep -q '^bad accepted' && { echo "FILE ORDER: bad accepted"; bad=1; }
grep -A100 "== good not" /tmp/sk-ga.$$ | grep -B100 "== bad declined" | grep -q '^good' && { echo "FILE ORDER: a good test not accepted"; bad=1; }
grep -q ' crash(' /tmp/sk-ga.$$ && { echo "FILE ORDER: small tests crashed"; bad=1; }
rm -f /tmp/sk-ga.$$
run() { # ORDER WORKERS CORPUS
  r=$(SK_ORDER=$1 SK_POISON=1 "$CAP" 6000 900 $BIN $S/sz/$3.susz $2 2>/dev/null | tail -1)
  echo "poison $1 w$2 $3: $r"; case "$r" in accepted*) ;; *) bad=1;; esac
}
run ns 4 init; run ns 4 con-leche; run file 4 init; run ns 8 init
# milestone 35: sessions cut every 2 declarations (a table stamped with an
# old session's ids is read in the next one: mutant dm_gen)
r=$(SK_SESSION_DECLS=2 SK_ORDER=ns SK_POISON=1 "$CAP" 6000 900 $BIN $S/sz/init.susz 4 2>/dev/null | tail -1)
echo "poison ns w4 init, sessions of 2: $r"; case "$r" in accepted*) ;; *) bad=1;; esac
SK_ORDER=ns $D/scripts/parity.sh $BIN || bad=1
SK_ORDER=file $D/scripts/parity.sh $BIN || bad=1
echo "GATESDONE bad=$bad"
exit $bad
