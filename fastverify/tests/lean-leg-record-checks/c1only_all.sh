#!/bin/bash
# c1only_all.sh [DIR] : the C1-only exports (mk_c1only.py) through every candidate Lean-leg binary and the pinned ones,
# in their judge modes (default walk par + --seq; incr plain; notary; ultralowmem --low-mem --evict=smart; warm CHECK_FULL).
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
D=${1:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/c1only}; C=${FV_LEANLEG_CANDIDATES:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/leanleg-candidates}
EMPTY=$(mktemp /tmp/leanleg-empty.XXXXXX.export); echo '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.36.0"}}}' > $EMPTY
warm() { local out; out=$(printf 'CHECK_FULL\tq\t%s\nQUIT\n' "$2" | LEAN_STACK_SIZE_KB=917376 "$1" --base $EMPTY -j4 2>/dev/null | tail -1); echo "$out" | grep -q '"status":"ok"' && { echo accepts; return 0; } || { echo "rejects $(echo $out | cut -c1-200)"; return 1; }; }
run() { local lab=$1; shift
  for x in $D/*.export; do n=$(basename $x .export)
    if [ "$1" = warm ]; then warm "$2" $x > /tmp/leanleg-c1only.log 2>&1; rc=$?; else LEAN_STACK_SIZE_KB=917376 timeout 300 "$@" $x > /tmp/leanleg-c1only.log 2>&1; rc=$?; fi
    case $n in *control*) w=control;; *) w=attack;; esac
    if [ $w = control ]; then [ $rc = 0 ] && ok=PASS || ok=FAIL; else [ $rc != 0 ] && ok=PASS || ok=FAIL; fi
    printf '%s\t%s\t%s\t%s\trc=%s\t%s\n' $ok "$lab" $n $w $rc "$(grep -E 'rejects|accepts' /tmp/leanleg-c1only.log | tail -1 | cut -c1-130)"
  done; }
run cand-par $C/pleanchecker -j4
run cand-seq $C/pleanchecker -j4 --seq
run cand-incr $C/pleanchecker-incr -j4
run cand-notary $C/pleanchecker-notary -j4
run cand-ulm $C/pleanchecker-lowmem --low-mem --evict=smart -j4
run cand-warm warm $C/pleanchecker-warm
run live-par /scratch/fastverify-next/sound/53957eed/pleanchecker -j4
run live-incr /scratch/fastverify-next/sound/6a909238/pleanchecker-targeted -j4
run live-notary $LIGHT_LEAN/fastverify/check/notary/bin/pleanchecker-notary -j4
run live-ulm /scratch/fastverify-next/lowmem/d27c3bdd/pleanchecker-lowmem --low-mem --evict=smart -j4
run live-warm warm /scratch/fastverify-next/warm/9dce81f2/pleanchecker-warm
rm -f $EMPTY
