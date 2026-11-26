#!/bin/bash
# plain_variants.sh : the forged-constructor exports (forged ctor record, inductInfo-field and unsafe-recursor variants; honest control)
# through every candidate Lean-leg binary in its plain judge mode (and the pinned ones): notary, ultralowmem (--low-mem --evict=smart),
# warm (CHECK_FULL on an empty base).
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
Q=${FV_FORGED_CTOR_DIR:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/forged-ctor}; C=${FV_LEANLEG_CANDIDATES:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/leanleg-candidates}
[ -d "$Q" ] || { echo "SKIP plain_variants: needs the forged-constructor exports at $Q, which are not part of the repository"; exit 0; }
EMPTY=$(mktemp /tmp/leanleg-empty.XXXXXX.export); echo '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.36.0"}}}' > $EMPTY
run() { # run LABEL CMD...  (export appended)
  local lab=$1; shift
  for x in honest forged forged-d-only ind-isrec ind-nidx ind-nnested ind-refl rec-unsafe; do
    if [ "$1" = warm ]; then warm "$2" $Q/$x.export > /tmp/leanleg-forged.log 2>&1; rc=$?
    else LEAN_STACK_SIZE_KB=917376 timeout 300 "$@" $Q/$x.export > /tmp/leanleg-forged.log 2>&1; rc=$?; fi
    w=attack; [ $x = honest ] && w=control
    if [ $w = control ]; then [ $rc = 0 ] && ok=PASS || ok=FAIL; else [ $rc != 0 ] && ok=PASS || ok=FAIL; fi
    printf '%s\t%s\t%s\t%s\trc=%s\t%s\n' $ok "$lab" $x $w $rc "$(grep -E 'rejects|accepts' /tmp/leanleg-forged.log | tail -1 | cut -c1-110)"
  done
}
warm() { # warm BIN EXPORT -> rc 0 iff CHECK_FULL status ok
  local out; out=$(printf 'CHECK_FULL\tq\t%s\nQUIT\n' "$2" | LEAN_STACK_SIZE_KB=917376 "$1" --base $EMPTY -j4 2>/dev/null | tail -1)
  echo "$out" | grep -q '"status":"ok"' && { echo "Lean default kernel accepts"; return 0; } || { echo "rejects: $out" | cut -c1-200; return 1; }
}
run cand-notary $C/pleanchecker-notary -j4
run notary-live $LIGHT_LEAN/fastverify/check/notary/bin/pleanchecker-notary -j4
run cand-ulm $C/pleanchecker-lowmem --low-mem --evict=smart -j4
run ulm-live /scratch/fastverify-next/lowmem/d27c3bdd/pleanchecker-lowmem --low-mem --evict=smart -j4
run cand-warm warm $C/pleanchecker-warm
run warm-live warm /scratch/fastverify-next/warm/9dce81f2/pleanchecker-warm
rm -f $EMPTY
