#!/bin/bash
CAP=${CAP:-$(cd "$(dirname "$0")" && pwd)/capped}
# Verdict parity with Pestka (the oracle): Gruszka's verdict on each corpus
# must equal Pestka's (data/m4/pestka-verdicts.txt). 4 workers, 6 GB cap.
# Usage: [SK_ORDER=file|ns] parity.sh [BIN] [CORPORA...]; exit 1 on any
# difference. The order (default ns) is printed on every line.
D=${GRUSZKA_DIR:-$(cd "$(dirname "$0")/.." && pwd)}
S=${GRUSZKA_WORK:-${TMPDIR:-/tmp}/gruszka-work}
BIN=${1:-$D/target/release/gruszka}; shift
CS=${*:-init std con-leche reachability cedar etale}
bad=0
for c in $CS; do
  want=$(awk -v c=$c '$1==c {print $2}' $D/data/m4/pestka-verdicts.txt)
  got=$("$CAP" 6000 900 $BIN $S/sz/$c.susz 4 2>/dev/null | tail -1)
  case "$got" in "$want"*) echo "parity ok   ${SK_ORDER:-ns} $c: $got";; *) echo "PARITY FAIL ${SK_ORDER:-ns} $c: pestka $want, gruszka $got"; bad=1;; esac
done
exit $bad
