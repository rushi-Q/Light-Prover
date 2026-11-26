#!/bin/bash
# 0xx repro (MEDIUM, resources): rh-mid ref export (1.1 GB, /scratch/bench-inputs/rh-mid on every test host).
#  part 1: official lake comparator (+nanoda) vs pchk run.sh: wall time and PEAK summed RSS of the process tree
#  part 2: pleanchecker-k on the export vs the same export + ONE trailing line {"in":999999999,...} (sparse name index:
#          legal for the official reader, FastParse declines at EOF -> official parser re-reads everything; per-chunk
#          persistent objects of the first pass are never freed)
# ~15 min. PART=1 or PART=2 to run one part. Writes the late file (1.1 GB) to a private mktemp dir under /scratch.
set -u
H=$(cd "$(dirname "$0")" && pwd); M=$H/memwatch.py
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi
CH=/scratch/bench-inputs/rh-mid/challenge; SOL=/scratch/bench-inputs/rh-mid/ref/solution.export
W=$(mktemp -d /tmp/x04-res.XXXXXX); trap 'rm -rf "$W"' EXIT; cd $W; cp $CH/comparator.nanoda.json .
if [ "${PART:-1}" = 1 ] || [ -z "${PART:-}" ]; then
  echo "== part 1: OFFICIAL lake comparator (+nanoda)"
  PATH=$TC/bin:$PATH python3 $M -- $TC/bin/lake comparator --config comparator.nanoda.json --challenge-from-export $CH/challenge.export --solution-from-export $SOL 2>&1 | grep -E "memwatch|okay|^error"
  echo "== part 1: FAST pchk run.sh T=32"
  CCMP_LEANCHECKER=$PLC python3 $M -- sh $PCHK/run.sh $PCHK $SOL 32 $CH/challenge.export 2>&1 | grep -E "memwatch|okay|^error"
fi
if [ "${PART:-2}" = 2 ] || [ -z "${PART:-}" ]; then
  L=$(mktemp -d ${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-039.XXXXXX); trap 'rm -rf "$W" "$L"' EXIT; LATE=$L/rhmid-late.export   # private per run
  cp $SOL $LATE && echo '{"in":999999999,"str":{"pre":0,"str":"zzzLateSparse"}}' >> $LATE
  for f in $SOL $LATE; do
    echo "== part 2: $f"
    echo "-- OFFICIAL leanchecker"; LEAN_ABORT_ON_PANIC=1 python3 $M -- $TC/bin/leanchecker --silent --from-export $f 2>&1 | grep memwatch
    echo "-- FAST pleanchecker-k -j32"; python3 $M -- $PLC --silent -v -j32 --from-export $f 2>&1 | grep -E "memwatch|\[pchk\] (read|replay)"
  done
fi
