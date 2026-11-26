#!/bin/bash
# 007 repro: an export that the official Lean kernel rejects (theorem badThm : False := True) is ACCEPTED by pchk's
# pleanchecker (and by run.sh's kernel-only mode) when the export is read from a pipe (/dev/stdin, <(...)).
# bad.export = in/solution.export (official Lean 4.33.1 + official lean4export v4.33.0 of in/Main.lean) + in/append.ndjson
# (4 lines with SPARSE indices 1000000.. -- legal for the official reader, which uses hash maps; FastParse requires dense
# indices and declines on them; its fallback then re-opens the path -> a drained pipe -> EOF -> empty environment).
set -u
H=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk
KRUN=${FV_KRUN:-krun}
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi   # a local rebuild of pchk d876802 (build_k.sh)
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=$PCHK/.lake/build/bin/pleanchecker; fi
echo "pchk Lean-kernel replay binary used: $PLC  (deployed pleanchecker-k needs glibc 2.38; PLC=... to override)"
W=$(mktemp -d $H/run.XXXXXX); trap 'rm -rf "$W"' EXIT
cat $H/in/solution.export $H/in/append.ndjson > $W/bad.export
B=$W/bad.export
r() { $KRUN "$1" > $W/log 2>&1; echo "exit $?   $(grep -m1 -E 'kernel (accepts|rejects)|error' $W/log | cut -c1-110)"; }
echo "OFFICIAL leanchecker 4.36 --from-export FILE          : $(r "$TC/bin/leanchecker --from-export $B")"
echo "OFFICIAL leanchecker 4.36 --from-export /dev/stdin <pipe: $(r "cat $B | $TC/bin/leanchecker --from-export /dev/stdin")"
echo "FAST pleanchecker --from-export FILE                  : $(r "$PLC --from-export $B")"
echo "FAST pleanchecker --from-export /dev/stdin <pipe      : $(r "cat $B | $PLC --from-export /dev/stdin")"
echo "FAST pleanchecker --from-export <(cat FILE)           : $(r "bash -c '$PLC --from-export <(cat $B)'")"
echo "FAST run.sh SRC /dev/stdin 8   <pipe (kernel-only)    : $(r "cat $B | CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK /dev/stdin 8")"
if docker info >/dev/null 2>&1; then   # the DEPLOYED pleanchecker-k (needs glibc 2.38) in a throw-away ubuntu:24.04 container
  echo "FAST DEPLOYED pleanchecker-k (container) /dev/stdin <pipe: $(bash -c "cat $B | $H/pk-deployed --from-export /dev/stdin" > $W/log 2>&1; echo "exit $?   $(grep -m1 -E 'kernel (accepts|rejects)' $W/log | cut -c1-90)")"
fi
