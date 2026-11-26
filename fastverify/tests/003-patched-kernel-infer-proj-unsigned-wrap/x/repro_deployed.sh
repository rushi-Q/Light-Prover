#!/bin/bash
# 003 with the REAL deployed binary /scratch/fastverify/checkers/pchk/.lake/build/bin/pleanchecker-k (glibc 2.38) run inside an
# ubuntu:24.04 container (pkd.sh: no network, image's own GMP 6.3.0, host libuv only). ~200 GB RAM.
# Usage: bash repro_deployed.sh   (4 CPUs are enough)
D=$(cd "$(dirname "$0")" && pwd); TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
P=${FV_REPRO_DIR:-$LIGHT_LEAN/repro}/tools/pkd.sh
for f in ctl0 idx1 wrap; do
  echo "=== $f.ndjson: $(grep -o '"proj":{[^}]*}' "$D/$f.ndjson")"
  bash ${FV_REPRO_DIR:-$LIGHT_LEAN/repro}/tools/sbx.sh "$D" "LEAN_ABORT_ON_PANIC=1 $TC/bin/leanchecker --from-export $D/$f.ndjson; echo OFFICIAL leanchecker rc=\$?"
  PK_BIND="$D" bash $P --from-export "$D/$f.ndjson" 2>&1 | grep -v '^\[pchk'; echo "DEPLOYED pleanchecker-k rc=${PIPESTATUS[0]}"
done
