#!/bin/bash
# mklocal.sh DEST   (run ON the benchmark host)  -> a node-local fastverify installation without NFS on the hot path:
#   DEST/elan/toolchains/{v4.33.1,v4.36.0}  copies of the official toolchains (verified by the package's own preflight)
#   DEST/ll/env/tools/lean4export            copy of the official exporter
#   DEST/ws                                   copy of the trusted workspace verify/challenge (Mathlib 0df444a + deps, .git kept)
#   DEST/fv                                   copy of the package, configured by tools/configure.py for the paths above
# Use: DEST/fv/bin/fastverify PROJECT CHALLENGE OUT ... --packages DEST/ws
# Why: where /home is NFS, every lean process pays ~20 s (Mathlib import) / ~1.7 s (core Init) of NFS
# latency when the toolchain / workspace live there. Code and pins are unchanged (configure.py only
# substitutes ${ELAN_HOME}/${LIGHT_LEAN}); re-run to refresh the package copy.
set -eu
D=${1:?dest}; H=$HOME; LL=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
mkdir -p $D/elan/toolchains $D/ll/env/tools
for t in leanprover--lean4---v4.33.1 leanprover--lean4---v4.36.0; do
  [ -d $D/elan/toolchains/$t ] || rsync -a $H/.elan/toolchains/$t/ $D/elan/toolchains/$t/
done
[ -d $D/ll/env/tools/lean4export ] || rsync -a $LL/env/tools/lean4export/ $D/ll/env/tools/lean4export/
[ -d $D/ws/.lake/packages/mathlib ] || rsync -a $LL/verify/challenge/ $D/ws/
rsync -a --delete --exclude=__pycache__ --exclude=pipeline --exclude='*.lock' $LL/fastverify/ $D/fv/
python3 -I $D/fv/tools/configure.py --elan-home $D/elan --light-lean $D/ll
echo "local install ready: $D/fv (packages: $D/ws)"
