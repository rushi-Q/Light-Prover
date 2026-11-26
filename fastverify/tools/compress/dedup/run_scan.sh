#!/bin/bash
# run_scan.sh LIST OUTDIR RO_ROOT[:RO_ROOT2...] [N] : dupscan scan over LIST ("module<TAB>path.olean" lines) in N chunks,
# each inside the read-only bwrap sandbox without network (sandbox_ro.sh; only OUTDIR writable). The oleans come from
# untrusted code: they are only READ (readModuleData), never executed. DUPSCAN = the built binary (default: ./dupscan/...).
set -e
H=$(cd "$(dirname "$0")" && pwd); L=$(readlink -f $1); D=$(mkdir -p $2 && readlink -f $2); RO=$3; N=${4:-32}
B=${DUPSCAN:-$H/dupscan/.lake/build/bin/dupscan}; BD=$(dirname $(dirname $(dirname $(dirname $B))))
mkdir -p $D/chunks $D/out; rm -f $D/chunks/* $D/out/*
split -n l/$N -d -a 3 $L $D/chunks/c
for f in $D/chunks/c*; do
  b=$(basename $f)
  $H/sandbox_ro.sh $D/out $RO:$D/chunks:$BD -- $B scan $D/out/$b.tsv $f 2> $D/out/$b.err &
done
wait; echo DONE
