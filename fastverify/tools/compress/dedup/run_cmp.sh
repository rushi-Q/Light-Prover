#!/bin/bash
# run_cmp.sh LIST OUTDIR RO_ROOT [N] : dupscan cmp (structural confirmation of hash groups) over LIST
# ("group<TAB>module<TAB>path.olean<TAB>name" lines) in N chunks (split by group id), in the read-only sandbox.
set -e
H=$(cd "$(dirname "$0")" && pwd); L=$(readlink -f $1); D=$(mkdir -p $2 && readlink -f $2); RO=$3; N=${4:-32}
B=${DUPSCAN:-$H/dupscan/.lake/build/bin/dupscan}; BD=$(dirname $(dirname $(dirname $(dirname $B))))
mkdir -p $D/chunks $D/out; rm -f $D/chunks/* $D/out/*
awk -F'\t' -v N=$N -v D=$D '{ f=sprintf("%s/chunks/c%03d", D, $1 % N); print > f }' $L
for f in $D/chunks/c*; do
  b=$(basename $f)
  $H/sandbox_ro.sh $D/out $RO:$D/chunks:$BD -- $B cmp $D/out/$b.tsv $f 2> $D/out/$b.err &
done
wait; echo DONE
