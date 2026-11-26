#!/bin/bash
# refs.sh PROJ OUTDIR [CHUNKS] : olean_refs (ranges + hashes) over every project olean of a built tree, read-only bwrap
# (variant of ../prune/refs_for.sh; OLEAN_REFS_DIR = a built olean_refs directory, e.g. a node-local copy).
set -e
P=$1; O=$2; N=${3:-64}; T=${OLEAN_REFS_DIR:?directory with sandbox_ro.sh and a built .lake/build/bin/olean_refs (required)}
mkdir -p $O/chunks $O/out
L=$P/.lake/build/lib/lean
(cd $L && find . -name '*.olean' | sed 's#^\./##; s#\.olean$##' | while read r; do printf '%s\t%s\n' "$(echo $r | tr / .)" "$L/$r.olean"; done) > $O/all.list
rm -f $O/chunks/c* ; split -n l/$N -d -a 3 $O/all.list $O/chunks/c
for f in $O/chunks/c*; do
  b=$(basename $f)
  $T/sandbox_ro.sh $O/out $P:$O/chunks -- env OLEAN_REFS_RANGES=1 OLEAN_REFS_HASH=1 $T/.lake/build/bin/olean_refs $O/out/$b.tsv $f 2> $O/out/$b.err &
done
wait; wc -l $O/all.list; du -sh $O/out
