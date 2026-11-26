#!/bin/bash
# tryat_batch.sh PROJ SRC LIST WD TACS HB MODE MINLINES JOBS TIMEOUT [MAXLINES]
# Run TryAt.lean (inside bwrap) on every module (relative .lean path) of LIST, JOBS at a time; results WD/res/<n>.jsonl
set -u
PROJ=$1; SRC=$2; LIST=$3; WD=$4; TACS=$5; HB=$6; MODE=$7; MINL=$8; JOBS=$9; TO=${10}; MAXL=${11:-1000000}
T=$(dirname $(readlink -f $0))
mkdir -p $WD/res $WD/in; cp $T/TryAt.lean $WD/TryAt.lean
cp $TACS $WD/tacs.txt
nl -ba -nln $LIST | while read n rel; do echo "$n $rel"; done > $WD/index.txt
one() {
  n=$1; rel=$2
  [ -s $WD/res/$n.done ] && return 0
  mod=$(echo ${rel%.lean} | tr / .)
  cp $SRC/$rel $WD/in/$n.lean
  s=$(date +%s.%N)
  timeout -k 10 $TO $T/bwrun.sh $PROJ $WD lean --run TryAt.lean in/$n.lean $mod tacs.txt $HB $MODE res/$n.jsonl $MINL $MAXL > $WD/res/$n.err 2>&1
  rc=$?
  e=$(date +%s.%N)
  echo "$rc $(echo "$e - $s" | bc) $rel" > $WD/res/$n.done
}
export -f one; export WD PROJ SRC T HB MODE MINL MAXL TO
xargs -d '\n' -P $JOBS -I{} bash -c 'read -r n rel <<< "$1"; one "$n" "$rel"' _ {} < $WD/index.txt
