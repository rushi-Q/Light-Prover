#!/bin/bash
# run_mergesample.sh GROUPS.txt SRCDIR WORKROOT JOBS
G=$1; S=$2; W=$3; J=${4:-8}; T=$(dirname $(readlink -f $0))
mkdir -p $W
cat $G | xargs -P $J -I{} bash -c 'line="{}"; k=${line%% *}; '"$T"'/mergecheck.sh "$line" '"$S"'/$k.lean '"$W"'/$k 2>&1 | grep RESULT'
