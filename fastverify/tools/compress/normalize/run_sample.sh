#!/bin/bash
# run_sample.sh LIST ORIGDIR NEWDIR WORKROOT JOBS -> modcheck on every module of LIST, JOBS in parallel
L=$1; O=$2; N=$3; W=$4; J=${5:-8}
T=$(dirname $(readlink -f $0))
mkdir -p $W
cat $L | xargs -P $J -I{} bash -c 'm={}; r=${m//.//}; '"$T"'/modcheck.sh $m '"$O"'/$r.lean '"$N"'/$r.lean '"$W"'/$m 2>&1 | grep RESULT'
