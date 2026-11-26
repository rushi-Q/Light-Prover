#!/bin/bash
# deploy-one.sh NAME SRCHOST HOST... : copy /scratch/fastverify-next/tc/NAME from SRCHOST to the same path on each HOST
# (additive directory, read-only afterwards; build.sh verifies every file against toolchains/unofficial/NAME.json before use)
set -u
N=$1 S=$2; shift 2
for h in "$@"; do
  ssh -o BatchMode=yes $h "test -d /scratch/fastverify-next/tc/$N" && { echo "$h present"; continue; }
  ssh -o BatchMode=yes $S "rsync -a /scratch/fastverify-next/tc/$N/ $h:/scratch/fastverify-next/tc/.$N.tmp/" && \
    ssh $h "chmod u+w /scratch/fastverify-next/tc/.$N.tmp && mv /scratch/fastverify-next/tc/.$N.tmp /scratch/fastverify-next/tc/$N && chmod -R a-w /scratch/fastverify-next/tc/$N" && echo "$h deployed" || echo "$h FAILED"
done
