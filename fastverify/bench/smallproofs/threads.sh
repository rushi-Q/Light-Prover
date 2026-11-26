#!/bin/bash
# threads.sh CORPUS OUTROOT CASE... : --preset sound with a given challenge at --threads 1, 2, 4 (availability at the low
# thread counts a many-proofs service would use; tests/sound-gates' thread matrix also starts at 1, but on RH-size exports).
set -u
H=$(dirname "$(readlink -f "$0")")
C=$1; R=$2; shift 2
for CASE in "$@"; do for T in 1 2 4; do RUNTAG=t$T "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given; done; done
