#!/bin/bash
# profile.sh CORPUS OUTDIR JOBS CASE... : official Lean 4.33.1 with -Dprofiler=true on each case's Solution.lean (bwrap,
# no network; packages = $LEANWS or the trusted workspace; a node-local copy avoids NFS noise) -> OUTDIR/CASE.prof (profiler output + /usr/bin/time line)
set -u
C=$1; O=$2; J=$3; shift 3
mkdir -p "$O"
export SCRATCH=${SCRATCH:-/scratch}
export SPDIR=$(dirname "$(readlink -f "$0")")
one() {
  local c=$1 d; d=$(mktemp -d "$SCRATCH/smallproofs-prof.XXXX"); cp "$C/projects/$c/Solution.lean" "$d/"
  /usr/bin/time -f "WALL %e CPU %U+%S MAXRSS %M" "$SPDIR/leandev.sh" "$d" Solution.lean -Dprofiler=true > "$O/$c.prof" 2>&1
  echo "RC $?" >> "$O/$c.prof"; rm -rf "$d"
}
export -f one; export C O SPDIR SCRATCH
printf '%s\n' "$@" | xargs -P "$J" -I{} bash -c 'one {}'
