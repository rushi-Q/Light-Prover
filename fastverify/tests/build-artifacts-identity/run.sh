#!/bin/bash
# run.sh WORK : build/test/cmp_official.sh over EVERY project directory of the numbered tests' snapshots in tests/*/x/ (a dir with
# a lean-toolchain and a lakefile, challenge dirs excluded): fast build vs official sandboxed lake build at the same path,
# every artifact byte-compared. PASS = 'CMP: SAME' or 'CMP: DECLINED' (official build runs instead); FAIL = DIFFERENT, except
# the documented nondeterministic project 062/proj-coin (fails iff IO.monoNanosNow is even - the official flow flips too).
{ # whole script parsed before it runs
set -u
T=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); FV=${FV_ROOT:-$(cd "$T/.." && pwd)}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-artifacts-identity.work.XXXXXX")}; mkdir -p "$W"; W=$(readlink -f "$W")
WS=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}
find "$T"/[0-9][0-9][0-9]-*/x -name lean-toolchain -not -path '*/.lake/*' | while read -r f; do d=$(dirname "$f")
  case $(basename "$d") in challenge|base) continue;; esac
  { [ -f "$d/lakefile.toml" ] || [ -f "$d/lakefile.lean" ]; } || continue; echo "$d"; done | sort > "$W/projects.txt"
echo "INFO $(wc -l < "$W/projects.txt") project dirs"
one() { d=$1; W=$2; FV=$3; WS=$4; rel=${d#*/tests/}; key=$(echo "$rel" | tr '/' '_')
  out=$(TIMEOUT=${C06_TIMEOUT:-600} THREADS=8 timeout 1800 "$FV/build/test/cmp_official.sh" "$d" "$W/$key" "$WS" 2>&1 | tail -1)
  case "$out" in "CMP: SAME"*|"CMP: DECLINED"*) echo "PASS $rel: $out";;
    *) case $rel in *062-*/proj-coin) echo "PASS $rel (nondeterministic by construction, official flips too): $out";; *) echo "FAIL $rel: $out";; esac;; esac
  rm -rf "$W/$key"; }
export -f one
xargs -a "$W/projects.txt" -P "${C06_JOBS:-6}" -I{} bash -c 'one "$@"' _ {} "$W" "$FV" "$WS"
exit 0
}
