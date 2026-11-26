#!/bin/bash
CAP=${CAP:-$(cd "$(dirname "$0")" && pwd)/capped}
# Runs the Arena perf tests: verdict, wall, max RSS, instructions.
X=${ARENA_TESTS:?set ARENA_TESTS to the Arena tests directory}
BIN=${1:-$(cd "$(dirname "$0")/.." && pwd)/target/release/gruszka}
W=${2:-1}
cd $X
for f in $(ls good/perf/*.ndjson bad/perf/*.ndjson); do
  out=$( { /usr/bin/time -l "$CAP" 2000 20 $BIN $f $W; } 2>&1 )
  v=$(echo "$out" | grep -E "^(accepted|rejected|declined)" | head -1 | cut -c1-90)
  [ -z "$v" ] && v="CRASH/timeout: $(echo "$out" | grep -E 'capped|panicked' | head -1)"
  wall=$(echo "$out" | awk '/real/ {print $1}')
  rss=$(echo "$out" | awk '/maximum resident/ {printf "%.0f", $1/1048576}')
  ins=$(echo "$out" | awk '/instructions retired/ {printf "%.2f", $1/1e9}')
  printf "%-45s %6ss %6sMB %8sG  %s\n" $f "$wall" "$rss" "$ins" "$v"
done
