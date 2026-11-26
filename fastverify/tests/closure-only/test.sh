#!/bin/bash
# tests/closure-only/test.sh [WORK]  -- B3 item closure-only=MODULE (~1 min, no Mathlib):
# a project whose default targets contain a module that does not compile (Pkg.Dead) but whose solution module Main does
# not import it. For each release in {4.33.1 (Planner.lean), 4.37.0-rc1 (Planner435.lean)} present in config:
#   (1) build.sh --preset B3 --unsafe sound-fast-path            -> FAILED (exit 1: the default targets include Pkg.Dead)
#   (2) build.sh --preset B3 --unsafe sound-fast-path,closure-only=Main -> BUILT; Main.olean present, Pkg/Dead.olean absent
#   (3) build.sh (B1) with closure-only -> refused (B3 only)
#   (4) the .olean of Main from (2) is byte-identical to the official `lake build Main` (sandboxed, same path)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FV_PKG:-$(cd "$H/../.." && pwd)}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/closure-only.XXXXXX")}; rm -rf "$W"; mkdir -p "$W/ws"; W=$(readlink -f "$W"); fail=0
row() { echo "$1 $2: $3"; [ "$1" = FAIL ] && fail=1; return 0; }
for R in 4.33.1 4.37.0-rc1; do
  TC=$(python3 -I -c 'import json,sys; t=json.load(open(sys.argv[1]))["lean_toolchains"].get("leanprover/lean4:v"+sys.argv[2]); print(t["prefix"] if t else "")' "$FV/config/components.json" "$R")
  [ -n "$TC" ] && [ -x "$TC/bin/lean" ] || { echo "SKIP $R: not in config / not installed"; continue; }
  mk() { rm -rf "$W/$1"; mkdir -p "$W/$1"; cp -a "$H/proj" "$W/$1/proj"; echo "leanprover/lean4:v$R" > "$W/$1/proj/lean-toolchain"; }
  mk "$R-default"
  "$FV/build/build.sh" "$W/$R-default/proj" "$W/ws" "$TC" --log "$W/$R-default/log" --threads 4 --preset B3 --unsafe sound-fast-path > "$W/$R-default/out.json" 2>&1; rc=$?
  [ $rc = 1 ] && row PASS "$R default targets" "FAILED as expected (Pkg.Dead does not compile)" || row FAIL "$R default targets" "exit $rc"
  mk "$R-closure"
  "$FV/build/build.sh" "$W/$R-closure/proj" "$W/ws" "$TC" --log "$W/$R-closure/log" --threads 4 --preset B3 --unsafe sound-fast-path,closure-only=Main > "$W/$R-closure/out.json" 2>&1; rc=$?
  L=$W/$R-closure/proj/.lake/build/lib/lean
  if [ $rc = 0 ] && [ -f "$L/Main.olean" ] && [ -f "$L/Pkg/A.olean" ] && [ ! -e "$L/Pkg/Dead.olean" ]; then row PASS "$R closure-only=Main" "BUILT, Pkg.Dead not built"
  else row FAIL "$R closure-only=Main" "exit $rc $(tail -1 "$W/$R-closure/out.json" | cut -c1-200)"; fi
  mk "$R-b1"
  "$FV/build/build.sh" "$W/$R-b1/proj" "$W/ws" "$TC" --log "$W/$R-b1/log" --threads 4 --preset B2 --unsafe closure-only=Main > "$W/$R-b1/out.json" 2>&1; rc2=$?
  [ $rc2 = 2 ] && [ ! -e "$W/$R-b1/proj/.lake/build/lib/lean/Main.olean" ] && row PASS "$R closure-only without B3" "refused (exit 2)" || row FAIL "$R closure-only without B3" "exit $rc2"
  # official lake build of the solution module at the same path, then compare Main.olean
  mv "$W/$R-closure/proj" "$W/$R-closure/proj.fast"; cp -a "$H/proj" "$W/$R-closure/proj"; echo "leanprover/lean4:v$R" > "$W/$R-closure/proj/lean-toolchain"
  (cd "$W/$R-closure/proj" && env -i PATH=$TC/bin:/usr/bin:/bin HOME=/tmp/fvh-$$ /usr/bin/bwrap --ro-bind / / --bind "$W/$R-closure/proj" "$W/$R-closure/proj" --tmpfs /tmp --dev /dev --proc /proc --unshare-all --die-with-parent --chdir "$W/$R-closure/proj" -- "$TC/bin/lake" build Main) > "$W/$R-closure/off.log" 2>&1; orc=$?
  if [ $orc = 0 ] && cmp -s "$W/$R-closure/proj/.lake/build/lib/lean/Main.olean" "$W/$R-closure/proj.fast/.lake/build/lib/lean/Main.olean"; then
    row PASS "$R Main.olean" "byte-identical to the official lake build Main"
  else row FAIL "$R Main.olean" "official exit $orc or bytes differ"; fi
done
[ $fail = 0 ] && { echo "RESULT: PASS"; exit 0; } || { echo "RESULT: FAIL"; exit 1; }
