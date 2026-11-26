#!/bin/bash
# export.sh W LEAN_PATH OFFICIAL_EXPORTER TARGETS_FILE   -> W/solution.export
# Runs $LEAN4EXPORT_BIN (harness-built, byte-identical native exporter) if set, else the official lean4export v4.33.0.
# If the native exporter fails (rc != 0 or empty output), the official exporter is run instead (correctness first).
# Always inside the bwrap sandbox with the OFFICIAL 4.33.1 toolchain bound (its lib/lean is on LEAN_PATH).
set -uo pipefail
W=$1; LP=$2; OFF=$3; TG=$4; D=$(cd "$(dirname "$0")" && pwd); E=$LIGHT_LEAN/env
TCW=$E/tc-v4.33.1-wrapped
cp "$TG" "$W/log/export-targets.txt"; cp "$OFF" "$W/log/bin/lean4export.official"
run() {  # $1 = exporter path inside log/bin, $2 = tag
  "$D/sbx.sh" "$W/proj" "$W/log" "$TCW" -- /bin/bash -c "cd $W/proj && ${LEAN4EXPORT_EXPR_ESTIMATE_LOG2:+LEAN4EXPORT_EXPR_ESTIMATE_LOG2=$LEAN4EXPORT_EXPR_ESTIMATE_LOG2} LEAN_PATH='$LP' /usr/bin/time -v $W/log/bin/$1 Main -- \$(cat $W/log/export-targets.txt) > $W/log/solution.export 2> $W/log/export.$2.time"
}
rc=1
if [ -n "${LEAN4EXPORT_BIN:-}" ] && [ -x "$LEAN4EXPORT_BIN" ]; then
  cp "$LEAN4EXPORT_BIN" "$W/log/bin/lean4export.native"
  # at full-RH scale (~1.1G exprs) start the native exporter's expr table at 2^31 keys (skips 2 aborted attempts of
  # the restart ladder); small inputs keep the default sizing. Output is independent of the sizing (ladder tested identical).
  NM=$(cat "$W/log/nmodules.txt" 2>/dev/null || echo 0)
  if [ -z "${LEAN4EXPORT_EXPR_ESTIMATE_LOG2:-}" ] && [ "$NM" -gt 100000 ]; then export LEAN4EXPORT_EXPR_ESTIMATE_LOG2=31; fi
  echo "export: native, modules=$NM LEAN4EXPORT_EXPR_ESTIMATE_LOG2=${LEAN4EXPORT_EXPR_ESTIMATE_LOG2:-default}"
  t0=$(date +%s.%N); run lean4export.native native; rc=$?
  echo "export: native rc=$rc $(stat -c %s "$W/log/solution.export" 2>/dev/null) bytes $(echo "$(date +%s.%N) - $t0" | bc | cut -c1-6)s; $(grep -E 'Elapsed|Maximum resident' "$W/log/export.native.time" | tr -s ' ' | tr '\n' ' ')"
  if [ $rc -ne 0 ] || [ ! -s "$W/log/solution.export" ]; then echo "export: native FAILED -> official fallback"; tail -5 "$W/log/export.native.time"; rc=1; fi
fi
if [ $rc -ne 0 ]; then
  t0=$(date +%s.%N); run lean4export.official official; rc=$?
  echo "export: official rc=$rc $(stat -c %s "$W/log/solution.export" 2>/dev/null) bytes $(echo "$(date +%s.%N) - $t0" | bc | cut -c1-6)s; $(grep -E 'Elapsed|Maximum resident' "$W/log/export.official.time" | tr -s ' ' | tr '\n' ' ')"
  [ $rc -eq 0 ] || { echo "export: official FAILED"; tail -20 "$W/log/export.official.time"; exit 1; }
fi
mv "$W/log/solution.export" "$W/solution.export"
