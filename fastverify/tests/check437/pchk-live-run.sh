#!/bin/bash
# pchk-live-run.sh BIN EXPORT HIDEFILE OUTDIR [THREADS] [LIVE_MS] - DIAGNOSTIC run of a pleanchecker binary on an export inside
# bwrap (no network, read-only inputs), with the encapsulated replay's hide list and the live monitor (PCHK_LIVE_MS; tools/mk_pchk_live.py):
# finds the declarations that keep running at RH scale. Not a verdict of anything: no comparator, no pins, no challenge.
set -u
BIN=$1; E=$2; H=$3; O=$4; T=${5:-128}; LIVE=${6:-60000}
TC=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.37.0-rc1"]["prefix"])' "${FV_PKG:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}/config/components.json")
mkdir -p "$O"; sha256sum "$BIN" "$H" > "$O/inputs.sha256"; echo "export $E $(stat -c %s "$E") B" >> "$O/inputs.sha256"
echo "[live] $(date -u +%FT%TZ) start: $T threads, live every $LIVE ms, bin $(sha256sum "$BIN" | cut -c1-16)"
/usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc \
  --ro-bind "$TC" "$TC" --ro-bind "$(dirname "$E")" "$(dirname "$E")" --ro-bind "$(dirname "$H")" "$(dirname "$H")" --ro-bind "$(dirname "$BIN")" "$(dirname "$BIN")" \
  --clearenv --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN_NUM_THREADS "$T" --setenv LEAN_STACK_SIZE_KB 917376 \
  --setenv PCHK_SLOW_MS 1000 --setenv PCHK_HIDE_FILE "$H" --setenv PCHK_LIVE_MS "$LIVE" --setenv LANG C.UTF-8 \
  -- /usr/bin/time -f "%e s wall %M KB maxrss" "$BIN" -j$T -v --from-export "$E" > "$O/run.out" 2> "$O/run.err"
rc=$?; echo "[live] $(date -u +%FT%TZ) rc=$rc $(tail -1 "$O/run.err")"; tail -3 "$O/run.out"
