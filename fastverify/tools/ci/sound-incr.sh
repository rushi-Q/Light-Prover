#!/bin/bash
# tools/ci/sound-incr.sh PREV NEW_SOURCES CHALLENGE OUT --challenge-sha256 HEX [incr-reverify options...]
#
# One commit of a CI stream in SOUND mode: re-verify NEW_SOURCES incrementally on top of the previous commit's build
# (tools/incr/incr-reverify.sh) and leave OUT/next-base for the next commit, so that a whole commit history is
# verified as a chain: cold `bin/fastverify ... --preset sound --unsafe <list without merge> --keep-work` on the first
# commit, then sound-incr.sh for every later commit (PREV = the cold OUT or the previous sound-incr OUT).
# Nothing here is trusted: the verdict of every commit is the trusted check's (check/sound/check-sound.sh) on the export of
# that commit's tree against the pinned official challenge export (incr-reverify.sh); the previous build tree is reused
# read-only (reflink/full copy, never hard links) and stale outputs can only cause a reject (README 1b).
# --warm-prev: start the warm Lean-kernel leg with the PREVIOUS commit's export as untrusted snapshot (needs the previous
# OUT to have kept its export: this script always passes --keep-export to incr-reverify and keeps the last export only).
# Output: OUT/summary.json (incr-reverify's), OUT/next-base/ (base view: work/proj, log/build-fast/plan.jsonl, ...).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=${FASTVERIFY:-$(cd "$H/../.." && pwd)}
PREV=$(readlink -f "$1") NEW=$2 CH=$3 OUT=$4; shift 4
WARMPREV=0; ARGS=()
while [ $# -gt 0 ]; do case "$1" in --warm-prev) WARMPREV=1; shift ;; *) ARGS+=("$1"); shift ;; esac; done
if [ -f "$PREV/result.json" ] && [ -d "$PREV/work/proj" ]; then BASE=$PREV            # a cold fastverify OUT
elif [ -d "$PREV/next-base" ]; then BASE=$PREV/next-base                               # a previous sound-incr OUT
else echo "sound-incr: $PREV is neither a fastverify --keep-work OUT nor a sound-incr OUT" >&2; exit 2; fi
W=()
if [ $WARMPREV = 1 ]; then
  PX=$(readlink -f "$BASE/solution.export" 2>/dev/null)
  [ -f "$PX" ] && W=(--warm "$PX") || echo "sound-incr: no previous export -> cold check" >&2
fi
"$PKG/tools/incr/incr-reverify.sh" "$BASE" "$NEW" "$CH" "$OUT" --keep-export "${W[@]}" "${ARGS[@]}"; rc=$?
# base view for the next commit: the LAST attempt's tree (a2-full after a failed optimistic/interface attempt)
A=$(ls -d "$OUT"/a[0-9]-* 2>/dev/null | sort | tail -1)
if [ -n "$A" ] && [ -f "$A/work/log/plan.jsonl" ] && grep -q ' check' "$A/times" 2>/dev/null; then
  B=$OUT/next-base; mkdir -p "$B/work" "$B/log/build-fast"
  ln -s "$A/work/proj" "$B/work/proj"; ln -s "$A/work/log/plan.jsonl" "$B/log/build-fast/plan.jsonl"
  for x in fastexact planner; do [ -e "$BASE/log/build-fast/$x" ] && ln -s "$(readlink -f "$BASE/log/build-fast/$x")" "$B/log/build-fast/$x"; done
  cp "$BASE/log/export-targets.txt" "$B/log/export-targets.txt"; ln -s "$(readlink -f "$BASE/result.json")" "$B/result.json"
  [ -e "$A/solution.export" ] && ln -s "$(readlink -f "$A/solution.export")" "$B/solution.export"
else
  # build failed / no export: the next commit builds on the previous good base (like a CI that keeps the last green cache)
  ln -s "$BASE" "$OUT/next-base"
fi
exit $rc
