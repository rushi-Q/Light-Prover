#!/bin/bash
# run1.sh CORPUS CASE PRESET OUTROOT THREADS [CHALLENGE_DIR_KIND] [extra fastverify args...]
#   CHALLENGE_DIR_KIND = src (challenge sources: the challenge is built officially by B0+E0 inside the run) or
#   given (OUTROOT/given/<case>: the official challenge export produced by an earlier reference run, pinned with
#   --challenge-sha256).  Output: OUTROOT/runs/<case>.<preset>[.tag]/, one line in OUTROOT/summary.tsv.
set -u
H=$(dirname "$(readlink -f "$0")"); FASTVERIFY=${FASTVERIFY:-$(cd "$H/../.." && pwd)}; LIGHT_LEAN=${LIGHT_LEAN:-$(dirname "$FASTVERIFY")}
C=$1; CASE=$2; PRESET=$3; R=$4; T=$5; KIND=${6:-src}; shift 6 2>/dev/null || shift $#
FV=${FV:-$FASTVERIFY/bin/fastverify}
WS=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}
TAG=$CASE.$PRESET${RUNTAG:+.$RUNTAG}
OUT=$R/runs/$TAG; rm -rf "$OUT"; mkdir -p "$R/runs"
if [ "$KIND" = given ]; then
  CH=$R/given/$CASE; EXTRA=(--challenge-sha256 "$(cat "$CH/challenge.export.sha256" | cut -d' ' -f1)" --comparator-sha256 "$(sha256sum "$CH/comparator.json" | cut -d' ' -f1)")   # pin pair
else
  CH=$C/challenges/$CASE; EXTRA=()
fi
t0=$(date +%s.%N)
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV" "$C/projects/$CASE" "$CH" "$OUT" --preset "$PRESET" \
   --threads "$T" --packages "$WS" "${EXTRA[@]}" "$@" > "$R/runs/$TAG.log" 2>&1
rc=$?
t1=$(date +%s.%N)
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$TAG" "$CASE" "$PRESET" "$KIND" "$rc" "$(python3 -c "print(round($t1-$t0,2))")" \
  "$(hostname -s)" "$(date -u +%FT%TZ)" >> "$R/summary.tsv"
