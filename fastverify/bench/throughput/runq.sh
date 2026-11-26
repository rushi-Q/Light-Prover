#!/bin/bash
# runq.sh QUEUE LANES : run every line "CASE PRESET MODE [extra fastverify args]" of QUEUE through the frozen package
# ($FV_PKG/bin/fastverify), LANES runs at a time, each with --threads $THREADS.  MODE = src (the challenge is built officially
# by the package: B0 + E0) | pin (the official challenge export of an earlier src run, $R/chx/<challenge>/challenge.export,
# given and pinned with --challenge-sha256).  Corpus: $CORPUS (gen.py output).  Outputs: $R/runs/<case>.<preset>.<mode>/
# (result.json + log/; the solution export is deleted after the run, its size/sha256 stay in result.json).
# One line per run in $R/runs/done.tsv: tag case preset mode exit wall_s host start_iso
set -u
Q=$1; LANES=${2:-4}
: "${R:?R=run root}" "${CORPUS:?CORPUS=corpus dir}" "${FV_PKG:?FV_PKG=frozen package}"
THREADS=${THREADS:-8}
WS=${WS:-$LIGHT_LEAN/verify/challenge}
mkdir -p "$R/runs" "$R/chx"
one() {
  set -u
  local CASE=$1 PRESET=$2 MODE=$3; shift 3
  local LBL=""; case "${1:-}" in @*) LBL=".${1#@}"; shift;; esac
  local CH; CH=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]]["challenge"])' "$CORPUS/cases.json" "$CASE")
  local TAG=$CASE.$PRESET.$MODE$LBL${SUFFIX:-}; local OUT=$R/runs/$TAG; rm -rf "$OUT"
  local CHD=$CORPUS/challenges/$CH; local EXTRA=()
  if [ "$MODE" = pin ]; then
    local PD=$R/chx/$CH
    [ -f "$PD/challenge.export" ] || { echo "no pinned challenge for $CH" >&2; return 1; }
    CHD=$R/chpin/$CH
    if [ ! -f "$CHD/challenge.export" ]; then
      mkdir -p "$R/chpin"; rm -rf "$CHD.tmp.$$"; cp -r "$CORPUS/challenges/$CH" "$CHD.tmp.$$"
      ln "$PD/challenge.export" "$CHD.tmp.$$/challenge.export" 2>/dev/null || cp "$PD/challenge.export" "$CHD.tmp.$$/challenge.export"
      mv -T "$CHD.tmp.$$" "$CHD" 2>/dev/null || rm -rf "$CHD.tmp.$$"
    fi
    [ "$PRESET" = sound ] && EXTRA=(--challenge-sha256 "$(cut -d' ' -f1 "$PD/challenge.export.sha256")")
  fi
  local t0 s0; t0=$(date +%s.%N); s0=$(date -u +%FT%TZ)
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV_PKG/bin/fastverify" "$CORPUS/projects/$CASE" "$CHD" "$OUT" \
      --preset "$PRESET" --threads "$THREADS" --packages "$WS" "${EXTRA[@]}" "$@" > "$R/runs/$TAG.log" 2>&1
  local rc=$?
  local t1; t1=$(date +%s.%N)
  if [ "$MODE" = src ] && [ -f "$OUT/challenge.export" ] && [ ! -f "$R/chx/$CH/challenge.export" ]; then
    mkdir -p "$R/chx/$CH.tmp.$$" && cp "$OUT/challenge.export" "$R/chx/$CH.tmp.$$/" && \
      (cd "$R/chx/$CH.tmp.$$" && sha256sum challenge.export > challenge.export.sha256) && \
      { mv -T "$R/chx/$CH.tmp.$$" "$R/chx/$CH" 2>/dev/null || rm -rf "$R/chx/$CH.tmp.$$"; }
  fi
  # keep result.json + logs; drop the big files (solution export may be a symlink into --export-dir)
  local se; se=$(readlink -f "$OUT/solution.export" 2>/dev/null)
  [ -n "$se" ] && [ -f "$se" ] && { chmod u+w "$se" 2>/dev/null; rm -f "$se"; }
  rm -f "$OUT/solution.export" "$OUT/challenge.export"; rm -rf "$OUT/work" "$OUT/snapshots"
  find "$OUT/log" -path '*/planner/planner' -type f -delete 2>/dev/null   # the per-run compiled Lake planner (~140 MB)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$TAG" "$CASE" "$PRESET" "$MODE" "$rc" \
    "$(python3 -c "print(round($t1-$t0,2))")" "$(hostname)" "$s0" >> "$R/runs/done.tsv"
}
export -f one; export R CORPUS FV_PKG THREADS WS SUFFIX
grep -v '^\s*#' "$Q" | grep -v '^\s*$' | xargs -P "$LANES" -L 1 bash -c 'one "$@"' _
