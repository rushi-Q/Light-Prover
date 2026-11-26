#!/bin/bash
# incr_gates.sh PKG OUT THREADS CASEFILE : the soundness gates of the OVERLAPPED Lean leg through the real wiring:
# for every case a fresh incremental server (PKG/overlap/incr-server.sh with PKG's pinned pleanchecker) ingests the given
# snapshot exports, then PKG/check/sound/check-sound.sh judges the final export with --incr-dir.
# CASEFILE lines: NAME<TAB>EXPECTED(0|1)<TAB>EXPORT<TAB>CHALLENGE<TAB>CONFIG<TAB>SNAPSHOTS(comma list or -)
# Paths in CASEFILE may start with ${FV_BENCH_INPUTS} or ${OVERLAP_INPUTS} (taken from the environment; cases-mid.tsv
# uses both: benchmark inputs rh-mid/ + rh-miniF/, and the adversarial inputs midmut/, mid/, cmpx/ of the overlap tests).
# PASS iff the exit code equals EXPECTED and (for ACCEPT cases) the server answered (incremental path used).
set -u
PKG=$(readlink -f "$1"); OUT=$2; T=$3; CF=$4; mkdir -p "$OUT"; OUT=$(readlink -f "$OUT")
PLC=$(awk '$1=="PIN" && $2=="pleanchecker_incr" {print $4}' "$PKG/check/sound/pins.env")
[ -n "$PLC" ] || PLC=$(awk '$1=="PIN" && $2=="pleanchecker" {print $4}' "$PKG/check/sound/pins.env")
for v in FV_BENCH_INPUTS OVERLAP_INPUTS; do
  if grep -qF "\${$v}" "$CF" && [ -z "${!v:-}" ]; then echo "incr_gates: $CF uses \${$v}: set $v" >&2; exit 2; fi
done
pass=0; fail=0; : > "$OUT/incr_gates.tsv"; mkdir -p "$OUT/wd"
while IFS=$'\t' read -r name exp exp_file chal cfg snaps; do
  [ -z "$name" ] || [ "${name:0:1}" = "#" ] && continue
  for v in exp_file chal cfg snaps; do
    s=${!v}; s=${s//'${FV_BENCH_INPUTS}'/${FV_BENCH_INPUTS:-}}; s=${s//'${OVERLAP_INPUTS}'/${OVERLAP_INPUTS:-}}; printf -v "$v" '%s' "$s"
  done
  D=$OUT/$name.incr; rm -rf "$D"; mkdir -p "$D"
  "$PKG/overlap/incr-server.sh" "$D" "$PLC" "$T" > /dev/null 2>&1 &
  SP=$!
  for _ in $(seq 100); do [ -p "$D/cmd" ] && break; sleep 0.1; done
  ns=0
  if [ "$snaps" != - ]; then
    IFS=, read -r -a SN <<< "$snaps"
    for s in "${SN[@]}"; do printf 'snap %s\n' "$s" > "$D/cmd"; ns=$((ns+1)); done
  fi
  # wait until every snapshot was ingested or dropped (so that the final really runs against them)
  while [ "$(grep -cE '^\[incr\] snapshot [0-9]+.*(ingested \(|dropped)' "$D/server.log" 2>/dev/null)" -lt "$ns" ]; do
    kill -0 $SP 2>/dev/null || break; sleep 1; done
  t0=$(date +%s.%N)
  "$PKG/check/sound/check-sound.sh" "$exp_file" "$chal" "$cfg" --threads "$T" --incr-dir "$D" --workdir "$OUT/wd" --json "$OUT/$name.json" \
     --log "$OUT/$name.log" > /dev/null 2>&1
  rc=$?; dt=$(echo "$(date +%s.%N) - $t0" | bc)
  answered=$(grep -c '^\[incr\] answered' "$D/server.log" 2>/dev/null)
  how=$(grep -E '^\[incr\] (final|incremental path)' "$D/server.log" | tail -1 | cut -c1-160)
  kill $SP 2>/dev/null; wait $SP 2>/dev/null
  st=FAIL
  if [ "$rc" = "$exp" ]; then
    if [ "$exp" = 0 ] && [ "$answered" -lt 1 ]; then st=WARN-NOT-INCREMENTAL; else st=PASS; fi
  fi
  case $st in PASS|WARN*) pass=$((pass+1));; *) fail=$((fail+1));; esac
  printf '%s\t%s\texp=%s rc=%s\t%.1fs\tsnaps=%s answered=%s\t%s\n' "$st" "$name" "$exp" "$rc" "$dt" "$ns" "$answered" "$how" | tee -a "$OUT/incr_gates.tsv"
done < "$CF"
echo "RESULT incremental gates: pass=$pass fail=$fail ($OUT/incr_gates.tsv)"
[ $fail = 0 ]
