#!/bin/bash
# tests/gruszka-worker-retry/run.sh [WORKDIR] - regression test of an availability defect: the gruszka
# leg of every judge (check-sound, check-sound-svc, check-sound-lowmem, check-sound-ultralowmem; check-notary once it carries
# the hunk) retries a decline that is ONLY for worker-table room ("declined: NAME: a worker table is full") ONCE with 1
# worker and keeps that answer; a rejection or any other decline is never retried.
# Part 1 (always): the wrapper exactly as each judge script writes it (its heredoc, expanded with a test W / T = 16), with
#   the pinned binary replaced by a stub that declines for room above a worker threshold. Rows: worker counts used, status.
# Part 2 (F35_OM_EXPORT=DIR with solution.export, challenge.export, comparator.json - e.g. the recorded OM MultitapeWeakETH
#   case, 2.87 GB: gruszka v3 declines at 4 / 8 / 100 workers and accepts with 1 worker): check-sound.sh --threads ${F35_OM_THREADS:-100}
#   must give ACCEPTED (an INFO line says whether the first parallel attempt declined and the retry decided - the schedule
#   decides that, so it is not asserted). Skipped without F35_OM_EXPORT
# Part 3 (F35_E2E_COPY=DIR, a scratch COPY of the package): end to end through the four judges with a stub gruszka (the judged
#   export declines for room above 1 worker, everything else = the pinned binary) via test pins files written in the copy:
#   ACCEPTED, JSON legs.k2.retry = {reason, first_rc 2, workers 1}, the first attempt's log printed. (the export is too large for the repository).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd)
W0=${1:-$(mktemp -d /tmp/f35-test.XXXXXX)}; mkdir -p "$W0"; P=0; F=0
ok() { if [ "$2" = "$3" ]; then echo "PASS $1 ($2)"; P=$((P+1)); else echo "FAIL $1: got '$2', want '$3'"; F=$((F+1)); fi; }
STUB=$W0/stub-gruszka
cat > "$STUB" <<'ST'
#!/bin/sh
# stub: MODE in $STUB_MODE; the worker count is the last argument; every call appended to $STUB_CALLS
for a; do w=$a; done; echo "$w" >> "$STUB_CALLS"
case $STUB_MODE in
  room) if [ "$w" -gt "$STUB_OK_AT" ]; then echo "note: $w workers"; echo "declined: Big.decl: a worker table is full"; exit 2; fi; echo accepted; exit 0;;
  room-reject) if [ "$w" -gt "$STUB_OK_AT" ]; then echo "declined: Big.decl: a worker table is full"; exit 2; fi; echo "rejected: Bad.decl: type mismatch"; exit 1;;
  reject) echo "rejected: Bad.decl: type mismatch"; exit 1;;
  other) echo "declined: X: recursion too deep (stack limit)"; exit 2;;
  spoof) echo "declined: X: a worker table is full: unknown constant"; exit 2;;
  two) echo "declined: A: a worker table is full"; echo "declined: B: a worker table is full"; exit 2;;
  withrej) echo "rejected: Y: bad"; echo "declined: A: a worker table is full"; exit 2;;
  nlname) printf 'declined: X: a worker table is full\nY: recursion too deep (stack limit)\n'; exit 2;;
  nolf) if [ "$w" -gt 1 ]; then printf 'declined: Big.decl: a worker table is full'; exit 2; fi; echo accepted; exit 0;;
  cont) if [ "$w" -gt 1 ]; then printf 'declined: Big.decl: a worker table is full\n  continued diagnostic\n'; exit 2; fi; echo accepted; exit 0;;
  note) if [ "$w" -gt 1 ]; then echo "note: 8 workers (the block arenas of 16 do not fit)"; echo "declined: Big.decl: a worker table is full"; exit 2; fi; echo accepted; exit 0;;
  rc3) echo "declined: Big.decl: a worker table is full"; exit 3;;
  slow) if [ "$w" -gt 1 ]; then echo "declined: Big.decl: a worker table is full"; exit 2; fi; sleep 8; echo accepted; exit 0;;
  term) if [ "$w" -gt 1 ]; then echo "declined: Big.decl: a worker table is full"; exit 2; fi; kill -TERM $$; sleep 5; echo accepted; exit 0;;
  digest) echo partial > "$GRUSZKA_DIGEST_OUT.seen-$w"; [ -e "$GRUSZKA_DIGEST_OUT" ] && echo stale > "$GRUSZKA_DIGEST_OUT.stale-$w"
          echo "digest-$w" > "$GRUSZKA_DIGEST_OUT"; if [ "$w" -gt 1 ]; then echo "declined: Big.decl: a worker table is full"; exit 2; fi; echo accepted; exit 0;;
esac
ST
chmod 755 "$STUB"
# gen SCRIPT DIR: write DIR/bin/gruszka-kernel with SCRIPT's own heredoc (W=DIR, T=T_EFF=16, the binary = the stub)
gen() {
  local blk; blk=$(awk '/^cat > "\$W\/bin\/gruszka-kernel" <<EOF$/{p=1} p{print} p&&/^EOF$/{exit}' "$1")
  [ -n "$blk" ] || { echo "FAIL $(basename "$1"): no gruszka-kernel heredoc"; F=$((F+1)); return 1; }
  grep -q 'a worker table is full' <<< "$blk" || { echo "FAIL $(basename "$1"): heredoc without the worker-room retry"; F=$((F+1)); return 1; }
  mkdir -p "$2/bin" "$2/tmp"; W=$2 GRUSZKA=$STUB T=16 T_EFF=${4:-16} GRZ_LM_ARGS= DL=${3:-0} bash -c "$blk"; chmod 755 "$2/bin/gruszka-kernel"
}
run() {  # run DIR MODE OK_AT -> "rc|calls|leg.rc"
  : > "$1/calls"; rm -f "$1"/tmp/*
  STUB_MODE=$2 STUB_OK_AT=${3:-0} STUB_CALLS=$1/calls "$1/bin/gruszka-kernel" "$1/solution.export" > /dev/null 2>&1; local rc=$?
  echo "$rc|$(tr '\n' ' ' < "$1/calls" | sed 's/ $//')|$(cat "$1/tmp/leg-k2.rc" 2>/dev/null)"
}
SCRIPTS="check/sound/check-sound.sh check/sound/check-sound-svc.sh check/lowmem/check-sound-lowmem.sh check/lowmem/check-sound-ultralowmem.sh"
[ -n "${F35_WITH_NOTARY:-}" ] && SCRIPTS="$SCRIPTS check/notary/check-notary.sh"
for s in $SCRIPTS; do
  n=$(basename "$s" .sh); D=$W0/$n; gen "$FV/$s" "$D" || continue
  ok "$n room, accepts with 1 worker: 16 -> 1, ACCEPTED"   "$(run "$D" room 1)" "0|16 1|0"
  ok "$n room with 1 worker too: one retry, DECLINED"       "$(run "$D" room 0)" "2|16 1|2"
  ok "$n room, then a rejection with 1 worker: REJECTED"    "$(run "$D" room-reject 1)" "1|16 1|1"
  ok "$n accepted at once: no retry"                        "$(run "$D" room 16)" "0|16|0"
  ok "$n rejection: never retried"                          "$(run "$D" reject)" "1|16|1"
  ok "$n other decline reason: never retried"               "$(run "$D" other)" "2|16|2"
  ok "$n reason only CONTAINING the text: never retried"    "$(run "$D" spoof)" "2|16|2"
  ok "$n two declined lines: never retried"                 "$(run "$D" two)" "2|16|2"
  ok "$n a rejected line next to the decline: never retried" "$(run "$D" withrej)" "2|16|2"
  ok "$n a name with a newline imitating the line (not the last line): never retried" "$(run "$D" nlname)" "2|16|2"
  ok "$n log without a final newline (cut): never retried" "$(run "$D" nolf)" "2|16|2"
  ok "$n a continuation line after the decline: never retried" "$(run "$D" cont)" "2|16|2"
  ok "$n a 'note:' line before the decline: retried" "$(run "$D" note)" "0|16 1|0"
  ok "$n the line with exit 3 (not exactly 2): never retried" "$(run "$D" rc3)" "3|16|3"
  r=$(: > "$D/calls"; rm -f "$D"/tmp/*; STUB_MODE=room STUB_OK_AT=1 STUB_CALLS=$D/calls "$D/bin/gruszka-kernel" "$D/selftest-good.export" > /dev/null 2>&1; echo "$?|$(tr '\n' ' ' < "$D/calls" | sed 's/ $//')")
  ok "$n a self-test leg: never retried" "$r" "2|16"
  r=$(run "$D" term 1); ok "$n a retry ended by SIGTERM: exit 143 recorded (no verdict)" "$r" "143|16 1|143"
  # the low-memory judges start gruszka with T_EFF (the memory-capped worker count), the others with T
  gen "$FV/$s" "$D" 0 2
  case $n in *lowmem*) want="0|2 1|0";; *) want="0|16 1|0";; esac
  ok "$n T=16, T_EFF=2: first attempt with the judge's own worker count, then 1" "$(run "$D" room 1)" "$want"
  gen "$FV/$s" "$D" "$(( $(date +%s) - 1 ))"
  ok "$n no time left in the --timeout budget: no retry" "$(run "$D" room 1)" "2|16|2"
  ok "$n ... and the first attempt is archived with the reason" "$(grep -c 'no time left' "$D/tmp/leg-k2-retries.log")" "1"
  gen "$FV/$s" "$D" "$(( $(date +%s) + 3 ))"
  r=$(run "$D" slow 1); ok "$n a retry over the remaining budget is killed: no verdict (124)" "${r%%|*}|${r#*|}" "124|16 1|124"
  gen "$FV/$s" "$D"
  run "$D" room 1 > /dev/null; ok "$n retry marker leg-k2.retry = first exit status" "$(cat "$D/tmp/leg-k2.retry" 2>/dev/null)" "2"
  run "$D" other > /dev/null; ok "$n no retry marker without a retry" "$([ -e "$D/tmp/leg-k2.retry" ] && echo present || echo absent)" "absent"
  run "$D" room 1 > /dev/null; ok "$n the first attempt is kept in leg-k2-retries.log" "$(grep -c 'again with 1 worker' "$D/tmp/leg-k2-retries.log")" "1"
  if [ "$n" = check-notary ]; then
    run "$D" digest > /dev/null
    ok "$n retry removes the partial R7 digest first" "$(ls "$D/tmp" | grep -c '\.stale-')" "0"
    ok "$n the digest is the final run's" "$(cat "$D/tmp/digest-k2.txt" 2>/dev/null)" "digest-1"
  fi
done
if [ -n "${F35_E2E_COPY:-}" ]; then   # end to end through the four judges (JSON legs.k2.retry, retries log printed)
  C=$(readlink -f "$F35_E2E_COPY"); [ "$C" != "$FV" ] || { echo "FAIL F35_E2E_COPY must be a scratch COPY, not this package"; F=$((F+1)); C=; }
fi
if [ -n "${C:-}" ]; then
  REAL=$(awk '$1=="PIN" && $2=="gruszka"{print $4}' "$C/check/sound/pins.env"); RL=$(awk '$1=="PIN" && $2=="gruszka_lowmem"{print $4}' "$C/check/lowmem/pins-ultralowmem.env")
  # mkstub FILE REAL [MODE]: the judged export declines for room above 1 worker; with 1 worker MODE: exec (the pinned
  # binary decides), slow (sleeps 120 s), term (killed by SIGTERM); everything else (self-tests) = the pinned binary
  mkstub() { local tail1="exec $2 \"\$@\""; case ${3:-exec} in slow) tail1='sleep 120; echo accepted; exit 0';; term) tail1='kill -TERM $$; sleep 5; exit 0';; esac
    printf '#!/bin/sh\nfor a; do w=$a; done\nj=0; for a; do case "$a" in */solution.export|*/solution.ndjson) j=1;; esac; done\n[ $j = 1 ] || exec %s "$@"\necho "note: stub workers=$w"\n[ "$w" -gt 1 ] && { echo "declined: Big.decl: a worker table is full"; exit 2; }\n%s\n' "$2" "$tail1" > "$1"; chmod 755 "$1"; }
  # the stubs live in the copy (the judges' sandboxes hide /tmp, /home, /var and /run)
  SD=$C/f35e2e-stubs; mkdir -p "$SD"; mkstub "$SD/stub" "$REAL"; mkstub "$SD/stub-lm" "$RL"; SS=$(sha256sum "$SD/stub" | cut -d' ' -f1); SL=$(sha256sum "$SD/stub-lm" | cut -d' ' -f1)
  repin() { awk -v k="$1" -v s="$2" -v p="$3" '$1=="PIN" && $2==k {$3=s; $4=p} {print}' "$4"; }
  repin gruszka "$SS" "$SD/stub" "$C/check/sound/pins.env" > "$C/check/sound/pins-f35e2e.env"
  repin gruszka "$SS" "$SD/stub" "$C/check/lowmem/pins.env" > "$C/check/lowmem/pins-f35e2e.env"
  cp -p "$C/check/lowmem/pins-ultralowmem.env" "$W0/pins-ultralowmem.env.orig"
  repin gruszka_lowmem "$SL" "$SD/stub-lm" "$W0/pins-ultralowmem.env.orig" > "$C/check/lowmem/pins-ultralowmem.env"
  pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$C/check/sound/pins.env"; }
  G=$(pin selftest_good); CH=$(pin selftest_challenge); CF=$(pin selftest_comparator)
  e2e_one() {  # e2e_one SUBDIR NAME [PINS]
    local n=$2 rc r; local pa=(); [ -n "${3:-}" ] && pa=(--pins "$3")
    (cd /tmp && "$C/check/$1/$n.sh" "$G" "$CH" "$CF" --threads 4 "${pa[@]}" --json "$W0/e2e-$n.json" --log "$W0/e2e-$n.log" > /dev/null 2>&1); rc=$?
    ok "$n end to end: room decline at 4 workers -> retry -> ACCEPTED" "$rc" "0"
    ok "$n end to end: JSON legs.k2.retry" "$(/usr/bin/python3 -I -c 'import json,sys; print(json.dumps(((json.load(open(sys.argv[1])).get("legs") or {}).get("k2") or {}).get("retry"), sort_keys=True))' "$W0/e2e-$n.json" 2>/dev/null)" '{"first_rc": 2, "reason": "a worker table is full", "workers": 1}'
    r=no; grep -q -- '--- leg-k2-retries.log' "$W0/e2e-$n.log" && r=yes; ok "$n end to end: the first attempt's log is printed" "$r" "yes"
  }
  e2e_one sound check-sound "$C/check/sound/pins-f35e2e.env"; e2e_one sound check-sound-svc "$C/check/sound/pins-f35e2e.env"
  e2e_one lowmem check-sound-lowmem "$C/check/lowmem/pins-f35e2e.env"; e2e_one lowmem check-sound-ultralowmem
  # under --threads 16 --mem-budget-mb 512 the low-memory judges cap their workers (T_EFF); the first
  # gruszka attempt must use that capped count, the retry 1
  for j in "check-sound-lowmem:$C/check/lowmem/pins-f35e2e.env" "check-sound-ultralowmem:"; do
    n=${j%%:*}; pf=${j#*:}; pa=(); [ -n "$pf" ] && pa=(--pins "$pf")
    (cd /tmp && "$C/check/lowmem/$n.sh" "$G" "$CH" "$CF" --threads 16 --mem-budget-mb 512 "${pa[@]}" --json "$W0/e2e-cap-$n.json" --log "$W0/e2e-cap-$n.log" > /dev/null 2>&1); rc=$?
    cap=$(grep -o 'capping worker threads 16 -> [0-9]*' "$W0/e2e-cap-$n.log" | head -1 | awk '{print $NF}')
    seen=$(grep -o 'note: stub workers=[0-9]*' "$W0/e2e-cap-$n.log" | cut -d= -f2 | sort -n | tr '\n' ' ' | sed 's/ $//')
    ok "$n --threads 16 --mem-budget-mb 512: ACCEPTED" "$rc" "0"
    ok "$n ... the attempts used 1 and the capped worker count (${cap:-?}), never 16" "$seen" "1 ${cap:-none}"
  done
  # through check-sound: a retry over the remaining --timeout budget, and a retry killed by SIGTERM
  for m in slow term; do
    mkstub "$SD/stub-$m" "$REAL" "$m"; repin gruszka "$(sha256sum "$SD/stub-$m" | cut -d' ' -f1)" "$SD/stub-$m" "$C/check/sound/pins.env" > "$C/check/sound/pins-f35e2e-$m.env"
  done
  KB=$(pin selftest_kbad)
  cs() { (cd /tmp && "$C/check/sound/check-sound.sh" "$1" "$CH" "$CF" --threads 4 --pins "$C/check/sound/pins-f35e2e-$2.env" ${3:+--timeout $3} --json "$W0/e2e-$4.json" --log "$W0/e2e-$4.log" > /dev/null 2>&1); echo $?; }
  t0=$(date +%s); r=$(cs "$G" slow 30 slow); t1=$(date +%s)
  ok "check-sound retry over the --timeout 30 budget (good export): DECLINED, never ACCEPTED" "$r" "2"
  ok "check-sound ... within the budget (<= 30 + 35 s)" "$([ $((t1 - t0)) -le 65 ] && echo yes || echo "no ($((t1 - t0)) s)")" "yes"
  ok "check-sound retry killed by SIGTERM, good export (official leg accepts): DECLINED" "$(cs "$G" term '' term-good)" "2"
  ok "check-sound ... JSON legs.k2.rc = 143" "$(/usr/bin/python3 -I -c 'import json,sys; print(((json.load(open(sys.argv[1])).get("legs") or {}).get("k2") or {}).get("rc"))' "$W0/e2e-term-good.json" 2>/dev/null)" "143"
  [ -n "$KB" ] && ok "check-sound retry killed by SIGTERM, kernel-invalid export: REJECTED by the official leg (existing rule)" "$(cs "$KB" term '' term-kbad)" "1"
  rm -f "$C/check/sound/pins-f35e2e-slow.env" "$C/check/sound/pins-f35e2e-term.env"
  cp -p "$W0/pins-ultralowmem.env.orig" "$C/check/lowmem/pins-ultralowmem.env"; rm -rf "$C/check/sound/pins-f35e2e.env" "$C/check/lowmem/pins-f35e2e.env" "$SD"
else
  echo "SKIP end to end through the judges (set F35_E2E_COPY=a scratch copy of the package; test pins files are written there)"
fi
if [ -n "${F35_OM_EXPORT:-}" ]; then
  E=$F35_OM_EXPORT
  "$FV/check/sound/check-sound.sh" "$E/solution.export" "$E/challenge.export" "$E/comparator.json" --threads "${F35_OM_THREADS:-100}" \
    --json "$W0/om.json" --log "$W0/om.log" > /dev/null 2>&1; rc=$?
  ok "OM recorded case: check-sound ACCEPTED (was DECLINED: worker table full)" "$rc" "0"
  # the first (parallel) attempt may accept or decline - the schedule decides; report which
  if grep -q 'declined for worker-table room' "$W0/om.log"; then echo "INFO OM recorded case: first attempt DECLINED for room, the 1-worker retry decided"
  else echo "INFO OM recorded case: the first attempt decided (no retry needed this time)"; fi
else
  echo "SKIP OM recorded case (set F35_OM_EXPORT=DIR with solution.export, challenge.export, comparator.json)"
fi
echo "gruszka-worker-retry: $P passed, $F failed"; [ -n "${1:-}" ] || rm -rf "$W0"; [ $F = 0 ]
