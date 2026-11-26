#!/bin/bash
# resmatrix.sh OUT : the UNMODIFIED check-sound.sh under resource limits (address space, stack, open files, file size,
# processes, CPU time, its own --timeout) on honest and rejected exports. Pass: a rejected case is never ACCEPTED; an honest
# export is ACCEPTED or gets no verdict (DECLINED / no output), never REJECTED.
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
OUT=$1; mkdir -p "$OUT"; CS=$FV/check/sound/check-sound.sh; : > "$OUT/rows.tsv"
cases=()
for b in ind quot univ hole lit; do base_inputs $b && cases+=("honest-$b|$SOL|$CH|$CFG|ACCEPTED"); done
if base_inputs cmpx; then
  for x in reject-illegal-axiom reject-kernel-only-illtyped-extra-def reject-stmt-true; do cases+=("$x|$CMPX_DIR/$x.ndjson|$CH|$CFG|REJECTED"); done
fi
if [ -d "$W/seams/ind" ]; then base_inputs ind; for x in A4-target-proof-via-unsafe-def G5-second-thm-bogus C_dummy; do
  [ -f "$W/seams/ind/ind-$x.ndjson" ] && cases+=("seam-$x|$W/seams/ind/ind-$x.ndjson|$CH|$CFG|REJECTED"); done; fi
limits=( "none|:" "as1G|ulimit -v 1048576" "as3G|ulimit -v 3145728" "as8G|ulimit -v 8388608" "stack256K|ulimit -s 256" "stack64M|ulimit -s 65536"
         "nofile16|ulimit -n 16" "nofile64|ulimit -n 64" "fsize1M|ulimit -f 2048" "fsize64M|ulimit -f 131072" "nproc64|ulimit -u 64"
         "cpu2s|ulimit -t 2" "timeout1|TMO" )
for c in "${cases[@]}"; do IFS='|' read -r name e ch cfg want <<< "$c"
  for l in "${limits[@]}"; do IFS='|' read -r lname lcmd <<< "$l"
    extra=""; pre=$lcmd; [ "$lcmd" = TMO ] && { extra="--timeout 1"; pre=:; }
    v=$(bash -c "$pre; exec \"$CS\" \"$e\" \"$ch\" \"$cfg\" --threads 4 --hints none $extra" 2>/dev/null | tail -1 | python3 -I -c 'import json,sys
try: j=json.load(sys.stdin); print(j["verdict"]+"\t"+j.get("reason","")[:120])
except Exception: print("NO-OUTPUT\t(no JSON line: the script could not start)")')
    vv=${v%%$'\t'*}; st=PASS
    [ "$want" = REJECTED ] && [ "$vv" = ACCEPTED ] && st=FAIL-CRITICAL
    [ "$want" = ACCEPTED ] && [ "$vv" = REJECTED ] && st=FAIL-REJECT
    [ "$vv" != "$want" ] && [ "$st" = PASS ] && st=PASS-NOVERDICT
    printf '%s\t%s\t%s\twant=%s\t%s\n' "$st" "$name" "$lname" "$want" "$v" >> "$OUT/rows.tsv"
  done
done
cut -f1 "$OUT/rows.tsv" | sort | uniq -c
! grep -q '^FAIL' "$OUT/rows.tsv"
