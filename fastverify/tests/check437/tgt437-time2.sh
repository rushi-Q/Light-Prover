#!/bin/bash
# tgt437-time.sh DIR [THREADS] [TIMEOUT_S] - for each per-declaration closure export DIR/<k>.export (as produced by
# tgt437-export.sh; waits for <k>.secs to appear): time pleanchecker-437 (-v, PCHK_SLOW_MS=1000: every job >= 1 s is named at
# the end) and the OFFICIAL 4.37 leanchecker on it, each sandboxed, with a wall-clock timeout and max-RSS recording.
# Results DIR/<k>.plc.{out,time} and DIR/<k>.lc.{out,time}, summary DIR/timing.tsv. Untrusted diagnostics.
# v2: /usr/bin/time runs INSIDE the sandbox (rusage does not cross bwrap's pid namespace), so max RSS is the checker's own.
set -u
DIR=$1; T=${2:-4}; TMO=${3:-900}
PLC=/scratch/fastverify-next/sound/acf82e83/pleanchecker; TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.37.0-rc1
TSV=$DIR/timing.tsv; [ -f "$TSV" ] || echo -e "k\tname\tbytes\tplc_rc\tplc_wall_s\tplc_maxrss_GB\tplc_longest\tlc_rc\tlc_wall_s\tlc_maxrss_GB" > "$TSV"
sb() { /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc --ro-bind "$TC" "$TC" --bind "$DIR" "$DIR" --clearenv --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN_NUM_THREADS "$T" --setenv LEAN_STACK_SIZE_KB 917376 --setenv PCHK_SLOW_MS 1000 --setenv LANG C.UTF-8 -- "$@"; }
k=0
while k=$((k+1)); [ $k -le 20 ]; do
  f=$DIR/$k.export; sec=$DIR/$k.secs
  n=0; while [ ! -f "$sec" ]; do sleep 20; n=$((n+1)); [ $n -gt 90 ] && break 2; done   # wait up to 30 min for the next export
  [ -f "$sec" ] || break
  name=$(cat "$DIR/$k.name"); bytes=$(stat -c %s "$f"); [ "$bytes" -lt 1000 ] && { echo -e "$k\t$name\t$bytes\tSKIP(empty)" >> "$TSV"; continue; }
  timeout --kill-after=10 $TMO /bin/bash -c "$(declare -f sb); TC=$TC; DIR=$DIR; T=$T; sb /usr/bin/time -f '%e %M' -o $DIR/$k.plc.time $PLC -j$T -v --from-export $f" > "$DIR/$k.plc.out" 2>&1; prc=$?
  read pw pm < "$DIR/$k.plc.time" 2>/dev/null || { pw=-; pm=0; }; [ "$prc" = 124 ] && pw="TIMEOUT($TMO)"
  longest=$(grep -o "longest job [0-9]* ms ([^)]*" "$DIR/$k.plc.out" | tail -1 | cut -c1-80)
  timeout --kill-after=10 $TMO /bin/bash -c "$(declare -f sb); TC=$TC; DIR=$DIR; T=$T; sb /usr/bin/time -f '%e %M' -o $DIR/$k.lc.time $TC/bin/leanchecker --from-export $f" > "$DIR/$k.lc.out" 2>&1; lrc=$?
  read lw lm < "$DIR/$k.lc.time" 2>/dev/null || { lw=-; lm=0; }; [ "$lrc" = 124 ] && lw="TIMEOUT($TMO)"
  echo -e "$k\t$name\t$bytes\t$prc\t$pw\t$(awk -v m=$pm 'BEGIN{printf "%.1f", m/1048576}')\t${longest:-}\t$lrc\t$lw\t$(awk -v m=$lm 'BEGIN{printf "%.1f", m/1048576}')" | tee -a "$TSV"
done
echo "[tgt437-time] done"; cat "$TSV"
