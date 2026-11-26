#!/bin/bash
# tgt437-export.sh OUTDIR NAMES_FILE - per-declaration closure exports (one name per line in NAMES_FILE) of the given declarations from a cache-restored
# community-main tree (read-only), with the native 4.37 exporter (E1-437, lean4export-v4.37.0-rc1-c338a2c) in a bwrap sandbox
# without network; one export per name (OUTDIR/<k>.export + <k>.name + <k>.secs).
set -u
O=$1; NF=$2; mkdir -p "$O"
P=${FV_RHC_TREE:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/rh437/proj}; X=/scratch/fastverify-next/exporter/lean4export-v4.37.0-rc1-c338a2c
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.37.0-rc1
LP=$P/.lake/build/lib/lean; for d in $P/.lake/packages/*/.lake/build/lib/lean; do LP=$LP:$d; done
k=0
while IFS= read -r n; do [ -z "$n" ] && continue; k=$((k+1)); echo "$n" > "$O/$k.name"; t0=$(date +%s.%N)
  /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc --ro-bind "$P" "$P" --ro-bind "$TC" "$TC" --bind "$O" "$O" --clearenv --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_PATH "$LP" --setenv LEAN_NUM_THREADS 16 --setenv HOME /tmp --setenv LANG C.UTF-8 -- "$X" Main -- "$n" > "$O/$k.export" 2> "$O/$k.err"; rc=$?
  t1=$(date +%s.%N); printf "%s rc=%s %.1f s %s bytes\n" "$n" $rc $(echo "$t1 - $t0" | bc) $(stat -c %s "$O/$k.export") | tee "$O/$k.secs"
done < "$NF"
