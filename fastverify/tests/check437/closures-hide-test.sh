#!/bin/bash
# closures-hide-test.sh HIDEFILE OUTDIR [PAR] [JOBS] [CAP_S] - run pleanchecker-437e (pinned 4e5a3d1f) on each of the
# isolated closure exports ($CLOSURES/<k>.export, names in <k>.name) with the given hide list (PCHK_HIDE_FILE), PAR
# closures at a time, -j JOBS each, CAP_S seconds cap, inside bwrap without network. Writes OUTDIR/results.tsv (name, rc, wall s,
# max RSS KB, verdict line). Diagnostic only (availability of hide-list variants); no verdict of anything.
set -u
H=$1; O=$2; PAR=${3:-4}; J=${4:-4}; CAP=${5:-600}; B=${PLC:-/scratch/fastverify-next/sound/acf82e83/pleanchecker}; D=${CLOSURES:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/rh437/closures}   # PLC= / CLOSURES= / XENV=K=V overrides
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.37.0-rc1
mkdir -p "$O"; sha256sum "$H" "$B" > "$O/inputs.sha256"; : > "$O/results.tsv"
one() { k=$1; n=$(cat "$D/$k.name"); t0=$(date +%s.%N)
  timeout --kill-after=10 "$CAP" /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc \
    --ro-bind "$TC" "$TC" --ro-bind "$D" "$D" --ro-bind "$(dirname "$H")" "$(dirname "$H")" --ro-bind "$(dirname "$B")" "$(dirname "$B")" \
    --clearenv --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN_NUM_THREADS "$J" --setenv LEAN_STACK_SIZE_KB 917376 \
    --setenv PCHK_SLOW_MS 1000 --setenv PCHK_HIDE_FILE "$H" --setenv LANG C.UTF-8 ${XENV:+--setenv ${XENV%%=*} ${XENV#*=}} \
    -- /usr/bin/time -f "%e s %M KB" "$B" -j$J -v --from-export "$D/$k.export" > "$O/$k.out" 2> "$O/$k.err"; rc=$?
  t1=$(date +%s.%N); printf "%s\t%s\t%.1f\t%s\t%s\n" "$n" "$rc" "$(echo "$t1 - $t0" | bc)" "$(grep -o '[0-9.]* s [0-9]* KB' "$O/$k.err" | tail -1)" "$(tail -1 "$O/$k.out" | cut -c1-80)" >> "$O/results.tsv"; }
export -f one; export H O J CAP B D TC XENV
ls "$D"/*.name | sed 's#.*/##; s#\.name##' | sort -n | xargs -P "$PAR" -I{} bash -c 'one {}'
echo "[closures-hide-test] done $(date -u +%FT%TZ)"; sort -t$'\t' -k1,1 "$O/results.tsv"
