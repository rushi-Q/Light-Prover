#!/bin/bash
# continue_build.sh RUNDIR [CPUS] [MEM] [THREADS] - continue the official `lake build` of a kept bin/fastverify run tree
# (RUNDIR/work/proj, --keep-work) after an external failure (here: the disk filled up at 122,149 of 146,883 modules),
# in the same bwrap sandbox as build/official-build.sh with the same read-only package binds (RUNDIR/log/binds.tsv), under one
# cgrun scope; the summed wall of the two parts is the cold official build time. Output RUNDIR/../continue/{build.log,cg.json}.
set -u
R=$1; CPUS=${2:-8-71}; MEM=${3:-256G}; T=${4:-64}
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.37.0-rc1
CG=${CGRUN:-$(dirname "$(readlink -f "$0")")/cgrun.sh}
P=$R/work/proj; D=$(dirname "$R")/continue; mkdir -p "$D"
ARGS=(--ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home --tmpfs /run --tmpfs /var
      --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --bind "$P" "$P")
while IFS=$'\t' read -r src dst; do [ -n "$src" ] && ARGS+=(--ro-bind "$src" "$dst"); done < "$R/log/binds.tsv"
ARGS+=(--setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_NUM_THREADS "$T"
       --unshare-all --die-with-parent --new-session --chdir "$P")
printf '%q ' env -i /usr/bin/bwrap "${ARGS[@]}" -- "$TC/bin/lake" build > "$D/cmd.txt"; echo >> "$D/cmd.txt"
cat > "$D/build.sh" <<EOS
#!/bin/bash
exec $(cat "$D/cmd.txt")
EOS
chmod +x "$D/build.sh"
echo "$(date -u +%FT%TZ) continue: lake build in $P (cpus $CPUS, mem $MEM, LEAN_NUM_THREADS=$T, $(wc -l < "$R/log/binds.tsv") binds)"
"$CG" --name "fv-main437-continue" --cpus "$CPUS" --mem "$MEM" --ps 30 --json "$D/cg.json" --timeline "$D/tl" --timeout 14400 -- "$D/build.sh" > "$D/build.log" 2>&1
rc=$?
echo "$(date -u +%FT%TZ) continue: rc=$rc built=$(grep -c Built "$D/build.log") $(tail -1 "$D/build.log" | tr -d '\r' | cut -c1-160)"
