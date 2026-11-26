#!/bin/bash
# export_kept.sh RUNDIR [CPUS] [MEM] [THREADS] - E1-437 export (the native 4.37 exporter, as export.sh calls it) of the Main closure
# of a kept bin/fastverify run tree whose official build finished outside the orchestrator (continue_build.sh), for the pinned
# targets of the RH challenge; same read-only package binds as the build; closure guard afterwards. Output RUNDIR/../export-kept/.
set -u
R=$1; CPUS=${2:-8-71}; MEM=${3:-256G}; T=${4:-64}
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.37.0-rc1
NATIVE=/scratch/fastverify-next/exporter/lean4export-v4.37.0-rc1-c338a2c
CLOSURE=/scratch/fastverify-next/exporter/closure_check-60b84139b18e
TARGETS=${BENCH_INPUTS:-/scratch/bench-inputs}/main437/targets.nl
CG=${CGRUN:-$(dirname "$(readlink -f "$0")")/cgrun.sh}
P=$R/work/proj; D=$(dirname "$R")/export-kept; mkdir -p "$D"
LPF=$(ls "$R"/log/*lean_path* 2>/dev/null | head -1)
if [ -n "$LPF" ]; then LP=$(tr -d '\n' < "$LPF"); else
  # the official build writes the lean path only after a successful build; the same path by construction: every bound
  # dependency's lib dir (binds.tsv destinations), the project's own lib dir, the toolchain's lib (as the build's leanpath.txt)
  LP=""
  while IFS=$'\t' read -r src dst; do [ -n "$src" ] && LP="${LP:+$LP:}$src/.lake/build/lib/lean"; done < "$R/log/binds.tsv"   # the real package dirs (the bind targets are empty on the host)
  LP="$LP:$P/.lake/build/lib/lean:$TC/lib/lean"
fi
echo "LEAN_PATH=$LP" > "$D/lean_path.txt"
NM=$(find "$P/.lake/build/lib/lean" -name '*.olean' 2>/dev/null | wc -l)
ARGS=(--ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home --tmpfs /run --tmpfs /var
      --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --bind "$P" "$P")
while IFS=$'\t' read -r src dst; do [ -n "$src" ] && ARGS+=(--ro-bind "$src" "$dst"); done < "$R/log/binds.tsv"
ARGS+=(--setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP"
       --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN4EXPORT_VERBOSE 1 --setenv LEAN4EXPORT_THREADS "$T")
[ "$NM" -gt 100000 ] && ARGS+=(--setenv LEAN4EXPORT_EXPR_ESTIMATE_LOG2 31)
ARGS+=(--unshare-all --die-with-parent --new-session --chdir "$P")
{ printf 'exec env -i /usr/bin/bwrap'; printf ' %q' "${ARGS[@]}" -- "$NATIVE" Main --; printf ' %s' $(cat "$TARGETS"); printf ' > %q 2> %q\n' "$D/solution.export" "$D/export.err"; } > "$D/export.cmd"
printf '#!/bin/bash\n%s' "$(cat "$D/export.cmd")" > "$D/export.sh"; chmod +x "$D/export.sh"
echo "$(date -u +%FT%TZ) export-kept: E1-437 on $P ($NM oleans, cpus $CPUS, mem $MEM, threads $T)"
"$CG" --name "fv-main437-export" --cpus "$CPUS" --mem "$MEM" --ps 5 --json "$D/cg.json" --timeline "$D/tl" --timeout 7200 -- "$D/export.sh" > "$D/export.log" 2>&1
rc=$?; EB=$(stat -c %s "$D/solution.export" 2>/dev/null || echo 0)
"$CLOSURE" "$D/solution.export" "$TARGETS" "$T" > "$D/closure.out" 2>&1; CRC=$?
SHA=$(sha256sum "$D/solution.export" | cut -c1-64); echo "$SHA  solution.export" > "$D/solution.export.sha256"
echo "$(date -u +%FT%TZ) export-kept: rc=$rc bytes=$EB closure_guard_rc=$CRC sha=$SHA $(tail -1 "$D/closure.out" | cut -c1-120)"
