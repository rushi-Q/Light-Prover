#!/bin/bash
# legs.sh OUTDIR LABEL INDIR CPUBASE "T1 T2 ..." [LEGS]
#   each leg of the trusted check ALONE under cgrun (memory unlimited), once per thread count T:
#     plc    = pleanchecker -jT -v EXPORT            (the official-kernel leg, exactly the wrapper's environment)
#     grz    = gruszka EXPORT T                      (the second kernel)
#     ccmp   = ccmp with STUB kernels (compare = parse + compareAt + checkAxioms only; stubs exit 0 at once)
#   The binaries and paths come from check/sound/pins.env (sha256 re-checked here). Measurement only: no verdict is
#   produced or recorded anywhere but OUTDIR. JSON per run: OUTDIR/<LABEL>.<leg>.T<T>.json (existing = skipped).
set -u
OUT=$1; LABEL=$2; IN=$3; CPUBASE=$4; TS=$5; LEGS=${6:-"plc grz ccmp"}
FV=${FV:-$LIGHT_LEAN/fastverify}
CG=${CGRUN:-$(dirname "$(readlink -f "$0")")/cgrun.sh}
mkdir -p "$OUT"
E=$IN/solution.export; C=$IN/challenge/challenge.export; J=$IN/challenge/comparator.json
PINS=$FV/check/sound/pins.env
declare -A P S
while read -r tag name sum path; do [ "$tag" = PIN ] && { P[$name]=$path; S[$name]=$sum; }; done < "$PINS"
for n in ccmp pleanchecker gruszka; do
  [ "$(sha256sum "${P[$n]}" | cut -d' ' -f1)" = "${S[$n]}" ] || { echo "pin mismatch $n"; exit 2; }
done
TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
W=$OUT/.w.$LABEL; rm -rf "$W"; mkdir -p "$W/bin" "$W/home" "$W/tmp"
printf '#!/bin/sh\nexit 0\n' > "$W/bin/stubkernel"; chmod 755 "$W/bin/stubkernel"
printf '#!/bin/sh\ncommand -v "$1"\n' > "$W/bin/which"; chmod 755 "$W/bin/which"
/usr/bin/python3 -I -c '
import json,sys
c=json.load(open(sys.argv[1])); c.pop("enable_nanoda",None); c["external_kernels"]={"stub (second kernel)":[sys.argv[3]]}
json.dump(c,open(sys.argv[2],"w"))' "$J" "$W/comparator.json" "$W/bin/stubkernel"
run1() { # tag threads cmd...
  local tag=$1 t=$2; shift 2
  [ -s "$OUT/$tag.json" ] && { echo "skip $tag"; return; }
  local cpus="$CPUBASE-$(( CPUBASE + t - 1 ))"
  echo "$(date -u +%FT%TZ) start $tag threads=$t cpus=$cpus"
  "$CG" --name "lg-$tag" --cpus "$cpus" --json "$OUT/$tag.json.part" --timeline "$OUT/$tag.tl" --timeout 7200 -- "$@" > "$OUT/$tag.out" 2>&1
  local rc=$?
  mv "$OUT/$tag.json.part" "$OUT/$tag.json"
  echo "$(date -u +%FT%TZ) done  $tag rc=$rc $(grep -a -m1 -E 'accepts|rejected|error|RESULT|verdict' "$OUT/$tag.out" | cut -c1-120)"
}
for t in $TS; do
  for leg in $LEGS; do
    case $leg in
      plc)  run1 "$LABEL.plc.T$t" "$t" env -i PATH=/usr/bin:/bin LANG=C.UTF-8 LEAN_ABORT_ON_PANIC=1 PCHK_SLOW_MS=10000 LEAN_STACK_SIZE_KB=917376 LEAN_NUM_THREADS=$t "${P[pleanchecker]}" -j$t -v "$E";;
      grz)  run1 "$LABEL.grz.T$t" "$t" env -i PATH=/usr/bin:/bin LANG=C.UTF-8 "${P[gruszka]}" "$E" "$t";;
      ccmp) run1 "$LABEL.ccmp.T$t" "$t" env -i PATH="$W/bin:$TC36/bin:/usr/bin:/bin" HOME="$W/home" TMPDIR="$W/tmp" LANG=C.UTF-8 LEAN_ABORT_ON_PANIC=1 LEAN_NUM_THREADS=$t CCMP_LEANCHECKER="$W/bin/stubkernel" "${P[ccmp]}" "$TC36" "$W/comparator.json" "$C" "$E";;
    esac
  done
done
echo LEGS_DONE
