#!/bin/bash
# difftest.sh WORK NRUNS SEED [JOBS]  — random-target differential test of the native exporter against the official
# lean4export on the rh-mid environment (Mathlib 0df444a + rh-mid project, 1.1M constants). Each run picks a random
# number (1..4000, log-uniform) of random constant names as targets, exports with both exporters (same oleans, same
# targets, root Main) and compares bytes. PASS iff every run is IDENTICAL or the native exporter DECLINED (exit 2).
set -u
W=$1; N=$2; SEED=$3; J=${4:-8}
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=$(cd "$H/../../.." && pwd)
T33=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1
BI=${FV_BENCH_INPUTS:-/scratch/bench-inputs}
OFF=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["official"]["path"])' "$PKG/export/components.json")
NAT=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["native"]["path"])' "$PKG/export/components.json")
R=$BI/rh-mid/ref/proj; LP=$R/.lake/build/lib/lean
for p in $R/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done; LP=$LP:$T33/lib/lean
mkdir -p "$W"; cd "$W"
if [ ! -s names.txt ]; then
  # compiled ListConsts.lean (lake build with the official 4.33.1; `lean --run` hits vm.max_map_count on this env)
  LC=${LISTCONSTS:-}
  if [ -z "$LC" ]; then   # build the lister with the official 4.33.1 Lake (a few seconds)
    mkdir -p "$W/lister" && cp "$H/ListConsts.lean" "$W/lister/" && printf 'name = "listconsts"\ndefaultTargets = ["listconsts"]\n\n[[lean_exe]]\nname = "listconsts"\nroot = "ListConsts"\nsupportInterpreter = true\n' > "$W/lister/lakefile.toml"
    (cd "$W/lister" && env -i PATH=$T33/bin:/usr/bin:/bin HOME=/tmp $T33/bin/lake build > build.log 2>&1) || { echo "lister build failed"; exit 2; }
    LC=$W/lister/.lake/build/bin/listconsts
  fi
  (cd $R && env -i PATH=$T33/bin:/usr/bin:/bin LEAN_PATH=$LP "$LC" Main > "$W/names.txt" 2> "$W/names.err") || { echo "listing failed"; exit 2; }
fi
echo "names: $(wc -l < names.txt)"
/usr/bin/python3 -I - "$N" "$SEED" <<'PY'
import math, random, sys
n, seed = int(sys.argv[1]), int(sys.argv[2])
names = open("names.txt").read().split("\n")[:-1]
rnd = random.Random(seed)
for i in range(n):
    k = int(math.exp(rnd.uniform(0, math.log(4000))))
    with open(f"tg.{i}", "w") as f:
        f.write(" ".join(rnd.sample(names, k)) + "\n")
PY
one() {
  i=$1; cd "$R"
  read -r -d '' -a T < "$W/tg.$i"
  env -i PATH=$T33/bin:/usr/bin:/bin LEAN_PATH=$LP LEAN4EXPORT_THREADS=8 LEAN4EXPORT_VERBOSE=0 LEAN_ABORT_ON_PANIC=1 "$NAT" Main -- "${T[@]}" > "$W/nat.$i" 2> "$W/nat.$i.err"; nrc=$?
  env -i PATH=$T33/bin:/usr/bin:/bin LEAN_PATH=$LP LEAN_ABORT_ON_PANIC=1 "$OFF" Main -- "${T[@]}" > "$W/off.$i" 2> "$W/off.$i.err"; orc=$?
  if [ $nrc = 2 ]; then s="DECLINED($(grep -m1 '^lean4export (native): ' "$W/nat.$i.err" | cut -c23-90))"
  elif [ $nrc = 0 ] && [ $orc = 0 ] && cmp -s "$W/nat.$i" "$W/off.$i"; then s=IDENTICAL
  else s="DIFFERENT(native $nrc official $orc)"; fi
  echo "run $i targets=${#T[@]} bytes=$(stat -c %s "$W/off.$i") $s"
  [ "${s%%(*}" = DIFFERENT ] || rm -f "$W/nat.$i" "$W/off.$i"
}
export -f one; export W R LP T33 NAT OFF
seq 0 $((N-1)) | xargs -P "$J" -I{} bash -c 'one {}' | tee "$W/results.txt"
echo "SUMMARY: $(grep -c IDENTICAL "$W/results.txt") identical, $(grep -c DECLINED "$W/results.txt") declined, $(grep -c DIFFERENT "$W/results.txt") DIFFERENT of $N"
! grep -q DIFFERENT "$W/results.txt"
