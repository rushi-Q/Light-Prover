#!/bin/bash
# gen.sh GENDIR [--heavy] : (re)generate the check-B regression inputs that are not stored in the repository, with the
# OFFICIAL Lean 4.33.1 + official lean4export v4.33.0 (068: flip.py forges one exported flag; 071: run_cmd addDecl of a
# deep binder nest; 005: the honest-looking export under a path containing /arena/suite/; --heavy: 044's 0.5 GB level chain)
# (whole body in main(): bash parses it completely before running, so editing this file cannot corrupt a running copy)
main() {
set -eu
G=$(mkdir -p "$1" && cd "$1" && pwd); H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); ROOT=$(cd "$H/../../.." && pwd)
X=$ROOT/tests; BENCH=${FV_BENCH_INPUTS:-/scratch/bench-inputs}     # finding inputs: tests/NNN-*/x snapshots
# the OFFICIAL Lean 4.33.1 and the official lean4export, as pinned in config/components.json
T33=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$ROOT/config/components.json")
EXP=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["official_lean4export"]["path"])' "$ROOT/config/components.json")
mkdir -p "$G/arena/suite"; cp $X/005-*/x/Main.export "$G/arena/suite/s.export"
if [ ! -s "$G/068/sol_Tree_numNested0.export" ]; then
  mkdir -p "$G/068"; D=$(ls -d $X/068-*/x); cp $D/Main.lean $D/Challenge.lean $D/mkexp.sh "$G/068/"
  ( cd "$G/068" && bash mkexp.sh Challenge main_thm > /dev/null 2>&1 && bash mkexp.sh Main main_thm > /dev/null 2>&1 && python3 -I $D/flip.py Main.export "$G/068" )
fi
# 056 negatives: the numeric projection of I4.get with an out-of-range index (1, 2): must stay rejected after fix-056
mkdir -p "$G/056neg"; E=$(ls $X/056-*/x/Main.export); L=$(grep -n '"typeName":122' "$E" | head -1 | cut -d: -f1)
for i in 1 2; do sed "${L}s/\"idx\":0/\"idx\":$i/" "$E" > "$G/056neg/sol-idx$i.export"; done
H=$(ls -d $X/071-*/x)
for N in 32766 32768 65535; do
  [ -s "$G/071/sol-A-$N.export" ] && continue
  mkdir -p "$G/071/w$N"; sed "s/^def bvN : Nat := 32768/def bvN : Nat := $N/" $H/Main.lean > "$G/071/w$N/Main.lean"
  ( cd "$G/071/w$N" && PATH=$T33/bin:$PATH lean -o Main.olean Main.lean > build.log 2>&1 && \
    LEAN_PATH=$PWD:$T33/lib/lean PATH=$T33/bin:$PATH $EXP Main -- $(cat $H/export-targets.txt) > "$G/071/sol-A-$N.export" )
done
if [ "${2:-}" = --heavy ] && [ ! -s "$G/039/late-sparse.export" ]; then
  # 039: rh-mid + ONE trailing sparse-index name record (legal for Lean's parser; official nanoda declines it)
  mkdir -p "$G/039"; cp $BENCH/rh-mid/ref/solution.export "$G/039/late-sparse.export"
  echo '{"in":999999999,"str":{"pre":0,"str":"zzzLateSparse"}}' >> "$G/039/late-sparse.export"
fi
if [ "${2:-}" = --heavy ] && [ ! -s "$G/044/sol-level.export" ]; then
  mkdir -p "$G/044"; python3 -I $X/044-*/x/deeplevel.py $X/044-*/x/Main.export 16777216 "$G/044/sol-level.export"
fi
echo "gen.sh: inputs in $G"
}
main "$@"; exit $?
