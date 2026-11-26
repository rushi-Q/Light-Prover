#!/bin/bash
# defs/difffuzz.sh BASE CHALLENGE N SEED REFCMPD OUTDIR [KCOMPARE]: N structural mutants of the solution export BASE
# (an external structural mutator, not shipped: $MUTATE), judged by the official reference REFCMPD (RefCmpD.lean:
# Lean 4.36 Lake.Check compareAt + checkAxioms incl. definition targets) and by kcompare --definitions (default: the pinned
# binary of check/checkB/components.json). Prints "seed S: n=.. agree=.. disagree=.. declined=.."; disagreeing mutants are
# kept in OUTDIR (OUTDIR/disagree.txt), the rest deleted. Names = the defs/run.sh corpus (BASE = WORK/<case>/out.export).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); ROOT=$(cd "$H/../../../.." && pwd)
BASE=$1; CH=$2; N=$3; SEED=$4; REF=$5; O=$6
KC=${7:-$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["bin_dir"])' "$ROOT/check/checkB/components.json")/kcompare}
MUT=${MUTATE:?path of the export mutation tool mutate.py}
TH=foo,bar,baz; DF=myDef,myFun,idU,spare,pf; AX=propext,Quot.sound
W=$O/s$SEED; rm -rf "$W"; mkdir -p "$W"
python3 -I "$MUT" "$BASE" "$W" "$N" "$SEED" > /dev/null
ls "$W"/*.export > "$W/list.txt"
"$REF" "$CH" $TH $DF $AX --list "$W/list.txt" > "$W/ref.out" 2>&1
declare -A RF
while read -r tag rc f; do [ "$tag" = RESULT ] && RF[$f]=$rc; done < "$W/ref.out"
agree=0; dis=0; dec=0
for f in $(cat "$W/list.txt"); do
  out=$("$KC" -j 2 --challenge "$CH" --theorems $TH --definitions $DF --axioms $AX "$f" 2>&1); rc=$?; r=${RF[$f]:-X}
  if [ $rc = 2 ]; then dec=$((dec+1)); echo "DECLINE ref=$r $f :: $out" >> "$O/declines.txt"; rm -f "$f"
  elif [ "$rc" = "$r" ]; then agree=$((agree+1)); rm -f "$f"
  else dis=$((dis+1)); echo "DISAGREE ref=$r kcompare=$rc $f :: $out" | tee -a "$O/disagree.txt"; fi
done
echo "seed $SEED base $BASE: n=$N agree=$agree disagree=$dis declined=$dec"
