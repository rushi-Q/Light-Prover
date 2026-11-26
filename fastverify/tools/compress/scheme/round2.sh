#!/bin/bash
# round2.sh TREE REFS_DIR WORK OUTC [OTHER_EDITS...] -- second pruning round on an ACCEPTED candidate tree: ../prune/prune.py
# with the closure recomputed from the candidate's OWN oleans (refs from refs.sh over its build tree), then dropempty ->
# normalize (+dfsverify) -> chainmerge (+cm_deny, iterated) -> OUTC/t2.tar.gz.
# env: FV_PACKAGES (Lake workspace with the materialized dependencies, default $LIGHT_LEAN/verify/challenge), ELAN_HOME.
set -u
TREE=$1; REFS=$2; R=$3; C=$4; shift 4; OTHER=("$@")   # edit lists applied together with this round: --other-edits (inside the fixpoint)
rm -rf $R; mkdir -p $R $C
FV=${FV:-$(cd "$(dirname "$0")/../../.." && pwd)}; PR=$FV/tools/compress/prune; N=$FV/tools/compress/normalize
TOOLS=${TOOLS:-$FV/tools/compress/scheme}
WSP=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}/.lake/packages
TCS=$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/src/lean
ts() { date +%s.%N; }
exec > >(tee $C/round2.log) 2>&1
echo "== round2 $(date -u +%FT%TZ) TREE=$TREE REFS=$REFS"
t0=$(ts); python3 -I $PR/refs_index.py $R/index.pkl $REFS/c0*.tsv; echo "refs_index rc=$? $(echo "$(ts) - $t0" | bc) s"
t0=$(ts); python3 -I $PR/prune.py $R/index.pkl $TREE $R/t0 --drop-empty-modules --ext-namespaces $PR/data/ext_namespaces-mathlib0df444a-lean4.33.1.txt --report $R/prune.json ${OTHER[@]:+--other-edits "${OTHER[@]}"} 2>&1 | grep -v '^  *"' | tail -8; echo "prune rc=$? $(echo "$(ts) - $t0" | bc) s"
python3 -c "import json; d=json.load(open('$R/prune.json')); r=d.get('report',d); print({k:v for k,v in r.items() if not isinstance(v,(dict,list))})"
python3 -I $PR/fixlake.py $R/t0; cp $TREE/lake-manifest.json $R/t0/ 2>/dev/null
t0=$(ts); python3 -I $N/dropempty.py $R/t0 $R/t0e; echo "dropempty rc=$? $(echo "$(ts) - $t0" | bc) s"; cp $TREE/lake-manifest.json $R/t0e/ 2>/dev/null; python3 -I $PR/fixlake.py $R/t0e
t0=$(ts); python3 -I $N/normalize.py $R/t0e --packages $WSP --toolchain-src $TCS --classes ${NORM_CLASSES:-imp,opt,optres} --edits $R/norm.tsv --json $R/norm.json --graph-out $R/g; echo "normalize rc=$? $(echo "$(ts) - $t0" | bc) s"
g++ -O2 -std=c++17 -pthread -o $R/dfsverify $N/dfsverify/dfsverify.cpp && $R/dfsverify $R/g.old.txt $R/g.new.txt $R/g.roots.txt 16; echo "dfsverify rc=$?"; rm -f $R/g.*.txt
python3 -I $N/apply_tree.py $R/t0e $R/t1 $R/norm.tsv; cp $TREE/lake-manifest.json $R/t1/ 2>/dev/null
t0=$(ts); python3 -I $N/chainmerge.py $R/t1 $R/t2 --packages $WSP --toolchain-src $TCS; echo "chainmerge rc=$? $(echo "$(ts) - $t0" | bc) s"
: > $R/cm-deny.txt
for it in 1 2 3 4 5 6; do
  python3 -I $TOOLS/cm_deny.py $R/t1/src $R/t2/.chainmerge.tsv $R/cm-deny.new
  [ -s $R/cm-deny.new ] || break
  cat $R/cm-deny.new >> $R/cm-deny.txt; rm -rf $R/t2
  python3 -I $N/chainmerge.py $R/t1 $R/t2 --packages $WSP --toolchain-src $TCS --deny $R/cm-deny.txt; echo "chainmerge (cm-deny round $it) rc=$?"
done
cp $TREE/lake-manifest.json $R/t2/ 2>/dev/null; python3 -I $PR/fixlake.py $R/t2
# merge chain-merge maps: the round-1 map (member -> kept) composed with this round's
for t in $TREE $R/t0 $R/t0e $R/t1 $R/t2; do echo "TREE $(basename $t) files=$(find $t/src -name '*.lean' | wc -l) lines=$(find $t/src -name '*.lean' -print0 | xargs -0 cat | wc -l) bytes=$(find $t/src -name '*.lean' -print0 | xargs -0 cat | wc -c) chars=$(find $t/src -name '*.lean' -print0 | xargs -0 cat | LC_ALL=C.UTF-8 wc -m)"; done
cp $R/prune.json $R/prune.json.deleted.tsv $R/prune.json.dropped.txt $R/norm.json $C/ 2>/dev/null
(cd $R/t2 && tar --exclude=.lake -czf $C/t2.tar.gz .); sha256sum $C/t2.tar.gz
echo "== done $(date -u +%FT%TZ)"
