#!/bin/bash
# build_tree.sh C1DIR WORKDIR -- build the combined candidate tree from C1DIR/manifest.tsv (owner<TAB>file, priority order):
# apply_edits -> fixlake -> dropempty -> normalize (+dfsverify) -> apply_tree -> chainmerge -> fixlake.
# Writes C1DIR/t2.tar.gz, C1DIR/pipeline.log and summaries.
# env: RH_PROJECT (base sources, default $LIGHT_LEAN/alpoge-rh/lean), FV_PACKAGES (Lake workspace with the materialized
#      dependencies, default $LIGHT_LEAN/verify/challenge), ELAN_HOME, NORMDIR, APPLY, TOOLS, CM_DENY, NOCM, NORM_CLASSES.
set -u
C=$1; R=$2; rm -rf $R; mkdir -p $R
FV=$(cd "$(dirname "$0")/../../.." && pwd); N=${NORMDIR:-$FV/tools/compress/normalize}; APPLY=${APPLY:-$FV/tools/compress/dedup/apply_edits.py}; TOOLS=${TOOLS:-$(cd "$(dirname "$0")" && pwd)}
RH=${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}
WSP=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}/.lake/packages
TCS=$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/src/lean
ts() { date +%s.%N; }
exec > >(tee $C/pipeline.log) 2>&1
echo "== C1 pipeline $(date -u +%FT%TZ) $(hostname) APPLY=$APPLY N=$N CM_DENY=${CM_DENY:-} NOCM=${NOCM:-}"
args=(); prio=()
while IFS=$'\t' read -r owner f; do [ -n "$owner" ] || continue; args+=("$C/$f"); prio+=("$owner"); echo "edit list $owner $f $(wc -l < "$C/$f") lines sha256 $(sha256sum < "$C/$f" | cut -c1-16)"; done < "$C/manifest.tsv"
P=$(IFS=,; echo "${prio[*]}")
mkdir -p $R/rh; (cd "$RH" && tar --exclude=.lake --exclude=.git -cf - .) | (cd $R/rh && tar xf -)
t0=$(ts); python3 -I $APPLY $R/rh $R/t0 "${args[@]}" --priority "$P" > $R/apply.out 2>&1; echo "apply_edits rc=$? $(echo "$(ts) - $t0" | bc) s"; tail -3 $R/apply.out | cut -c1-3000
[ -f $R/t0/.apply-conflicts.tsv ] && echo "conflicts: $(wc -l < $R/t0/.apply-conflicts.tsv)" && awk -F'\t' '{print $5}' $R/t0/.apply-conflicts.tsv | sort | uniq -c | head
python3 -I $FV/tools/compress/prune/fixlake.py $R/t0
t0=$(ts); python3 -I $N/dropempty.py $R/t0 $R/t0e; echo "dropempty rc=$? $(echo "$(ts) - $t0" | bc) s"; cp $R/t0/lake-manifest.json $R/t0e/ 2>/dev/null; python3 -I $FV/tools/compress/prune/fixlake.py $R/t0e
t0=$(ts); python3 -I $N/normalize.py $R/t0e --packages $WSP --toolchain-src $TCS --classes ${NORM_CLASSES:-imp,opt,optres} --edits $R/norm.tsv --json $R/norm.json --graph-out $R/g; echo "normalize rc=$? $(echo "$(ts) - $t0" | bc) s"
g++ -O2 -std=c++17 -pthread -o $R/dfsverify $N/dfsverify/dfsverify.cpp && $R/dfsverify $R/g.old.txt $R/g.new.txt $R/g.roots.txt 16; echo "dfsverify rc=$?"; rm -f $R/g.*.txt
python3 -I $N/apply_tree.py $R/t0e $R/t1 $R/norm.tsv; cp $R/t0/lake-manifest.json $R/t1/ 2>/dev/null
if [ -z "${NOCM:-}" ]; then
t0=$(ts); python3 -I $N/chainmerge.py $R/t1 $R/t2 --packages $WSP --toolchain-src $TCS ${CM_DENY:+--deny $CM_DENY}; echo "chainmerge rc=$? $(echo "$(ts) - $t0" | bc) s"
# private-name clashes inside a merge group (cm_deny.py) -> deny those kept modules and merge again
# (iterated: denying a kept module can create new, shorter groups)
cat ${CM_DENY:-/dev/null} > $R/cm-deny.txt
for it in 1 2 3 4 5 6; do
  python3 -I $TOOLS/cm_deny.py $R/t1/src $R/t2/.chainmerge.tsv $R/cm-deny.new
  [ -s $R/cm-deny.new ] || break
  cat $R/cm-deny.new >> $R/cm-deny.txt; rm -rf $R/t2
  t0=$(ts); python3 -I $N/chainmerge.py $R/t1 $R/t2 --packages $WSP --toolchain-src $TCS --deny $R/cm-deny.txt; echo "chainmerge (cm-deny round $it, $(wc -l < $R/cm-deny.txt) denied) rc=$? $(echo "$(ts) - $t0" | bc) s"
done; cp $R/cm-deny.txt $C/
else cp -a $R/t1 $R/t2; echo "chainmerge skipped"; fi
cp $R/t0/lake-manifest.json $R/t2/ 2>/dev/null; python3 -I $FV/tools/compress/prune/fixlake.py $R/t2
python3 -I $N/normalize.py $R/t2 --packages $WSP --toolchain-src $TCS --classes ${NORM_CLASSES:-imp,opt,optres} --edits $R/norm2.tsv --json $R/norm2.json > /dev/null; echo "idempotence: $(wc -l < $R/norm2.tsv) further normalize edits on t2"
for t in $R/rh $R/t0 $R/t0e $R/t1 $R/t2; do echo "TREE $(basename $t) files=$(find $t/src -name '*.lean' | wc -l) lines=$(find $t/src -name '*.lean' -print0 | xargs -0 cat | wc -l) bytes=$(find $t/src -name '*.lean' -print0 | xargs -0 cat | wc -c) nonws=$(find $t/src -name '*.lean' -print0 | xargs -0 cat | tr -d ' \n\t\r' | wc -c) chars=$(find $t/src -name '*.lean' -print0 | xargs -0 cat | LC_ALL=C.UTF-8 wc -m)"; done
cp $R/t0/.apply-summary.json $C/apply-summary.json 2>/dev/null; cp $R/t0/.apply-conflicts.tsv $C/apply-conflicts.tsv 2>/dev/null; cp $R/norm.json $C/; cp $R/t2/.chainmerge.tsv $C/chainmerge.tsv 2>/dev/null; cp $R/t0e/.dropempty.txt $C/dropempty.txt 2>/dev/null
t0=$(ts); (cd $R/t2 && tar --exclude=.lake -czf $C/t2.tar.gz .); echo "tar $(echo "$(ts) - $t0" | bc) s $(du -sh $C/t2.tar.gz)"; sha256sum $C/t2.tar.gz
echo "== done $(date -u +%FT%TZ)"
