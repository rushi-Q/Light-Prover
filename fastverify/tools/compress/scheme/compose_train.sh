#!/bin/bash
# compose_train.sh TRAIN_DIR -- stage-3 integrator: build a train's manifest from TRAIN_DIR/intake.tsv and compose its tree.
# intake.tsv (priority order): owner_key<TAB>path<TAB>mode   mode =
#   base      a list of the accepted base train (proven together; copied unchanged)
#   new       a list joining after the pruning rounds: newlist_guard.py (drops declarations whose new code names a
#             declaration that the base deletion lists delete)
#   new-auto  as new + decl_exclude.py against P05-dhe (an automated closer may use a hypothesis DHE removes)
#   new-docs  insert_guard.py against the deletion lists (docs anchored in deleted code)
# Every new list's owner column is rewritten to its key (apply_edits.py priority is by owner column).
# Then build_tree.sh composes TRAIN_DIR/t2.tar.gz. Untrusted; the train is judged by the trusted check.
# env: DECLS (declaration table of the pruning report, prune.py --report R.json -> R.json.decls.tsv; required),
#      WORK (default $FV_SCRATCH/work-<train>), RH_PROJECT (default $LIGHT_LEAN/alpoge-rh/lean), NOBUILD=1.
set -u
C=$1; W=${WORK:-${FV_SCRATCH:?node-local scratch directory for the build (required; or set WORK)}/work-$(basename $C)}
S=$(cd "$(dirname "$0")" && pwd); T=$S
DECLS=${DECLS:?declaration table of the pruning report (R.json.decls.tsv) (required)}; SRC=${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}/src
mkdir -p $C/lists; : > $C/manifest.tsv; : > $C/guard.log
DEL=(); DHE=
while IFS=$'\t' read -r key path mode; do
  case "$key" in ''|'#'*) continue;; esac
  case "$key" in P01|P01r2|P03-dedup) DEL+=("$path");; P05-dhe) DHE=$path;; esac
done < $C/intake.tsv
echo "deletion lists: ${DEL[*]}  dhe: $DHE" | tee -a $C/guard.log
while IFS=$'\t' read -r key path mode; do
  case "$key" in ''|'#'*) continue;; esac
  out=$C/lists/$key.tsv
  echo "== $key $mode $path $(wc -l < $path) rows sha256 $(sha256sum < $path | cut -c1-16)" | tee -a $C/guard.log
  case $mode in
    base) cp $path $out;;
    new|new-auto|new-docs)
      awk -F'\t' -v OFS='\t' -v k="$key" 'NF>=5 {$5=k; print}' $path > $out.in
      if [ $mode = new-docs ]; then python3 -I $S/insert_guard.py $out.in $out.g "${DEL[@]}" 2>&1 | tee -a $C/guard.log
      else python3 -I $T/newlist_guard.py $DECLS $out.in $out.g --deleted "${DEL[@]}" --src $SRC --report $C/guard-$key.tsv 2>&1 | tee -a $C/guard.log; fi
      if [ $mode = new-auto ] && [ -n "$DHE" ]; then python3 -I $S/decl_exclude.py $out.g $DHE $DECLS $out 2>&1 | tee -a $C/guard.log; else mv $out.g $out; fi
      rm -f $out.in $out.g;;
    *) echo "unknown mode $mode"; exit 2;;
  esac
  printf '%s\t%s\n' "$key" "lists/$key.tsv" >> $C/manifest.tsv
  echo "   -> $(wc -l < $out) rows sha256 $(sha256sum < $out | cut -c1-16)" | tee -a $C/guard.log
done < $C/intake.tsv
cat $C/manifest.tsv
[ -n "${NOBUILD:-}" ] && exit 0
TOOLS=$S bash $S/build_tree.sh $C $W
