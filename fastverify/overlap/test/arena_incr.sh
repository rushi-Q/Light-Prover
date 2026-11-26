#!/bin/bash
# arena_incr.sh PLEANCHECKER OUTDIR [THREADS] : the lean-kernel-arena suite (225 exports, label = good/ or bad/) through the
# INCREMENTAL Lean leg in three protocols: (F) final only, (S) snapshot = the export itself + final, (P) plain checkExport.
# PASS iff every protocol's exit code equals the label (good 0 / bad 1) - i.e. equals the official leanchecker's verdict
# (it agrees with the labels on 225/225). The suite is read from $FV_BENCH_INPUTS/arena/suite/{good,bad}/.
set -u
P=$1; O=$2; T=${3:-8}; mkdir -p "$O"
SUITE=${FV_BENCH_INPUTS:?benchmark inputs directory with arena/suite/good and arena/suite/bad (required)}/arena/suite
pass=0; fail=0; : > "$O/arena_incr.tsv"
while IFS= read -r f; do
  case "$f" in "$SUITE"/good/*) exp=0;; *) exp=1;; esac
  name=${f#$SUITE/}
  timeout 600 "$P" -j$T "$f" > /dev/null 2>&1; rp=$?
  printf 'final %s\n' "$f" | timeout 600 "$P" --incremental -j$T > /dev/null 2>"$O/err.txt"; rf=$?
  printf 'snap %s\nfinal %s\n' "$f" "$f" | timeout 600 "$P" --incremental -j$T > /dev/null 2>>"$O/err.txt"; rs=$?
  if [ $rp = $exp ] && [ $rf = $exp ] && [ $rs = $exp ]; then st=PASS; pass=$((pass+1)); else st=FAIL; fail=$((fail+1)); fi
  printf '%s\t%s\texp=%s plain=%s final=%s snap+final=%s\n' "$st" "$name" "$exp" "$rp" "$rf" "$rs" >> "$O/arena_incr.tsv"
done < <(find "$SUITE" -type f -name '*.ndjson' | sort)
echo "RESULT arena incremental: pass=$pass fail=$fail ($O/arena_incr.tsv)"
[ $fail = 0 ]
