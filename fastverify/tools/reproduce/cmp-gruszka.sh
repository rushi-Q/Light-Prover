#!/bin/bash
# cmp-gruszka.sh PINNED CANDIDATE SUITE_DIR OUT [THREADS] - run two gruszka binaries on every export of SUITE_DIR (arena
# layout: good/**.ndjson, bad/**.ndjson) with identical arguments and compare exit codes and output; prints a TSV + summary.
set -u
A=$1; B=$2; S=$3; O=$4; T=${5:-4}; mkdir -p "$O"
printf "label\tfile\trc_pinned\trc_cand\tsame_rc\tsame_out\n" > "$O/cmp.tsv"
n=0; diff_rc=0; diff_out=0
while IFS= read -r f; do
  lab=$(case "$f" in */good/*) echo good;; */bad/*) echo bad;; *) echo other;; esac)
  oa=$(timeout 300 "$A" "$f" "$T" 2>&1); ra=$?
  ob=$(timeout 300 "$B" "$f" "$T" 2>&1); rb=$?
  so=$([ "$oa" = "$ob" ] && echo 1 || echo 0); sr=$([ $ra = $rb ] && echo 1 || echo 0)
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$lab" "${f#$S/}" "$ra" "$rb" "$sr" "$so" >> "$O/cmp.tsv"
  n=$((n+1)); [ $sr = 1 ] || diff_rc=$((diff_rc+1)); [ $so = 1 ] || { diff_out=$((diff_out+1)); printf '%s\n--- pinned\n%s\n--- cand\n%s\n' "$f" "$oa" "$ob" >> "$O/outdiff.txt"; }
done < <(find "$S" -name '*.ndjson' | sort)
echo "files=$n different_exit=$diff_rc different_output=$diff_out" | tee "$O/summary.txt"
