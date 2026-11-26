#!/bin/bash
# cmp-plc.sh PINNED CANDIDATE SUITE_DIR OUT [THREADS] - run two pleanchecker binaries on every export of SUITE_DIR with the
# arguments and environment of check-sound.sh's wrapper (-jT -v --from-export, 1 GiB-128 MiB worker stacks, no hints) and
# compare exit codes (strict) and messages (timing lines '... finished after N ms', '[..] N ms' removed). TSV + summary.
set -u
A=$1; B=$2; S=$3; O=$4; T=${5:-4}; mkdir -p "$O"; : > "$O/hints"
printf "label\tfile\trc_pinned\trc_cand\tsame_rc\tsame_msg\n" > "$O/cmp.tsv"
norm() { grep -v '^\[pchk' | sed -E 's/[0-9]+ ms/N ms/g; s/0x[0-9a-f]+/0xX/g'; }
run() { PCHK_PRIO_FILE=$O/hints PCHK_SLOW_MS=10000 LEAN_STACK_SIZE_KB=917376 LEAN_ABORT_ON_PANIC=1 timeout 600 "$1" -j$T -v --from-export "$2" 2>&1; }
n=0; dr=0; dm=0
while IFS= read -r f; do
  lab=$(case "$f" in */good/*) echo good;; */bad/*) echo bad;; *) echo other;; esac)
  oa=$(run "$A" "$f"); ra=$?; ob=$(run "$B" "$f"); rb=$?
  sr=$([ $ra = $rb ] && echo 1 || echo 0); sm=$([ "$(printf '%s' "$oa" | norm)" = "$(printf '%s' "$ob" | norm)" ] && echo 1 || echo 0)
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$lab" "${f#$S/}" "$ra" "$rb" "$sr" "$sm" >> "$O/cmp.tsv"
  n=$((n+1)); [ $sr = 1 ] || dr=$((dr+1)); [ $sm = 1 ] || { dm=$((dm+1)); printf '%s\n--- pinned\n%s\n--- cand\n%s\n' "$f" "$oa" "$ob" >> "$O/msgdiff.txt"; }
done < <(find "$S" -name '*.ndjson' | sort)
echo "files=$n different_exit=$dr different_message=$dm" | tee "$O/summary.txt"
