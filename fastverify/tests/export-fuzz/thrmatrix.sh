#!/bin/bash
# thrmatrix.sh CAMPAIGN_ROOT OUT JOBS THREADS... : CS (bulk variant) again on every kept mutant of a campaign at each thread
# count; the verdict must equal the campaign's (threads=1) verdict.
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
R=$1; OUT=$2; J=$3; shift 3; mkdir -p "$(dirname "$OUT")"; : > "$OUT"
export R W
one() {
  b=$1; id=$2; v1=$3; t=$4; f=$R/$b/m/$id.ndjson; [ -f "$f" ] || exit 0
  . "$H/common.sh"; base_inputs "$b" || exit 0
  v=$("$W/check-sound-bulk.sh" "$f" "$CH" "$CFG" --threads "$t" --hints none 2>/dev/null | tail -1 | python3 -I -c 'import json,sys; print(json.load(sys.stdin)["verdict"])' 2>/dev/null)
  [ "$v" = "$v1" ] && st=SAME || st=DIFF
  printf '%s\t%s\t%s\tT=%s\t%s\t%s\n' "$st" "$b" "$id" "$t" "$v1" "$v"
}
export -f one; export H
for t in "$@"; do for d in "$R"/*/; do b=$(basename "$d"); awk -F'\t' -v b="$b" -v t="$t" '{print b"\t"$1"\t"$6"\t"t}' "$d/results.tsv"; done; done \
  | xargs -P "$J" -L 1 bash -c 'one "$0" "$1" "$2" "$3"' >> "$OUT"
cut -f1,4 "$OUT" | sort | uniq -c
