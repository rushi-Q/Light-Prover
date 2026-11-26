#!/bin/bash
# e2e_exportin.sh SEAMS_OUTROOT OUT JOBS : every case of a runseams.sh run through the orchestrator in export-in mode
# (bin/fastverify - CHALLENGE OUT --from-export E --preset sound --challenge-sha256 H): result.json verdict must equal the
# recorded CS verdict and must never be ACCEPTED where the official comparator did not accept.
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
R=$1; OUT=$2; J=$3; mkdir -p "$OUT"
export R OUT FV
one() {
  b=$1; id=$2; cs=$3; of=$4; f=$R/$b/m/$id.ndjson; c=$OUT/chal-$b; o=$OUT/out-$id; rm -rf "$o"
  "$FV/bin/fastverify" - "$c" "$o" --from-export "$f" --preset sound --threads 2 --challenge-sha256 "$(cut -d' ' -f1 "$c/challenge.export.sha256")" --comparator-sha256 "$(sha256sum "$c/comparator.json" | cut -d' ' -f1)" > "$OUT/log-$id" 2>&1; rc=$?
  set -- $(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["verdict"], r.get("trust"))' "$o/result.json" 2>/dev/null)
  st=PASS; [ "${1:-NONE}" = "$cs" ] || st=MISMATCH; [ "${1:-}" = ACCEPTED ] && [ "$of" != ACCEPTED ] && st=FAIL-CRITICAL
  printf '%s\t%s\tfv=%s/%s/rc%s\tcs=%s\tof=%s\n' "$st" "$id" "${1:-NONE}" "${2:-}" "$rc" "$cs" "$of"
}
export -f one
for d in "$R"/*/; do b=$(basename "$d"); base_inputs "$b" || continue
  c=$OUT/chal-$b; mkdir -p "$c"; cp "$CH" "$c/challenge.export"; cp "$CFG" "$c/comparator.json"
  sha256sum "$c/challenge.export" | sed 's#  .*#  challenge.export#' > "$c/challenge.export.sha256"
  awk -F'\t' -v b="$b" '{print b"\t"$1"\t"$6"\t"$8}' "$d/results.tsv"
done | xargs -P "$J" -L 1 bash -c 'one "$0" "$1" "$2" "$3"' > "$OUT/rows.tsv"
cut -f1 "$OUT/rows.tsv" | sort | uniq -c
