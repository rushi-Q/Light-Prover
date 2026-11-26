#!/bin/bash
# parsediff/realrun.sh OUT FILE_OR_DIR... : parser agreement on real exports (sandboxed). Files > 256 MB use only the
# streaming readers that ccmp/pleanchecker use (PD_STREAM_ONLY=1). Prints the status counts; exit 1 on any DIVERGE row.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); W=${EXPORT_FUZZ_WORK:-${TMPDIR:-/tmp}/$USER-exportfuzz}
PD=$W/pd/.lake/build/bin/parsediff; OUT=$1; shift; : > "$OUT"
ro=(); files=()
for a in "$@"; do
  if [ -d "$a" ]; then ro+=("$(readlink -f "$a")"); mapfile -t -O "${#files[@]}" files < <(find "$a" -type f \( -name '*.ndjson' -o -name '*.export' \) | sort)
  else ro+=("$(dirname "$(readlink -f "$a")")"); files+=("$(readlink -f "$a")"); fi
done
small=()
for f in "${files[@]}"; do
  if [ "$(stat -c %s "$f")" -gt 268435456 ]; then "$H/sbx.sh" "${ro[@]}" "$(dirname "$PD")" -- /usr/bin/env PD_STREAM_ONLY=1 "$PD" "$f" >> "$OUT"
  else small+=("$f"); fi
done
[ ${#small[@]} -gt 0 ] && printf '%s\n' "${small[@]}" | xargs -P "${PD_JOBS:-8}" -n 25 "$H/sbx.sh" "${ro[@]}" "$(dirname "$PD")" -- "$PD" >> "$OUT"
cut -f1 "$OUT" | sort | uniq -c
! grep -q '^DIVERGE' "$OUT"
