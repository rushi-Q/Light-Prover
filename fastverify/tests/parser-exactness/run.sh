#!/bin/bash
# tests/parser-exactness/run.sh [FV_ROOT]: the trusted export reader FastParse must return exactly
# the official reader's environment or decline (exactness contract of check/sound/src/FastParse.lean). x/ holds 15 malformed or
# non-canonical exports (tests/export-fuzz/xfuzz.py: NUL inside a line, bad whitespace, trailing garbage, duplicate keys, raw
# control characters, index rebinding / forward references / dense re-numbering) that the soundness-suite corpora lack; together they
# catch 31 mutants of FastParse's fast-path templates that no suite notices (each makes the fast reader accept a line the official
# reader rejects, or read it differently). Builds parsediff from THIS package's check/sound/src with tests/export-fuzz/parsediff/
# build.sh and runs it in bwrap (sbx.sh); PASS iff no DIVERGE / missing line.
set -u
FV=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}; X=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)/x
W=$(mktemp -d "${TMPDIR:-/tmp}/parser-exactness.XXXXXX"); trap 'rm -rf "$W"' EXIT
if ! FV_UNDER_TEST=$FV bash "$FV/tests/export-fuzz/parsediff/build.sh" "$W/pd" > "$W/build.log" 2>&1; then echo "FAIL build: $(tail -3 "$W/build.log")"; echo "RESULT pass=0 fail=1"; exit 1; fi
PD=$W/pd/.lake/build/bin/parsediff
bash "$FV/tests/export-fuzz/parsediff/sbx.sh" "$X" "$(dirname "$PD")" -- "$PD" "$X"/*.ndjson > "$W/out" 2>&1
pass=0; fail=0
for f in "$X"/*.ndjson; do
  st=$(awk -F'\t' -v f="$f" '$2==f {print $1}' "$W/out")
  case "$st" in SAME|FALLBACK|BOTHFAIL|PARTIAL) echo "PASS $(basename "$f") ($st)"; pass=$((pass+1));;
    *) echo "FAIL $(basename "$f") (${st:-no output}): $(awk -F'\t' -v f="$f" '$2==f {print $3}' "$W/out" | cut -c1-200)"; fail=$((fail+1));; esac
done
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]
