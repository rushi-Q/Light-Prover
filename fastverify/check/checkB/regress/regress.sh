#!/bin/bash
# regress.sh GENDIR [--heavy] [--official] [--bin DIR] [--threads N] [--only REGEX] [--single]
#   --single: test option C4 (gruszka + kcompare) instead of C3 (default: dual kernels)
# Runs fast check B (check-b.sh) on every case of cases.tsv in BOTH comparator configurations (the finding's config with
# the official nanoda kernel, and the same config Lean-kernel-only) and compares with the OFFICIAL verdict:
#   PASS        = check B gives exactly the official verdict
#   PASS-DECL   = check B declines (exit 2): fail closed, the official comparator decides (counted separately: no verdict)
#   FAIL-ACCEPT = check B accepts what the official comparator rejects   (must never happen)
#   FAIL-REJECT = check B rejects what the official comparator accepts   (false reject)
# --official: also run the OFFICIAL comparator (check/official/check.sh) on each case and use ITS verdict (recorded values
# from cases.tsv are printed beside it; a disagreement is flagged RECORDED-DIFFERS).
# (whole body in main(): bash parses it completely before running, so editing this file cannot corrupt a running copy)
main() {
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); ROOT=$(cd "$H/../../.." && pwd)
G=$(cd "${1:-/nonexistent}" 2>/dev/null && pwd) || { echo "regress.sh: GENDIR '${1:-}' missing (run gen.sh GENDIR first)"; exit 2; }; shift
HEAVY=0; OFF=0; BIN=(); TH=8; ONLY=.; MODE=()
while [ $# -gt 0 ]; do case "$1" in
  --heavy) HEAVY=1; shift;; --official) OFF=1; shift;; --bin) BIN=(--bin "$2"); shift 2;;
  --threads) TH=$2; shift 2;; --only) ONLY=$2; shift 2;; --single) MODE=(--single); shift;; *) echo "unknown $1"; exit 2;; esac; done
X=$ROOT/tests; BENCH=${FV_BENCH_INPUTS:-/scratch/bench-inputs}   # finding inputs: tests/NNN-*/x snapshots
W=$(mktemp -d "${TMPDIR:-/tmp}/fv-regressB.XXXXXX"); trap 'rm -rf "$W"' EXIT
res() { python3 -I -c 'import json,sys
try: r=json.loads(open(sys.argv[1]).read().strip().splitlines()[-1]); print(r["exit"], r["verdict"], (r.get("detail") or "")[:160].replace("\t"," "))
except Exception as e: print("E ERROR", e)' "$1"; }
printf '%-24s %-8s %-4s %-4s %-11s %s\n' case config off fast result detail
n=0; bad=0; decl=0
grep -v '^#' "$H/cases.tsv" | while IFS=$'\t' read -r name fid sol chal cfg offn offl heavy; do
  [ -n "$name" ] || continue
  echo "$name" | grep -qE "$ONLY" || continue
  [ "$heavy" = 1 ] && [ $HEAVY = 0 ] && { printf '%-24s %s\n' "$name" "skipped (heavy)"; continue; }
  sol=$(eval echo "$sol"); chal=$(eval echo "$chal"); cfg=$(eval echo "$cfg")
  [ -f "$sol" ] || { printf '%-24s %s\n' "$name" "MISSING INPUT $sol (run gen.sh)"; continue; }
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("external_kernels",None); c.pop("enable_nanoda",None); json.dump(c,open(sys.argv[2],"w"))' "$cfg" "$W/leanonly.json"
  for variant in nanoda leanonly; do
    if [ $variant = nanoda ]; then c=$cfg; off=$offn; else c=$W/leanonly.json; off=$offl; fi
    rec=$off
    if [ $OFF = 1 ]; then
      bash "$ROOT/check/official/check.sh" "$sol" "$chal" "$c" --json "$W/off.json" < /dev/null > /dev/null 2>&1
      off=$(res "$W/off.json" | cut -d' ' -f1)
    fi
    bash "$H/../check-b.sh" "$sol" "$chal" "$c" --threads "$TH" "${BIN[@]}" "${MODE[@]}" --json "$W/b.json" < /dev/null > /dev/null 2> "$W/b.err"
    set -- $(res "$W/b.json"); fx=$1; shift 2; det="$*"
    if [ "$fx" = 2 ]; then r=PASS-DECL; elif [ "$fx" = "$off" ]; then r=PASS; elif [ "$fx" = 0 ]; then r=FAIL-ACCEPT; elif [ "$fx" = 1 ]; then r=FAIL-REJECT; else r=ERROR; fi
    [ "$off" = "?" ] && [ "$fx" != 0 ] && r="PASS-NOREF"
    [ "$off" = "?" ] && [ "$fx" = 0 ] && r="UNKNOWN-REF"
    extra=; [ $OFF = 1 ] && [ "$rec" != "?" ] && [ "$rec" != "$off" ] && extra=" RECORDED-DIFFERS(recorded $rec)"
    printf '%-24s %-8s %-4s %-4s %-11s %s\n' "$name" "$variant" "$off" "$fx" "$r$extra" "$det"
  done
done
}
main "$@"; exit $?
