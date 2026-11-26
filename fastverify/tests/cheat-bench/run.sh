#!/bin/bash
# run.sh OUTROOT LANES THREADS "PRESETS" ["GLOB1 GLOB2 ..."]
# Proof-cheating benchmark runner: generates the corpus (gen.py) into OUTROOT/corpus, freezes a copy of the package
# (FV_UNDER_TEST, default the live fastverify/) into OUTROOT/pkg, runs every case x preset through bin/fastverify
# (all project code is elaborated inside the package's bwrap sandbox), then summarize.py -> OUTROOT/summary.{tsv,md}.
set -u
H=$(dirname "$(readlink -f "$0")")
mkdir -p "$1" && R=$(readlink -f "$1") && [ -n "$R" ] || { echo "run.sh: cannot create $1" >&2; exit 2; }
LANES=$2; T=$3; PRESETS=$4; GLOB=${5:-*}
FVSRC=${FV_UNDER_TEST:-$LIGHT_LEAN/fastverify}
mkdir -p "$R/runs"
if [ ! -x "$R/pkg/fastverify/bin/fastverify" ]; then
  mkdir -p "$R/pkg"
  rsync -a --exclude tests --exclude pipeline --exclude 'review-*' --exclude __pycache__ "$FVSRC/" "$R/pkg/fastverify/"
  (cd "$R/pkg/fastverify" && find . -type f | sort | xargs sha256sum | sha256sum | cut -c1-16) > "$R/pkg/DIGEST"
fi
[ -d "$R/corpus" ] || python3 -I "$H/gen.py" "$R/corpus"
run_one() {
  local c=$1 p=$2; local OUT=$R/runs/$c.$p
  rm -rf "$OUT"
  local CH; CH=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]]["challenge"])' "$R/corpus/cases.json" "$c")
  local extra=(); case $c in F24-*|F27-*|F28-*|F29-*|F32-*|F35-*|T21-*|T22-*) extra+=(--keep-work);; esac
  if python3 -I -c 'import json,sys; sys.exit(0 if json.load(open(sys.argv[1]))[sys.argv[2]].get("mathlib") else 1)' "$R/corpus/cases.json" "$c"; then
    extra+=(--packages "${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}")
  fi
  local t0; t0=$(date +%s.%N)
  timeout 3600 "$R/pkg/fastverify/bin/fastverify" "$R/corpus/cases/$c" "$R/corpus/challenges/$CH" "$OUT" --preset "$p" \
     --threads "$T" "${extra[@]}" > "$R/runs/$c.$p.log" 2>&1
  local rc=$?
  echo "$c $p $rc $(python3 -c "import sys; print(round($(date +%s.%N)-$t0,1))")" >> "$R/runs/done.txt"
}
export -f run_one; export R T
for c in $(cd "$R/corpus/cases" && for g in $GLOB; do ls -d $g; done | sort -u | grep -v -E "${EXCLUDE:-^$}"); do for p in $PRESETS; do echo "$c $p"; done; done \
  | xargs -P "$LANES" -L 1 bash -c 'run_one "$@"' _
python3 -I "$H/summarize.py" "$R"
