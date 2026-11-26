#!/bin/bash
# officialflow.sh PRISTINE WORK CHALLENGE_DIR  -> prints "OFFICIAL: <verdict>" ; exit 0 iff ACCEPTED
# (copy of the original officialflow.sh, plus package checkouts for projects that require aesop)
# The OFFICIAL flow: original structure, official Lean 4.33.1 `lake build` (project's own lakefile), official lean4export
# v4.33.0 (env/tools/lean4export), unmodified Lean 4.36 `lake comparator` (Lean kernel + nanoda).
{ # whole script parsed before it runs (safe against edits while running)
set -u
# generic: the solution module is read from CHALLENGE_DIR/comparator.json (the original copies hard-code Main)
P=$(readlink -f "$1"); W=$2; C=$(readlink -f "$3"); R=$LIGHT_LEAN
T33=${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}; T36=${FV_T36:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}
EXP=${FV_OFFICIAL_EXPORTER:-$R/env/tools/lean4export/.lake/build/bin/lean4export}
SM=$(python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))[\"solution_module\"])" "$C/comparator.json")
rm -rf "$W"; mkdir -p "$W/log"; W=$(readlink -f "$W"); cp -a "$P" "$W/proj"
# the project requires aesop (+ batteries): provide the pinned checkouts (same revs as the RH Mathlib cache, which is
# exactly what the fast pipeline binds) so that `lake build` works offline. Copies, never the shared cache itself.
PK=${FV_PACKAGES:-$R/verify/challenge}/.lake/packages
if grep -q '"name": "mathlib"' "$W/proj/lake-manifest.json" 2>/dev/null; then
  mkdir -p "$W/proj/.lake/packages"; cp -a "$PK"/. "$W/proj/.lake/packages/"      # (057): full pinned Mathlib cache copy (7.6 GB)
elif grep -q '"name": "aesop"' "$W/proj/lake-manifest.json" 2>/dev/null; then
  mkdir -p "$W/proj/.lake/packages"; cp -a "$PK/aesop" "$PK/batteries" "$W/proj/.lake/packages/"
fi
# challenge export (official build + official exporter)
if [ ! -s "$C/challenge.export" ]; then
  ( cd "$C" && export PATH=$T33/bin:/usr/bin:/bin && lake build > "$W/log/challenge.build.log" 2>&1 && \
    LEAN_PATH=$C/.lake/build/lib/lean:$T33/lib/lean $EXP Challenge -- $(cat export-targets.txt) > challenge.export ) || { echo "challenge build failed"; exit 2; }
fi
echo "official: lake build (Lean 4.33.1)"
( cd "$W/proj" && PATH=$T33/bin:/usr/bin:/bin timeout 3600 lake build ) > "$W/log/build.log" 2>&1; brc=$?
echo "official: lake build rc=$brc"; grep -E 'error' "$W/log/build.log" | head -5
if [ $brc -ne 0 ]; then echo "OFFICIAL: REJECTED (build failed, rc=$brc)"; exit 1; fi
( cd "$W/proj" && export PATH=$T33/bin:/usr/bin:/bin && LEAN_PATH=$(for d in $W/proj/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && printf "%s:" "$d"; done)$W/proj/.lake/build/lib/lean:$T33/lib/lean $EXP $SM -- $(cat "$C/export-targets.txt") > "$W/solution.export" 2> "$W/log/export.err" ); erc=$?
echo "official: lean4export rc=$erc $(stat -c %s "$W/solution.export") bytes sha256 $(sha256sum < "$W/solution.export" | cut -c1-16)"
[ $erc -eq 0 ] || { echo "OFFICIAL: REJECTED (export failed)"; exit 1; }
( cd "$C" && PATH=$T36/bin:/usr/bin:/bin timeout 3600 lake comparator --config "$C/comparator.json" \
    --challenge-from-export "$C/challenge.export" --solution-from-export "$W/solution.export" ) > "$W/log/comparator.log" 2>&1; crc=$?
tail -4 "$W/log/comparator.log" | sed 's/^/official: comparator: /'
if [ $crc -eq 0 ]; then echo "OFFICIAL: ACCEPTED (lake comparator rc=0)"; exit 0; else echo "OFFICIAL: REJECTED (lake comparator rc=$crc)"; exit 1; fi
exit $?
}
