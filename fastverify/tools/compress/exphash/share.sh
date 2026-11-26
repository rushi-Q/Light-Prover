#!/bin/bash
# share.sh SOLUTION_EXPORT CHALLENGE_EXPORT COMPARATOR_JSON OUTDIR [--check THREADS] [--name-only]
# Generic export-level sharing (no project list): every constant of the CHALLENGE export stays nominal and is never
# redirected; all other theorems/definitions/inductive blocks are shared by semantic class (--name-only: same-statement
# theorems and identical definitions by name-based hashes), representatives chosen by expcompress --choose.
# Writes OUTDIR/{chal,sol}/decls.tsv, plan.tsv, solution.export, redirects.tsv, stats.json [, check.json].
# With --check N: runs the trusted check (fastverify/check/sound/check-sound.sh) on the result.
set -eu
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../../.." && pwd)
if [ -n "${EXPHASH_BIN:-}" ] && [ -x "$EXPHASH_BIN/exphash" ]; then
  BIN="$EXPHASH_BIN"
elif [ -x "${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-exphash-target/release/exphash" ]; then   # build.sh's default target
  BIN="${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-exphash-target/release"
else
  BIN=$("$HERE/build.sh" | tail -1)
fi
SOL=$1; CHAL=$2; CFG=$3; OUT=$4; shift 4
CHECK=; SEM=--semantic; CL=--classes
while [ $# -gt 0 ]; do case $1 in --check) CHECK=$2; shift 2;; --name-only) SEM=; CL=; shift;; *) echo "bad arg $1"; exit 2;; esac; done
mkdir -p "$OUT"
python3 -I - "$CFG" > "$OUT/targets.txt" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
prim = "Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam".split()
q = "Quot Quot.mk Quot.lift Quot.ind".split() if "Quot.sound" in c["permitted_axioms"] else []
print(" ".join(q + c["theorem_names"] + c.get("definition_names", []) + c["permitted_axioms"] + prim))
PY
"$BIN/exphash" "$CHAL" "$OUT/chal" 2> "$OUT/chal.log"
awk -F'\t' 'NR>1{print $2}' "$OUT/chal/decls.tsv" > "$OUT/nominal.txt"
if [ -n "$CL" ]; then "$BIN/exphash" --classes --nominal "$OUT/nominal.txt" "$SOL" "$OUT/sol" 2> "$OUT/sol.log"
else "$BIN/exphash" "$SOL" "$OUT/sol" 2> "$OUT/sol.log"; fi
python3 "$HERE/classes_plan.py" "$OUT/sol/decls.tsv" "$OUT/plan.tsv" --nominal "$OUT/nominal.txt" --targets "$OUT/targets.txt" $SEM 2> "$OUT/plan.log"
"$BIN/expcompress" "$SOL" --choose "$OUT/plan.tsv" "$OUT/targets.txt" "$OUT/solution.export" --stats "$OUT/stats.json" \
  --write-redirects "$OUT/redirects.tsv" 2> "$OUT/expcompress.log"
cat "$OUT/stats.json"
if [ -n "$CHECK" ]; then
  "$FV/check/sound/check-sound.sh" "$OUT/solution.export" "$CHAL" "$CFG" --threads "$CHECK" --log "$OUT/check.log" --json "$OUT/check.json" | tail -1
fi
