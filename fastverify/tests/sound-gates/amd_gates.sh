#!/bin/bash
# [EXPECT_CS_SHA16=<16 hex>] amd_gates.sh LABEL [GATES...]  -- the soundness suites of the DEPLOYED sound check on a 384-thread AMD
# host (run as a job with a copy of this directory, tests/sound-gates). Uses the corpora under $BENCH_INPUTS (default /scratch/bench-inputs) and
# the package under test (check/sound/check-sound.sh + its pins). Outputs under the work dir set below (O=).
# GATES (suite names) default: arena suitex cmpx threads  (mutants: add "mutants"; needs ~250 GB free on /scratch unless reflinks work)
set -u
LABEL=${1:?label}; shift
GATES=("$@"); [ ${#GATES[@]} -gt 0 ] || GATES=(arena suitex cmpx threads)
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
# the package under test: a shipped copy next to this script (./fastverify, = the published package frozen at queue time)
# if present, else the package containing this directory (or FV_UNDER_TEST)
FV=${FV_UNDER_TEST:-$(cd "$HERE/../.." && pwd)}; [ -x "$HERE/fastverify/check/sound/check-sound.sh" ] && FV=$HERE/fastverify
CS=$FV/check/sound/check-sound.sh
O=${SOUND_GATES_WORK:-${TMPDIR:-/tmp}/$USER-soundgates}/gates/$LABEL; mkdir -p "$O"
I=${BENCH_INPUTS:-/scratch/bench-inputs}
echo "== host $(hostname) $(date -u +%FT%TZ) nproc $(nproc)"; ls $I; df -h /scratch | tail -1; findmnt -n -o FSTYPE /scratch
echo "== deployed package: $(cat $FV/DEPLOYED 2>/dev/null | head -2)"; sha256sum "$CS" "$FV/check/sound/pins.env" "$FV/lib/fastverify.py"
if [ -n "${EXPECT_CS_SHA16:-}" ] && [ "$(sha256sum "$CS" | cut -c1-16)" != "$EXPECT_CS_SHA16" ]; then
  echo "deployed check-sound.sh is $(sha256sum "$CS" | cut -c1-16), expected $EXPECT_CS_SHA16: not testing it"; exit 3; fi
"$CS" --preflight | tail -1 || { echo "check-sound preflight failed"; exit 2; }
ARENA=; for d in $I/suite $I/arena/suite $I/lean-arena/suite /scratch/bench-inputs/arena/suite; do [ -d $d/good ] && { ARENA=$d; break; }; done
CH=$I/rh-miniF/challenge
# legs exactly as check-sound.sh runs them (pins.env)
PLC=$(awk '$1=="PIN" && $2=="pleanchecker"{print $4}' $FV/check/sound/pins.env)
GRZ=$(awk '$1=="PIN" && $2=="gruszka"{print $4}' $FV/check/sound/pins.env)
TC36=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' $FV/config/components.json)
cat > "$O/legs.json" <<EOF
{"lean": {"argv": ["$PLC", "-j{threads}", "-v", "--from-export", "{export}"],
          "env": {"LEAN_ABORT_ON_PANIC": "1", "LEAN_NUM_THREADS": "{threads}", "LEAN_STACK_SIZE_KB": "917376"}},
 "k2": {"argv": ["$GRZ", "{export}", "{threads}"], "env": {}},
 "ro": ["$(dirname "$PLC")", "$(dirname "$GRZ")", "$TC36"]}
EOF
# rh-mid mutants (first / last theorem outside the challenge: value := its own type) for the thread matrix
mkdir -p "$O/midmut"
g++ -O2 -std=c++17 -pthread -o "$O/fvmut" "$HERE/tools/fvmut.cpp" || clang++ -O2 -std=c++17 -pthread -o "$O/fvmut" "$HERE/tools/fvmut.cpp"
for m in midM1 midM2; do "$O/fvmut" $I/rh-mid/ref/solution.export "$O/midmut/$m.export" "$HERE/specs/$m.spec" --threads 16 > /dev/null || echo "fvmut $m failed"; done
MUTJSON="[]"
if printf '%s\n' "${GATES[@]}" | grep -qx mutants; then
  H=${RH_HONEST_EXPORT:-$I/rh/solution.export}   # read-only honest RH export (never modified)
  mkdir -p "$O/rhmut"
  for m in M1 M2 M4 M3; do "$O/fvmut" "$H" "$O/rhmut/$m.export" "$HERE/specs/$m.spec" --threads 64 || echo "fvmut $m failed"; done
  MUTJSON="[{\"name\":\"honest\",\"export\":\"$H\",\"expect\":\"ACCEPTED\"},{\"name\":\"M1\",\"export\":\"$O/rhmut/M1.export\"},{\"name\":\"M3\",\"export\":\"$O/rhmut/M3.export\"},{\"name\":\"M4\",\"export\":\"$O/rhmut/M4.export\"},{\"name\":\"M2\",\"export\":\"$O/rhmut/M2.export\"}]"
fi
cat > "$O/inputs.json" <<EOF
{"arena": "${ARENA:-/nonexistent}", "suitex": "$I/suitex", "cmpx": "$I/cmpx",
 "cmpx_challenge": "$CH/challenge.export",
 "cmpx_configs": ["$CH/comparator.leanonly.json", "$CH/comparator.nanoda.json"],
 "mutants": $MUTJSON,
 "mutants_challenge": "${FV_PACKAGES:-$FV/../verify/challenge}/challenge.export",
 "mutants_config": "${FV_PACKAGES:-$FV/../verify/challenge}/comparator.json",
 "threads_cases": [
  {"name": "rhmid-honest", "export": "$I/rh-mid/ref/solution.export", "challenge": "$I/rh-mid/challenge/challenge.export", "config": "$I/rh-mid/challenge/comparator.json"},
  {"name": "rhmid-M1-first-thm", "export": "$O/midmut/midM1.export", "challenge": "$I/rh-mid/challenge/challenge.export", "config": "$I/rh-mid/challenge/comparator.json"},
  {"name": "rhmid-M2-last-thm", "export": "$O/midmut/midM2.export", "challenge": "$I/rh-mid/challenge/challenge.export", "config": "$I/rh-mid/challenge/comparator.json"},
  {"name": "cmpx-reject-stmt-true", "export": "$I/cmpx/reject-stmt-true.ndjson", "challenge": "$CH/challenge.export", "config": "$CH/comparator.json"},
  {"name": "cmpx-reject-illegal-axiom", "export": "$I/cmpx/reject-illegal-axiom.ndjson", "challenge": "$CH/challenge.export", "config": "$CH/comparator.json"},
  {"name": "cmpx-accept-base", "export": "$I/cmpx/accept-base.ndjson", "challenge": "$CH/challenge.export", "config": "$CH/comparator.json"}],
 "threads_list": [384, 256, 255, 128, 32, 1]}
EOF
GA=(); for g in "${GATES[@]}"; do GA+=(--gate "$g"); done
for g in arena suitex cmpx; do
  printf '%s\n' "${GATES[@]}" | grep -qx $g && python3 -I "$HERE/gates.py" --out "$O/$g" --check "$CS" --legs "$O/legs.json" \
     --inputs "$O/inputs.json" --gate $g --jobs 32 --threads 8 --label "$LABEL amd $g"
done
printf '%s\n' "${GATES[@]}" | grep -qx threads && python3 -I "$HERE/gates.py" --out "$O/threads" --check "$CS" --inputs "$O/inputs.json" --gate threads --label "$LABEL amd threads"
printf '%s\n' "${GATES[@]}" | grep -qx mutants && python3 -I "$HERE/gates.py" --out "$O/mutants" --check "$CS" --inputs "$O/inputs.json" --gate mutants --jobs 1 --threads 384 --label "$LABEL amd mutants"
rm -rf "$O/rhmut" "$O/midmut"
echo "== RESULTS $LABEL"; for f in "$O"/*/*.tsv; do [ -f "$f" ] || continue; echo "-- $f"; awk -F'\t' 'NR>1{s[$0 ~ /\tFAIL\t/ ? "FAIL" : ($0 ~ /\tWARN\t/ ? "WARN" : "PASS")]++} END{for(k in s) printf "%s=%d ", k, s[k]; print ""}' "$f"; grep -P '\t(FAIL|WARN)\t' "$f" | cut -c1-260 | head -20; done
cat "$O"/*/summary.txt 2>/dev/null
