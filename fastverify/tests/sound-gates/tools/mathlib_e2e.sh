#!/bin/bash
# mathlib_e2e.sh OUTROOT LANES [PRESET] [EXTRA fastverify ARGS...]
# Mathlib differential END TO END through bin/fastverify (default --preset sound): every case of
# the Mathlib-differential case set MATHLIB_DIFF (projects/<case>, challenges/<P>; the challenge is built by the
# official B0+E0 since no challenge.export is shipped), LANES runs in parallel. Exercises the orchestrator's verdict logic
# (decide_sound, build-failure / export paths) on top of the check. Writes OUTROOT/e2e.tsv:
#   case  expected  verdict  trust  exit  seconds  build_option  export_option  status  basis
# status PASS iff verdict == cases.json expected_official (FAIL-CRITICAL if ACCEPTED otherwise; WARN for a false reject /
# no verdict). Exit 0 iff no FAIL.
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
R=${1:?outroot}; LANES=${2:-3}; PRESET=${3:-sound}; shift; shift; [ $# -gt 0 ] && shift
V=${MATHLIB_DIFF:-${BENCH_INPUTS:-/scratch/bench-inputs}/mathlib-differential}
WS=${FV_PACKAGES:-$FV/../verify/challenge}
mkdir -p "$R/runs"
CASES=$(python3 -I -c 'import json,sys; print(" ".join(sorted(json.load(open(sys.argv[1])))))' "$V/cases.json")
run_case() {
  local CASE=$1; shift; local CH=${CASE%%-*}; local OUT=$R/runs/$CASE; rm -rf "$OUT"
  local t0; t0=$(date +%s)
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$V/projects/$CASE" "$V/challenges/$CH" "$OUT" \
     --preset "$PRESET" --threads "${THREADS:-32}" --packages "$WS" "$@" > "$R/runs/$CASE.log" 2>&1
  echo "$CASE $? $(( $(date +%s) - t0 ))" >> "$R/runs/done.txt"
}
export -f run_case; export R PRESET FV V WS THREADS
: > "$R/runs/done.txt"
printf '%s\n' $CASES | xargs -P "$LANES" -I{} bash -c 'run_case "$@"' _ {} "$@"
python3 -I - "$V/cases.json" "$R" <<'PY'
import json, os, sys
cases = json.load(open(sys.argv[1])); R = sys.argv[2]
secs = {l.split()[0]: l.split()[2] for l in open(os.path.join(R, "runs", "done.txt")) if l.strip()}
rows, bad = [], 0
for c, info in sorted(cases.items()):
    exp = info["expected_official"]
    try:
        r = json.load(open(os.path.join(R, "runs", c, "result.json")))
    except Exception as e:
        r = {"verdict": "NO-RESULT", "verdict_basis": str(e)}
    v = r.get("verdict")
    st = "PASS" if v == exp else ("FAIL-CRITICAL" if v == "ACCEPTED" else "WARN")
    bad += st.startswith("FAIL")
    rows.append([c, exp, v, r.get("trust"), r.get("exit"), secs.get(c, ""), (r.get("build") or {}).get("option"),
                 (r.get("export") or {}).get("option"), st, (r.get("verdict_basis") or "")[:160]])
with open(os.path.join(R, "e2e.tsv"), "w") as f:
    f.write("case\texpected\tverdict\ttrust\texit\tseconds\tbuild_option\texport_option\tstatus\tbasis\n")
    for x in rows:
        f.write("\t".join(str(y) for y in x) + "\n")
print("mathlib e2e: %d cases, %d PASS, %d FAIL" % (len(rows), sum(x[8] == "PASS" for x in rows), bad))
sys.exit(1 if bad else 0)
PY
