#!/bin/bash
# heavy (1,657 RH modules + Mathlib imports; ~10-15 min with 64 threads)
# test rh-minif-export (kind bench/e2e: a real RH sub-project through the package with the RH challenge, compared with the ORIGINAL-LEAN
#   reference export of the same project: /scratch/bench-inputs/rh-miniF/ref/solution.export, sha256 b38f52932340a437)
# finding: rh-minif-export: on real RH code the package's export must be byte-identical to the original-Lean export and the verdicts official
# proj/ = rh-miniF pristine sources made lake-buildable (defaultTargets restricted / empty missing lib dirs; prepared as inputs/miniF-lake2).
# Rows: verdict (official ACCEPTED expected), export (sha vs the original-Lean reference), fast (the fast checks' verdict);
# the note carries the package path and stage seconds (speed).
{ # whole script parsed before it runs
set -u
TD=$(cd "$(dirname "$0")" && pwd); FVB=${FV_BIN:-$TD/../../bin/fastverify}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/rh-minif-export.XXXXXX")}; mkdir -p "$(dirname "$W")"; W=$(readlink -f "$(dirname "$W")")/$(basename "$W"); rm -rf "$W"; mkdir -p "$W"
C=/scratch/bench-inputs/rh-miniF/challenge; REF=/scratch/bench-inputs/rh-miniF/ref/solution.export; L=$W.log
case $FVB in *standin*) echo "=== RESULT case=verdict official=0 fast=3" > "$L";; *)
if [ "${FV_FAST:-}" = deployed ] || [ ! -s "$REF" ]; then echo "=== RESULT case=verdict official=0 fast=3" > "$L"; else
  t0=$(date +%s)
  env -i HOME="$HOME" PATH=/usr/bin:/bin "$FVB" "$TD/proj" "$C" "$W/out" ${FV_ARGS:---check C3,C0} --threads "${FV_BENCH_THREADS:-48}" \
    --packages $LIGHT_LEAN/verify/challenge --comparator-config "$C/comparator.nanoda.json" \
    --reference-export "$REF" > "$W/fastverify.log" 2>&1; rc=$?
  tail -5 "$W/fastverify.log" > "$L"
  python3 -I - "$W/out/result.json" "$rc" "$(( $(date +%s) - t0 ))" >> "$L" 2>&1 <<'PY'
import json, sys
try: r = json.load(open(sys.argv[1]))
except Exception as e: print(f'=== RESULT case=verdict official=0 fast=4'); sys.exit()
v = r.get('verdict'); vf = r.get('verdict_fast'); e = r.get('export') or {}; ref = (e.get('reference') or {})
st = r.get('stage_seconds') or {}; b = r.get('build') or {}
path = f"build={b.get('mode')} export={e.get('mode')} secs={sys.argv[3]} " + ' '.join(f'{k}={v}' for k, v in st.items() if isinstance(v, (int, float)))
print(f'fast: path {path}')
code = {'ACCEPTED': 0, 'REJECTED': 1, 'DECLINED': 2}
print(f"=== RESULT case=verdict official=0 fast={code.get(v, 4)}")
print(f"=== RESULT case=export official=0 fast={0 if e.get('sha256') else 4} osha={(ref.get('sha256') or 'b38f52932340a437')[:16]} fsha={(e.get('sha256') or '-')[:16]}")
print(f"=== RESULT case=fast-checks official=0 fast={code.get(vf, 4)}")
PY
fi;; esac
python3 -I "$TD/../lib/parse.py" rh-minif-export "$L" | tee "$W.tsv"
[ -n "${KEEP_WORK:-}" ] || rm -rf "$W"
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}
