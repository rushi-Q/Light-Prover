#!/bin/bash
# repro.sh [WORKDIR]: finding 069 - official vs fast flow of proj/ (TOOLWRAP_LOG marker) and proj-lp/ (LEAN_PATH shape)
# (harness from tests/063-*), any x86-64 host, ~2 min. FAST_PIPELINE_DIR=<tree> selects another pipeline (fastflow.sh).
D=$(cd "$(dirname "$0")" && pwd); H=$(ls -d $LIGHT_LEAN/fastverify/tests/063-*/x); W=${1:-${TMPDIR:-/tmp}/$USER-envdiff}
rm -rf "$W"; mkdir -p "$W"; cp -a "$H/challenge" "$W/challenge"; unset LEAN_TC FAST_TC; W0=$W
for PR in proj proj-lp; do W=$W0/$PR; mkdir -p "$W"; cp -a "$D/$PR" "$W/p"; echo "########## $PR"
bash "$H/officialflow.sh" "$W/p" "$W/off" "$W0/challenge" > "$W/off.log" 2>&1; orc=$?
bash "$H/fastflow.sh" "$W/p" "$W/fast" "$W0/challenge/challenge.export" > "$W/fast.log" 2>&1; frc=$?
echo "--- official build log (ENV lines / errors)"; grep -E 'ENV |error' "$W/off/log/build.log" | cut -c1-200 | sed 's/^/  /'
grep -E '^OFFICIAL' "$W/off.log" | sed 's/^/  /'
echo "--- fast"; grep -E '^FAST|fast: .*(RETRY|EXIT|SUMMARY)' "$W/fast.log" | cut -c1-250 | sed 's/^/  /'
python3 -I -c 'import json,sys
for l in open(sys.argv[1]):
    r=json.loads(l); print("  module", r["module"], "rc", r["rc"]); [print("   ", x[:200]) for x in r.get("output_head","").splitlines() if "ENV " in x or "error" in x]' "$W/fast/run/log/modules.jsonl" 2>/dev/null | head -60
echo "=== SUMMARY $PR official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
echo "--- environment of the module's lean process (Env.lean writes .lake/envprobe.txt): official | fast"
paste -d'|' "$W/off/proj/.lake/envprobe.txt" "$W/fast/run/proj/.lake/envprobe.txt" 2>/dev/null | cut -c1-260 | sed 's/^/  /'
done
[ -n "${KEEP:-}" ] || rm -rf "$W0"
