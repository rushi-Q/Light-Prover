#!/bin/bash
# Self-contained repro (~1 min). A VALID 2-module project (proj/): Main imports Helpers; Helpers.lean
# starts with two ordinary LINE comments, the first mentions the block-comment opener "/-", the second the closer "-/"
# followed by the words "import Main". Lean ignores both lines. The fast pipeline's header parser (prep.py header(),
# same rules in sched_r.py header_imports) looks for "/-" BEFORE stripping "--" comments, so it believes a block
# comment opens in line 1 and closes in line 2, and parses the rest of line 2 as a header command: Helpers "imports" Main.
# -> local graph Main->Helpers->Main -> sched_r.py: SystemExit('import cycle among local modules') -> BUILD FAILED.
# Official flow: lake build 4.33.1 + official lean4export + lake comparator 4.36 -> ACCEPTED.
# officialflow.sh / fastflow.sh / challenge/ are the harness from test 034 (copied unchanged).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-054-$$}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"
echo "prep.py header() on the two modules (same function as the deployed pipeline):"
python3 -I - "$W/proj/src" <<'PY'
import sys, os
src = open('$LIGHT_LEAN/fastverify/pipeline/prep.py').read()
ns = {'HDR_KW': ('import', 'public', 'meta', 'private', 'module', 'prelude')}
exec(src[src.index('def header'):src.index('def scan')], ns)
for m in ('Helpers', 'Main'):
    imps, _ = ns['header'](open(os.path.join(sys.argv[1], m + '.lean')).read())
    print(f'  {m}: local imports seen = {[i for i in imps if i in ("Helpers", "Main")]}')
PY
bash "$D/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
grep -h 'cycle' "$W/fast/pipeline.log" "$W/fast/run/log/"*.log 2>/dev/null | head -3 | sed 's/^/fast: /'
echo "=== SUMMARY official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
[ -z "${KEEP:-}" ] && rm -rf "$W"
