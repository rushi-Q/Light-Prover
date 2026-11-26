#!/bin/bash
# Regression test: an illegal axiom named [anonymous] (name index 0) used by the target's proof must never be ACCEPTED
# by any sound judge. usage: a01-regress.sh [CHECK_SCRIPT [extra args...]]   (default: all four judges, live pins)
# exit 0 iff every judge run gives a non-ACCEPTED verdict (REJECTED expected).
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
F=$(cd "$HERE/../../check" && pwd)   # the judges of THIS package copy (was a fixed path to the live package)
S=/scratch/fastverify-next/selftest
W=$(mktemp -d "${TMPDIR:-/tmp}/a01-regress.XXXXXX") || { echo "FAIL setup: mktemp"; exit 1; }; trap 'rm -rf "$W"' EXIT
mkdir -p "$W/wd"
python3 -I - "$S/good.export" "$W/a01.export" <<'PY'
import json, sys
src, out = sys.argv[1:3]
lines = open(src, 'rb').read().split(b'\n')
if lines[-1] == b'': lines.pop()
recs = [json.loads(l) for l in lines[1:]]
names = {0: ()}; nexpr = 0
for r in recs:
    if 'in' in r:
        k = 'str' if 'str' in r else 'num'
        names[r['in']] = names[r[k]['pre']] + ((r[k]['str'],) if k == 'str' else (r[k]['i'],))
    elif 'ie' in r: nexpr = max(nexpr, r['ie'] + 1)
idx = {v: k for k, v in names.items()}
tgt = idx[('fvSelfTest',)]
k = next(i for i, r in enumerate(recs) if 'thm' in r and r['thm']['name'] == tgt)
thm = recs.pop(k)['thm']
def e(kind, data):
    global nexpr
    recs.append({'ie': nexpr, kind: data}); nexpr += 1; return nexpr - 1
f = e('const', {'name': idx[('False',)], 'us': []})
recs.append({'axiom': {'isUnsafe': False, 'levelParams': [], 'name': 0, 'type': f}})
anon = e('const', {'name': 0, 'us': []})
el = e('const', {'name': idx[('False', 'elim')], 'us': [0]})
pf = e('app', {'arg': anon, 'fn': e('app', {'arg': thm['type'], 'fn': el})})
recs.append({'thm': dict(thm, value=pf)})
with open(out, 'w') as o:
    o.write(lines[0].decode() + '\n')
    for r in recs: o.write(json.dumps(r, sort_keys=True, separators=(',', ':'), ensure_ascii=False) + '\n')
PY
fails=0
run() {  # run LABEL SCRIPT [args]
  local lab=$1 scr=$2; shift 2
  "$scr" "$W/a01.export" "$S/challenge.export" "$S/comparator.json" --threads 2 --workdir "$W/wd" "$@" > "$W/$lab.json" 2>/dev/null; local rc=$?
  local v why; v=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])["verdict"])' "$W/$lab.json" 2>/dev/null)
  why=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])["reason"][:200])' "$W/$lab.json" 2>/dev/null)
  if [ -z "$v" ]; then echo "FAIL $lab: rc=$rc, no verdict JSON (judge did not run?)"; fails=$((fails+1));
  elif [ "$rc" = 0 ] || [ "$v" = ACCEPTED ]; then echo "FAIL $lab: rc=$rc verdict=$v (false ACCEPTED)"; fails=$((fails+1));
  else echo "PASS $lab: rc=$rc verdict=$v ($why)"; fi
}
if [ $# -gt 0 ]; then
  run custom "$@"
else
  run sound "$F/sound/check-sound.sh"
  run lowmem "$F/lowmem/check-sound-lowmem.sh"
  run ultralowmem "$F/lowmem/check-sound-ultralowmem.sh"
  run lowmem437 "$F/lowmem/check-sound-lowmem.sh" --pins "$F/lowmem/pins-437.env"
fi
[ "$fails" = 0 ]
