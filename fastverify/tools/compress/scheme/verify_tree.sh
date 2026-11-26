#!/bin/bash
# verify_tree.sh -- build + E1 export + TRUSTED sound check of a compressed RH candidate tree on one node
# (cwd = ship dir: fv/ = fastverify package copy, c1/t2.tar.gz = candidate tree, bin/expdiff, tools/).
# MODE=nomerge (default): --preset sound items minus merge, keep-going copy of the UNTRUSTED scheduler (lists every
# failing module). MODE=preset: plain --preset sound (timing-comparable). Then expdiff evidence vs the honest export
# (REF, default $RH_REF, used if REF_READY exists).
# env: WORKROOT (default $FV_SCRATCH, required), RH_CHALLENGE (default $LIGHT_LEAN/verify/challenge), TAG, THREADS, MODE,
#      KEEP_WORK, KEEP_EXPORT, KEEP_SHM.
set -u
S=$(pwd); TAG=${TAG:-c1}; R=${WORKROOT:-${FV_SCRATCH:?node-local scratch directory for the run (required; or set WORKROOT)}}/run-$TAG-$(date -u +%m%dT%H%M); mkdir -p "$R"
T=${THREADS:-${AMD_THREADS:-$(nproc)}}; MODE=${MODE:-nomerge}
WS=${RH_CHALLENGE:-$LIGHT_LEAN/verify/challenge}
REF=${REF:-${RH_REF:-}}; REF_READY=${REF_READY:-$REF.sha256}
# the shipped package's own --preset sound unsafe items minus merge (no hard-coded copy of the list)
U=$(python3 -I -c "import sys; sys.path.insert(0, '$S/fv/lib'); import fastverify as f; print(','.join(x for x in f.PRESETS['sound']['unsafe'] if x != 'merge'))") || { echo "cannot read PRESETS from $S/fv"; exit 2; }
ts() { date +%s.%N; }
echo "== $TAG $(date -u +%FT%TZ) host=$(hostname) threads=$T mode=$MODE R=$R"; df -h "$R" /dev/shm | tail -2
if [ "$MODE" = nomerge ]; then
KG=${KEEP_GOING_FLAG:-$(dirname "$R")/KEEP_GOING}   # stable flag path (a re-run in the same ship dir must not inherit
                                                    # the flag path of an earlier, deleted run dir: C4 v2 stopped at 4k modules)
python3 -I - "$S/fv/build/sched.py" "$KG" <<'PY'
import re, sys
p, flag = sys.argv[1], sys.argv[2]; s = open(p).read()
line = 'KEEP_GOING = os.path.exists(%r)  # scheme copy only: keep building after a failure (untrusted)' % flag
if 'KEEP_GOING = os.path.exists(' in s:
    s = re.sub(r'KEEP_GOING = os\.path\.exists\([^)]*\)  # scheme copy only[^\n]*', lambda m: line, s)
else:
    lines = s.split('\n'); i = max(k for k, l in enumerate(lines[:80]) if l.startswith('import ') or l.startswith('from '))
    lines.insert(i + 1, line); s = '\n'.join(lines)
    old = 'while ready and len(running) < jobs and not failed and not crashed and not srcchanged:'
    assert old in s, 'sched.py changed'
    s = s.replace(old, 'while ready and len(running) < jobs and (KEEP_GOING or not failed) and not crashed and not srcchanged:')
open(p, 'w').write(s)
print('sched.py keep-going patch ok ->', flag)
PY
touch "$KG"; UNSAFE=(--unsafe "$U")
else UNSAFE=(); fi
mkdir -p "$R/t2"; t0=$(ts); tar xzf "$S/c1/t2.tar.gz" -C "$R/t2"; echo "extract $(echo "$(ts) - $t0" | bc) s"; sha256sum "$S/c1/t2.tar.gz"
echo "TREE files=$(find $R/t2/src -name '*.lean' | wc -l) lines=$(find $R/t2/src -name '*.lean' -print0 | xargs -0 cat | wc -l)"
REFARG=(); [ -f "$REF_READY" ] && REFARG=(--reference-export "$REF")
o=$R/run; t0=$(ts)
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$S/fv/bin/fastverify" "$R/t2" "$WS" "$o" --preset sound --threads "$T" \
  "${UNSAFE[@]}" --no-build-fallback --export-dir /dev/shm --keep-work \
  --challenge-sha256 3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d --comparator-sha256 d419c0d8cd8696eb6c3ebc01deb500038fb5820f04c6edc2b1b4ec24673b84c0 "${REFARG[@]}" > "$o.log" 2>&1
rc=$?; echo "fastverify rc=$rc wall=$(echo "$(ts) - $t0" | bc) s"
python3 -I - "$o/result.json" "$o/log/build-fast/sched.out" "$R/t2/.chainmerge.tsv" <<'PY'
import json, sys, os
r = json.load(open(sys.argv[1])); e = r.get("export") or {}
print("RESULT verdict=%s trust=%s basis=%s" % (r.get("verdict"), r.get("trust"), r.get("verdict_basis")))
print("RESULT export sha256=%s size=%s identical_to_reference=%s" % (e.get("sha256"), e.get("size"), (e.get("reference") or {}).get("identical")))
print("RESULT stage_seconds=%s" % json.dumps(r.get("stage_seconds")))
cs = (r.get("checks") or {}).get("sound") or {}
print("RESULT check=%s %s s legs=%s" % (cs.get("verdict"), cs.get("seconds"), json.dumps((cs.get("stage") or {}).get("leg_ms"))))
if os.path.exists(sys.argv[2]):
    mods = [json.loads(l) for l in open(sys.argv[2]) if '"event": "module"' in l]
    last = {}
    for m in mods: last[m['module']] = m
    fails = sorted(n for n, m in last.items() if m.get('rc') != 0 or m.get('error_msg') or m.get('missing'))
    print("RESULT modules=%d sum_cpu=%.0f makespan=%.0f failed=%d" % (len(mods), sum(m.get('cpu', 0) for m in mods),
          max((m['start'] + m['wall'] for m in mods), default=0), len(fails)))
    merged = {}
    if os.path.exists(sys.argv[3]):
        for l in open(sys.argv[3]): a, b = l.split(); merged.setdefault(b, []).append(a)
    for n in fails:
        d = last[n].get('stdout_head', '') or ''
        i = d.find('"data":"')
        print('FAIL', n, 'merged:' + ','.join(merged.get(n, [])) if n in merged else '', (d[i + 8:i + 400] if i >= 0 else d[:400]).replace('\\n', ' '))
PY
EXP=$(readlink -f "$o/solution.export" 2>/dev/null)
if [ -f "$EXP" ]; then
  sha256sum "$EXP" | tee "$R/export.sha256"
  if [ -f "$REF_READY" ]; then
    EXPDIFF="$S/bin/expdiff" AMD_THREADS=${EVID_THREADS:-64} bash "$S/tools/amd-evidence.sh" "$EXP" "$R/evidence" "$REF" "$WS/export-targets.txt" 2>&1 | tail -60
  fi
  [ -n "${KEEP_EXPORT:-}" ] && { cp "$EXP" "$R/solution.export"; echo "export kept $R/solution.export"; }
fi
PROJ="$o/work/proj"
mkdir -p "$R/keep"; cp "$R/keep-meta-metrics.json" "$R/blueprint.md" "$R/keep/" 2>/dev/null; cp "$o/result.json" "$o.log" "$R/read-t2/metrics.json" "$R/export.sha256" "$R/keep/" 2>/dev/null
cp "$o"/log/*.json "$o/log/build-fast/sched.out" "$R/t2/.chainmerge.tsv" "$R/keep/" 2>/dev/null
cp -r "$R/evidence" "$R/keep/" 2>/dev/null
[ -n "$EXP" ] && [ -z "${KEEP_SHM:-}" ] && case "$EXP" in /dev/shm/*) rm -rf "$(dirname "$EXP")";; esac   # KEEP_SHM=1: leave the export in /dev/shm (disk-tight nodes)
[ -z "${KEEP_WORK:-}" ] && rm -rf "$o/work"
echo "kept: $(du -sh $R/keep)"; df -h "$R" | tail -1; echo "== done $(date -u +%FT%TZ)"
exit $rc
