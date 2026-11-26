#!/bin/bash
# component.sh ID WORK SCRIPT [ARGS...]
# Runs a component regression script that prints 'PASS <text>' / 'FAIL <text>' / 'SKIP <text>' lines (and, for the toolchain test,
# the toolchain regression's '  regress: SAME|DIFFERENT  NNN... ' lines) ONCE per suite run (cached in the parent of WORK, guarded by flock, so
# several findings can share one run of an expensive script), and prints the TSV rows that concern finding ID:
#   * regress lines whose case starts with ID                         -> PASS (SAME) / FAIL (DIFFERENT)
#   * PASS/FAIL lines that mention 'ID' or carry the tag [ID] / or all of them when FV_COMPONENT_ALL=1
# Exit 0 iff no FAIL row. Rows: id case - - - - PASS|FAIL|SKIP note (SKIP: a row whose input or environment is missing;
# it is neither PASS nor FAIL)
{ # whole script parsed before it runs (safe against edits while running)
set -u
id=$1; W=$2; S=$(readlink -f "$3"); shift 3   # canonical path: one shared run per script
mkdir -p "$(dirname "$W")"; P=$(readlink -f "$(dirname "$W")"); key=$(echo "${FV_RUN_ID:-$$} $S $*" | md5sum | cut -c1-12)   # shared only within one run_all.sh run
C=$P/component-$key.out
(
  flock 9
  [ -s "$C.done" ] || { bash "$S" "$@" > "$C" 2>&1; echo "exit $?" > "$C.done"; }
) 9> "$P/component-$key.lock"
cp "$C" "$W.log"; cat "$C.done" >> "$W.log"
python3 -I - "$id" "$C" "${FV_COMPONENT_ALL:-0}" "$(basename "$S")" <<'EOF' | tee "$W.tsv"
import re, sys
fid, path, allrows, script = sys.argv[1], sys.argv[2], sys.argv[3] == '1', sys.argv[4]
rows = []
for ln in open(path, errors='replace'):
    ln = ln.rstrip('\n')
    m = re.match(r'\s*regress:\s+(SAME|DIFFERENT)\s+(\S.*)$', ln)
    if m:
        case = re.sub(r'\s+', ' ', m.group(2))[:70]
        if case.startswith(fid):
            rows.append((case.replace('\t', ' '), 'PASS' if m.group(1) == 'SAME' else 'FAIL', 'regress_toolchain'))
        continue
    m = re.match(r'(PASS|FAIL|SKIP) (.*)$', ln)
    if not m:   # 'RESULT <case> ... PASS|FAIL' (check B wrapper test)
        m2 = re.match(r'RESULT (\S+.*?)\s+(PASS|FAIL)\s*$', ln)
        if m2: m = type('M', (), {'group': lambda self, i, a=(None, m2.group(2), m2.group(1)): a[i]})()
    if not m and '\t' in ln:   # TSV row whose last field is PASS|FAIL (export stage test)
        f = ln.split('\t')
        if len(f) >= 2 and f[-1].strip() in ('PASS', 'FAIL'):
            c = ' '.join(x for x in f[:-1] if x)
            m = type('M', (), {'group': lambda self, i, a=(None, f[-1].strip(), c): a[i]})()
    if m and (allrows or fid in m.group(2) or f'[{fid}]' in m.group(2)):
        rows.append((re.sub(r'\s+', ' ', m.group(2))[:70].replace('\t', ' '), m.group(1), script))
if not rows:
    rows.append(('-', 'ERROR', f'no rows for {fid} in {script} output'))
for c, r, n in rows:
    print('\t'.join([fid, c, '-', '-', '-', '-', r, n]))
EOF
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}
