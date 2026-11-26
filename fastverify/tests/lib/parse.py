#!/usr/bin/env python3
"""parse.py ID LOG [EXPECT]  ->  one TSV row per case:  id case official_rc fast_rc official_sha fast_sha result note

Understands the output formats of the original repro scripts:
  multi-case: '######## case a' blocks + one '=== SUMMARY case a: official_rc=.. fast_rc=..; case b: ...' line
  per-project: '##### proj-x' blocks, each ending with '=== SUMMARY proj-x official_rc=.. fast_rc=..'
  single-project repros: '=== SUMMARY official_rc=.. fast_rc=..'
and the generic lines printed by tests/lib/*.sh:  '=== RESULT case=<c> official=<rc> fast=<rc> [osha=..] [fsha=..]'.

result:  PASS         fast rc == official rc and (when both exported) same export sha256
         PASS-DECLINE fast tool declined (rc 2) where the official REJECTS -> the official path decides
         WARN-DECLINE fast tool declined where the official ACCEPTS (no fast verdict; final verdict still official)
         WARN-ERROR   the package refused / gave no verdict (ERROR) where the official REJECTS
         WARN-REFUSED the package refused (ERROR, fail closed: e.g. a symlink leaving the project) where the official ACCEPTS
         WARN-CRASH   fast tool crashed/timed out (exit not 0/1/2) where the official REJECTS (not an accept)
         FAIL-ACCEPT  official REJECTS, fast ACCEPTS   (accuracy violation)
         FAIL-EXPORT  both flows produced an export and the exports differ (accuracy violation, whatever the verdicts)
         FAIL-REJECT  official ACCEPTS, fast REJECTS    (false reject)
         SKIP         component missing (fast rc 3) / case not run
EXPECT (optional, lines 'case official_rc [official_sha16]'): the official verdict recorded with the repro; a live official result
that differs is reported in the note column as DRIFT (the environment changed - investigate before trusting the row)."""
import os, re, sys

fid, logf = sys.argv[1], sys.argv[2]
log = open(logf, errors='replace').read()
expect = {}
if len(sys.argv) > 3:
    try:
        for ln in open(sys.argv[3]):
            ln = ln.split('#')[0].split()
            if len(ln) >= 2:
                expect[ln[0]] = (ln[1], ln[2] if len(ln) > 2 else '-')
    except FileNotFoundError:
        pass

parts = re.split(r'^#{3,} ?(?:case )?([^\n:]+?)\s*(?::.*)?$', log, flags=re.M)
blocks = {} if len(parts) > 1 else {'-': log}
for i in range(1, len(parts) - 1, 2):
    blocks[parts[i].strip()] = parts[i + 1]
rows = []
forced = {}   # RESULT lines may carry result=<class> (custom tests that know the expected behaviour better)
for line in log.splitlines():
    if line.startswith('=== RESULT'):
        kv = dict(re.findall(r'(\w+)=(\S+)', line))
        rows.append((kv.get('case', '-'), kv.get('official', '?'), kv.get('fast', '?'), kv.get('osha'), kv.get('fsha')))
        if 'result' in kv:
            forced[len(rows) - 1] = kv['result']
    elif line.startswith('=== SUMMARY'):
        if 'case ' in line:
            rows += [(c.strip(), o, f, None, None) for c, o, f in re.findall(r'case ([^:;]+): official_rc=(\d+) fast_rc=(\d+)', line)]
        else:
            m = re.match(r'=== SUMMARY\s+(?:(\S+)\s+)?official_rc=(\d+) fast_rc=(\d+)', line)
            if m:
                rows.append(((m.group(1) or '-').strip(), m.group(2), m.group(3), None, None))
out = []
for ri, (c, o, f, osha, fsha) in enumerate(rows):
    b = blocks.get(c, log if len(blocks) <= 1 else '')
    if osha is None:
        s = re.findall(r'official: lean4export rc=0 \d+ bytes sha256 (\w+)', b)
        osha = s[-1] if s else '-'
    if fsha is None:
        s = re.findall(r'fast: export \S+ bytes sha256 (\w+)', b)
        fsha = s[-1] if s else '-'
    note = ''
    pth = re.findall(r'fast: path (.*)', b)
    if pth:
        note = 'path ' + pth[-1].strip()
    if f == '3':
        res = 'SKIP'
    elif osha != '-' and fsha != '-' and osha[:16] != fsha[:16]:
        res = 'FAIL-EXPORT'   # both flows exported (whatever the verdicts): the exports must be byte-identical
    elif o == f:
        res = 'PASS'
        if o == '0' and (osha == '-' or fsha == '-'):
            note = (note + '; ' if note else '') + 'export sha not compared'
    elif f == '2':   # decline -> the official path decides; on an official ACCEPT the fast check gave no verdict (perf/coverage)
        res = 'PASS-DECLINE' if o == '1' else 'WARN-DECLINE'
        note = (note + '; ' if note else '') + 'declined'
    elif f == '4':   # the package refused / gave no verdict (ERROR): never an accept
        res = 'WARN-ERROR' if o == '1' else 'WARN-REFUSED'   # explicit refusal = fail closed (no verdict), not a reject
        note = (note + '; ' if note else '') + 'package ERROR (refused / no verdict)'
    elif f.startswith('E'):   # crash / timeout of a fast checker: never an accept, but no verdict either
        res = 'WARN-CRASH' if o == '1' else 'FAIL-REJECT'
        note = (note + '; ' if note else '') + f'checker exit {f[1:]}'
    elif o == '1' and f == '0':
        res = 'FAIL-ACCEPT'
    elif o == '0' and f != '0':
        res = 'FAIL-REJECT'
    else:
        res = 'FAIL'
    if res == 'PASS' and o == '0' and re.search(r'fast: disagreement: fast checks REJECTED', b):
        res = 'FAIL-REJECT'   # the official comparator accepted, but the package's fast verdict REJECTED (false reject)
        note = (note + '; ' if note else '') + 'fast checks REJECTED a project the official accepts'
    if ri in forced:
        res = forced[ri]
    if res.startswith('FAIL') and ('!unsafe' in c or os.environ.get('FV_UNSAFE_RUN') == '1'):
        res = 'UNSAFE-' + res   # documented breakage of an opt-in UNSAFE option (not a failure of the exact package)
    if c in expect:
        eo, es = expect[c]
        if eo != o or (es != '-' and osha != '-' and es[:16] != osha[:16]):
            note = (note + ' ' if note else '') + f'DRIFT(recorded official {eo} {es})'
    out.append((c, o, f, osha[:16], fsha[:16], res, note))
for c in expect:
    if c not in [r[0] for r in out]:
        out.append((c, expect[c][0], '-', expect[c][1], '-', 'SKIP', 'case not run'))
if not out:
    out.append(('-', '-', '-', '-', '-', 'ERROR', 'no SUMMARY/RESULT line in log'))
for r in out:
    print('\t'.join([fid] + list(r)))
