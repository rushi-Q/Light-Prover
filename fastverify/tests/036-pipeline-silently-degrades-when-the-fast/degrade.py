#!/usr/bin/env python3
"""degrade.py WORK : finding 036 (the deployed pipeline silently degraded when the fast toolchain/exporter could not start:
every module built 3x, official fallbacks, exit 0, provenance claiming the fast components).
Fixed behaviour tested here on a COPY of the package (tests/, pipeline/ and other non-package dirs excluded) in which one pinned component
is broken (one byte flipped -> sha256 mismatch, or truncated -> cannot start):
  normal          : intact package -> verdict == official (ACCEPTED), result.json records which tool produced each stage
  bad-exporter    : native exporter corrupted     -> refuse (no verdict), or official verdict with export NOT by the native tool
  bad-checkB      : check-B gruszka corrupted      -> refuse, or official verdict and checkB never ACCEPTED
  (bad-checkA was removed with check A; the package runs --check C3,C0 = check B + the official comparator)
  bad-toolchain   : official lean pin altered      -> must refuse (no verdict at all: the official toolchain is untrusted)
Prints '=== RESULT case=<c> official=<rc> fast=<rc>' lines (fast: 0 acc, 1 rej, 2 refused/declined) for lib/parse.py;
a degradation that is not reported (or a verdict produced by a broken component) is printed as fast=0 against official=1."""
import json, os, re, shutil, subprocess, sys

W = os.path.realpath(sys.argv[1]); os.makedirs(W, exist_ok=True)
TD = os.path.dirname(os.path.realpath(__file__)); FV = os.path.realpath(os.environ.get('FV_ROOT') or os.path.join(TD, '..', '..'))
PROJ = os.path.join(TD, 'x', 'proj'); CH = os.path.realpath(os.path.join(TD, '..', '059-pipeline-export-sh-breaks-on-a-work-dire', 'x', 'challenge'))
T = os.environ.get('EVAL_THREADS', '8'); HOME = os.environ.get('HOME', '/tmp')


def cpdir(src, dst):   # writable copy (the deployed bin dirs are read-only)
    shutil.copytree(src, dst, copy_function=shutil.copyfile)
    for dp, dn, fn in os.walk(dst):
        os.chmod(dp, 0o755)
        for x in fn: os.chmod(os.path.join(dp, x), 0o755)


def flip(src, dst, truncate=False):
    if os.path.lexists(dst): os.unlink(dst)
    shutil.copyfile(src, dst); os.chmod(dst, 0o755)
    with open(dst, 'r+b') as f:
        if truncate:
            f.truncate(100)
        else:
            f.seek(4096); b = f.read(1); f.seek(4096); f.write(bytes([b[0] ^ 1]))


def copy_pkg(name):
    d = os.path.join(W, name, 'fv')
    shutil.copytree(FV, d, symlinks=True, ignore=shutil.ignore_patterns('tests', 'pipeline', 'review-*', '__pycache__', 'results'))
    return d


def run(pkg, name):
    out = os.path.join(W, name, 'out')
    p = subprocess.run(['env', '-i', f'HOME={HOME}', 'PATH=/usr/bin:/bin', os.path.join(pkg, 'bin', 'fastverify'), PROJ, CH, out,
                        '--check', 'C3,C0', '--threads', T], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    r = {}
    try:
        r = json.load(open(os.path.join(out, 'result.json')))
    except Exception:
        pass
    print(f'##### {name}\n  fastverify exit {p.returncode}: ' + ' | '.join(p.stdout.strip().splitlines()[-3:])[:600])
    return p.returncode, r


def official():
    p = subprocess.run(['bash', os.path.join(TD, '..', 'lib', 'officialflow.sh'), PROJ, os.path.join(W, 'official'), CH],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return 0 if p.returncode == 0 else 1


def verdict_rc(rc, r):
    v = str(r.get('verdict', '')).upper()
    if rc == 0 and v == 'ACCEPTED': return 0
    if rc == 1 and v == 'REJECTED': return 1
    return 2


orc = official()
print(f'  official flow: {orc}')
# normal
rc, r = run(FV, 'normal')
f = verdict_rc(rc, r); e = r.get('export') or {}
prov = any(k in e for k in ('mode', 'tool', 'impl', 'by', 'exporter'))
print(f'  export provenance recorded: {prov} ({ {k: e.get(k) for k in ("mode", "tool", "impl", "by", "exporter") if k in e} })')
if f == 0 and not prov:
    print('  WARNING: no export provenance in result.json')
print(f'=== RESULT case=normal official={orc} fast={f}')

# bad-exporter
d = copy_pkg('bad-exporter'); cj = os.path.join(d, 'export', 'components.json'); c = json.load(open(cj))
flip(c['native']['path'], os.path.join(W, 'bad-exporter', 'lean4export.bad')); c['native']['path'] = os.path.join(W, 'bad-exporter', 'lean4export.bad')
json.dump(c, open(cj, 'w'), indent=1)
rc, r = run(d, 'bad-exporter'); f = verdict_rc(rc, r); e = r.get('export') or {}
native = 'native' in json.dumps(e).lower() and 'official' not in str(e.get('mode', e.get('tool', ''))).lower()
print(f'  export record: {json.dumps(e)[:400]}')
if f == orc: print(f'  export produced by: {e.get("mode")}')
if f in (0, 1) and native:
    print('  FAIL: a verdict was produced while claiming the (broken) native exporter'); f = 1 - orc if orc in (0, 1) else 0
print(f'=== RESULT case=bad-exporter official={orc} fast={f}' + (' result=PASS-REFUSED' if f == 2 else ''))

# bad-checkB
d = copy_pkg('bad-checkB'); cj = os.path.join(d, 'check', 'checkB', 'components.json'); c = json.load(open(cj))
bd = os.path.join(W, 'bad-checkB', 'bin'); cpdir(c['bin_dir'], bd); flip(os.path.join(c['bin_dir'], 'gruszka'), os.path.join(bd, 'gruszka'))
c['bin_dir'] = bd; json.dump(c, open(cj, 'w'), indent=1)
rc, r = run(d, 'bad-checkB'); f = verdict_rc(rc, r); cb = (r.get('checks') or {}).get('checkB') or {}
print(f'  checkB record: {json.dumps(cb)[:300]}')
if str(cb.get('verdict', '')).upper() == 'ACCEPTED':
    print('  FAIL: check B ACCEPTED with a corrupted gruszka'); f = 0 if orc == 1 else f
print(f'=== RESULT case=bad-checkB official={orc} fast={f}' + (' result=PASS-REFUSED' if f == 2 else ''))

# bad-toolchain: official lean pin altered -> must refuse
d = copy_pkg('bad-toolchain'); cj = os.path.join(d, 'config', 'components.json'); c = json.load(open(cj))
for tc in c.get('lean_toolchains', {}).values():
    tc['sha256']['bin/lean'] = '0' * 64
json.dump(c, open(cj, 'w'), indent=1)
rc, r = run(d, 'bad-toolchain'); f = verdict_rc(rc, r)
if f != 2:
    print('  FAIL: the package produced a verdict although the official toolchain does not match its pin')
print(f'=== RESULT case=bad-toolchain official={orc} fast={f} result=' + ('PASS-REFUSED' if f == 2 else 'FAIL-UNPINNED'))
