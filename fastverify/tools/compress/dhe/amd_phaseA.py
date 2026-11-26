#!/usr/bin/env python3
"""amd_phaseA.py — module-level check of an edit list against a read-only build tree (DHE).
For every edited module: write the edited source + the module's exact setup (from the build plan) into WORK/<mod>/,
elaborate it with LEAN inside bwrap (no network, home hidden, everything read-only except WORK/<mod>), compare the new
.olean with the tree's .olean using DeadLetCheck (batch mode). Outputs in OUT: results.tsv, pass_edits.tsv (the edit
lines of passing modules), summary.json."""
import argparse, collections, concurrent.futures as cf, json, os, re, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from editlib import read_edits, apply

ap = argparse.ArgumentParser()
for k in ('edits', 'src', 'plan', 'lean-path', 'base-proj', 'lean', 'tc', 'dlc', 'work', 'out'):
    ap.add_argument('--' + k, required=True)
ap.add_argument('--threads', type=int, default=os.cpu_count())
ap.add_argument('--timeout', type=int, default=1200)
ap.add_argument('--extra', default='-Ddebug.skipKernelTC=true,-Dlinter.all=false')
a = ap.parse_args()
T0 = time.time()
os.makedirs(a.work, exist_ok=True); os.makedirs(a.out, exist_ok=True)
E, RAW = read_edits(a.edits)
mods = sorted(E)
need = set(mods)
plan = {}
with open(a.plan) as f:
    for ln in f:
        if not ln.startswith('{"argv"'):
            continue
        r = json.loads(ln)
        if r['name'] in need:
            plan[r['name']] = r
print(f"edited modules {len(mods)}, in plan {len(plan)}", flush=True)
tc = os.path.realpath(a.tc)
lean = os.path.realpath(a.lean)

def sbx(wd, argv, env_lp):
    return ['env', '-i', '/usr/bin/bwrap', '--ro-bind', '/', '/', '--tmpfs', '/home', '--tmpfs', '/root', '--tmpfs',
            '/run/user', '--tmpfs', '/tmp', '--dir', '/tmp/home', '--tmpfs', '/run', '--tmpfs', '/var', '--dev', '/dev',
            '--proc', '/proc', '--clearenv', '--ro-bind', tc, tc, '--bind', wd, wd,
            '--setenv', 'PATH', f'{tc}/bin:/usr/bin:/bin', '--setenv', 'HOME', '/tmp/home', '--setenv', 'LANG', 'C.UTF-8',
            '--setenv', 'LEAN_PATH', env_lp, '--unshare-all', '--die-with-parent', '--new-session', '--chdir', wd, '--'] + argv

def one(m):
    wd = os.path.join(a.work, m)
    os.makedirs(wd, exist_ok=True)
    r = plan.get(m)
    if r is None:
        return m, 'noplan', 0.0, ''
    srcp = os.path.join(a.src, m.replace('.', '/') + '.lean')
    L = open(srcp, encoding='utf-8').read().split('\n')
    N = apply(L, E[m])
    with open(os.path.join(wd, 'M.lean'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(N))
    with open(os.path.join(wd, 'setup.json'), 'w') as f:
        f.write(r['setup'])
    tst = [x for x in r['argv'] if x.startswith('--tstack')]
    argv = [lean] + tst + [os.path.join(wd, 'M.lean'), '-o', os.path.join(wd, 'M.olean'), '--setup',
                           os.path.join(wd, 'setup.json')] + [x for x in a.extra.split(',') if x]
    t = time.time()
    try:
        p = subprocess.run(sbx(wd, argv, a.lean_path), capture_output=True, text=True, timeout=a.timeout)
        rc = p.returncode; out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        rc = 'timeout'; out = ''
    wall = time.time() - t
    err = ''
    if rc != 0:
        m_ = re.search(r'error[^:]*: (.*)', out)
        err = (m_.group(1) if m_ else out.strip().split('\n')[-1] if out.strip() else '')[:160]
        with open(os.path.join(wd, 'out.txt'), 'w') as f:
            f.write(out[-20000:])
    return m, rc, wall, err

res = {}
with cf.ThreadPoolExecutor(a.threads) as ex:
    for k, (m, rc, wall, err) in enumerate(ex.map(one, mods)):
        res[m] = (rc, wall, err)
        if (k + 1) % 1000 == 0:
            print(f"elaborated {k + 1}/{len(mods)} at {time.time() - T0:.0f} s", flush=True)
TA = time.time()
ok = [m for m in mods if res[m][0] == 0]
print(f"elaboration done: {len(ok)} of {len(mods)} OK, {TA - T0:.0f} s", flush=True)
# DeadLetCheck in batches
nb = max(1, min(a.threads // 2, len(ok) // 50 + 1))
chunks = [ok[i::nb] for i in range(nb)]
dlcw = os.path.join(a.work, '_dlc'); os.makedirs(dlcw, exist_ok=True)
import shutil
shutil.copy(a.dlc, os.path.join(dlcw, 'DeadLetCheck.lean'))
def dlc(i):
    lf = os.path.join(dlcw, f'list{i}.txt')
    with open(lf, 'w') as f:
        for m in chunks[i]:
            base = plan[m]['outputs'][0]
            assert base.endswith('.olean')
            f.write(f"{m} {base} {os.path.join(a.work, m, 'M.olean')}\n")
    argv = [f'{tc}/bin/lean', '--run', os.path.join(dlcw, 'DeadLetCheck.lean'), '--list', lf]
    p = subprocess.run(sbx(dlcw, argv, f'{tc}/lib/lean'), capture_output=True, text=True)
    return p.stdout
summ = {}
detail = collections.defaultdict(list)
with cf.ThreadPoolExecutor(nb) as ex:
    for outp in ex.map(dlc, range(nb)):
        for ln in outp.split('\n'):
            if not ln.strip():
                continue
            m, rest = ln.split(' ', 1)
            if rest.startswith('SUMMARY') or rest.startswith('ERROR'):
                summ[m] = rest
            else:
                detail[m].append(rest)
TB = time.time()
S = collections.Counter()
lines_pass = 0
with open(os.path.join(a.out, 'results.tsv'), 'w') as f, open(os.path.join(a.out, 'pass_edits.tsv'), 'w') as pf:
    for m in mods:
        rc, wall, err = res[m]
        sm = summ.get(m, '')
        if rc != 0:
            verdict = 'build-failed' if rc != 'timeout' else 'timeout'
        elif sm.startswith('SUMMARY'):
            d = dict(x.split('=') for x in sm.split()[1:])
            if d['different'] == '0' and d['onlyA'] == '0' and d['onlyB'] == '0':
                verdict = 'pass-' + ('auxmod' if d.get('auxmod') == '1' else 'moddead' if d['moddead'] != '0' else 'alpha' if d['alpha'] != '0' else 'same')
            else:
                verdict = 'different'
        else:
            verdict = 'dlc-error'
        S[verdict] += 1
        S['edits_' + verdict.split('-')[0]] += len(E[m])
        if verdict.startswith('pass'):
            for ln in RAW[m]:
                pf.write(ln)
            lines_pass += sum(e - s + 1 for s, e, act, _, _ in E[m] if act == 'delete')
        f.write(f"{m}\t{verdict}\t{rc}\t{wall:.2f}\t{len(E[m])}\t{sm}\t{err}\t{';'.join(detail[m][:5])}\n")
S['modules'] = len(mods)
S['deleted_lines_pass'] = lines_pass
S['elab_s'] = round(TA - T0, 1); S['dlc_s'] = round(TB - TA, 1)
S['sum_wall_s'] = round(sum(res[m][1] for m in mods), 1)
json.dump(S, open(os.path.join(a.out, 'summary.json'), 'w'), indent=1)
print(json.dumps(S), flush=True)
