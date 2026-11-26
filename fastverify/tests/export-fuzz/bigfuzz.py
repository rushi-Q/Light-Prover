#!/usr/bin/env python3
"""bigfuzz.py: export fuzzing for BIG bases (Mathlib-scale exports, hundreds of MB): the base is parsed once, worker
processes (fork, copy-on-write) generate one mutant at a time, run the official comparator + CS (bulk) + the second kernel
alone, write a results row and delete the mutant (disk use = workers x export size). Same row format as runfuzz.py.

  bigfuzz.py --base SOL --challenge CH --config CFG --out OUT --ops OP,.. --per-op N --seed S --workers W --threads T
             --pkg FASTVERIFY [--parsediff BIN] [--timeout SEC]"""
import argparse, json, os, sys, time, multiprocessing as mp, random, hashlib
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import xfuzz
from runfuzz import run, lastjson
EX = None; CTX = None; A = None
def work(job):
    name, k = job
    cls, _, f = xfuzz.OPS[name]
    r = random.Random(f'{A.bh}:{name}:{A.seed}:{k}')
    try:
        res = f(r, EX, CTX)
    except (IndexError, KeyError, ValueError):
        res = None
    if res is None:
        return None
    blob, det = res
    mid = f'{name}-{A.seed}-{k}'; fpath = os.path.join(A.md, mid + '.ndjson')
    open(fpath, 'wb').write(blob); del blob
    pdst = ('NA', '')
    if A.parsediff:
        rc, so, se, _ = run([os.path.join(HERE, 'parsediff', 'sbx.sh'), A.md, os.path.dirname(A.parsediff), '--', '/usr/bin/env', 'PD_STREAM_ONLY=1', A.parsediff, fpath], A.timeout)
        p = so.strip().split('\t'); pdst = (p[0], p[2][:300]) if len(p) >= 3 else ('NA', se[-200:])
    rc2, so2, se2, t2 = run([os.path.join(A.pkg, 'check/official/check.sh'), fpath, A.challenge, A.config, '--timeout', str(A.timeout)], A.timeout + 60)
    j2 = lastjson(so2)
    rc1, so1, se1, t1 = run([A.cs_bulk, fpath, A.challenge, A.config, '--threads', str(A.threads), '--hints', 'none'], A.timeout)
    j1 = lastjson(so1)
    if j1.get('verdict') == 'ACCEPTED' and j2.get('verdict') != 'ACCEPTED':
        rc1b, so1b, se1b, _ = run([os.path.join(A.pkg, 'check/sound/check-sound.sh'), fpath, A.challenge, A.config, '--threads', str(A.threads), '--hints', 'none'], A.timeout)
        j1b = lastjson(so1b)
        if j1b.get('verdict') != 'ACCEPTED':
            j1 = {'verdict': 'MISMATCH-' + str(j1b.get('verdict')), 'reason': 'bulk ACCEPTED, full: ' + str(j1b.get('reason'))}
    k2 = 'NA'
    if A.k2:
        rc3, so3, se3, _ = run([os.path.join(HERE, 'parsediff', 'sbx.sh'), A.md, os.path.dirname(A.k2), '--', A.k2, fpath, str(A.threads)], A.timeout)
        k2 = {0: 'K2-ACCEPT', 1: 'K2-REJECT', 2: 'K2-DECLINE'}.get(rc3, f'K2-RC{rc3}')
    csv = j1.get('verdict', 'NONE'); ofv = j2.get('verdict', 'NONE')
    if csv == 'ACCEPTED' and ofv != 'ACCEPTED': st = 'FAIL-CRITICAL'
    elif pdst[0].startswith('DIVERGE'): st = 'FAIL-PARSER'
    elif ofv == 'ACCEPTED' and csv != 'ACCEPTED': st = 'WARN-AVAIL'
    elif ofv == 'ACCEPTED': st = 'OK-ACCEPT'
    elif ofv == 'REJECTED' and csv == 'REJECTED': st = 'OK-REJECT'
    elif ofv == 'REJECTED': st = 'OK-DECLINE'
    else: st = 'OF-ERROR'
    if not st.startswith(('FAIL', 'WARN')):
        os.unlink(fpath)
    csr = (j1.get('reason') or se1[-200:]).replace('\t', ' ').replace('\n', ' ')[:300]
    ofr = (j2.get('detail') or se2[-200:]).replace('\t', ' ').replace('\n', ' ')[-300:]
    return [mid, name, cls, det.replace('\t', ' '), pdst[0], csv, str(rc1), ofv, str(rc2), st, f'{t1:.1f}', f'{t2:.1f}', csr, ofr, pdst[1].replace('\t', ' '), k2]

def main():
    global EX, CTX, A
    ap = argparse.ArgumentParser()
    for k in ('base', 'challenge', 'config', 'out', 'ops', 'pkg'): ap.add_argument('--' + k, required=True)
    ap.add_argument('--per-op', type=int, default=3); ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--workers', type=int, default=4); ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--parsediff', default=''); ap.add_argument('--timeout', type=int, default=3600)
    ap.add_argument('--k2', default=None)
    ap.add_argument('--cs-bulk', default=os.path.join(os.environ.get('EXPORT_FUZZ_WORK') or (os.environ.get('TMPDIR') or '/tmp') + '/%s-exportfuzz' % os.environ.get('USER', 'user'), 'check-sound-bulk.sh'))
    A = ap.parse_args()
    if A.k2 is None:
        A.k2 = next((l.split()[3] for l in open(os.path.join(A.pkg, 'check/sound/pins.env')) if l.startswith('PIN gruszka ')), '')
    A.md = os.path.join(os.path.abspath(A.out), 'm'); os.makedirs(A.md, exist_ok=True)
    t0 = time.time(); data = open(A.base, 'rb').read(); A.bh = hashlib.sha256(data).hexdigest()[:12]
    EX = xfuzz.Ex(data); del data
    c = json.load(open(A.config))
    CTX = {'targets': set(c['theorem_names'] + c.get('definition_names', []) + c['permitted_axioms'])}
    if any(o.startswith('P_') for o in A.ops.split(',')):
        xfuzz.proof_only(EX, CTX)
    print(f'base parsed in {time.time() - t0:.0f} s: {len(EX.lines)} lines, {len(EX.decls)} decls', flush=True)
    resf = os.path.join(A.out, 'results.tsv')
    done = {l.split('\t')[0] for l in open(resf)} if os.path.exists(resf) else set()
    jobs = [(o, k) for o in A.ops.split(',') for k in range(1, A.per_op + 1) if f'{o}-{A.seed}-{k}' not in done]
    with open(resf, 'a') as R, mp.get_context('fork').Pool(A.workers) as pool:
        for row in pool.imap_unordered(work, jobs):
            if row:
                R.write('\t'.join(row) + '\n'); R.flush()
    rows = [l.split('\t') for l in open(resf)]
    s = {}
    for r in rows: s[r[9]] = s.get(r[9], 0) + 1
    print(json.dumps(s))
if __name__ == '__main__':
    main()
