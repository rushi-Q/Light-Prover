#!/usr/bin/env python3
"""runfuzz.py: differential export fuzzing of the SOUND check (check-sound.sh = CS) against the official
`lake comparator` 4.36 (check/official/check.sh = OF), plus the parser differential (parsediff).

  runfuzz.py --base SOL.export --challenge CH.export --config CFG.json --targets T1,T2,.. --out OUT
             [--ops all|OP,..] [--per-op N] [--seed S] [--jobs J] [--threads T] [--pkg FASTVERIFY] [--parsediff BIN]
             [--keep-all]

Row statuses (OUT/results.tsv):
  FAIL-CRITICAL   CS ACCEPTED and the official comparator did not accept  (soundness oracle violated)
  FAIL-PARSER     parsediff: the trusted fast reader returned something other than the official reader
  WARN-AVAIL      the official comparator ACCEPTED and CS did not (availability: decline / false reject)
  OK-ACCEPT / OK-REJECT / OK-DECLINE (CS declined, official rejected) / OF-ERROR (official could not run; CS not accepting)
Mutant files are deleted except for FAIL/WARN rows and the first 3 of every (op, status) pair (or all with --keep-all)."""
import argparse, concurrent.futures as cf, json, os, subprocess, sys, time, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.environ.get('EXPORT_FUZZ_WORK') or (os.environ.get('TMPDIR') or '/tmp') + '/%s-exportfuzz' % os.environ.get('USER', 'user')
PKG_DEFAULT = os.path.abspath(os.path.join(HERE, '..', '..'))

def run(cmd, timeout):
    t0 = time.time()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        return p.returncode, p.stdout.decode('utf-8', 'replace'), p.stderr.decode('utf-8', 'replace'), time.time() - t0
    except subprocess.TimeoutExpired:
        return 124, '', 'timeout', time.time() - t0

def lastjson(s):
    for l in reversed(s.strip().split('\n')):
        try:
            return json.loads(l)
        except Exception:
            continue
    return {}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', default=''); ap.add_argument('--challenge', required=True); ap.add_argument('--config', required=True)
    ap.add_argument('--targets', default=''); ap.add_argument('--out', required=True)
    ap.add_argument('--ops', default='all'); ap.add_argument('--per-op', type=int, default=5); ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--jobs', type=int, default=16); ap.add_argument('--threads', type=int, default=2)
    ap.add_argument('--pkg', default=PKG_DEFAULT)
    ap.add_argument('--parsediff', default=os.path.join(WORK, 'pd', '.lake', 'build', 'bin', 'parsediff'))
    ap.add_argument('--keep-all', action='store_true'); ap.add_argument('--label', default='')
    ap.add_argument('--timeout', type=int, default=900)
    ap.add_argument('--premade', default='')
    ap.add_argument('--k2', default=None, help='second kernel run alone per mutant (default: the gruszka pinned in PKG/check/sound/pins.env; "" = skip)')
    ap.add_argument('--cs-script', default='', help='CS script for the bulk runs (default: PKG/check/sound/check-sound-bulk.sh if present)')
    a = ap.parse_args()
    if a.k2 is None:
        a.k2 = next((l.split()[3] for l in open(os.path.join(a.pkg, 'check/sound/pins.env')) if l.startswith('PIN gruszka ')), '')
    out = os.path.abspath(a.out); md = os.path.join(out, 'm'); os.makedirs(md, exist_ok=True)
    # 1. generate (or use a premade case directory: --premade DIR with DIR/manifest.tsv and DIR/<id>.ndjson)
    if a.premade:
        for l in open(os.path.join(a.premade, 'manifest.tsv')):
            mid = l.split('\t')[0]
            dst = os.path.join(md, mid + '.ndjson')
            if not os.path.exists(dst):
                shutil.copyfile(os.path.join(a.premade, mid + '.ndjson'), dst)
        shutil.copyfile(os.path.join(a.premade, 'manifest.tsv'), os.path.join(md, 'manifest.tsv'))
    else:
        subprocess.run([sys.executable, '-I', os.path.join(HERE, 'xfuzz.py'), 'gen', a.base, md, '--ops', a.ops, '--per-op', str(a.per_op),
                        '--seed', str(a.seed), '--targets', a.targets], check=True)
    man = [l.rstrip('\n').split('\t', 3) for l in open(os.path.join(md, 'manifest.tsv'))]
    done = set()
    resf = os.path.join(out, 'results.tsv')
    if os.path.exists(resf):
        done = {l.split('\t')[0] for l in open(resf)}
    man = [m for m in man if m[0] not in done]
    # 2. parser differential, in batches, sandboxed
    pd = {}
    if os.path.exists(a.parsediff):
        batch = [os.path.join(md, m[0] + '.ndjson') for m in man]
        def pdrun(chunk):
            rc, so, se, _ = run([os.path.join(HERE, 'parsediff', 'sbx.sh'), md, os.path.dirname(a.parsediff), '--', a.parsediff] + chunk, 3600)
            return so
        chunks = [batch[i:i + 40] for i in range(0, len(batch), 40)]
        with cf.ThreadPoolExecutor(max(1, a.jobs // 2)) as ex:
            for so in ex.map(pdrun, chunks):
                for l in so.splitlines():
                    p = l.split('\t')
                    if len(p) >= 3:
                        pd[os.path.basename(p[1])[:-7]] = (p[0], p[2][:300])
    # 3. CS and OF per mutant
    cs_full = os.path.join(a.pkg, 'check/sound/check-sound.sh'); of_sh = os.path.join(a.pkg, 'check/official/check.sh')
    cs_sh = a.cs_script or os.path.join(WORK, 'check-sound-bulk.sh')
    if not os.path.exists(cs_sh):
        cs_sh = cs_full
    if cs_sh != cs_full:   # pins + toolchain + self-test once, with the unmodified script
        rc, so, se, _ = run([cs_full, '--preflight'], 600)
        if rc != 0:
            sys.exit('check-sound.sh --preflight failed: ' + so[-500:] + se[-500:])
    def one(m):
        mid, opn, cls, det = m
        f = os.path.join(md, mid + '.ndjson')
        rc2, so2, se2, t2 = run([of_sh, f, a.challenge, a.config, '--timeout', str(a.timeout)], a.timeout + 60)
        j2 = lastjson(so2)
        rc1, so1, se1, t1 = run([cs_sh, f, a.challenge, a.config, '--threads', str(a.threads), '--hints', 'none'], a.timeout)
        j1 = lastjson(so1)
        if j1.get('verdict') == 'ACCEPTED' and cs_sh != cs_full and j2.get('verdict') != 'ACCEPTED':
            # every bulk ACCEPT is confirmed by the unmodified script (the bulk variant only skips input-independent checks)
            rc1b, so1b, se1b, _ = run([cs_full, f, a.challenge, a.config, '--threads', str(a.threads), '--hints', 'none'], a.timeout)
            j1b = lastjson(so1b)
            if j1b.get('verdict') != 'ACCEPTED':
                j1 = {'verdict': 'MISMATCH-' + str(j1b.get('verdict')), 'reason': 'bulk ACCEPTED, full: ' + str(j1b.get('reason'))}
        # the second kernel alone (gruszka, as pinned for CS), sandboxed: how many official rejects would a single
        # independent kernel have caught (C4-style), and its availability
        k2 = 'NA'
        if a.k2:
            rc3, so3, se3, _ = run([os.path.join(HERE, 'parsediff', 'sbx.sh'), md, os.path.dirname(a.k2), '--', a.k2, f, str(a.threads)], a.timeout)
            k2 = {0: 'K2-ACCEPT', 1: 'K2-REJECT', 2: 'K2-DECLINE'}.get(rc3, f'K2-RC{rc3}')
        csv = j1.get('verdict', 'NONE'); ofv = j2.get('verdict', 'NONE')
        pds = pd.get(mid, ('NA', ''))
        if csv == 'ACCEPTED' and ofv != 'ACCEPTED':
            st = 'FAIL-CRITICAL'
        elif pds[0].startswith('DIVERGE'):
            st = 'FAIL-PARSER'
        elif ofv == 'ACCEPTED' and csv != 'ACCEPTED':
            st = 'WARN-AVAIL'
        elif ofv == 'ACCEPTED':
            st = 'OK-ACCEPT'
        elif ofv == 'REJECTED' and csv == 'REJECTED':
            st = 'OK-REJECT'
        elif ofv == 'REJECTED':
            st = 'OK-DECLINE'
        else:
            st = 'OF-ERROR'
        csr = (j1.get('reason') or se1[-200:]).replace('\t', ' ').replace('\n', ' ')[:300]
        ofr = (j2.get('detail') or se2[-200:]).replace('\t', ' ').replace('\n', ' ')[-300:]
        return [mid, opn, cls, det.replace('\t', ' '), pds[0], csv, str(rc1), ofv, str(rc2), st, f'{t1:.1f}', f'{t2:.1f}', csr, ofr, pds[1].replace('\t', ' '), k2]
    seen = {}
    with open(resf, 'a') as R, cf.ThreadPoolExecutor(a.jobs) as ex:
        for row in ex.map(one, man):
            R.write('\t'.join(row) + '\n'); R.flush()
            key = (row[1], row[9]); seen[key] = seen.get(key, 0) + 1
            keep = a.keep_all or row[9].startswith(('FAIL', 'WARN', 'OF-ERROR')) or seen[key] <= 3
            if not keep:
                try:
                    os.unlink(os.path.join(md, row[0] + '.ndjson'))
                except OSError:
                    pass
    # 4. summary
    rows = [l.rstrip('\n').split('\t') for l in open(resf)]
    summ = {}
    for r in rows:
        summ.setdefault(r[9], 0); summ[r[9]] += 1
    byop = {}
    for r in rows:
        byop.setdefault(r[1], {}).setdefault(r[9], 0); byop[r[1]][r[9]] += 1
    json.dump({'label': a.label, 'base': a.base, 'challenge': a.challenge, 'config': a.config, 'rows': len(rows), 'status': summ,
               'by_op': byop, 'pkg': a.pkg}, open(os.path.join(out, 'summary.json'), 'w'), indent=1)
    print(json.dumps(summ))

if __name__ == '__main__':
    main()
