#!/usr/bin/env python3
"""train_report.py TRAIN_ID TRAIN_DIR JOB_LOG SHIP_DIR OUT_JSON -- stage-3 integrator: fv-stage3-train-v1 manifest.json
from MEASURED outputs only: TRAIN_DIR/{manifest.tsv, guard.log, pipeline.log, t2.tar.gz}, the
verify_tree.sh job log (RESULT lines), the shipped package snapshot (SHA256SUMS, check/sound/pins.env). Fields that
no measured output gives (expdiff certificate, rubric, model-side acceptance) stay null.
Prints a one-line summary as well. Untrusted bookkeeping."""
import hashlib, json, os, re, sys

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()

def main():
    tid, C, log, ship, out = sys.argv[1:6]
    L = open(log, encoding='utf-8', errors='replace').read()
    P = open(os.path.join(C, 'pipeline.log'), encoding='utf-8', errors='replace').read()
    m = {}
    for k, pat in (('verdict', r'RESULT verdict=(\S+)'), ('export_sha', r'RESULT export sha256=(\S+)'),
                   ('export_size', r'RESULT export sha256=\S+ size=(\d+)'), ('stages', r'RESULT stage_seconds=(.*)'),
                   ('check', r'RESULT check=(\S+) (\S+) s'), ('mods', r'RESULT modules=(\d+)'),
                   ('failed', r'RESULT modules=\d+ sum_cpu=\S+ makespan=\S+ failed=(\d+)'),
                   ('host', r'== D17 \S+ \S+ host=(\S+) threads=(\d+) mode=(\S+)'), ('wall', r'fastverify rc=\S+ wall=(\S+) s')):
        x = re.search(pat, L)
        m[k] = (x.groups() if x and len(x.groups()) > 1 else (x.group(1) if x else None))
    trees = {}
    for t in re.finditer(r'TREE (\S+) files=(\d+) lines=(\d+) bytes=(\d+) nonws=(\d+)(?: chars=(\d+))?', P):
        trees[t.group(1)] = dict(files=int(t.group(2)), lines=int(t.group(3)), bytes=int(t.group(4)), nonws=int(t.group(5)))
    st = json.loads(m['stages']) if m.get('stages') and m['stages'] not in ('null', 'None') else {}
    lists = [l.rstrip('\n').split('\t') for l in open(os.path.join(C, 'manifest.tsv')) if l.strip()]
    pins = os.path.join(ship, 'fv/check/sound/pins.env')
    host = m.get('host') or (None, None, None)
    t2 = os.path.join(C, 't2.tar.gz')
    J = {
        'schema': 'fv-stage3-train-v1', 'train_id': tid, 'track': 'A-4.33.1',
        'utc_finished': None,
        'host': {'node': host[0], 'threads': int(host[1]) if host[1] else None, 'mode': (host[2] + '+keep_going') if host[2] == 'nomerge' else host[2]},
        'manifest': [{'owner': o, 'list': f, 'sha256': sha(os.path.join(C, f)), 'rows': sum(1 for _ in open(os.path.join(C, f)))} for o, f in lists],
        'provenance': {'base_tree': 'alpoge-rh/lean (pristine, original 4.33.1 RH)', 'composite_tree_sha': sha(t2) if os.path.exists(t2) else None,
                       'fv_snapshot_sha': sha(os.path.join(ship, 'SHA256SUMS')) if os.path.exists(os.path.join(ship, 'SHA256SUMS')) else None,
                       'pins_sha': sha(pins) if os.path.exists(pins) else None,
                       'challenge_export_sha': '3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d'},
        'verdict': {'trusted_status': m.get('verdict'), 'judge': 'check-sound.sh (--preset sound items minus merge, keep-going build copy)',
                    'export_sha256': m.get('export_sha'), 'check': m.get('check'),
                    'expdiff_closure_statement_changed': None, 'expdiff_unexplained_statement_changed': None,
                    'expdiff_targets_identical': None, 'failed_modules': int(m['failed']) if m.get('failed') else None},
        'size': {'modules': trees.get('t2', {}).get('files'), 'lines': trees.get('t2', {}).get('lines'),
                 'non_ws_bytes': trees.get('t2', {}).get('nonws'), 'bytes': trees.get('t2', {}).get('bytes'),
                 'export_bytes': int(m['export_size']) if m.get('export_size') else None,
                 'original': trees.get('rh')},
        'timing_s': {'build': st.get('build'), 'export': st.get('export'), 'check_cs': st.get('check'),
                     'total_wall': float(m['wall']) if m.get('wall') else None, 'stage_seconds': st},
    }
    json.dump(J, open(out, 'w'), indent=1)
    o = trees.get('rh') or {}; t = trees.get('t2') or {}
    def d(a, b): return f'{(b - a) / a * 100:+.1f}%' if a and b else '?'
    print(f"TRAIN {tid} (A-4.33.1, {host[0]}/{host[1]}, snap {(J['provenance']['fv_snapshot_sha'] or '?')[:8]}): {m.get('verdict')} | "
          f"build={st.get('build')}s E1={st.get('export')}s CS={st.get('check')}s | mods={t.get('files')} ({d(o.get('files'), t.get('files'))}) "
          f"lines={t.get('lines')} ({d(o.get('lines'), t.get('lines'))}) non_ws={t.get('nonws')} ({d(o.get('nonws'), t.get('nonws'))}) | "
          f"fails={m.get('failed')} | tree {(J['provenance']['composite_tree_sha'] or '?')[:8]} export {(m.get('export_sha') or '?')[:8]}")

if __name__ == '__main__':
    main()
