#!/usr/bin/env python3
"""install-tc.py STAGE1 ORIG_MANIFEST OUT [--report FILE]
Install a rebuilt toolchain with EXACTLY the file layout of the pinned original (the paths of ORIG_MANIFEST: files, symlinks, dirs),
copied from the build's stage1 directory, then compare every file with the original manifest (sha256, exec bit, size).
Prints a per-category table (identical / different / missing) and writes a JSON report. Read-only on STAGE1; OUT is created fresh."""
import hashlib, json, os, shutil, stat, sys, collections, concurrent.futures as cf

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb', buffering=0) as f:
        for b in iter(lambda: f.read(1 << 22), b''):
            h.update(b)
    return h.hexdigest()

def cat(p):
    b = os.path.basename(p)
    if p.startswith('bin/'): return p
    for suf in ('.olean.private.hash', '.olean.server.hash', '.olean.hash', '.ir.sig.hash', '.ir.hash', '.ilean.hash', '.c.hash',
                '.olean.private', '.olean.server', '.olean', '.ilean', '.ir.sig', '.ir', '.c.o.export.hash', '.c.o.export',
                '.c.o.noexport.hash', '.c.o.noexport', '.trace', '.json', '.c', '.rsp', '.a', '.so', '.h', '.hash'):
        if b.endswith(suf): return suf
    return '(other)'

def main(a):
    st1, man, out = a[0], a[1], a[2]
    rep = a[a.index('--report') + 1] if '--report' in a else out + '.report.json'
    m = json.load(open(man))
    if os.path.exists(out): sys.exit(f'{out} exists')
    os.makedirs(out)
    for d in sorted(m['dirs']):
        if d != '.': os.makedirs(os.path.join(out, d), exist_ok=True)
    missing, todo = [], []
    for p in sorted(m['files']):
        s = os.path.join(st1, p)
        if not os.path.isfile(s) or os.path.islink(s): missing.append(p); continue
        shutil.copyfile(s, os.path.join(out, p))
        x = os.stat(s).st_mode & 0o111
        os.chmod(os.path.join(out, p), 0o755 if (m['files'][p][1] == 'x' or x) else 0o644)
        todo.append(p)
    for p, t in m.get('symlinks', {}).items():
        os.symlink(t, os.path.join(out, p))
    extra = []
    for d, dns, fns in os.walk(st1):
        for n in fns:
            rp = os.path.relpath(os.path.join(d, n), st1)
            if rp not in m['files'] and rp.split('/')[0] in ('bin', 'lib', 'include'): extra.append(rp)
    with cf.ThreadPoolExecutor(32) as ex:
        hs = dict(zip(todo, ex.map(lambda p: sha(os.path.join(out, p)), todo)))
    same, diff, xbit = collections.Counter(), collections.Counter(), []
    diffs = collections.defaultdict(list)
    for p in todo:
        c = cat(p)
        if hs[p] == m['files'][p][0]: same[c] += 1
        else: diff[c] += 1; diffs[c].append(p)
        if (m['files'][p][1] == 'x') != bool(os.stat(os.path.join(out, p)).st_mode & 0o100): xbit.append(p)
    r = {'stage1': st1, 'orig_manifest': man, 'orig_name': m.get('name'), 'out': out, 'nfiles': len(m['files']),
         'identical': dict(same), 'different': dict(diff), 'missing': missing, 'extra_in_build': sorted(extra)[:200],
         'n_extra_in_build': len(extra), 'exec_bit_mismatch': xbit, 'different_files': {k: v[:50] for k, v in diffs.items()}}
    json.dump(r, open(rep, 'w'), indent=1, sort_keys=True)
    print(f"{m.get('name')} -> {out}: {len(todo)} files installed, {len(missing)} missing, {len(extra)} extra in build (not installed)")
    print('  categories: identical / different')
    for c in sorted(set(same) | set(diff)):
        print(f'   {c:24s} {same[c]:6d} / {diff[c]:6d}')
    if missing: print('  missing e.g.', missing[:5])
    if xbit: print('  exec-bit mismatch', xbit[:5])
    print('  report', rep)

if __name__ == '__main__':
    main(sys.argv[1:])
