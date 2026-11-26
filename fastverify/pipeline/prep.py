#!/usr/bin/env python3
"""prep.py PRISTINE_SRC OUT_SRC LOGDIR JOBS [--no-deny] [--protect Statements,Main]
Prepare stage (organization only, pure text, computed from PRISTINE inside the run):
 1. copies every .lean file of PRISTINE_SRC to OUT_SRC (only src/ - never PRISTINE/.lake: the rh-full pristine may contain a
    reference build), in parallel;
 2. ktc_guard (on the PRISTINE text): modules whose own source may catch kernel errors (to_additive/to_dual,
    decide +kernel/decide!, local metaprograms) are listed in LOGDIR/ktc_guard.txt and never get -Ddebug.skipKernelTC;
 3. deny line (leak-free variant) appended at EOF of every module whose imports reach Mathlib /
    Lean.LibrarySuggestions (generality guard, linear topological pass) except the protected ones (Statements, Main);
    LOGDIR/deny_sizes.json = {module: original byte size} so the scheduler can restore the PRISTINE text exactly
    (truncate) and retry a failing module without any transformation;
 4. LOGDIR/deps.json = {module: [project imports]} (comment-aware header parse, same rules as sched_plain).
"""
import json, os, re, sys, time
from concurrent.futures import ProcessPoolExecutor

LINE = ('run_cmd Lean.modifyEnv fun env => '
        'Lean.LibrarySuggestions.typePrefixDenyListExt.modifyState env (Lean.Name.anonymous :: ·)\n').encode()
HDR_KW = ('import', 'public', 'meta', 'private', 'module', 'prelude')
# guard extension: run_tac/run_cmd/run_elab, Elab.async and kernel := true ANYWHERE on a line (evalExpr runs with async=false)
KTC = re.compile(rb'to_additive|to_dual|decide\s*\+kernel|decide!|^\s*(?:run_cmd|run_tac|run_elab|elab_rules|elab\s|#eval|initialize)'
                 rb'|Elab\.async|run_tac|run_cmd|run_elab|kernel\s*:=\s*true', re.M)


def header(text):
    imps, depth, prelude = [], 0, False
    for raw in text.split('\n'):
        line = raw.strip()
        if '/-' in line or depth:
            out, i = [], 0
            while i < len(line):
                if line.startswith('/-', i): depth += 1; i += 2; continue
                if depth and line.startswith('-/', i): depth -= 1; i += 2; continue
                if not depth: out.append(line[i])
                i += 1
            line = ''.join(out)
        line = line.split('--', 1)[0].strip()
        if not line: continue
        toks = line.split()
        if toks[0] not in HDR_KW: break
        if toks[0] == 'prelude': prelude = True
        if 'import' in toks:
            k = toks.index('import'); imps.extend(t for t in toks[k + 1:] if t != 'all')
    return imps, prelude


def scan(args):
    """copy one chunk of files; return per-file (module, imports, prelude, ktc_hit, size, ends_nl)"""
    src, dst, rels = args
    out = []
    made = set()
    for rel in rels:
        with open(os.path.join(src, rel), 'rb') as f: b = f.read()
        d = os.path.dirname(os.path.join(dst, rel))
        if d not in made: os.makedirs(d, exist_ok=True); made.add(d)
        with open(os.path.join(dst, rel), 'wb') as f: f.write(b)
        imps, prel = header(b[:65536].decode('utf-8', 'replace'))
        out.append((rel[:-5].replace(os.sep, '.'), imps, prel, bool(KTC.search(b)), len(b), b.endswith(b'\n')))
    return out


def append(args):
    dst, items = args
    for rel, nl in items:
        with open(os.path.join(dst, rel), 'ab') as f: f.write((b'' if nl else b'\n') + LINE)
    return len(items)


def provides(ext):
    return ext == 'Mathlib' or ext.startswith('Mathlib.') or ext == 'Lean' or ext.startswith('Lean.LibrarySuggestions')


def chunks(xs, n):
    k = max(1, (len(xs) + n - 1) // n)
    return [xs[i:i + k] for i in range(0, len(xs), k)]


def main():
    a = sys.argv[1:]
    deny = '--no-deny' not in a; a = [x for x in a if x != '--no-deny']
    prot = {'Statements', 'Main'}
    if '--protect' in a:
        k = a.index('--protect'); prot = set(a[k + 1].split(',')); del a[k:k + 2]
    src, dst, logd, jobs = a[0], a[1], a[2], int(a[3])
    t0 = time.time()
    rels = []
    for root, _, fs in os.walk(src):
        for fn in fs:
            if fn.endswith('.lean'): rels.append(os.path.relpath(os.path.join(root, fn), src))
    rels.sort()
    t1 = time.time()
    with ProcessPoolExecutor(jobs) as ex:
        res = [r for part in ex.map(scan, [(src, dst, c) for c in chunks(rels, jobs * 8)]) for r in part]
    t2 = time.time()
    info = {r[0]: r for r in res}; relof = {r[0]: rel for r, rel in zip(res, rels)}
    deps = {m: sorted(set(i for i in info[m][1] if i in info)) for m in info}
    with open(os.path.join(logd, 'ktc_guard.txt'), 'w') as f:
        f.write(''.join(m + '\n' for m in sorted(m for m in info if info[m][3])))
    nden = 0; sizes = {}
    if deny:
        # ok(m) = Lean.LibrarySuggestions reachable through m's imports; linear pass in topological order
        rdeps = {m: [] for m in info}; indeg = {m: len(deps[m]) for m in info}
        for m, ds in deps.items():
            for d in ds: rdeps[d].append(m)
        q = [m for m in info if indeg[m] == 0]; order = []
        while q:
            m = q.pop(); order.append(m)
            for r in rdeps[m]:
                indeg[r] -= 1
                if indeg[r] == 0: q.append(r)
        if len(order) != len(info): raise SystemExit('prep: import cycle among local modules')
        ok = {}
        for m in order:
            imps, prel = info[m][1], info[m][2]
            ok[m] = (not prel) and (any(provides(i) for i in imps if i not in info) or any(ok[d] for d in deps[m]))
        todo = [m for m in order if ok[m] and m not in prot]
        sizes = {m: info[m][4] for m in todo}
        items = sorted((relof[m], info[m][5]) for m in todo)
        with ProcessPoolExecutor(jobs) as ex: nden = sum(ex.map(append, [(dst, c) for c in chunks(items, jobs * 8)]))
    with open(os.path.join(logd, 'deny_sizes.json'), 'w') as f: json.dump(sizes, f)
    with open(os.path.join(logd, 'nmodules.txt'), 'w') as f: f.write(f'{len(info)}\n')
    with open(os.path.join(logd, 'deps.json'), 'w') as f: json.dump({m: [relof[m], deps[m]] for m in info}, f)
    t3 = time.time()
    print(f'prep: {len(info)} modules copied, ktc_guard {sum(1 for m in info if info[m][3])}, deny {nden} '
          f'(protected {sorted(prot)}); walk {t1 - t0:.1f}s copy+scan {t2 - t1:.1f}s deny+write {t3 - t2:.1f}s')


if __name__ == '__main__':
    main()
