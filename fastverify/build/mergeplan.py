#!/usr/bin/env python3
"""mergeplan.py PLAN_IN OUTDIR [--max-members N] [--max-lines L] [--jobs J] [--stats-only] [--deny FILE]
UNTRUSTED build transform for the sound preset: module MERGING as a plan-to-plan rewrite.

Input: the planner's plan.jsonl (header line, one record per module, end line) of a project.
Output: OUTDIR/plan.jsonl (same format; every multi-member group is ONE record named after its SINK, whose source is the
merged file OUTDIR/src/<sink path>.lean), OUTDIR/fallback.jsonl (the ORIGINAL plan records of every member of every
multi-member group, the sink included: sched.py --split-fallback rebuilds a failed group from them), OUTDIR/groups.json,
OUTDIR/stats.json. The project's own sources are never modified.

Grouping rule (importer-closed, reverse topological greedy): module m joins the group of its importers iff ALL its
importers are in one group g (so no module outside g ever imports m: every import statement of the merged project still
names an existing module, and every module outside g sees exactly the declarations it saw before), and
  * m's lean invocation equals the sink's up to the module name/paths (same lib, options, flags, package),
  * neither m nor the sink is "special" (Main/Statements-like roots are not special by name: any module with global
    syntax/macro/notation/elab/initialize/option/attribute-erasure/export/#exit/mutual stays a singleton or a sink),
  * no private-name collision inside the group, caps on members and lines.
Members are emitted in a topological order (DFS post-order from the sink = Lean's own import order), each inside
`section ... end` with its unclosed namespaces/sections closed first, so open/variable/universe/set_option/local
attributes/notations do not leak between members. Remaining leaks (a member sees earlier members' global instances /
simp lemmas / names it did not import) can only make elaboration FAIL or differ, never make the check accept anything:
the build is untrusted, the export is checked from scratch; a failing group falls back to its members' exact original
invocations (sched.py --split-fallback).
--deny FILE: module names (one per line, '#' comments) whose merged group FAILED in a measured run of the same project
(build/hints/merge-deny.txt; written from sched.out by build/test/merge-deny.py): every group containing one of them is
dissolved into singletons after all other rules (the other groups stay exactly as planned).
"""
import collections, json, os, re, stat, sys, time
from concurrent.futures import ProcessPoolExecutor

# the plan's source paths come from the UNTRUSTED lakefile.toml (srcDir) and this transform runs on the
# HOST (with merge=late concurrently with the untrusted build, which can replace project files by symlinks). Every source
# it reads must therefore be a regular file that IS inside the project: --confine PROJ (build.sh passes it) checks each
# path as a string (absolute, no '..') and, race-free, the file actually opened (/proc/self/fd -> path under PROJ, S_ISREG,
# O_NONBLOCK: a FIFO never blocks). A source outside the project -> the merge planner fails -> the build runs unmerged.
CONFINE = None


def read_source(path):
    if CONFINE is not None and (not path.startswith(CONFINE + os.sep) or '..' in path.split('/')):
        raise OSError(f'source {path!r} outside the project')
    # (r2, review L4) an O_PATH descriptor first (opens nothing: a FIFO / device is never opened for reading), checked to be
    # a regular file inside the project, then re-opened for reading through that very descriptor (race-free)
    if sys.platform == 'darwin':   # neither O_PATH nor /proc: opened without blocking (a FIFO returns at once) and with
        # O_NOFOLLOW_ANY, which follows no link in any part of the path: what is opened is the file inside the project
        fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOCTTY | os.O_CLOEXEC | 0x20000000)
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            os.close(fd); raise OSError(f'source {path!r} is not a regular file')
        with open(fd, encoding='utf-8') as f:
            return f.read()
    pfd = os.open(path, os.O_PATH | os.O_CLOEXEC)
    try:
        if not stat.S_ISREG(os.fstat(pfd).st_mode):
            raise OSError(f'source {path!r} is not a regular file')
        if CONFINE is not None and not os.readlink(f'/proc/self/fd/{pfd}').startswith(CONFINE + os.sep):
            raise OSError(f'source {path!r} resolves outside the project')
        with open(f'/proc/self/fd/{pfd}', encoding='utf-8') as f:
            return f.read()
    finally:
        os.close(pfd)

HDR_KW = ('import', 'public', 'meta', 'private', 'module', 'prelude')
META_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:scoped)\s+)?'
                     r'(syntax|macro|macro_rules|elab|elab_rules|initialize|builtin_initialize|declare_syntax_cat|'
                     r'register_option|register_simp_attr|register_label_attr|register_builtin_option|run_cmd|run_elab|'
                     r'run_meta|notation|notation3|infix|infixl|infixr|prefix|postfix|binder_predicate|add_decl_doc|'
                     r'declare_aesop_rule_sets|declare_simp_like_tactic|unif_hint|export|mutual|#exit|'
                     r'deriving\s+instance|termination_by|decreasing_by|builtin_\w+)\b')
# global attribute changes that persist for the rest of the file (erasures, reducibility) -> only allowed as the LAST
# member (the sink): attribute [-x], attribute [irreducible|reducible|semireducible|instance_reducible] without local
SINKONLY_RE = re.compile(r'^attribute\s+\[\s*(-|(?:irreducible|reducible|semireducible|instance_reducible|simp|instance)\b)')
PRIV_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?private\s+(?:noncomputable\s+)?(?:nonrec\s+)?(?:partial\s+)?(?:unsafe\s+)?'
                     r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|opaque|axiom|class)\s+(\S+)')
NS_RE = re.compile(r'^namespace\s+(\S+)\s*$')
SEC_RE = re.compile(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$')
END_RE = re.compile(r'^end(?:\s+(\S+))?\s*$')
HB_RE = re.compile(r'maxHeartbeats\s+(\d+)')
PRIVFROM_RE = re.compile(r'open\s+private\b[^\n]*?\bfrom\s+([^\s]+)')   # refers to ANOTHER module by name
ANYDECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
                        r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example|attribute)\b')
INST_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|scoped|private|protected)\s+)*instance\b|^attribute\s+\[(?:scoped\s+)?instance')
DEF_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:def|abbrev|instance|structure|class|inductive|opaque)\b')
DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                     r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s:({\[]+)')


def split_header(text):
    """(imports, lines, body_start). Header = leading import / module-system keyword lines; comments tolerated."""
    lines = text.split('\n')
    imps, depth, body = [], 0, len(lines)
    for i, raw in enumerate(lines):
        line, out, j = raw.strip(), [], 0
        while j < len(line):
            if line.startswith('/-', j): depth += 1; j += 2; continue
            if depth and line.startswith('-/', j): depth -= 1; j += 2; continue
            if not depth: out.append(line[j])
            j += 1
        line = ''.join(out).split('--', 1)[0].strip()
        if not line: continue
        toks = line.split()
        if toks[0] in HDR_KW and 'import' in toks:
            imps.extend(t for t in toks[toks.index('import') + 1:] if t != 'all')
            continue
        if toks[0] in ('prelude', 'module'): return None   # module system / prelude files: never merged
        body = i
        break
    return imps, lines, body


def scan(path):
    try:
        text = read_source(path)
    except (OSError, UnicodeDecodeError):
        return None
    h = split_header(text)
    if h is None: return None
    imps, lines, body = h
    stack, privs, special, sinkonly, depth, decls, opens, ndecl, ninst, ndef = [], set(), False, False, 0, set(), set(), 0, 0, 0
    scopedns = set()
    for raw in lines[body:]:
        # track block comments to avoid acting on commented-out commands (approximate, column-0 commands only)
        if depth:
            depth += raw.count('/-') - raw.count('-/')
            if depth < 0: depth = 0
            continue
        if raw.startswith('/-'):
            depth = raw.count('/-') - raw.count('-/')
            if depth < 0: depth = 0
            continue
        if not raw or raw[0] in ' \t': continue
        m = NS_RE.match(raw)
        if m:
            stack.append(('ns', m.group(1)))
            full = '.'.join(n for k, n in stack if k == 'ns' and n).split('.')
            for i in range(1, len(full) + 1): opens.add('.'.join(full[:i]))
            continue
        if raw.startswith('open '):
            for t in raw[5:].split():
                if t in ('in', 'hiding', 'renaming') or t.startswith('('): break
                opens.add(t)
        m = SEC_RE.match(raw)
        if m: stack.append(('sec', m.group(1))); continue
        m = END_RE.match(raw)
        if m:
            if not stack: special = True   # unbalanced: do not merge
            else: stack.pop()
            continue
        if META_RE.match(raw): special = True
        if ANYDECL_RE.match(raw): ndecl += 1
        if INST_RE.match(raw): ninst += 1
        if raw.startswith(('scoped ', '@[scoped', 'export ')):
            scopedns.add('.'.join(n for k, n in stack if k == 'ns' and n))
        if DEF_RE.match(raw): ndef += 1
        if SINKONLY_RE.match(raw): sinkonly = True
        m = PRIV_RE.match(raw)
        if m:
            ns = '.'.join(n for k, n in stack if k == 'ns' and n)
            privs.add((ns + '.' if ns else '') + m.group(1))
        else:
            m = DECL_RE.match(raw)
            if m and not raw.startswith('instance :') and not raw.startswith('instance  :'):
                nm = m.group(1)
                if nm.startswith('_root_.'): decls.add(nm[7:])
                else:
                    ns = '.'.join(n for k, n in stack if k == 'ns' and n)
                    decls.add((ns + '.' if ns else '') + nm)
    hb = max((int(x) for x in HB_RE.findall(text)), default=0)
    privfrom = sorted(set(PRIVFROM_RE.findall(text)))
    toks = ' '.join(set(TOK_RE.findall('\n'.join(lines[body:]))))   # identifier tokens (ambiguity rule), one string
    # static 'possibly heavy' markers (RH B1 walls: base rate of > 30 s elaboration 1.2%; with_unfolding_all 44%,
    # maxRecDepth 41%, backward.isDefEq.respectTransparency 7.3%, synthInstance.* 6.3%)
    hv = any(p in text for p in ('with_unfolding_all', 'maxRecDepth', 'respectTransparency', 'synthInstance.'))
    return {'imports': imps, 'body': body, 'nlines': len(lines), 'scopes': stack, 'privs': sorted(privs),
            'special': special, 'sinkonly': sinkonly, 'hb': hb, 'hv': hv, 'decls': sorted(decls),
            'opens': sorted(opens), 'ndecl': ndecl, 'toks': toks, 'ninst': ninst, 'ndef': ndef, 'scopedns': sorted(scopedns), 'privfrom': privfrom}


def write_merged(job):
    path, ext, members = job
    try:
        parts = [f'import {t}' for t in ext] + ['']
        for n, src, scopes in members:
            text = read_source(src)
            _, lines, body = split_header(text)
            body_txt = '\n'.join(lines[body:]).rstrip('\n')
            closers = [(f'end {nm}' if nm else 'end') for _, nm in reversed(scopes)]
            parts += [f'-- merged from {n}', 'section', '', body_txt, ''] + closers + ['end', '']
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, 'w', encoding='utf-8') as f: f.write('\n'.join(parts) + '\n')
        return True
    except (OSError, UnicodeDecodeError):
        return False


TOK_RE = re.compile(r"[A-Za-z_\u0370-\u03ff][A-Za-z0-9_'!?\u0370-\u03ff\u2080-\u209c]*")


SCAN_VERSION = 5   # bump whenever scan() output changes (a prescan cache of another version is ignored)
_LK = {}   # exact-leak post-pass data, set by main() right before forking the workers that read it


def _leak_check(gi):
    """Risky members of group gi (see the EXACT LEAK rule in main)."""
    g = _LK['groups'][gi]; eclo = _LK['eclo']; deps = _LK['deps']; pos = _LK['pos']; infos = _LK['infos']
    nsidx = _LK['nsidx']; instbits = _LK['instbits']
    ms = set(g); U = 0; allm = 0
    for m in g:
        allm |= 1 << pos[m]
        for d in deps[m]:
            if d not in ms: U |= eclo[d] | (1 << pos[d])
    R = []
    for x in g[1:]:   # g[0] is the sink: its closure contains everything visible in the group
        leak = (U | allm) & ~eclo[x] & ~(1 << pos[x])
        ix = infos[x]
        if _LK.get('instmember') and ix.get('ninst', 0): R.append(x); continue   # its instances would move later
        if not leak: continue
        if instbits and (ix.get('ndef', 0) or _LK.get('instleakall')) and (leak & instbits): R.append(x); continue
        if _LK.get('toxbits') and (leak & _LK['toxbits']): R.append(x); continue   # --toxic-leak-rule
        if any((leak & b) for ns_, b in _LK['scopedby'].items() if ns_ in ix['opens'] or ns_ == ''):
            R.append(x); continue   # a leaked scoped notation/instance or export alias in a namespace x opens
        toks = set(ix['toks'].split())
        o = set(ix['opens']); vis = {''} | o
        for p in o:
            for q in o: vis.add(p + '.' + q)
        hit = False
        for ns_ in vis:
            d = nsidx.get(ns_)
            if not d: continue
            hits = (d[t] for t in toks if t in d) if len(toks) < len(d) else (v for t, v in d.items() if t in toks)
            for ps in hits:
                for p in ps:
                    if (leak >> p) & 1: hit = True; break
                if hit: break
            if hit: break
        if not hit:   # private declarations of the OTHER members are visible inside the merged file too
            for y in g:
                if y == x: continue
                for q in infos[y]['privs']:
                    ns_, _, t = q.rpartition('.')
                    if t in toks and ns_ in vis: hit = True; break
                if hit: break
        if hit: R.append(x)
    return gi, R


def rel_of(name):
    return name.replace('.', '/')


def inv_key(r):
    """The module's lean invocation with its own name/paths abstracted: two modules with equal keys are compiled by
    exactly the same command apart from the module name (same lib options, flags, package)."""
    rel = rel_of(r['name'])
    if r.get('isModule'): return None
    st = r['setup']   # Lake's pretty printer may break the line after '"name":' for long names
    if '"importArts": {}' not in st or '"imports"' in st:   # explicit import artifacts / header override (S07)
        try:
            d = json.loads(st)
        except ValueError:
            return None
        if d.get('name') != r['name'] or not isinstance(d.get('importArts', {}), dict): return None
        d.pop('importArts', None); d['name'] = '@MOD@'
        if 'imports' in d: d['imports'] = '@PRESENT@'   # only modules that all (or none) override their header merge
        return '\x00'.join([a.replace('/' + rel + '.', '/@MOD@.') for a in r['argv']] + [json.dumps(d, sort_keys=True)])
    i = st.find('"name":'); qn = json.dumps(r['name'])
    if i < 0 or st.find('"name":', i + 1) >= 0: return None
    j = i + 7
    while j < len(st) and st[j] in ' \n\t': j += 1
    if not st.startswith(qn, j): return None
    st2 = st[:i] + '"name": @MOD@' + st[j + len(qn):]
    return '\x00'.join([a.replace('/' + rel + '.', '/@MOD@.') for a in r['argv']] + [st2])


def prescan(root, outp, jobs):
    """--prescan ROOT OUT: scan every .lean file under ROOT (not .lake) while Lake's planner runs; OUT = pickle
    {absolute path: (size, mtime_ns, scan result)}. The main run uses an entry only if size and mtime still match."""
    import pickle
    paths = []
    for dp, dn, fn in os.walk(os.path.abspath(root)):
        dn[:] = [d for d in dn if d != '.lake']
        paths += [os.path.join(dp, f) for f in fn if f.endswith('.lean')]
    with ProcessPoolExecutor(jobs) as ex:
        res = list(ex.map(scan, paths, chunksize=256))
    cache = {}
    for p, r in zip(paths, res):
        try:
            st = os.stat(p); cache[p] = (st.st_size, st.st_mtime_ns, r)
        except OSError:
            pass
    with open(outp + '.tmp', 'wb') as f: pickle.dump({'version': SCAN_VERSION, 'cache': cache}, f, protocol=pickle.HIGHEST_PROTOCOL)
    os.replace(outp + '.tmp', outp)
    return 0


def main():
    a = sys.argv[1:]
    global CONFINE
    if sys.platform == 'darwin':   # the pools below rely on fork (workers inherit this process's state)
        import multiprocessing; multiprocessing.set_start_method('fork')
    if len(a) >= 3 and a[0] == '--prescan':
        CONFINE = os.path.realpath(a[1])   # the prescan reads only files that are inside the scanned project
        return prescan(a[1], a[2], int(a[a.index('--jobs') + 1]) if '--jobs' in a else 16)
    if len(a) < 2:
        print(__doc__); return 2
    plan_in, out = a[0], a[1]
    def opt(k, d):
        return a[a.index(k) + 1] if k in a else d
    if '--confine' in a:   # set before the worker pool forks (the workers inherit it)
        CONFINE = os.path.realpath(opt('--confine', ''))
    maxm = int(opt('--max-members', '24')); maxl = int(opt('--max-lines', '3000')); jobs = int(opt('--jobs', '16'))
    T0 = time.time(); tm = {}
    # one worker pool, forked while this process is still small (cheap forks; the workers get only their arguments)
    POOL = ProcessPoolExecutor(jobs); POOL.submit(int, 0).result()
    with open(plan_in) as f:
        header = json.loads(f.readline())
        recs = {}; raw = {}; end = None
        for line in f:
            r = json.loads(line)
            if 'end' in r: end = r['end']; break
            recs[r['name']] = r; raw[r['name']] = line if line.endswith('\n') else line + '\n'
    if end != len(recs) or header.get('nmods') != len(recs):
        print('mergeplan: inconsistent plan'); return 2
    names = list(recs); tm['read'] = round(time.time() - T0, 2)
    cache = {}
    if '--scan-cache' in a and os.path.exists(opt('--scan-cache', '')):
        import pickle
        try:
            with open(opt('--scan-cache', ''), 'rb') as f: pc = pickle.load(f)
            cache = pc['cache'] if isinstance(pc, dict) and pc.get('version') == SCAN_VERSION else {}
        except Exception:   # noqa: BLE001 - a broken cache only costs the scan
            cache = {}
    def cached(p):
        c = cache.get(p)
        if c is None: return None
        try:
            st = os.stat(p)
        except OSError:
            return None
        return c[2] if (st.st_size, st.st_mtime_ns) == (c[0], c[1]) else None
    infos = {n: cached(recs[n]['src']) for n in names}
    miss = [n for n in names if infos[n] is None]
    if miss:
        infos.update(zip(miss, POOL.map(scan, [recs[n]['src'] for n in miss], chunksize=256)))
    tm['scan_cache_hits'] = len(names) - len(miss)
    tm['scan'] = round(time.time() - T0, 2)
    key = {n: inv_key(recs[n]) for n in names}
    tm['key'] = round(time.time() - T0, 2)
    deps = {n: [d for d in recs[n]['deps'] if d in recs] for n in names}
    rd = collections.defaultdict(list)
    for n, ds in deps.items():
        for d in ds: rd[d].append(n)
    indeg = {n: len(deps[n]) for n in names}; q = [n for n in names if indeg[n] == 0]; order = []
    if sys.platform == 'darwin':   # APFS lists a directory in hash order: Lake's discovery order is arbitrary there.
        q.sort()                   # Sorted, ties of the greedy grouping break the same way on every checkout
        for importers in rd.values(): importers.sort()
    while q:
        n = q.pop(); order.append(n)
        for r in rd[n]:
            indeg[r] -= 1
            if indeg[r] == 0: q.append(r)
    if len(order) != len(names):
        print('mergeplan: cycle'); return 2
    tm['topo'] = round(time.time() - T0, 2)
    def mergeable(n):
        i = infos[n]
        return i is not None and key[n] is not None and not i['special']
    # static cost model (no timings: in-pipeline): c(m) = A + B*k(m) + C*lines(m); k(m) = project modules in m's import
    # closure, estimated on a deterministic sample of <= 8192 modules (bitsets); fit on the walls of an RH B1 run
    A, B, C = float(opt('--cost-a', '5.98')), float(opt('--cost-b', '0.000334')), float(opt('--cost-c', '0.031'))
    slackf_pre = float(opt('--slack', '1e18')); lmax_pre = float(opt('--max-leak', '1e18'))
    pos = {n: i for i, n in enumerate(order)}
    S = min(8192, len(order)); step = max(1, len(order) // S)
    sbit = {n: (1 << (pos[n] // step)) if pos[n] % step == 0 else 0 for n in names}
    clo = {}
    if True:   # sampled closure sizes: cost model for the near-end rule (and the optional deadline / leak rules)
        for n in order:
            b = sbit[n]
            for d in deps[n]: b |= clo[d]
            clo[n] = b
    kest = {n: ((bin(clo[n]).count('1') - (1 if sbit[n] else 0)) * step if clo else 0) for n in names}
    lines_of = {n: (infos[n]['nlines'] if infos[n] else 0) for n in names}
    fixed = {n: A + B * kest[n] for n in names}
    elab = {n: C * lines_of[n] for n in names}
    cost = {n: fixed[n] + elab[n] for n in names}
    slackf = float(opt('--slack', '1e18'))   # deadline rule off by default (static costs miss heavy modules)
    DEADLINE = slackf < 1e17
    est = {}; tail = {}; T = 0.0
    if True:
        for n in order:
            est[n] = max((est[d] + cost[d] for d in deps[n]), default=0.0)
        for n in reversed(order):
            tail[n] = max((cost[r] + tail[r] for r in rd[n]), default=0.0)
        T = max(est[n] + cost[n] + tail[n] for n in names)
    HL, HH = int(opt('--heavy-lines', '300')), int(opt('--heavy-hb', '2000000'))
    # RH declares 12,762 theorem names in several modules (Lean's import keeps one copy); inside ONE merged file a second
    # declaration (or a declaration of a name another member's import brings in) is an error -> a module that declares
    # a name some other module also declares is never a non-sink member (as the sink it sees only its own closure).
    declcount = collections.Counter(d for n in names if infos[n] for d in infos[n]['decls'])
    dupdecl = {n for n in names if infos[n] and any(declcount[d] > 1 for d in infos[n]['decls'])}
    # a module named by `open private ... from M` (its private names) must keep existing as a module of its own name:
    # never a non-sink member (as a sink the merged module keeps the name M)
    privref = set(m for n in names if infos[n] for m in infos[n].get('privfrom', ()))
    dupdecl |= privref & set(names)
    # AMBIGUITY rule (leaks): inside a merged file member x also sees the other members' declarations; if x uses a short
    # name t that another (non-ancestor) member declares in a namespace x opens, Lean reports 'ambiguous term' (the most
    # frequent merged-group failure in the RH tests) -> such pairs are never put into one group (both directions).
    AMB = '--no-ambiguity-rule' not in a
    tokc, dlc, opc = {}, {}, {}
    def tok(x):   # identifier tokens of x's body (lazy)
        v = tokc.get(x)
        if v is None:
            i = infos.get(x); v = tokc[x] = set(i['toks'].split()) if i else set()
        return v
    def dl(y):    # y's declarations: last component -> namespaces (lazy)
        v = dlc.get(y)
        if v is None:
            v = dlc[y] = {}
            for q in (infos[y]['decls'] if infos.get(y) else ()):
                ns, _, t = q.rpartition('.'); v.setdefault(t, set()).add(ns)
        return v
    def opn(x):
        v = opc.get(x)
        if v is None:
            i = infos.get(x); v = opc[x] = (set(i['opens']) | {''}) if i else {''}
        return v
    def conflict(x, y):   # x would see y's declarations: does x use a short name y declares in a namespace x opens?
        dy = dl(y)
        if not dy: return False
        tx = tok(x); ox = None
        for t, nss in dy.items():
            if t in tx:
                if ox is None: ox = opn(x)
                if not nss.isdisjoint(ox): return True
        return False
    def amb_ok(g, n):
        if not AMB: return True
        # members of g that import n (transitively, inside g) already saw n's declarations, and n cannot see theirs
        desc, st = set(), [r for r in rd[n] if gid.get(r) == g]
        while st:
            x = st.pop()
            if x in desc: continue
            desc.add(x); st.extend(r for r in rd[x] if gid.get(r) == g)
        return not any(conflict(n, m) or conflict(m, n) for m in gset[g] if m not in desc)
    def heavy(n):   # static 'possibly heavy' signal (RH B1 walls: 2,013 modules with > 30 s elaboration; lines >= 300: 28% of them vs 5% of the rest
        return lines_of[n] >= HL or infos[n]['hb'] >= HH or infos[n]['hv']   # lines, 58% with maxHeartbeats >= 1e6): never a non-sink member
    # NEAR-END rule: members merged into a sink at the end of the static critical path (tail <= NEF x T, e.g. Main and
    # its padding chain) are elaborated after everything else, and a failure there (leak) costs the split fallback at the
    # very end of the build -> only declaration-free members (import padding such as MainTheoremsAll) may join them
    NEF, NEL = float(opt('--near-end-frac', '0.05')), int(opt('--near-end-lines', '40'))
    CPF, CPL = float(opt('--cp-frac', '0')), int(opt('--cp-lines', '40'))   # optional: protect the static critical chain
    def near_end_block(sink, n):
        if tail[sink] <= NEF * T and (lines_of[n] > NEL or infos[n]['ndecl'] > 0): return True
        return CPF > 0 and est[sink] + cost[sink] + tail[sink] >= (1 - CPF) * T and lines_of[n] > CPL
    def ext_ready(n, members):
        if not DEADLINE: return 0.0
        return max((est[d] + cost[d] for d in deps[n] if d not in members), default=0.0)
    # LEAK cap: in a merged file every member sees the closure of ALL members' imports (U); member x 'leaks' the modules
    # of U outside its own closure (mt1 on RH: groups with max leak < 10 never failed, failures grow with the leak).
    LMAX = float(opt('--max-leak', '1e18'))   # off by default: mt1 failure rate 1.3% uncapped, the fallback handles it
    LEAK = LMAX < 1e17
    def depclo(n):
        b = 0
        for d in deps[n]: b |= clo[d]
        return b
    def leak_ok(g, n):
        if not LEAK: return 0
        U = gU[g] | depclo(n)
        for x in gset[g] | {n}:
            if bin(U & ~clo[x]).count('1') * step > LMAX: return None
        return U
    tm['costs'] = round(time.time() - T0, 2)
    gid, groups, glines, gpriv, gready, gel, gset, gU = {}, [], [], [], [], [], [], []
    why = collections.Counter()
    for n in reversed(order):
        imps = rd[n]
        if not imps: why['no-importer'] += 1
        elif not mergeable(n): why['special/unparsed'] += 1
        elif infos[n]['sinkonly']: why['sinkonly'] += 1
        elif heavy(n): why['heavy'] += 1
        elif n in dupdecl: why['dupdecl'] += 1
        if imps and mergeable(n) and not infos[n]['sinkonly'] and not heavy(n) and n not in dupdecl:
            gs = set(gid[r] for r in imps)
            if len(gs) > 1: why['importers-in-several-groups'] += 1
            if len(gs) == 1:
                g = next(iter(gs)); sink = groups[g][0]
                i = infos[n]
                if not mergeable(sink): why['sink-special'] += 1
                elif key[n] != key[sink]: why['other-invocation'] += 1
                elif len(groups[g]) >= maxm or glines[g] + i['nlines'] > maxl: why['caps'] += 1
                elif set(i['privs']) & gpriv[g]: why['private-collision'] += 1
                elif near_end_block(sink, n): why['near-end'] += 1
                elif not amb_ok(g, n): why['ambiguity'] += 1
                else:
                    members = gset[g] | {n}
                    rdy = max(gready[g], ext_ready(n, members))
                    fin = rdy + fixed[sink] + gel[g] + elab[n]
                    U = leak_ok(g, n) if (not DEADLINE or fin <= T - tail[sink] + slackf) else None
                    if U is None: why['leak/deadline'] += 1
                    else:
                        groups[g].append(n); glines[g] += i['nlines']; gpriv[g] |= set(i['privs']); gid[n] = g
                        gready[g] = rdy; gel[g] += elab[n]; gset[g] = members; gU[g] = U
                        continue
        gid[n] = len(groups); groups.append([n])
        glines.append(lines_of[n]); gpriv.append(set(infos[n]['privs']) if infos[n] else set())
        gset.append({n}); gready.append(ext_ready(n, {n})); gel.append(elab[n]); gU.append(depclo(n) if LEAK else 0)
    del clo
    tm['plan'] = round(time.time() - T0, 2)
    # EXACT LEAK rule (post-pass; full-RH run 1 showed that a leak can change a merged member SILENTLY: a name that the
    # member uses resolves to a declaration it never imported - e.g. a namespace-local Geo.Tor.IsNormalScheme shadowing
    # the one it meant - so the merged group compiles but downstream modules break). For every member x of every
    # multi-member group: leak(x) = closure(group's external imports) + the other members - closure(x) (exact closures);
    # x is RISKY if some module in leak(x) declares N.t where t is an identifier token of x and N is a namespace x can see
    # unqualified (opened namespaces, its own namespace prefixes, combinations, the root). Risky members and every member
    # they import inside the group leave the group (singletons); the rest stays importer-closed (leaks only shrink).
    nrisky = nremoved = 0
    if '--no-exact-leak-rule' not in a:
        eclo = {}
        for n in order:
            b = 0
            for d in deps[n]: b |= eclo[d] | (1 << pos[d])
            eclo[n] = b
        nsidx = collections.defaultdict(lambda: collections.defaultdict(list))
        for n in names:
            if infos[n]:
                for q in infos[n]['decls']:
                    ns_, _, t = q.rpartition('.')
                    nsidx[ns_][t].append(pos[n])
        INSTR = '--no-instance-leak-rule' not in a
        instbits = 0
        if INSTR:
            for n in names:
                if infos[n] and infos[n].get('ninst', 0): instbits |= 1 << pos[n]
        scopedby = collections.defaultdict(int)   # namespace -> modules with scoped notations/instances or `export`s there
        for n in names:
            for ns_ in (infos[n].get('scopedns', ()) if infos[n] else ()):
                scopedby[ns_] |= 1 << pos[n]
        _LK.update(groups=groups, eclo=eclo, deps=deps, pos=pos, infos=infos,
                   nsidx={k: dict(v) for k, v in nsidx.items()}, instbits=instbits, scopedby=dict(scopedby))
        _LK['instmember'] = '--no-instance-member-rule' not in a
        _LK['instleakall'] = '--instance-leak-all' in a
        if '--toxic-leak-rule' in a:   # a leaked module with GLOBAL attribute changes (attribute [instance]/[simp]/[-x]/...)
            _LK['toxbits'] = sum(1 << pos[n] for n in names if infos[n] and infos[n]['sinkonly'])
        multi_idx = [gi for gi, g in enumerate(groups) if len(g) > 1]
        # forked now: the workers inherit _LK. Few workers: forking this large process costs more than the checks
        # (RH, 175k modules: 16 workers 4.7 s, 32: 5.7 s, 64: 8.6 s, 128: 15 s)
        with ProcessPoolExecutor(max(1, min(jobs, int(opt('--leak-jobs', '16'))))) as lex:
            results = list(lex.map(_leak_check, multi_idx, chunksize=64))
        _LK.clear()
        for gi, R in results:
            if not R: continue
            g = groups[gi]; ms = set(g); R = set(R)
            nrisky += len(R)
            st = list(R)   # risky members and everything they import inside the group leave it
            while st:
                y = st.pop()
                for d in deps[y]:
                    if d in ms and d not in R: R.add(d); st.append(d)
            nremoved += len(R)
            groups[gi] = [m for m in g if m not in R]
            for m in R:
                groups.append([m])
        del eclo
    tm['exact_leak'] = round(time.time() - T0, 2)
    # MEASURED DENY LIST (last rule): a group that contains a module whose merged group failed in an earlier run of the
    # same project is not merged (merging failures are deterministic per group: the same groups failed on two machines
    # with different toolchains/flags); dissolving it changes no other group
    ndeny_g = ndeny_m = 0; deny = set()
    if '--deny' in a:
        try:
            with open(opt('--deny', '')) as f:
                deny = {l.split('#')[0].strip() for l in f} - {''}
        except OSError as ex:
            print('mergeplan: deny list unreadable (ignored):', ex)
        for gi in range(len(groups)):
            g = groups[gi]
            if len(g) > 1 and any(m in deny for m in g):
                ndeny_g += 1; ndeny_m += len(g)
                groups[gi] = [g[0]]
                groups.extend([m] for m in g[1:])
    os.makedirs(os.path.join(out, 'src'), exist_ok=True)
    multi = [g for g in groups if len(g) > 1]
    stats = {'modules': len(names), 'groups': len(groups), 'multi_groups': len(multi), 'static_cp_est_s': round(T),
             'merged_members': sum(len(g) for g in multi), 'max_members': maxm, 'max_lines': maxl, 'max_leak': LMAX,
             'special': sum(1 for n in names if infos[n] is not None and infos[n]['special']),
             'not_merged_because': dict(why.most_common()), 'dup_declarers': len(dupdecl),
             'exact_leak_risky_members': nrisky, 'exact_leak_removed_members': nremoved,
             'deny_names': len(deny), 'deny_dissolved_groups': ndeny_g, 'deny_dissolved_members': ndeny_m, 'dup_names': sum(1 for v in declcount.values() if v > 1),
             'unparsed': sum(1 for n in names if infos[n] is None),
             'size_hist': dict(sorted(collections.Counter(len(g) for g in groups).items()))}
    if '--stats-only' in a:
        print(json.dumps(stats)); return 0
    newrecs = {}; fallback = []; gjson = {}; jobsw = []
    outabs = os.path.abspath(out)
    for g in groups:
        sink = g[0]
        if len(g) == 1:
            newrecs[sink] = None; continue
        members = set(g)
        # emission order: DFS post-order from the sink over intra-group imports, in header order (Lean's import order)
        emitted, seq = set(), []
        def visit(x):
            st = [(x, 0)]
            while st:
                y, k = st.pop()
                if k == 0:
                    if y in emitted: continue
                ims = [d for d in infos[y]['imports'] if d in members]
                if k < len(ims):
                    st.append((y, k + 1))
                    if ims[k] not in emitted: st.append((ims[k], 0))
                else:
                    if y not in emitted: emitted.add(y); seq.append(y)
        visit(sink)
        if len(seq) != len(g) or seq[-1] != sink:   # (cannot happen for importer-closed groups) -> keep singletons
            for n in g: newrecs[n] = None
            continue
        # external imports in the ORIGINAL first-reach order of Lean's import walk from the sink (header order, recursing
        # into members): every module importing the merged sink then gets EXACTLY the original module order minus the
        # members (equal-priority instances are tried most-recently-imported first, so a reordered header can change
        # which instance a DOWNSTREAM module picks: v3/v4 full-RH runs, StatementZ.instMeasMat vs
        # MatrixMeasurableSpace.matrixMeasurableSpace -> HolCoefPf failed alone)
        ext, seen, vis = [], set(), {sink}
        st = [iter(infos[sink]['imports'])]
        while st:
            imp = next(st[-1], None)
            if imp is None: st.pop(); continue
            if imp in members:
                if imp not in vis: vis.add(imp); st.append(iter(infos[imp]['imports']))
            elif imp not in seen:
                seen.add(imp); ext.append(imp)
        if '--member-import-order' in a:   # v3/v4 behaviour, kept ONLY for build/test/merge.sh (shows the downstream failure)
            ext = list(dict.fromkeys(imp for n in seq for imp in infos[n]['imports'] if imp not in members))
            if 'Mathlib' in ext: ext.remove('Mathlib'); ext.insert(0, 'Mathlib')
        path = os.path.join(outabs, 'src', rel_of(sink) + '.lean')
        jobsw.append((path, ext, [(n, recs[n]['src'], infos[n]['scopes']) for n in seq]))
        r = dict(recs[sink])
        r['argv'] = [path if x == recs[sink]['src'] else x for x in r['argv']]
        if path not in r['argv']:
            print(f'mergeplan: source path not in argv of {sink}'); return 2
        r['src'] = path
        r['deps'] = sorted(set(d for n in seq for d in deps[n] if d not in members))
        if any('"importArts": {}' not in recs[n]['setup'] or '"imports"' in recs[n]['setup'] for n in seq):
            # the merged module's import artifacts / header-override imports = the members' minus the members themselves
            arts = {}; imps2 = []; seen2 = set(); has_imps = False
            for n in seq:
                d = json.loads(recs[n]['setup'])
                arts.update(d.get('importArts') or {})
                if d.get('imports') is not None:
                    has_imps = True
                    for e in d['imports']:
                        mod = e.get('module') if isinstance(e, dict) else e
                        k = json.dumps(e, sort_keys=True)
                        if mod in members or k in seen2: continue
                        seen2.add(k); imps2.append(e)
            extpos = {m: i for i, m in enumerate(ext)}
            imps2.sort(key=lambda e: extpos.get(e.get('module') if isinstance(e, dict) else e, len(ext)))
            st = json.loads(recs[sink]['setup'])
            st['importArts'] = {k: v for k, v in arts.items() if k not in members}
            if has_imps: st['imports'] = imps2
            r['setup'] = json.dumps(st, indent=1)
        r['merged'] = seq
        newrecs[sink] = r
        gjson[sink] = seq
        for n in seq: fallback.append(raw[n])
    bad = [p for p, ok in zip((j[0] for j in jobsw), POOL.map(write_merged, jobsw, chunksize=64)) if not ok]
    POOL.shutdown()
    if bad:
        print(f'mergeplan: cannot write {bad[:3]}'); return 2
    hdr = dict(header); hdr['nmods'] = len(newrecs); hdr['merge'] = {'groups': len(gjson), 'members': sum(len(v) for v in gjson.values())}
    with open(os.path.join(out, 'plan.jsonl'), 'w') as f:
        f.write(json.dumps(hdr) + '\n')
        for n in names:
            if n in newrecs: f.write(raw[n] if newrecs[n] is None else json.dumps(newrecs[n]) + '\n')
        f.write(json.dumps({'end': len(newrecs)}) + '\n')
    with open(os.path.join(out, 'fallback.jsonl'), 'w') as f:
        f.writelines(fallback)
    with open(os.path.join(out, 'groups.json'), 'w') as f: json.dump(gjson, f)
    tm['write'] = round(time.time() - T0, 2); stats['times'] = tm
    with open(os.path.join(out, 'stats.json'), 'w') as f: json.dump(stats, f)
    print(json.dumps(stats))
    return 0


if __name__ == '__main__':
    sys.exit(main())
