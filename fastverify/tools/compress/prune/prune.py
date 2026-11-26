#!/usr/bin/python3 -I
"""prune.py INDEX.pkl SRC_PROJECT OUT_PROJECT [options]   (classic and module-system projects)
Closure pruning of a Lean 4 project (supports both traditional files and Lean 4 `module` / `public import` files).
"""
import sys, os, re, pickle, collections, json, argparse, shutil, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leansrc

DELETABLE = {'theorem', 'lemma', 'def', 'abbrev', 'example'}
FILELOCAL = {'module', 'import', 'namespace', 'section', 'end', 'open', 'variable', 'universe', 'set_option', 'omit', 'include'}
IMP_MODS = {'import', 'public', 'private', 'meta', 'all'}


def only_expose_attrs(attrs):
    """In Lean 4's `module` system, `@[expose]` only marks a body as exported in `.olean` (the default in non-module Lean);
    it registers no simp/ext/instance/coercion/elaborator hook, so dead `@[expose]`-only decls are G1-deletable."""
    if not attrs:
        return True
    for g in attrs:
        inner = g.strip()
        if inner.startswith('@[') and inner.endswith(']'):
            inner = inner[2:-1]
        for part in inner.split(','):
            if part.strip() != 'expose':
                return False
    return True


def parse_import_line(code_line):
    """Parse a comment-stripped header line. Returns None if not an import line, else
    (vis, is_special, mods_list) where vis in ('plain', 'public', 'private'),
    is_special = True if `meta`, `all`, or != 1 module on the line."""
    toks = code_line.split()
    if not toks or 'import' not in toks:
        return None
    idx = toks.index('import')
    pre = toks[:idx]
    if any(w not in ('public', 'private', 'meta') for w in pre):
        return None
    rest = toks[idx + 1:]
    has_all = False
    if rest and rest[0] == 'all':
        has_all = True
        rest = rest[1:]
    if not rest:
        return None
    has_meta = 'meta' in pre
    vis = 'public' if 'public' in pre else ('private' if 'private' in pre else 'plain')
    is_special = has_all or has_meta or (len(rest) != 1)
    return vis, is_special, rest


def last_component(name):
    if '«' in name:
        parts = re.findall(r'«[^»]*»|[^.]+', name)
    else:
        parts = name.split('.')
    return parts[-1].strip('«»')


def strip_private(name):
    if name.startswith('_private.'):
        m = re.match(r'_private\.(.*?)\.0\.(.*)$', name)
        if m:
            return m.group(2), True
    return name, False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('index'); ap.add_argument('src'); ap.add_argument('out')
    ap.add_argument('--protect', default='Main,Statements')
    ap.add_argument('--only-protect-explicit', action='store_true',
                    help='only protect modules in --protect (allow dropping unused secondary lean_lib roots; run fixlake.py after)')
    ap.add_argument('--drop-unbuilt', action='store_true',
                    help='drop .lean files that were not built into .olean in the reference build (outside idx["mods"])')
    ap.add_argument('--trim-barrels', action='store_true',
                    help='G1: trim dead subsystem imports from pure import-barrel files and drop unreachable modules outside the target cone')
    ap.add_argument('--drop-empty-modules', action='store_true')
    ap.add_argument('--keep-names', default='', help='file with constant/decl names never to delete (from failed builds)')
    ap.add_argument('--keep-modules', default='', help='file with module names never to drop/edit')
    ap.add_argument('--report', default=None)
    ap.add_argument('--ext-namespaces', default='', help='file: namespaces registered by non-project modules (Mathlib, core)')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--other-edits', nargs='*', default=[], help='edit lists (team TSV format) of other transformations')
    ap.add_argument('--extra-kinds', default='', help='G2: also delete dead commands of these kinds (e.g. instance,structure,class,inductive)')
    ap.add_argument('--allow-attrs', action='store_true', help='G2: also delete dead declarations that carry attributes')
    ap.add_argument('--no-allow-expose', action='store_true', help='do not treat @[expose]-only attributes as G1-safe')
    a = ap.parse_args()
    t0 = time.time()
    idx = pickle.load(open(a.index, 'rb'))
    live = idx['live']; consts = idx['consts']; ranges = idx['ranges']; imps = idx['mods']
    protect = set(x for x in a.protect.split(',') if x)
    if not a.only_protect_explicit:
        for lf in ('lakefile.toml', 'lakefile.lean'):
            p = os.path.join(a.src, lf)
            if not os.path.exists(p): continue
            t = open(p, encoding='utf-8').read()
            if lf.endswith('.toml'):
                for blk in re.split(r'(?m)^(?=\[\[)', t):
                    if blk.startswith('[[lean_lib]]') or blk.startswith('[[lean_exe]]'):
                        nm = re.search(r'^name\s*=\s*"([^"]*)"', blk, re.M)
                        rts = re.search(r'^roots\s*=\s*\[(.*?)\]', blk, re.M | re.S)
                        rt = re.search(r'^root\s*=\s*"([^"]*)"', blk, re.M)
                        if rts: protect.update(re.findall(r'"([^"]*)"', rts.group(1)))
                        elif rt: protect.add(rt.group(1))
                        elif nm: protect.add(nm.group(1))
            else:
                protect.update(re.findall(r'(?m)^\s*(?:@\[[^\]]*\]\s*)?lean_(?:lib|exe)\s+«?([\w.]+)»?', t))
                for grp in re.findall(r'roots\s*:=\s*#\[(.*?)\]', t, re.S):
                    protect.update(x.strip('`«» ') for x in grp.split(','))
                protect.update(re.findall(r'root\s*:=\s*`([\w.]+)', t))
    print('protected (solution module / library roots):', sorted(protect)[:12], file=sys.stderr, flush=True)
    extra_kinds = set(x for x in a.extra_kinds.split(',') if x)
    keep_names = set(open(a.keep_names).read().split()) if a.keep_names else set()
    keep_mods = set(open(a.keep_modules).read().split()) if a.keep_modules else set()
    srcdir = os.path.join(a.src, 'src') if os.path.isdir(os.path.join(a.src, 'src')) else a.src
    mods = {}
    stats = collections.Counter()
    unbuilt_dropped = {}
    for dp, dn, fn in os.walk(srcdir):
        dn[:] = [d for d in dn if not d.startswith('.')]
        for f in fn:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                mname = os.path.relpath(p, srcdir)[:-5].replace('/', '.')
                if a.drop_unbuilt and imps and (mname not in imps) and (mname not in protect) and (mname not in keep_mods):
                    unbuilt_dropped[mname] = p
                else:
                    mods[mname] = p
    if unbuilt_dropped:
        print('unbuilt .lean files outside reference build (dropped before analysis):', len(unbuilt_dropped), file=sys.stderr, flush=True)
    print('modules', len(mods), 'parse...', file=sys.stderr, flush=True)
    M = {}
    cand = []
    for m, p in mods.items():
        lines = open(p, encoding='utf-8').read().split('\n')
        cmds, code = leansrc.split_commands(lines)
        is_mod = any(cc.kind == 'module' for cc in cmds[:3])
        info = {'lines': lines, 'cmds': cmds, 'code': code, 'owned': [[] for _ in cmds], 'rnames': [[] for _ in cmds],
                'mutual': any(c.kind == 'mutual' for c in cmds), 'is_module': is_mod}
        info['ns'] = leansrc.namespaces(cmds, code)
        M[m] = info
        starts = [c.text_start for c in cmds]
        rset = {}
        import bisect
        for (nm, l, col, el, ec) in ranges.get(m, []):
            k = bisect.bisect_right(starts, l - 1) - 1
            if k < 0 or not (cmds[k].text_start <= l - 1 < cmds[k].end + 1):
                stats['range_outside_cmd'] += 1; k = -1
            elif el - 1 >= (cmds[k + 1].text_start if k + 1 < len(cmds) else len(lines)):
                stats['range_spans_cmds'] += 1; k = -2
            rset[nm] = k
            if k >= 0:
                info['rnames'][k].append(nm)
        for (cn, kind) in consts.get(m, []):
            parts = cn.split('.')
            k = None
            for j in range(len(parts), 0, -1):
                pre = '.'.join(parts[:j])
                if pre in rset:
                    k = rset[pre]; break
            if k is None:
                stats['orphan_consts'] += 1
                if cn in live: stats['orphan_live'] += 1
                continue
            if k < 0:
                stats['unmapped_consts'] += 1
                info.setdefault('poison', False)
                if cn in live: info['poison'] = True
                continue
            info['owned'][k].append(cn)
        for k, c in enumerate(cmds):
            stats['cmds'] += 1
            ow = info['owned'][k]
            is_live = any(x in live for x in ow) or any(x in keep_names for x in ow) or \
                any(x in keep_names for x in info['rnames'][k])
            c_dead = (bool(ow) and not is_live) or (c.kind == 'example' and not ow)
            if c.kind in DECL_KINDS_ALL:
                stats['decl_cmds'] += 1
                st_ = 'decl_live' if is_live else ('decl_dead' if c_dead else 'decl_noconst')
                stats[st_] += 1; stats['lines_' + st_] += c.end - c.start
            if not c_dead: continue
            if m in protect or m in keep_mods or info['mutual'] or info.get('poison'):
                stats['skip_protected'] += 1; continue
            if c.kind not in DELETABLE and c.kind not in extra_kinds:
                stats['skip_kind_' + str(c.kind)] += 1; continue
            safe_attr = (not c.attrs) or (not a.no_allow_expose and only_expose_attrs(c.attrs))
            if not safe_attr and not a.allow_attrs:
                stats['skip_attr'] += 1; continue
            if c.kind in extra_kinds or (not safe_attr):
                stats['g2_candidate_' + (c.kind if safe_attr else 'attr')] += 1
            cand.append((m, k))
    print('parsed', round(time.time() - t0, 1), 's; candidates', len(cand), dict(stats), file=sys.stderr, flush=True)

    barrel_killed_lines = collections.defaultdict(set)
    hdr_imp_lines = {}
    special_imported = set()
    for m, info in M.items():
        ilines = []
        for c in info['cmds']:
            if c.kind == 'import':
                for jj in range(c.text_start, c.end):
                    parsed = parse_import_line(info['code'][jj])
                    if parsed is not None:
                        vis, is_spec, ml = parsed
                        ilines.append((jj, vis, is_spec, ml))
                        if is_spec or vis == 'private':
                            special_imported.update(ml)
                    else:
                        raw = [x for x in info['code'][jj].split() if x not in IMP_MODS]
                        if raw:
                            ilines.append((jj, 'plain', True, raw))
                            special_imported.update(raw)
        hdr_imp_lines[m] = ilines

    if a.trim_barrels:
        seed_live = {m for m in M if any(cn in live for (cn, _) in consts.get(m, [])) or
                     any(cn in keep_names for (cn, _) in consts.get(m, []))}
        for t in idx.get('targets', ()):
            for m, cl in consts.items():
                if m in M and any(cn == t for (cn, _) in cl):
                    seed_live.add(m)
        cone_mods = set(seed_live | (keep_mods & set(M)))
        st_c = list(cone_mods)
        while st_c:
            xm = st_c.pop()
            nbrs = [y for (_, _, _, ml) in hdr_imp_lines.get(xm, ()) for y in ml if y in M]
            nbrs.extend(y for y in imps.get(xm, ()) if y in M)
            for y in nbrs:
                if y not in cone_mods:
                    cone_mods.add(y); st_c.append(y)
        pure_barrels = {
            m for m, info in M.items()
            if all(c.kind in ('module', 'import') and not c.attrs for c in info['cmds'])
            and not any(is_spec for (_, _, is_spec, _) in hdr_imp_lines[m])
        }
        reaches_cone = set(cone_mods)
        changed = True
        while changed:
            changed = False
            for b in pure_barrels:
                if b in reaches_cone:
                    continue
                if any(y in reaches_cone for (_, _, _, ml) in hdr_imp_lines[b] for y in ml if y in M):
                    reaches_cone.add(b); changed = True
        for b in pure_barrels:
            new_il = []
            for (jj, vis, is_spec, ml) in hdr_imp_lines[b]:
                if not is_spec and len(ml) == 1 and ml[0] in M and ml[0] not in reaches_cone:
                    barrel_killed_lines[b].add(jj)
                else:
                    new_il.append((jj, vis, is_spec, ml))
            hdr_imp_lines[b] = new_il
        roots_fwd = set(cone_mods)
        first_prot = next((x for x in a.protect.split(',') if x), '')
        for pm in list(protect):
            if pm in M and (pm not in pure_barrels or pm in reaches_cone or pm == first_prot):
                roots_fwd.add(pm)
            top_pm = pm.split('.')[0]
            if top_pm in M and top_pm in reaches_cone:
                roots_fwd.add(top_pm); protect.add(top_pm)
        st_f = list(roots_fwd)
        reach_mods = set(roots_fwd)
        while st_f:
            xm = st_f.pop()
            for (_, _, _, ml) in hdr_imp_lines.get(xm, ()):
                for y in ml:
                    if y in M and y not in reach_mods:
                        reach_mods.add(y); st_f.append(y)
        unreach = [u for u in list(M) if u not in reach_mods and u not in keep_mods]
        for u in unreach:
            unbuilt_dropped[u] = mods.pop(u)
            del M[u]
            hdr_imp_lines.pop(u, None)
            barrel_killed_lines.pop(u, None)
        cand = [(m, k) for (m, k) in cand if m in M]
        print('trim-barrels: cone_mods', len(cone_mods), 'pure_barrels', len(pure_barrels),
              'unreachable_dropped', len(unreach), 'surviving_M', len(M), file=sys.stderr, flush=True)

    locked = set(); other_mods = set(); global_tokens = set(); other_occ = []
    added_imports = collections.defaultdict(list)   # module -> imports ADDED by other owners' edits (D17)
    for ef in a.other_edits:
        for line in open(ef, encoding='utf-8'):
            p = line.rstrip('\n').split('\t')
            if len(p) < 5: continue
            em, es, ee, act = p[0], int(p[1]), int(p[2]), p[3]
            text = p[5].replace('\\n', '\n') if len(p) > 5 else ''
            for x in re.findall(r'^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.*)$', text, re.M):
                for y in x.split():
                    other_mods.add(y)
                    if em in M: added_imports[em].append(y)   # D17: the edge exists in the combined tree
            if act == 'newfile' or em not in M:
                global_tokens.update(leansrc.tokens(text)); other_mods.add(em); continue
            other_mods.add(em)
            cmds = M[em]['cmds']; kk = None
            for k, c in enumerate(cmds):
                if c.start <= ee - 1 and es - 1 < max(c.end, c.start + 1):
                    locked.add((em, k)); kk = k if kk is None else kk
            if text: other_occ.append((em, -1 - len(other_occ), text))
    if a.other_edits:
        print('other edits: locked commands', len(locked), 'modules kept', len(other_mods), 'global tokens',
              len(global_tokens), file=sys.stderr, flush=True)
        cand = [x for x in cand if x not in locked]

    keyof = {}
    for (m, k) in cand:
        c = M[m]['cmds'][k]
        names = M[m]['rnames'][k]
        keys = set(); priv = True
        for nm in names:
            base, isp = strip_private(nm)
            keys.add(last_component(base)); priv = priv and isp
        if c.kind == 'example':
            keys = set(); priv = False
        if not names and c.kind != 'example':
            continue
        if keys & global_tokens: continue
        if M[m]['is_module']:
            priv = False
        keyof[(m, k)] = (keys, priv and bool(names))
    K = set()
    for ks, _ in keyof.values(): K |= ks
    occ = collections.defaultdict(list)
    for m, info in M.items():
        code = info['code']
        for k, c in enumerate(info['cmds']):
            toks = collections.Counter(t for j in range(c.text_start, c.end) for t in leansrc.tokens(code[j]) if t in K)
            if not toks: continue
            if c.name:
                for comp in re.split(r'\.', c.name.replace('_root_.', '')):
                    if toks.get(comp): toks[comp] -= 1
            for t, n in toks.items():
                if n > 0: occ[t].append((m, k))
    for (em, kk, text) in other_occ:
        toks = set(t for t in leansrc.tokens(text) if t in K)
        for t in toks: occ[t].append((em, kk))
    openpriv = set()
    for m, info in M.items():
        for k, c in enumerate(info['cmds']):
            if c.kind == 'open' and 'private' in ' '.join(info['code'][c.text_start:c.end]).split()[:3]:
                openpriv.add((m, k))

    mid = {m: i for i, m in enumerate(M)}
    nonmod_mask = 0
    for m, info in M.items():
        if not info['is_module']:
            nonmod_mask |= (1 << mid[m])

    # Structured imports per module (already parsed above and trimmed if --trim-barrels)
    # imports added by other owners' edits count for visibility (name safety); without them pruning deleted the
    # targets of the dedup IMPORT-mode aliases ('Unknown constant', 139 modules in an RH candidate build)
    srcimp = {m: [y for (_, _, _, ml) in hdr_imp_lines[m] for y in ml if y in mid] + [y for y in added_imports.get(m, []) if y in mid] for m in M}

    importers = collections.defaultdict(list)
    for m, ims in srcimp.items():
        for x in ims: importers[x].append(m)
    order = []; state = {}
    for m0 in M:
        if m0 in state: continue
        stack = [(m0, iter(importers[m0]))]; state[m0] = 1
        while stack:
            m, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                stack.pop(); order.append(m); state[m] = 2
            elif nxt not in state:
                state[nxt] = 1; stack.append((nxt, iter(importers[nxt])))
    DOWN = {}
    for m in order:
        acc = 0
        for x in importers[m]:
            acc |= DOWN[x] | (1 << mid[x])
        DOWN[m] = acc
    print('reachability done', round(time.time() - t0, 1), 's', file=sys.stderr, flush=True)

    cmdkeys = {}
    for t, lst in occ.items():
        for (m, k) in lst:
            cmdkeys.setdefault((m, k), []).append(t)
    privopen = set()
    for (m, k) in openpriv:
        for t in cmdkeys.get((m, k), []): privopen.add(t)

    NONREF = {'module', 'import', 'namespace', 'section', 'end'}
    for t in list(occ.keys()):
        occ[t] = [(m, k) for (m, k) in occ[t] if k < 0 or M[m]['cmds'][k].kind not in NONREF]
    cmdkeys = {}
    for t, lst in occ.items():
        for (m, k) in lst:
            cmdkeys.setdefault((m, k), []).append(t)
    bykey = collections.defaultdict(list)
    for key, (ks, priv) in keyof.items():
        for kk in ks: bykey[kk].append(key)

    def fixpoint(force):
        kept = set(k for k in keyof if k in force)
        cnt = collections.defaultdict(collections.Counter); OCC = {}
        def add_cmd(m, k):
            new_t = []
            for t in cmdkeys.get((m, k), ()):
                cnt[t][m] += 1
                if cnt[t][m] == 1:
                    OCC[t] = OCC.get(t, 0) | (1 << mid[m]); new_t.append(t)
            return new_t
        queue = []
        for t, lst in occ.items():
            for (m, k) in lst:
                if (m, k) in keyof and (m, k) not in kept: continue
                cnt[t][m] += 1
        for t, cm in cnt.items():
            b = 0
            for m in cm: b |= 1 << mid[m]
            OCC[t] = b
            queue.append(t)
        rounds = 0
        while queue:
            rounds += 1
            nxt = []
            for t in set(queue):
                for key in bykey.get(t, ()):
                    if key in kept: continue
                    m, k = key
                    ks, priv = keyof[key]
                    hit = False
                    for kk in ks:
                        if cnt[kk][m] > 0: hit = True; break
                        if priv:
                            if kk in privopen: hit = True; break
                            continue
                        if OCC.get(kk, 0) & DOWN[m]: hit = True; break
                    if hit:
                        kept.add(key)
                        nxt.extend(add_cmd(m, k))
            queue = nxt
        deleted = set(k for k in keyof if k not in kept)
        return deleted, rounds

    def empty_modules(deleted, force_mods):
        dropped = set()
        if not a.drop_empty_modules: return dropped
        for m, info in M.items():
            if m in protect or m in keep_mods or m in force_mods or m in other_mods or m in special_imported:
                continue
            # If m has any special import line itself, do not drop m
            if any(is_spec for (_, _, is_spec, _) in hdr_imp_lines[m]):
                continue
            # If m is a `module` file with non-public imports AND a non-`module` file transitively imports m,
            # dropping m would either hide those private imports from the non-`module` importer or expose them to `module` importers.
            if info['is_module'] and (DOWN[m] & nonmod_mask):
                if any(vis != 'public' for (_, vis, _, _) in hdr_imp_lines[m]):
                    continue
            rest = [c for k, c in enumerate(info['cmds']) if (m, k) not in deleted]
            if all(c.kind in FILELOCAL for c in rest) and not any(c.attrs for c in rest):
                if any(c.kind == 'set_option' and c.mods for c in rest): continue
                dropped.add(m)
        return dropped

    nss = idx.get('nss', {})
    ext_ns = set()
    if a.ext_namespaces:
        ext_ns = set(open(a.ext_namespaces).read().split())
    orig_reg = collections.defaultdict(list)
    for m in M:
        for n in nss.get(m, []): orig_reg[n].append(m)
    def prefixes(n):
        ps = n.split('.')
        return ['.'.join(ps[:i]) for i in range(1, len(ps) + 1)]
    nscmd = {}; cmdsup = {}
    for m, info in M.items():
        s = {}
        for k, c in enumerate(info['cmds']):
            cur = info['ns'][k]
            if c.kind == 'namespace':
                toks = info['code'][c.text_start].split()
                if len(toks) > 1:
                    full = (cur + '.' if cur else '') + toks[1]
                    for n in prefixes(full): s.setdefault(n, k)
            sup = set()
            for nm in list(info['owned'][k]) + list(info['rnames'][k]):
                sup.update(prefixes(strip_private(nm)[0])[:-1])
            if sup: cmdsup[(m, k)] = sup
        nscmd[m] = s
    opens = []
    ident_re = re.compile(r"[\w'!?.₀-₉]+")
    known_ns = lambda n: n in ext_ns or n in orig_reg
    for m, info in M.items():
        scopes = [[]]
        for k, c in enumerate(info['cmds']):
            if c.kind in ('namespace', 'section'):
                scopes.append([]); continue
            if c.kind == 'end':
                if len(scopes) > 1: scopes.pop()
                continue
            if c.kind in ('open', 'export'):
                text = ' '.join(info['code'][c.text_start:c.end])
            else:
                text = ' '.join(md for md in c.mods if md.split()[:1] == ['open'])
            if not text: continue
            cur = info['ns'][k]
            persistent = c.kind in ('open', 'export') and not c.mods
            local_open = []
            for seg in re.findall(r'\b(?:open|export)\b(.*?)(?:\bin\b|$)', text):
                seg = re.sub(r'\([^)]*\)', ' ', seg)
                seg = re.split(r'\b(?:hiding|renaming)\b', seg)[0]
                for x in ident_re.findall(seg):
                    if x in ('scoped', 'private', 'hiding', 'renaming', 'from', 'in') or x[0].isdigit(): continue
                    opened = [o for sc in scopes for o in sc] + local_open
                    cands = ([p + '.' + x for p in reversed(prefixes(cur))] if cur else []) + \
                            [o + '.' + x for o in reversed(opened)] + [x]
                    if any(cc in orig_reg for cc in cands) and not any(cc in ext_ns for cc in cands):
                        opens.append((m, k, cands))
                    res = next((cc for cc in cands if known_ns(cc)), x)
                    local_open.append(res)
            if persistent:
                scopes[-1].extend(local_open)
    print('namespace check: project-registered open/export identifiers', len(opens), file=sys.stderr, flush=True)

    def visible(r, mo):
        return r == mo or (DOWN[r] >> mid[mo]) & 1

    force = set(); force_mods = set()
    for it in range(30):
        deleted, rounds = fixpoint(force)
        dropped = empty_modules(deleted, force_mods)
        srcs = collections.defaultdict(list)
        for m in M:
            for n, k in nscmd[m].items(): srcs[(m, n)].append(('ns', k))
        for (m, k), sup in cmdsup.items():
            for n in sup: srcs[(m, n)].append(('decl', k))
        supmods = collections.defaultdict(set)
        first_src = {}
        lost = set()
        for n, regs in orig_reg.items():
            for r in regs:
                if r in dropped:
                    lost.add(n); continue
                sl = srcs.get((r, n))
                if not sl:
                    supmods[n].add(r); first_src[(r, n)] = None; continue
                surv = [k for (t, k) in sl if t == 'ns' or (r, k) not in deleted]
                if not surv:
                    lost.add(n); continue
                supmods[n].add(r); first_src[(r, n)] = min(surv)
        def supported(cc, mo, k):
            for r in supmods.get(cc, ()):
                if r == mo:
                    f = first_src.get((r, cc))
                    if f is not None and f < k: return True
                elif visible(r, mo):
                    return True
            return False
        viol = 0; added = 0; unfixable = []
        for (mo, k, cands) in opens:
            if mo in dropped or (mo, k) in deleted: continue
            if not any(cc in lost for cc in cands): continue
            if any(supported(cc, mo, k) for cc in cands): continue
            viol += 1
            fixed = False
            for cc in cands:
                for r in sorted(orig_reg.get(cc, ())):
                    if r == mo:
                        sl = [kk for (t, kk) in srcs.get((r, cc), []) if t == 'decl' and kk < k and (r, kk) in deleted]
                        if sl: force.add((r, sl[0])); added += 1; fixed = True
                    elif visible(r, mo):
                        sl = srcs.get((r, cc), [])
                        if any(t == 'ns' for (t, kk) in sl) or not sl:
                            if r in dropped: force_mods.add(r); added += 1; fixed = True
                        else:
                            dk = sorted(kk for (t, kk) in sl if (r, kk) in deleted)
                            if dk: force.add((r, dk[0])); added += 1; fixed = True
                            if r in dropped: force_mods.add(r); added += 1; fixed = True
                    if fixed: break
                if fixed: break
            if not fixed: unfixable.append((mo, k, cands))
        print('iteration', it, 'fixpoint rounds', rounds, 'deleted', len(deleted), 'of', len(keyof), 'dropped',
              len(dropped), 'namespace violations', viol, 'restored', added, round(time.time() - t0, 1), 's',
              file=sys.stderr, flush=True)
        if viol == 0 or added == 0:
            if unfixable:
                print('UNFIXED namespace violations:', unfixable[:20], file=sys.stderr, flush=True)
            break

    livecmd = set()
    for m, info in M.items():
        for k in range(len(info['cmds'])):
            if any(x in live for x in info['owned'][k]): livecmd.add((m, k))
    blockers = collections.Counter(); blocker_samples = collections.defaultdict(list)
    for key in keyof:
        if key in deleted: continue
        if key in force: blockers['namespace-preservation'] += 1; continue
        m, k = key
        ks, priv = keyof[key]
        why = None; via_cand = None
        for kk in ks:
            for (om, ok_) in occ.get(kk, ()):
                if (om, ok_) == key or om in dropped: continue
                if (om, ok_) in keyof and (om, ok_) in deleted: continue
                if om != m:
                    if priv and (om, ok_) not in openpriv: continue
                    if not priv and not ((DOWN[m] >> mid[om]) & 1): continue
                if (om, ok_) in keyof:
                    if via_cand is None: via_cand = (kk, om, ok_)
                    continue
                if ok_ < 0: why = 'other-owner-edit'
                elif (om, ok_) in livecmd: why = 'named-in-live-decl'
                else:
                    c2 = M[om]['cmds'][ok_]
                    if c2.kind in DECL_KINDS_ALL: why = 'named-in-dead-noncandidate(' + ('attr' if c2.attrs else c2.kind) + ')'
                    else: why = 'named-in-' + str(c2.kind)
                break
            if why: break
        if why is None and via_cand is not None:
            why = 'transitive(named-in-kept-dead-candidate)'; kk, om, ok_ = via_cand
        blockers[why or 'unknown'] += 1
        if why and len(blocker_samples[why]) < 60 and hash(key) % 7 == 0:
            line = next((M[om]['lines'][j] for j in range(M[om]['cmds'][ok_].text_start, M[om]['cmds'][ok_].end)
                         if kk in leansrc.tokens(M[om]['code'][j])), '') if ok_ >= 0 else '(other edit)'
            blocker_samples[why].append([' '.join(M[m]['rnames'][k]), kk, om, line.strip()[:200]])
    print('kept dead candidates by first blocker:', dict(blockers.most_common()), file=sys.stderr, flush=True)

    rep = collections.Counter()
    unbuilt_lines = sum(len(open(p, encoding='utf-8').read().split('\n')) for p in unbuilt_dropped.values())
    rep['unbuilt_modules_dropped'] = len(unbuilt_dropped)
    rep['lines_in_unbuilt_dropped'] = unbuilt_lines
    lines_before = sum(len(info['lines']) for info in M.values()) + unbuilt_lines

    # Exported imports of a dropped module `x` (when `x` is a `module` file, only `public import`s are exported to `module` callers;
    # when `x` is non-`module`, all its plain/public imports are exported). Note `empty_modules` already ensured that if any
    # non-`module` file reaches a `module` file `x`, `x` has only `public import`s, so both modes agree!
    flat_cache = {}
    def flat_exported(x):
        if x in flat_cache: return flat_cache[x]
        res = []
        is_x_mod = M[x]['is_module']
        for (_, vis, _, ml) in hdr_imp_lines[x]:
            if is_x_mod and vis != 'public':
                continue
            for y in ml:
                if y in dropped:
                    res.extend(flat_exported(y))
                else:
                    res.append(y)
        flat_cache[x] = res
        return res

    out_lines_total = 0
    edits = []
    if not a.dry_run:
        if os.path.exists(a.out): shutil.rmtree(a.out)
        shutil.copytree(a.src, a.out, symlinks=True, ignore=shutil.ignore_patterns('.lake', 'src'))
    outsrc = os.path.join(a.out, 'src') if os.path.isdir(os.path.join(a.src, 'src')) else a.out
    for um, up in sorted(unbuilt_dropped.items()):
        if not a.dry_run:
            dst = os.path.join(outsrc, os.path.relpath(up, srcdir))
            if os.path.exists(dst): os.unlink(dst)
        edits.append('%s\t0\t0\tdeletefile\tP01\t' % um)
    for m, info in M.items():
        if m in dropped:
            rep['modules_dropped'] += 1; rep['lines_in_dropped_modules'] += len(info['lines'])
            if not a.dry_run:
                dst = os.path.join(outsrc, os.path.relpath(mods[m], srcdir))
                if os.path.exists(dst): os.unlink(dst)
            edits.append('%s\t0\t0\tdeletefile\tP01\t' % m)
            continue
        lines = info['lines']; cmds = info['cmds']
        kill = [False] * len(lines)
        for k, c in enumerate(cmds):
            if (m, k) in deleted:
                e = c.end + 1 if c.end < len(lines) and not lines[c.end].strip() else c.end
                for j in range(c.start, e): kill[j] = True
                edits.append('%s\t%d\t%d\tdelete\tP01\t' % (m, c.start + 1, e))
                rep['decls_deleted_' + str(c.kind)] += 1
                rep['lines_deleted_decls'] += e - c.start
        for jj in barrel_killed_lines.get(m, ()):
            kill[jj] = True
            edits.append('%s\t%d\t%d\tdelete\tP01\t' % (m, jj + 1, jj + 1))
            rep['barrel_imports_deleted'] += 1

        # In-place import flattening (keeps `module` header and comments before imports intact, preserves `public import`)
        imp_map = {}
        imp_changed = False
        for (jj, vis, is_spec, ml) in hdr_imp_lines[m]:
            if not is_spec and len(ml) == 1 and ml[0] in dropped:
                imp_changed = True
            imp_map[jj] = (vis, is_spec, ml)
        if imp_changed:
            rep['modules_import_flattened'] += 1
        seen_pub = set()
        seen_any = set()
        out = []
        for j, l in enumerate(lines):
            if kill[j]: continue
            if imp_changed and j in imp_map:
                vis, is_spec, ml = imp_map[j]
                if not is_spec and len(ml) == 1:
                    x = ml[0]
                    targets_y = flat_exported(x) if x in dropped else [x]
                    prefix = 'public import ' if vis == 'public' else ('private import ' if vis == 'private' else 'import ')
                    rep_lines = []
                    for y in targets_y:
                        if vis == 'public':
                            if y not in seen_pub:
                                seen_pub.add(y); seen_any.add(y); rep_lines.append(prefix + y)
                        else:
                            if y not in seen_any:
                                seen_any.add(y); rep_lines.append(prefix + y)
                    if x in dropped or rep_lines != [l]:
                        if rep_lines:
                            edits.append('%s\t%d\t%d\treplace\tP01\t%s' % (m, j + 1, j + 1, '\\n'.join(rep_lines)))
                        else:
                            edits.append('%s\t%d\t%d\tdelete\tP01\t' % (m, j + 1, j + 1))
                    out.extend(rep_lines)
                    continue
                else:
                    for y in ml:
                        seen_any.add(y)
                        if vis == 'public': seen_pub.add(y)
            out.append(l)

        res = []
        for l in out:
            if not l.strip() and res and not res[-1].strip(): continue
            res.append(l)
        out_lines_total += len(res)
        if not a.dry_run:
            dst = os.path.join(outsrc, os.path.relpath(mods[m], srcdir))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            with open(dst, 'w', encoding='utf-8') as fo:
                fo.write('\n'.join(res))
    rep['modules_before'] = len(M) + len(unbuilt_dropped); rep['modules_after'] = len(M) - len(dropped)
    rep['lines_before'] = lines_before; rep['lines_after'] = out_lines_total
    rep['decl_candidates_dead_safe_kind'] = len(keyof); rep['decls_deleted'] = len(deleted)
    allrep = {'report': dict(rep), 'stats': dict(stats), 'kept_dead_candidates_by_blocker': dict(blockers),
              'blocker_samples': dict(blocker_samples), 'seconds': round(time.time() - t0, 1)}
    print(json.dumps(allrep, indent=1, sort_keys=True))
    if a.report:
        with open(a.report, 'w') as fo:
            json.dump(allrep, fo, indent=1, sort_keys=True)
        with open(a.report + '.deleted.tsv', 'w') as fo:
            for (m, k) in sorted(deleted):
                c = M[m]['cmds'][k]
                fo.write('%s\t%s\t%s\t%d\t%d\n' % (m, c.kind, ' '.join(M[m]['rnames'][k]) or '-', c.start + 1, c.end))
        with open(a.report + '.decls.tsv', 'w') as fo:
            fo.write('#module\tstart\tend\tkind\tlive\tdeleted\tnames\n')
            for m, info in M.items():
                for k, c in enumerate(info['cmds']):
                    if c.kind not in DECL_KINDS_ALL: continue
                    fo.write('%s\t%d\t%d\t%s\t%d\t%d\t%s\n' % (m, c.start + 1, c.end, c.kind, (m, k) in livecmd,
                             (m, k) in deleted or m in dropped, ' '.join(info['rnames'][k]) or '-'))
        with open(a.report + '.edits.tsv', 'w') as fo:
            fo.write(''.join(e + '\n' for e in edits))
        with open(a.report + '.dropped.txt', 'w') as fo:
            fo.write(''.join(x + '\n' for x in sorted(dropped)))


DECL_KINDS_ALL = leansrc.DECL_WORDS

if __name__ == '__main__':
    main()
