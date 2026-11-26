#!/usr/bin/env python3
"""collapse.py SRC OUT [--pairs RULE] [--deny FILE] [--order host|proof] [--unify] [--comments] [--pairs-out FILE] [--limit N] [--stats FILE]

ALIAS-LAYER COLLAPSE: inline every "proof module" M into the ONE module H that imports it
(its statement card), delete M, and rewrite H's import list (M replaced in place by M's own imports). Source-level
module re-layout; the declarations of M and H are emitted verbatim, in the same order Lean saw them before (M first,
then H). Nothing is elaborated here (pure text); the result is judged only by the build + the trusted check.

RULE (--pairs): 'flt' = AI-FLT layout: M = P2M.Sol.S_X, H = Theorems.Thm_X (every S_X is imported by its card only);
'auto' = every project module with exactly one importer inside the project that is a card (= H's body is a short
alias statement) - see --max-host-lines. Pairs whose M is imported by any other module are skipped (never inlined).

--deny FILE: proof modules (first column, '#' comments) that are NOT inlined (collide.py's static name-collision list,
or modules whose merged build failed).
Merged H = (--order host, default) imports(H) with M replaced in place by imports(M) (first occurrence kept: the DFS
import order seen by H's own declarations is unchanged), or (--order proof) imports(M) first, then H's other imports
(the order seen by M's declarations is unchanged) + `section` M-body `<closers>` `end` + H-body. <closers> close every scope M left open
(Lean 4 semantics: `namespace A.B` / `section A.B` open one scope per name component, `end A.B` closes as many).

--unify (G2, statement unification; FLT rule only): where the card is ONE alias theorem `theorem X <stmt> := by
p2m_exact_reverting @P2MW.S_X.solution` and M's `theorem solution <stmt>` has the textually identical statement, the card
is dropped and M's `theorem solution` becomes `theorem _root_.X` (statement + proof stated once; the alias declaration
and the second statement disappear). The statement is then elaborated in M's context (M's erasure lists / opens) instead
of the card's: a difference can only make the build fail or change X's elaborated statement (the official targets are
compared with the challenge by the trusted check). Pairs not meeting the conditions are collapsed as above.
Why it cannot make a wrong proof pass: it only moves text; any change of meaning can only make the build fail or
produce different declarations, and the export is re-checked from scratch against the official challenge
(statement equality, axioms, both kernels). What CAN change (G1 'internal renaming'): private declarations of M get
H's module prefix (_private.<H>.0.* instead of _private.<M>.0.*); auxiliary declarations otherwise keep their names.
"""
import json, os, re, shutil, sys, collections

NS_RE = re.compile(r'^namespace\s+(\S+)\s*(?:--.*)?$')
SEC_RE = re.compile(r'^(?:noncomputable\s+)?section(?:\s+([^\s-]\S*))?\s*(?:--.*)?$')
END_RE = re.compile(r'^end(?:\s+([^\s-]\S*))?\s*(?:--.*)?$')
HDR_KW = ('import', 'public', 'meta', 'private', 'module', 'prelude')


def split_header(text):
    """(imports, lines, body_start) or None for module-system / prelude files."""
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
        if toks[0] in ('prelude', 'module'): return None
        body = i
        break
    return imps, lines, body


def open_scopes(lines):
    """Scopes left open at the end of the body (one entry per name component; '' = anonymous section).
    Column-0 commands only; block comments skipped. Returns None if unbalanced (more `end`s than scopes)."""
    stack, depth = [], 0
    for raw in lines:
        if depth:
            depth += raw.count('/-') - raw.count('-/')
            if depth < 0: depth = 0
            continue
        if raw.startswith('/-'):
            depth = max(0, raw.count('/-') - raw.count('-/'))
            continue
        if not raw or raw[0] in ' \t': continue
        m = NS_RE.match(raw)
        if m:
            stack.extend(m.group(1).split('.')); continue
        m = SEC_RE.match(raw)
        if m:
            stack.extend(m.group(1).split('.') if m.group(1) else ['']); continue
        m = END_RE.match(raw)
        if m:
            k = len(m.group(1).split('.')) if m.group(1) else 1
            if k > len(stack): return None
            del stack[len(stack) - k:]
    return stack


TH_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?theorem\s+(\S+)')
CARD_OK = ('import', 'attribute', 'p2m_hide', 'open', 'set_option', 'universe', 'theorem', ' ', '\t', '--', 'noncomputable section')


def stmt_of(lines, i, name_end):
    """statement text of the theorem starting at line i (from after its name up to the first ':='), whitespace-normalized"""
    buf, j = lines[i][name_end:], i
    while ':=' not in buf and j + 1 < len(lines):
        j += 1; buf += '\n' + lines[j]
    return ' '.join(buf.split(':=')[0].split())


def unify_plan(m, h, ml, mb, hl, hb):
    """(card name, index of M's solution line, prefix to replace) or None"""
    body = hl[hb:]
    ths = [(i, TH_RE.match(l)) for i, l in enumerate(body) if TH_RE.match(l)]
    if len(ths) != 1: return None
    i, mt = ths[0]
    x = mt.group(1)
    if x.startswith('P2M.Dup.') or '.{' in x or 'p2m_exact_reverting' not in '\n'.join(body[i:]): return None
    if any(l and not l.startswith(CARD_OK) for l in body[:i]): return None
    tail = '\n'.join(body[i:])
    if tail.count(':=') != 1 or not tail.rstrip().endswith('.solution'): return None
    if x.startswith('_root_.'): x = x[len('_root_.'):]
    sols = [k for k in range(mb, len(ml)) if re.match(r'^theorem (solution|_root_\.P2MW\.S_\S*\.solution)(\s|$)', ml[k])]
    if len(sols) != 1: return None
    k = sols[0]
    ms = re.match(r'^theorem (\S+)', ml[k])
    if stmt_of(ml, k, ms.end(1)) != stmt_of(body, i, mt.end(1)): return None
    # Static G2 safety guards (D19): avoid (a) renaming `solution` when `solution` is referenced
    # elsewhere in M (e.g. attribute/helper), and (b) recursive self-capture when short(x) occurs in M's body.
    if re.search(r'\bsolution\b', '\n'.join(ml[mb:k] + ml[k + 1:])): return None
    short = x.rsplit('.', 1)[-1]
    body_rhs = (ml[k].split(':=', 1)[1] if ':=' in ml[k] else '') + '\n' + '\n'.join(ml[k + 1:])
    if short and re.search(r'\b' + re.escape(short) + r'\b', body_rhs): return None
    return x, k, ms.group(0)


def modname(root, path):
    return os.path.relpath(path, root)[:-5].replace(os.sep, '.')


def main():
    a = sys.argv[1:]
    if len(a) < 2: print(__doc__); sys.exit(2)
    src, out = os.path.abspath(a[0]), os.path.abspath(a[1])
    opt = lambda k, d=None: a[a.index(k) + 1] if k in a else d
    rule, limit, stats_path = opt('--pairs', 'flt'), int(opt('--limit', '0')), opt('--stats')
    order = opt('--order', 'host')
    unify = '--unify' in a
    comments = '--comments' in a
    pairs_out = opt('--pairs-out')   # one line per inlined pair: M <TAB> H <TAB> unified|collapsed
    done = []   # marker comments in merged files (off by default: they would inflate comment metrics)
    deny = set()
    if opt('--deny'):
        for line in open(opt('--deny'), encoding='utf-8'):
            line = line.split('#', 1)[0].strip()
            if line: deny.add(line.split()[0])
    deny_unify = set()
    if opt('--deny-unify'):
        for line in open(opt('--deny-unify'), encoding='utf-8'):
            line = line.split('#', 1)[0].strip()
            if line: deny_unify.add(line.split()[0])
    if os.path.exists(out): print(f'refusing: {out} exists'); sys.exit(2)
    mods, paths = {}, {}
    for d, dirs, fs in os.walk(src):
        dirs[:] = [x for x in dirs if x not in ('.lake', '.git')]
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(d, f); m = modname(src, p); paths[m] = p
    importers = collections.defaultdict(set)
    heads = {}
    for m, p in paths.items():
        with open(p, encoding='utf-8') as fh: h = split_header(fh.read())
        heads[m] = h
        if h is None: continue
        for i in h[0]:
            if i in paths: importers[i].add(m)
    pairs = []
    if rule == 'flt':
        for m in sorted(paths):
            if not m.startswith('P2M.Sol.S_'): continue
            h = 'Theorems.Thm_' + m[len('P2M.Sol.S_'):]
            if h in paths and importers[m] == {h}: pairs.append((m, h))
    elif rule == 'auto':
        maxh = int(opt('--max-host-lines', '40'))
        for m in sorted(paths):
            imps = importers.get(m, set())
            if len(imps) != 1: continue
            h = next(iter(imps))
            hh = heads.get(h)
            if hh is None or heads.get(m) is None: continue
            if len(hh[1]) - hh[2] <= maxh: pairs.append((m, h))
        # a host may not itself be inlined in this pass (no chains)
        members = {m for m, _ in pairs}
        pairs = [(m, h) for m, h in pairs if h not in members]
    else:
        print('unknown --pairs rule'); sys.exit(2)
    ndeny = sum(1 for m, _ in pairs if m in deny)
    pairs = [(m, h) for m, h in pairs if m not in deny]
    if limit: pairs = pairs[:limit]
    # copy tree (hardlinks would share inodes with the read-only source: use real copies)
    shutil.copytree(src, out, ignore=shutil.ignore_patterns('.lake', '.git'))
    st = collections.Counter(); skipped = []
    for m, h in pairs:
        hm, hh = heads[m], heads[h]
        if hm is None or hh is None: skipped.append((m, 'module-system/prelude')); continue
        mi, ml, mb = hm; hi, hl, hb = hh
        scopes = open_scopes(ml[mb:])
        if scopes is None: skipped.append((m, 'unbalanced end')); continue
        # Static G2 guard (D19): if M declares `private ... _root_.<X>` with the same full name X as H's card theorem,
        # merging M into H produces `a private declaration '<X>' has already been declared` in Lean 4 -> skip collapse.
        h_ths = [TH_RE.match(l).group(1) for l in hl[hb:] if TH_RE.match(l)]
        if h_ths:
            mbody_chk = '\n'.join(ml[mb:])
            priv_clash = False
            for hx in h_ths:
                hx_clean = hx[len('_root_.'):] if hx.startswith('_root_.') else hx
                if re.search(r'(?m)^\s*private\b[^\n]*\b_root_\.' + re.escape(hx_clean) + r'\b', mbody_chk):
                    priv_clash = True; break
            if priv_clash:
                skipped.append((m, 'private-root-clash')); continue
        new_imps, seen = [], set()
        seq = [x for i in hi for x in (mi if i == m else [i])] if order == 'host' else mi + [i for i in hi if i != m]
        for j in seq:
            if j not in seen and j != m: seen.add(j); new_imps.append(j)
        closers = [(f'end {nm}' if nm else 'end') for nm in reversed(scopes)]
        up = unify_plan(m, h, ml, mb, hl, hb) if unify and rule == 'flt' and m not in deny_unify and h not in deny_unify else None
        if up:
            x, k, prefix = up
            ml2 = list(ml); ml2[k] = 'theorem _root_.' + x + ml2[k][len(prefix):]
            seqp = mi + [i for i in hi if i != m]
            imps2, seen2 = [], set()
            for j in seqp:
                if j not in seen2 and j != m: seen2.add(j); imps2.append(j)
            # Lean 4 does not register namespace `Ns` for `theorem _root_.Ns.foo` inside another namespace;
            # emit an empty `namespace Ns / end Ns` at root scope RIGHT AFTER IMPORTS (before M's body, so zero closers needed!).
            ns_reg = []
            if '.' in x:
                ns = x.rsplit('.', 1)[0]
                ns_reg = ['', f'namespace {ns}', f'end {ns}']
            txt = '\n'.join([f'import {i}' for i in imps2] + ns_reg + ([''] + ([f'-- statement and proof of {x} (card unified with {m})'] if comments else []))
                            + ml2[mb:]).rstrip('\n') + '\n'
            with open(os.path.join(out, os.path.relpath(paths[h], src)), 'w', encoding='utf-8') as fh: fh.write(txt)
            os.unlink(os.path.join(out, os.path.relpath(paths[m], src)))
            st['collapsed'] += 1; st['unified'] += 1; done.append((m, h, 'unified'))
            st['import_lines_before'] += len(hi) + len(mi); st['import_lines_after'] += len(imps2)
            continue
        mbody = '\n'.join(ml[mb:]).rstrip('\n')
        hbody = '\n'.join(hl[hb:]).rstrip('\n')
        txt = '\n'.join([f'import {i}' for i in new_imps] + [''] + ([f'-- proof (inlined from {m})'] if comments else []) + ['section', '', mbody, '']
                        + closers + ['end', ''] + (['-- statement card'] if comments else []) + [hbody, ''])
        with open(os.path.join(out, os.path.relpath(paths[h], src)), 'w', encoding='utf-8') as fh: fh.write(txt)
        os.unlink(os.path.join(out, os.path.relpath(paths[m], src)))
        st['collapsed'] += 1; done.append((m, h, 'collapsed'))
        st['closers'] += len(closers)
        st['import_lines_before'] += len(hi) + len(mi)
        st['import_lines_after'] += len(new_imps)
    res = {'rule': rule, 'order': order, 'unify': unify, 'unified': st['unified'], 'denied': ndeny, 'modules_before': len(paths), 'pairs': len(pairs), 'collapsed': st['collapsed'],
           'modules_after': len(paths) - st['collapsed'], 'skipped': len(skipped), 'skipped_sample': skipped[:20],
           'closers_emitted': st['closers'], 'import_lines_before': st['import_lines_before'],
           'import_lines_after': st['import_lines_after']}
    print(json.dumps(res, indent=1))
    if pairs_out:
        with open(pairs_out, 'w') as fh:
            for x in done: fh.write('\t'.join(x) + '\n')
    if stats_path:
        with open(stats_path, 'w') as fh: json.dump(res, fh, indent=1)


if __name__ == '__main__':
    main()
