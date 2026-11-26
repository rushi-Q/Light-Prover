#!/usr/bin/env python3
"""chainmerge.py — merge single-importer chains of a Lean 4 project into one file each
(with module-system support)."""
import os, sys, re, gzip, json, shutil, argparse, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import normalize as NZ

SCOPE_OPEN = re.compile(r'^(?:public\s+)?(?:noncomputable\s+)?section\b\s*(\S*)')


def load_costs(path):
    if not path:
        return {}
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt', encoding='utf-8') as f:
        raw = json.load(f)
    return {k: float(v) for k, v in raw.items() if isinstance(v, (int, float)) and not isinstance(v, bool)}


def split_chain_by_cost(chain, max_group, costs, max_cost, default_cost):
    """Split an ordered single-importer chain [m_0, ..., m_r] into contiguous valid merge segments (>=2)
    respecting both max_group and max_cost (greedy from leaf m_0 to root m_r)."""
    if max_cost is None and len(chain) <= max_group:
        return [chain]
    segs = []
    cur = []
    cur_cost = 0.0
    for m in chain:
        c = costs.get(m, default_cost) if max_cost is not None else 0.0
        if max_cost is not None and c > max_cost:
            if len(cur) >= 2:
                segs.append(cur)
            cur = []
            cur_cost = 0.0
            continue
        if cur and (len(cur) >= max_group or (max_cost is not None and cur_cost + c > max_cost)):
            if len(cur) >= 2:
                segs.append(cur)
            cur = [m]
            cur_cost = c
        else:
            cur.append(m)
            cur_cost += c
    if len(cur) >= 2:
        segs.append(cur)
    return segs


def body_and_scopes(lines, hdr_last):
    body = lines[hdr_last + 1:]
    stack = []
    for l in body:
        if not l or l[0].isspace(): continue
        if l.startswith('namespace '):
            for comp in l.split()[1].split('.'):
                stack.append(('ns', comp))
            continue
        m = SCOPE_OPEN.match(l)
        if m and not l.startswith('section_'):
            nm = m.group(1)
            if nm:
                for comp in nm.split('.'):
                    stack.append(('sec', comp))
            else:
                stack.append(('sec', ''))
            continue
        if l == 'mutual' or l.startswith('mutual '):
            stack.append(('mutual', '')); continue
        if l == 'end' or l.startswith('end '):
            parts = l.split()
            nclose = len(parts[1].split('.')) if len(parts) > 1 else 1
            for _ in range(nclose):
                if stack: stack.pop()
                else: return body, None
    return body, stack


def closing(stack):
    out = []
    for kind, name in reversed(stack):
        if kind == 'mutual': return None
        out.append(('end ' + name) if name else 'end')
    return out


def hdr_last_idx(lines, is_m, items):
    if items:
        return items[-1][0]
    if is_m:
        for i, l in enumerate(lines):
            if l.strip() == 'module': return i
    return -1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('project'); ap.add_argument('out')
    ap.add_argument('--srcdir', default='src'); ap.add_argument('--packages', default=None)
    ap.add_argument('--toolchain-src', default=None); ap.add_argument('--deny', default=None)
    ap.add_argument('--max-group', type=int, default=1000); ap.add_argument('--plan-only', action='store_true')
    ap.add_argument('--same-dir', action='store_true',
                    help='only merge single-importer chains within the same topic directory (preserves directory layout 100%%)')
    ap.add_argument('--costs', default=None,
                    help='JSON or .json.gz {module: seconds} build-cost hints (e.g. rh-build-costs.json.gz)')
    ap.add_argument('--max-cost', type=float, default=None,
                    help='split single-importer chains so no merged file exceeds max-cost seconds (e.g. 30.0)')
    ap.add_argument('--default-cost', type=float, default=2.5,
                    help='fallback module cost (seconds) when --max-cost is set and a module is absent from --costs')
    a = ap.parse_args()
    costs = load_costs(a.costs) if a.max_cost is not None else {}
    src = NZ.resolve_srcdir(a.project, a.srcdir)
    files = {}
    for root, dirs, fs in os.walk(src):
        dirs[:] = [d for d in dirs if d not in ('.lake', '.git')]
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(root, f); files[os.path.relpath(p, src)[:-5].replace('/', '.')] = p
    texts = {m: open(p, encoding='utf-8').read().split('\n') for m, p in files.items()}
    hdr = {}; unsupported = set()
    for m, lines in texts.items():
        h = NZ.parse_header_ext(lines)
        if h is None:
            unsupported.add(m)
            continue
        hdr[m] = h
    G_ext = {m: (is_m, [(vis, c) for (_, vis, c) in items]) for m, (is_m, items) in hdr.items()}
    G_all = {m: [c for (_, c) in items] for m, (_, items) in G_ext.items()}
    pk = a.packages or os.path.join(a.project, '.lake', 'packages')
    roots = [os.path.join(pk, d) for d in sorted(os.listdir(pk))] if os.path.isdir(pk) else []
    if a.toolchain_src: roots.append(a.toolchain_src)
    E_ext = NZ.ext_graph_ext(roots)
    _, N_ext = NZ.reduce_imports_modsys(G_ext, E_ext)
    base, libs = NZ.lake_options(a.project)
    lakeroots = set()
    lf = os.path.join(a.project, 'lakefile.toml')
    if os.path.exists(lf):
        t = open(lf, encoding='utf-8').read()
        for blk in re.split(r'(?m)^(?=\[\[)', t):
            if blk.startswith('[[lean_lib]]') or blk.startswith('[[lean_exe]]'):
                nm = re.search(r'^name\s*=\s*"([^"]*)"', blk, re.M)
                rts = re.search(r'^roots\s*=\s*\[(.*?)\]', blk, re.M | re.S)
                if rts: lakeroots |= set(NZ._toml_list(rts.group(1)))
                elif nm: lakeroots.add(nm.group(1))
    deny = (set(open(a.deny).read().split()) if a.deny else set()) | unsupported
    importers = collections.defaultdict(list)
    for m, L in G_all.items():
        for c in L:
            if c in G_all: importers[c].append(m)
    parent = {}; why = collections.Counter()
    for A in G_all:
        if len(importers[A]) != 1: why['importers!=1'] += 1; continue
        B = importers[A][0]
        if A in lakeroots or A in deny or B in deny: why['root/deny'] += 1; continue
        is_mA, itemsA = G_ext[A]
        is_mB, _ = G_ext[B]
        if is_mA != is_mB: why['module-mode mismatch'] += 1; continue
        if is_mA:
            # In `module` files, declarations are private by default unless in `public section`; wrapping A in `section`
            # could change default visibility if `public section` was used across files -> skip `module` files in G1*
            why['module-system file (skipped conservatively)'] += 1; continue
        if any(vis != 'plain' for (vis, _) in itemsA): why['special import'] += 1; continue
        if N_ext[B][1] != [('plain', A)]: why['importer header != [A]'] += 1; continue
        if NZ.lib_base(A, base, libs) != NZ.lib_base(B, base, libs): why['different lib options'] += 1; continue
        if a.same_dir and (A.rsplit('.', 1)[0] if '.' in A else '') != (B.rsplit('.', 1)[0] if '.' in B else ''):
            why['cross-topic dir (--same-dir)'] += 1; continue
        parent[A] = B

    def root(m):
        while m in parent: m = parent[m]
        return m

    groups = collections.defaultdict(list)
    for m in G_all: groups[root(m)].append(m)
    merged = {}; refused = collections.Counter(); cost_splits = 0
    for k, mem in groups.items():
        if len(mem) == 1: continue
        chain = [k]
        while True:
            prev = [x for x in G_all[chain[0]] if parent.get(x) == chain[0]]
            if not prev: break
            chain.insert(0, prev[0])
        if len(chain) != len(mem): refused['shape'] += 1; continue
        if a.max_cost is None and len(chain) > a.max_group: refused['shape'] += 1; continue
        segs = split_chain_by_cost(chain, a.max_group, costs, a.max_cost, a.default_cost)
        if a.max_cost is not None and len(segs) != 1:
            cost_splits += 1
        for seg in segs:
            seg_k = seg[-1]
            out_lines = []; ok = True
            first = seg[0]
            hl0 = hdr_last_idx(texts[first], hdr[first][0], hdr[first][1])
            out_lines.extend(texts[first][:hl0 + 1] if hl0 >= 0 else [])
            for x in seg[:-1]:
                hl = hdr_last_idx(texts[x], hdr[x][0], hdr[x][1])
                body, stack = body_and_scopes(texts[x], hl)
                cl = closing(stack) if stack is not None else None
                if cl is None: ok = False; refused['unbalanced scopes'] += 1; break
                while body and body[-1] == '': body.pop()
                out_lines.append(f'-- (merged) module {x}'); out_lines.append('section')
                out_lines.extend(body); out_lines.extend(cl); out_lines.append('end')
            if not ok: continue
            hlk = hdr_last_idx(texts[seg_k], hdr[seg_k][0], hdr[seg_k][1])
            out_lines.extend(texts[seg_k][hlk + 1:])
            merged[seg_k] = (seg, out_lines)
    members = {x: k for k, (chain, _) in merged.items() for x in chain[:-1]}
    # If chain splitting left a redundant `import X` (with X in members) inside an un-normalized later segment's header,
    # rewrite `import X -> import members[X]` and deduplicate header imports so un-normalized trees stay 100% buildable.
    imp_re = re.compile(r'^(\s*import\s+)([^\s]+)(.*)$')
    rewritten_plain = {}
    if members and a.max_cost is not None:
        for m in list(texts):
            if m in members:
                continue
            cur_lines = merged[m][1] if m in merged else texts[m]
            h = NZ.parse_header_ext(cur_lines)
            if not h or not h[1]:
                continue
            idx_set = {idx for idx, _, _ in h[1]}
            seen_imp = set()
            changed = False
            new_l = []
            for idx, ln in enumerate(cur_lines):
                if idx not in idx_set:
                    new_l.append(ln); continue
                mo = imp_re.match(ln)
                if not mo:
                    new_l.append(ln); continue
                pfx, tgt, sfx = mo.group(1), mo.group(2), mo.group(3)
                ntgt = members.get(tgt, tgt)
                if ntgt != tgt:
                    changed = True
                if ntgt in seen_imp:
                    changed = True; continue
                seen_imp.add(ntgt)
                new_l.append(f'{pfx}{ntgt}{sfx}')
            if changed:
                if m in merged:
                    merged[m] = (merged[m][0], new_l)
                else:
                    rewritten_plain[m] = new_l
    lines_before = sum(len(t) for t in texts.values())
    summary = {'modules_before': len(texts), 'pairs': len(parent), 'groups_merged': len(merged),
               'members_removed': len(members), 'modules_after': len(texts) - len(members), 'not_merged_reasons': dict(why),
               'refused_groups': dict(refused)}
    if a.max_cost is not None:
        summary['cost_split_chains'] = cost_splits
    if not a.plan_only:
        if os.path.exists(a.out): sys.exit(f'chainmerge: {a.out} exists')
        shutil.copytree(a.project, a.out, symlinks=True, ignore=shutil.ignore_patterns('.lake', '.git'))
        osrc = NZ.resolve_srcdir(a.out, a.srcdir)
        for x in members: os.unlink(os.path.join(osrc, x.replace('.', '/') + '.lean'))
        for k, (chain, out_lines) in merged.items():
            with open(os.path.join(osrc, k.replace('.', '/') + '.lean'), 'w', encoding='utf-8') as f: f.write('\n'.join(out_lines))
        for m, out_lines in rewritten_plain.items():
            with open(os.path.join(osrc, m.replace('.', '/') + '.lean'), 'w', encoding='utf-8') as f: f.write('\n'.join(out_lines))
        with open(os.path.join(a.out, '.chainmerge.tsv'), 'w') as f:
            for x, k in sorted(members.items()): f.write(f'{x}\t{k}\n')
        for root_d, dirs, fs in os.walk(osrc, topdown=False):
            if not os.listdir(root_d) and root_d != osrc: os.rmdir(root_d)
        lines_after = sum(len(out_lines) for (_, out_lines) in merged.values())
        lines_after += sum(len(rewritten_plain.get(m, texts[m])) for m in texts if m not in members and m not in merged)
        summary['lines_before'] = lines_before; summary['lines_after'] = lines_after
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
