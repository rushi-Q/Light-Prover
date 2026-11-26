#!/usr/bin/env python3
"""dropempty.py — drop EMPTY modules of a Lean 4 project and flatten their importers' headers in place
(with module-system support)."""
import os, sys, re, json, shutil, argparse, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import normalize as NZ

SCOPE_ONLY = re.compile(r'^(open\b(?!.*\bin\s*$)|namespace\b|(?:public\s+)?(?:noncomputable\s+)?section\b|end\b|end$|'
                        r'set_option\b(?!.*\bin\s*$)|variable\b|universe\b|include\b|omit\b|attribute\s*\[\s*local\b)')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:public|meta|private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|irreducible_def)\s+([^\s:({\[]+)')


def body_lines(lines, items, is_mod):
    if items:
        return lines[items[-1][0] + 1:]
    if is_mod:
        for i, l in enumerate(lines):
            if l.strip() == 'module':
                return lines[i + 1:]
    return lines


def is_empty(body):
    depth = 0
    for l in body:
        s = l.strip()
        if depth or s.startswith('/-'):
            depth += s.count('/-') - s.count('-/')
            if depth < 0: depth = 0
            if not s.startswith('/-') or depth: continue
            continue
        if not s or s.startswith('--'): continue
        if l[0].isspace(): return False
        if not SCOPE_ONLY.match(s): return False
    return True


def prefixes(n):
    p = n.split('.'); return ['.'.join(p[:i]) for i in range(1, len(p) + 1)]


def registered(lines):
    out = set(); stack = []
    for l in lines:
        if not l or l[0].isspace(): continue
        s = l.strip()
        if s.startswith('namespace '):
            n = s.split()[1]; full = '.'.join([x for x in stack if x] + [n]); stack.append(n)
            out.update(prefixes(full)); continue
        if re.match(r'^(public\s+)?(noncomputable\s+)?section\b', s): stack.append(None); continue
        if s == 'end' or s.startswith('end '):
            if stack: stack.pop()
            continue
        m = DECL.match(s)
        if m:
            name = m.group(1)
            ns = [x for x in stack if x]
            if name.startswith('_root_.'): full = name[len('_root_.'):]
            else: full = '.'.join(ns + [name])
            out.update(prefixes(full)[:-1])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('project'); ap.add_argument('out')
    ap.add_argument('--srcdir', default='src'); ap.add_argument('--protect', default='')
    ap.add_argument('--plan-only', action='store_true')
    a = ap.parse_args()
    src = NZ.resolve_srcdir(a.project, a.srcdir)
    files = {}
    for root, dirs, fs in os.walk(src):
        dirs[:] = [d for d in dirs if d not in ('.lake', '.git')]
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(root, f); files[os.path.relpath(p, src)[:-5].replace('/', '.')] = p
    texts = {m: open(p, encoding='utf-8').read().split('\n') for m, p in files.items()}
    hdr = {}; special_imported = set()
    for m, lines in texts.items():
        h = NZ.parse_header_ext(lines)
        if h is None:
            continue
        hdr[m] = h
        for (_, vis, c) in h[1]:
            if vis.startswith('special:') or vis == 'private':
                special_imported.add(c)
    # Re-exported project edges for namespace inheritance check
    reexp_G = {}
    all_G = {}
    for m, (is_m, items) in hdr.items():
        all_G[m] = [c for (_, _, c) in items]
        reexp_G[m] = [c for (_, vis, c) in items if (vis == 'public' if is_m else vis == 'plain')]
    protect = set(x for x in a.protect.split(',') if x)
    lf = os.path.join(a.project, 'lakefile.toml')
    if os.path.exists(lf):
        t = open(lf, encoding='utf-8').read()
        for blk in re.split(r'(?m)^(?=\[\[)', t):
            if blk.startswith('[[lean_lib]]') or blk.startswith('[[lean_exe]]'):
                nm = re.search(r'^name\s*=\s*"([^"]*)"', blk, re.M)
                rts = re.search(r'^roots\s*=\s*\[(.*?)\]', blk, re.M | re.S)
                if rts: protect |= set(NZ._toml_list(rts.group(1)))
                elif nm: protect.add(nm.group(1))
    reg = {m: registered(t) for m, t in texts.items()}
    idx, clo = NZ.closures(reexp_G)
    # Also compute reverse reachability to detect if a non-`module` file reaches a `module` file
    rev_G = collections.defaultdict(list)
    for m, L in all_G.items():
        for c in L:
            if c in hdr: rev_G[c].append(m)
    rev_idx, rev_clo = NZ.closures(rev_G)
    nonmod_bits = 0
    for m, (is_m, _) in hdr.items():
        if not is_m and m in rev_idx:
            nonmod_bits |= (1 << rev_idx[m])

    holders = collections.defaultdict(int)
    for m, ns in reg.items():
        if m in idx:
            b = 1 << idx[m]
            for n in ns: holders[n] |= b
    why = collections.Counter(); drop = set()
    for m, (is_m, items) in hdr.items():
        if m in protect or m in special_imported: continue
        if any(vis.startswith('special:') or vis == 'private' for (_, vis, _) in items): continue
        if is_m and (rev_clo.get(m, 0) & nonmod_bits) and any(vis != 'public' for (_, vis, _) in items):
            continue
        body = body_lines(texts[m], items, is_m)
        if not is_empty(body): continue
        own = set(); stack = []
        for l in body:
            s = l.strip()
            if s.startswith('namespace '):
                n = s.split()[1]; full = '.'.join([x for x in stack if x] + [n]); stack.append(n); own.update(prefixes(full))
            elif re.match(r'^(public\s+)?(noncomputable\s+)?section\b', s): stack.append('')
            elif (s == 'end' or s.startswith('end ')) and stack: stack.pop()
        c = clo.get(m, 0)
        if all(holders.get(n, 0) & c for n in own): drop.add(m)
        else: why['empty but registers a namespace not registered below it'] += 1

    memo = {}
    def expand(x):
        if x not in drop: return [x]
        if x in memo: return memo[x]
        out = []
        for y in reexp_G[x]: out.extend(expand(y))
        memo[x] = out; return out

    changed = {}
    for m, (_, items) in hdr.items():
        if m in drop: continue
        if any(c in drop for (_, _, c) in items):
            changed[m] = True
    summary = {'modules_before': len(texts), 'empty_dropped': len(drop), 'importers_flattened': len(changed),
               'modules_after': len(texts) - len(drop), 'kept_empty': dict(why)}
    if not a.plan_only:
        if os.path.exists(a.out): sys.exit(f'dropempty: {a.out} exists')
        shutil.copytree(a.project, a.out, symlinks=True, ignore=shutil.ignore_patterns('.lake', '.git'))
        osrc = NZ.resolve_srcdir(a.out, a.srcdir)
        for m in drop: os.unlink(os.path.join(osrc, m.replace('.', '/') + '.lean'))
        for m in changed:
            lines = texts[m]; pos = {i: (vis, c) for (i, vis, c) in hdr[m][1]}; out = []
            for i, l in enumerate(lines):
                if i in pos and pos[i][1] in drop:
                    vis, c = pos[i]
                    pfx = 'public import ' if vis == 'public' else 'import '
                    out.extend(pfx + y for y in expand(c))
                else:
                    out.append(l)
            q = os.path.join(osrc, m.replace('.', '/') + '.lean'); os.unlink(q)
            with open(q, 'w', encoding='utf-8') as f: f.write('\n'.join(out))
        for root, dirs, fs in os.walk(osrc, topdown=False):
            if not os.listdir(root) and root != osrc: os.rmdir(root)
        with open(os.path.join(a.out, '.dropempty.txt'), 'w') as f: f.write('\n'.join(sorted(drop)) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
