#!/usr/bin/python3 -I
"""fixlake.py PROJECT  - drop lakefile.toml library/exe targets, globs, and roots that match no module any more.

After closure pruning a library directory, secondary library root, or auxiliary executable/test target (e.g. SymCC in
Cedar, CleanTests in Clean, CslibTests/checkInitImports in Cslib, axiomsweep/AxiomSweepTestFixtures in ArkLib) can be
removed; `lake build` fails on missing roots/globs/testDriver. Removes unmatched globs/roots; any [[lean_lib]] or
[[lean_exe]] left without a surviving root/glob is removed together with its defaultTargets / testDriver entry.
"""
import os, re, sys


def has_modules(src, glob):
    if glob.endswith('.+') or glob.endswith('.*'):
        d = os.path.join(src, *glob[:-2].split('.'))
        if not os.path.isdir(d):
            return False
        for _, _, fn in os.walk(d):
            if any(f.endswith('.lean') for f in fn):
                return True
        return False
    return os.path.isfile(os.path.join(src, *glob.split('.')) + '.lean')


def main():
    proj = sys.argv[1]
    lf = os.path.join(proj, 'lakefile.toml')
    if not os.path.exists(lf):
        return
    text = open(lf, encoding='utf-8').read()
    blocks = re.split(r'(?m)^(?=\[\[)', text)
    head, rest = blocks[0], blocks[1:]
    m = re.search(r'^srcDir\s*=\s*"([^"]*)"', head, re.M)
    pkg_src = os.path.join(proj, m.group(1) if m else '.')
    removed = []
    out = []
    for b in rest:
        bm = re.search(r'^srcDir\s*=\s*"([^"]*)"', b, re.M)
        b_src = os.path.join(proj, bm.group(1)) if bm else pkg_src
        if b.startswith('[[lean_lib]]'):
            nm_m = re.search(r'^name\s*=\s*"([^"]*)"', b, re.M)
            name = nm_m.group(1) if nm_m else ''
            g = re.search(r'^globs\s*=\s*\[(.*?)\]', b, re.M | re.S)
            r = re.search(r'^roots\s*=\s*\[(.*?)\]', b, re.M | re.S)
            if g:
                gl = re.findall(r'"([^"]*)"', g.group(1))
                keep = [x for x in gl if has_modules(b_src, x)]
                if not keep:
                    removed.append(name); continue
                if keep != gl:
                    b = b[:g.start()] + 'globs = [' + ', '.join('"%s"' % x for x in keep) + ']' + b[g.end():]
                    print('globs', name, len(gl), '->', len(keep))
            elif r:
                rl = re.findall(r'"([^"]*)"', r.group(1))
                keep = [x for x in rl if has_modules(b_src, x) or has_modules(b_src, x + '.+')]
                if not keep:
                    removed.append(name); continue
                if keep != rl:
                    b = b[:r.start()] + 'roots = [' + ', '.join('"%s"' % x for x in keep) + ']' + b[r.end():]
                    print('roots', name, len(rl), '->', len(keep))
            elif name:
                if not has_modules(b_src, name) and not has_modules(b_src, name + '.+'):
                    removed.append(name); continue
        elif b.startswith('[[lean_exe]]'):
            nm_m = re.search(r'^name\s*=\s*"([^"]*)"', b, re.M)
            name = nm_m.group(1) if nm_m else ''
            rt_m = re.search(r'^root\s*=\s*"([^"]*)"', b, re.M)
            root = rt_m.group(1) if rt_m else name
            if root and not has_modules(b_src, root):
                removed.append(name); continue
        out.append(b)
    if removed:
        def fix_dt(mm):
            items = [x for x in re.findall(r'"([^"]*)"', mm.group(1)) if x not in removed]
            return 'defaultTargets = [' + ', '.join('"%s"' % x for x in items) + ']'
        head = re.sub(r'^defaultTargets\s*=\s*\[(.*?)\]', fix_dt, head, flags=re.M | re.S)
        td_m = re.search(r'^testDriver\s*=\s*"([^"]*)"\s*\n?', head, re.M)
        if td_m and td_m.group(1) in removed:
            head = head[:td_m.start()] + head[td_m.end():]
        print('removed targets', removed)
    new = head + ''.join(out)
    if new != text:
        st = os.stat(lf)
        open(lf, 'w', encoding='utf-8').write(new)
        os.utime(lf, (st.st_atime, st.st_mtime))


if __name__ == '__main__':
    main()
