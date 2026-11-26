#!/usr/bin/python3 -I
"""treestats.py PROJECT [--json OUT]  (module-system aware import counts)"""
import os, re, sys, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leansrc

IMP_RE = re.compile(r'^(?:public\s+|private\s+)?(?:meta\s+)?import\s')


def main():
    proj = sys.argv[1]
    src = os.path.join(proj, 'src') if os.path.isdir(os.path.join(proj, 'src')) else proj
    st = collections.Counter(); kinds = collections.Counter()
    for dp, dn, fn in os.walk(src):
        dn[:] = [d for d in dn if not d.startswith(".")]
        for f in fn:
            if not f.endswith('.lean'): continue
            t = open(os.path.join(dp, f), encoding='utf-8').read()
            lines = t.split('\n')
            st['modules'] += 1; st['lines'] += len(lines); st['bytes'] += len(t.encode('utf-8'))
            st['nonblank_lines'] += sum(1 for l in lines if l.strip())
            st['import_lines'] += sum(1 for l in lines if IMP_RE.match(l))
            cmds, _ = leansrc.split_commands(lines)
            for c in cmds:
                kinds[c.kind] += 1
    decl = sum(kinds[k] for k in ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class', 'inductive',
                                  'example', 'axiom', 'opaque'))
    out = dict(st); out['decl_commands'] = decl
    out['kinds'] = {k: v for k, v in kinds.most_common(25)}
    print(json.dumps(out))
    if len(sys.argv) > 3 and sys.argv[2] == '--json':
        json.dump(out, open(sys.argv[3], 'w'), indent=1)


if __name__ == '__main__':
    main()
