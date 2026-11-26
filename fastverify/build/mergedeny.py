#!/usr/bin/env python3
"""mergedeny.py LOGDIR... > merge-deny.txt   (S02; untrusted helper for the B3 'merge' item, sound preset)

Reads LOGDIR/sched.out (or sched.merged.out, the merged pass of a run that fell back to an unmerged rebuild) and
LOGDIR/merge/groups.json of one or more measured runs and prints, for every merged group whose merged lean process
FAILED, the group's sink and the member in which the first error was reported (error position -> the member section of
the merged source, via its '-- merged from M' marker). Failures of single modules are ignored. The list is the input of
mergeplan.py --deny (build/hints/merge-deny.txt): those groups are dissolved in later runs of the same project.
"""
import bisect, json, os, sys


def failing(logdir):
    gp = os.path.join(logdir, 'merge', 'groups.json')
    if not os.path.exists(gp):
        return
    groups = json.load(open(gp))
    seen = set()
    for fn in ('sched.merged.out', 'sched.out'):
        p = os.path.join(logdir, fn)
        if not os.path.exists(p):
            continue
        for line in open(p):
            if not line.startswith('{'):
                continue
            r = json.loads(line)
            m = r.get('module')
            if r.get('event') != 'module' or r.get('rc') == 0 or m in seen or len(groups.get(m, ())) < 2:
                continue
            seen.add(m)
            who = None
            for x in (r.get('stdout_head') or '').split('\n'):
                try:
                    e = json.loads(x)
                except ValueError:
                    continue
                if e.get('severity') != 'error':
                    continue
                try:
                    marks = [(i, t.split()[-1]) for i, t in enumerate(open(e['fileName']), 1)
                             if t.startswith('-- merged from ')]
                    k = bisect.bisect_right([i for i, _ in marks], e['pos']['line']) - 1
                    who = marks[k][1] if k >= 0 else None
                except (OSError, KeyError, TypeError):
                    who = None
                break
            yield m, who, os.path.basename(p)


def main():
    if len(sys.argv) < 2:
        print(__doc__); return 2
    out = {}
    for d in sys.argv[1:]:
        for sink, who, src in failing(d):
            out.setdefault(sink, f'# failed merged group (sink) in {d}/{src}')
            if who and who != sink:
                out.setdefault(who, f'# first error of the failed merged group {sink}')
    for n in sorted(out):
        print(f'{n}  {out[n]}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
