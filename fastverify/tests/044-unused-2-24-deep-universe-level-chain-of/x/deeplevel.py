#!/usr/bin/env python3
"""deeplevel.py BASE.export N OUT.export : append N unused level records forming a succ chain (depth N) after the base's
last level record (indices dense). Official Lean's Level.mkData panics ('universe level depth is too big') at depth > 2^24-1."""
import sys
base = open(sys.argv[1], encoding='utf-8').read().rstrip('\n').split('\n'); N = int(sys.argv[2])
lv = [i for i, l in enumerate(base) if l.startswith('{"il":')]
last = lv[-1]; maxl = max(int(base[i][6:base[i].index(',')]) for i in lv)
with open(sys.argv[3], 'w', encoding='utf-8') as g:
    g.write('\n'.join(base[:last + 1]) + '\n')
    prev = 0
    buf = []
    for k in range(N):
        i = maxl + 1 + k
        buf.append(f'{{"il":{i},"succ":{prev}}}')
        prev = i
        if len(buf) >= 100000: g.write('\n'.join(buf) + '\n'); buf = []
    if buf: g.write('\n'.join(buf) + '\n')
    g.write('\n'.join(base[last + 1:]) + '\n')
