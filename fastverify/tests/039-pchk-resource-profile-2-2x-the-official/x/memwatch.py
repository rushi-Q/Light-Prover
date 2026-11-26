#!/usr/bin/env python3
"""memwatch.py -- CMD...: run CMD, sample the summed RSS of its whole process tree every 0.25 s.
Prints: exit code, wall time, peak total RSS (GB) and the per-command peak RSS at that moment and overall."""
import os, subprocess, sys, time
def tree(root):
    kids = {}
    for p in os.listdir('/proc'):
        if not p.isdigit(): continue
        try:
            with open(f'/proc/{p}/stat') as f: s = f.read()
            ppid = int(s[s.rfind(')')+2:].split()[1]); kids.setdefault(ppid, []).append(int(p))
        except Exception: pass
    out, st = [], [root]
    while st:
        x = st.pop(); out.append(x); st.extend(kids.get(x, []))
    return out
def rss(pid):
    try:
        with open(f'/proc/{pid}/status') as f:
            name = None; r = 0
            for l in f:
                if l.startswith('Name:'): name = l.split()[1]
                if l.startswith('VmRSS:'): r = int(l.split()[1])
            return name, r
    except Exception: return None, 0
cmd = sys.argv[sys.argv.index('--')+1:]
t0 = time.time(); p = subprocess.Popen(cmd)
peak, peak_at, per = 0, {}, {}
while p.poll() is None:
    tot, now = 0, {}
    for q in tree(p.pid):
        n, r = rss(q)
        if n: tot += r; now[n] = now.get(n, 0) + r; per[n] = max(per.get(n, 0), r)
    if tot > peak: peak, peak_at = tot, now
    time.sleep(0.25)
print(f"memwatch: exit {p.returncode}  wall {time.time()-t0:.1f} s  PEAK TOTAL RSS {peak/1e6:.2f} GB  at peak: " +
      ", ".join(f"{k} {v/1e6:.2f}" for k, v in sorted(peak_at.items(), key=lambda kv: -kv[1]) if v > 1e5) +
      "  | per-process max: " + ", ".join(f"{k} {v/1e6:.2f}" for k, v in sorted(per.items(), key=lambda kv: -kv[1]) if v > 1e5), file=sys.stderr)
sys.exit(p.returncode)
