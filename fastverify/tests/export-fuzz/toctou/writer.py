#!/usr/bin/env python3
"""writer.py FILE AB.json SECONDS : rewrite the target line of FILE in place, alternating A and B, restoring the original
mtime after every write (same inode, same size, same mtime: the stamp check of check-sound.sh cannot see it)."""
import json, os, sys, time
f, abj, secs = sys.argv[1], sys.argv[2], float(sys.argv[3])
ab = json.load(open(abj)); off = ab['offset']; A = ab['A'].encode(); B = ab['B'].encode()
st = os.stat(f); t_end = time.time() + secs; k = 0
fd = os.open(f, os.O_WRONLY)
while time.time() < t_end:
    os.pwrite(fd, A if k % 2 == 0 else B, off); os.utime(f, ns=(st.st_atime_ns, st.st_mtime_ns)); k += 1
    time.sleep(0.0005)
os.pwrite(fd, A, off); os.utime(f, ns=(st.st_atime_ns, st.st_mtime_ns)); os.close(fd)
print('writes', k)
