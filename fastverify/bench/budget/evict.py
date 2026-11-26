#!/usr/bin/env python3
# evict.py DIR|FILE ... - drop the clean page-cache pages of the given files (posix_fadvise DONTNEED; no privileges needed,
# only files the caller may open; pages mapped by a running process stay). Used before "cold cache" rows of bench/budget so a
# cgroup's memory.peak charges the inputs' file pages to the measured scope.
import os, sys
n = b = 0
def one(p):
    global n, b
    try:
        fd = os.open(p, os.O_RDONLY)
    except OSError:
        return
    try:
        os.fsync(fd) if False else None
        os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED); n += 1; b += os.fstat(fd).st_size
    except OSError:
        pass
    finally:
        os.close(fd)
for a in sys.argv[1:]:
    if os.path.isdir(a):
        for d, _, fs in os.walk(a):
            for f in fs:
                p = os.path.join(d, f)
                if not os.path.islink(p): one(p)
    else:
        one(a)
print(f"evict: {n} files, {b/2**30:.2f} GB advised")
