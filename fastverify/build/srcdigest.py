#!/usr/bin/python3 -I
"""srcdigest.py PROJ  -> prints one sha256 over every file and symlink of PROJ outside PROJ/.lake (paths, kinds, contents,
link targets), then the number of entries. Used by build.sh before planning and after the build: the sources the plan is
computed from must be the sources lean compiled (fastverify build stage)."""
import hashlib, os, stat, sys


def main():
    root = os.path.realpath(sys.argv[1])
    h = hashlib.sha256(); n = 0
    entries = []
    for dp, dns, fns in os.walk(root):
        rel = os.path.relpath(dp, root)
        if rel == ".lake" or rel.startswith(".lake" + os.sep):
            dns[:] = []
            continue
        if rel == ".":
            dns[:] = [d for d in dns if d != ".lake"]
        # symlinked directories are not descended by os.walk; record them as links
        for d in dns:
            p = os.path.join(dp, d)
            if os.path.islink(p):
                entries.append(p)
        entries.extend(os.path.join(dp, f) for f in fns)
    for p in sorted(entries):   # sequential: 175k small files hash faster without a thread pool (GIL)
        st = os.lstat(p)
        r = os.path.relpath(p, root).encode("utf-8", "surrogateescape")
        if stat.S_ISLNK(st.st_mode):
            h.update(b"L\0" + r + b"\0" + os.readlink(p).encode("utf-8", "surrogateescape") + b"\0")
        elif stat.S_ISREG(st.st_mode):
            fh = hashlib.sha256()
            with open(p, "rb") as f:
                for chunk in iter(lambda: f.read(1 << 20), b""):
                    fh.update(chunk)
            h.update(b"F\0" + r + b"\0" + fh.digest())
        else:
            h.update(b"O\0" + r + b"\0" + str(stat.S_IFMT(st.st_mode)).encode() + b"\0")
        n += 1
    print(h.hexdigest(), n)


if __name__ == "__main__":
    main()
