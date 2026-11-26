#!/usr/bin/env python3
"""build/bcache.py - opt-in per-user cache of UNTRUSTED build helpers, used by build.sh --build-cache DIR.

  bcache.py check-dir DIR                      exit 0 iff DIR is a usable private cache (created 0700 if absent; must be a real
                                               directory owned by us, not group/world accessible, not a symlink)
  bcache.py stamps ROOT [EXTRA_FILE...]        prints one sha256 over (relative path, type, inode, size, mtime_ns, ctime_ns,
                                               mode) of every entry under ROOT (+ the extra files' contents), i.e. a cheap
                                               fingerprint that changes when any file of the tree is written, replaced,
                                               renamed or re-permissioned (ctime cannot be set back by unprivileged code)
  bcache.py key FILE|@FILE...                  prints sha256 over the files' paths, stamps and contents (for small files;
                                               @FILE = content only) - the cache key of a compiled helper
What is cached (both untrusted helpers of the build; a wrong or stale entry can only change what the untrusted build does,
which the trusted check re-establishes from the export - and every entry is checked before use):
  * t1-NAME.stamps: the tree fingerprint recorded after a FULL `toolchain.py verify-unofficial` of an unofficial toolchain
    tree succeeded; an identical fingerprint later skips the file-by-file re-hash (~3-6 s per run);
  * planner-KEY/planner + planner.sha256: the Lake planner compiled from build/planner/Planner.lean with the official
    toolchain (~5-6 s per run); before use the binary's sha256 must equal the recorded one.
"""
import hashlib, os, stat, sys


def check_dir(d):
    """every component of DIR is walked from / with O_NOFOLLOW (missing ones created 0700 relative
    to the parent's fd): a symlink at ANY component makes the cache unusable (r1-r5 makedirs followed intermediate links and
    created / wrote the cache outside; only the leaf was lstat'ed)"""
    fl = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    try:
        parts = [c for c in os.path.abspath(d).split("/") if c]
        fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
        try:
            for c in parts:
                try:
                    nfd = os.open(c, fl, dir_fd=fd)
                except FileNotFoundError:
                    os.mkdir(c, 0o700, dir_fd=fd)
                    nfd = os.open(c, fl, dir_fd=fd)
                os.close(fd)
                fd = nfd
            st = os.fstat(fd)
        finally:
            os.close(fd)
    except OSError:
        return False
    return stat.S_ISDIR(st.st_mode) and st.st_uid == os.getuid() and (st.st_mode & 0o077) == 0


def stamps(root, extra=()):
    h = hashlib.sha256()
    ents = []
    for dp, dns, fns in os.walk(root):
        dns.sort()
        for n in sorted(dns + fns):
            p = os.path.join(dp, n)
            try:
                st = os.lstat(p)
            except OSError:
                continue
            tgt = os.readlink(p) if stat.S_ISLNK(st.st_mode) else ""   # a symlink's target is part of the fingerprint
            ents.append("%s\0%o\0%d\0%d\0%d\0%d\0%s" % (os.path.relpath(p, root), st.st_mode, st.st_ino, st.st_size,
                                                        st.st_mtime_ns, st.st_ctime_ns, tgt))
    h.update("\n".join(ents).encode("utf-8", "surrogateescape"))
    for f in extra:
        with open(f, "rb") as fh:
            h.update(b"\0" + f.encode() + b"\0" + hashlib.sha256(fh.read()).digest())
    return h.hexdigest()


def key(files):
    h = hashlib.sha256()
    for f in files:
        if f.startswith("@"):   # content only (e.g. a per-run snapshot copy of a source file)
            with open(f[1:], "rb") as fh:
                h.update(b"@" + hashlib.sha256(fh.read()).digest())
            continue
        st = os.stat(f)
        h.update(("%s\0%d\0%d\0%d\0%d\n" % (f, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)).encode())
        if st.st_size <= (1 << 20):
            with open(f, "rb") as fh:
                h.update(hashlib.sha256(fh.read()).digest())
    return h.hexdigest()


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) == 2 and a[0] == "check-dir":
        sys.exit(0 if check_dir(a[1]) else 1)
    if len(a) >= 2 and a[0] == "stamps":
        print(stamps(a[1], a[2:]))
        sys.exit(0)
    if len(a) >= 2 and a[0] == "key":
        print(key(a[1:]))
        sys.exit(0)
    print(__doc__, file=sys.stderr)
    sys.exit(2)
