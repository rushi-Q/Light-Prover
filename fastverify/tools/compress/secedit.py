#!/usr/bin/python3 -I
"""secedit.py DOC KEY FILE : replace (or append) the section of DOC between the marker lines
    <!-- BEGIN KEY -->  and  <!-- END KEY -->
with the contents of FILE, under an exclusive flock on DOC.lock, written atomically (tmp + rename).
Lets several writers edit their own sections of one Markdown document without clobbering each other.
KEY: e.g. pruning, summary.  If DOC does not exist it is created.
secedit.py DOC KEY --print   prints the current section."""
import fcntl, os, sys, tempfile

def main():
    doc, key, src = sys.argv[1], sys.argv[2], sys.argv[3]
    b, e = f"<!-- BEGIN {key} -->", f"<!-- END {key} -->"
    with open(doc + ".lock", "a") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        cur = open(doc, encoding="utf-8").read() if os.path.exists(doc) else ""
        if src == "--print":
            i, j = cur.find(b), cur.find(e)
            print(cur[i + len(b):j].strip("\n") if i >= 0 and j > i else "(no section)")
            return 0
        body = open(src, encoding="utf-8").read().strip("\n")
        new = f"{b}\n{body}\n{e}"
        i, j = cur.find(b), cur.find(e)
        if i >= 0 and j > i:
            out = cur[:i] + new + cur[j + len(e):]
        else:
            out = (cur.rstrip("\n") + "\n\n" if cur.strip() else "") + new + "\n"
        d = os.path.dirname(os.path.abspath(doc))
        fd, tmp = tempfile.mkstemp(dir=d, prefix=".secedit.")
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(out)
        os.chmod(tmp, 0o664)
        os.rename(tmp, doc)
    return 0

if __name__ == "__main__":
    sys.exit(main())
