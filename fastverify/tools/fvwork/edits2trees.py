#!/usr/bin/python3 -I
"""tools/fvwork/edits2trees.py SRC EDITS.jsonl OUTDIR - materialize an edit stream (mkedits.py) as full source trees
OUTDIR/NNN-<kind>/ (cumulative: state k = state k-1 with the files of edit k replaced; hard links for unchanged files),
so that tools that take whole trees (tools/ci/official-incr.sh, tools/incr/incr-reverify.sh, lake build) replay the same
states as `replay.py --edits`. Benchmark helper, untrusted."""
import json, os, shutil, subprocess, sys


def main():
    src, edits, out = os.path.realpath(sys.argv[1]), sys.argv[2], os.path.realpath(sys.argv[3])
    os.makedirs(out, exist_ok=True)
    prev = src
    for k, ln in enumerate(open(edits)):
        if not ln.strip():
            continue
        e = json.loads(ln)
        d = os.path.join(out, "%03d-%s" % (k, e.get("kind", "edit")))
        if os.path.exists(d):
            sys.exit(f"edits2trees: {d} exists")
        r = subprocess.run(["cp", "-al", prev, d], capture_output=True)
        if r.returncode != 0:
            shutil.rmtree(d, ignore_errors=True)
            subprocess.run(["cp", "-a", prev, d], check=True)
        for rel, content in e["files"].items():
            q = os.path.join(d, rel)
            if os.path.lexists(q):
                os.unlink(q)   # new inode: never write through a hard link into the previous state
            if content is not None:
                os.makedirs(os.path.dirname(q), exist_ok=True)
                with open(q, "w") as f:
                    f.write(content)
        print(d)
        prev = d


if __name__ == "__main__":
    main()
