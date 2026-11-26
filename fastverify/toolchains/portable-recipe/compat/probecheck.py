#!/usr/bin/env python3
"""probecheck.py FV MATRIX.tsv NAME=TREE... -- IMAGE...
Validates the package's static startup probe (lib/autotune.py: GLIBC + GLIBCXX requirement + every DT_NEEDED library
resolvable; nothing executed) against ground truth: for every docker IMAGE the host facts (glibc version, libstdc++
GLIBCXX max, library names known to ld.so / in the standard dirs) are collected INSIDE the container, the probe's verdict
'starts' is computed for each tree with those facts, and compared with the matrix row (actual `lean --version` in that
image, compat-matrix.sh). A predicted start that does not start = the package would route builds to an unstartable tree."""
import json, os, re, subprocess, sys, importlib.util

def facts(img):
    sh = r'''g=$( (getconf GNU_LIBC_VERSION 2>/dev/null || ldd --version 2>&1 | head -1) | grep -o "[0-9]\.[0-9]*" | head -1); echo "G $g"
for f in /usr/lib/x86_64-linux-gnu/libstdc++.so.6 /usr/lib64/libstdc++.so.6 /lib/x86_64-linux-gnu/libstdc++.so.6 /usr/lib/libstdc++.so.6; do
  [ -e "$f" ] && { echo "X $(grep -ao 'GLIBCXX_3\.4\.[0-9]*' "$f" | sed 's/.*\.//' | sort -n | tail -1)"; break; }; done
(ldconfig -p 2>/dev/null || /sbin/ldconfig -p 2>/dev/null) | awk 'NR>1{print "L "$1}'
for d in /lib/x86_64-linux-gnu /usr/lib/x86_64-linux-gnu /lib64 /usr/lib64 /lib /usr/lib /usr/local/lib; do ls "$d" 2>/dev/null | sed "s|^|F |"; done'''
    out = subprocess.run(["docker", "run", "--rm", "--network", "none", img, "sh", "-c", sh], capture_output=True, text=True).stdout
    g = x = None; libs = set()
    for ln in out.splitlines():
        if ln.startswith("G ") and ln[2:].strip(): g = tuple(int(v) for v in ln[2:].strip().split("."))
        elif ln.startswith("X ") and ln[2:].strip(): x = int(ln[2:].strip())
        elif ln.startswith(("L ", "F ")): libs.add(ln[2:].strip())
    return g, x, libs

def main(a):
    fv, matrix = a[0], a[1]; i = a.index("--"); trees = dict(t.split("=", 1) for t in a[2:i]); images = a[i + 1:]
    spec = importlib.util.spec_from_file_location("autotune", os.path.join(fv, "lib", "autotune.py"))
    at = importlib.util.module_from_spec(spec); spec.loader.exec_module(at)
    truth = {}
    for ln in open(matrix):
        c = ln.rstrip("\n").split("\t")
        if c[0] != "image": truth[(c[0], c[2])] = c[3]
    rows = []; bad = 0
    for img in images:
        g, x, libs = facts(img)
        for name, tree in trees.items():
            def has(n, extra_dirs=(), libs=libs):
                return any(os.path.exists(os.path.join(d, n)) for d in extra_dirs) or n in libs
            at.host_has_lib = has
            req = at.required_glibc(tree); rx = at.required_glibcxx(tree); miss = at.missing_libs(tree)
            pred = bool(g and req and g >= req and (rx is None or (x is not None and x >= rx)) and not miss)
            act = truth.get((img, name), "?")
            ok = (pred and act == "ok") or (not pred and act == "FAIL")
            bad += (pred and act != "ok")
            rows.append((img, "%d.%d" % g if g else "musl", name, "starts" if pred else "refuse", act,
                         "agree" if ok else ("FALSE-START" if pred else "false-refuse"),
                         "req %s%s%s" % ("%d.%d" % req if req else "?", " cxx 3.4.%d" % rx if rx is not None else "",
                                         (" missing " + ",".join(miss)) if miss else "")))
    print("image\tglibc\ttree\tprobe\tactual\tresult\tdetail")
    for r in rows: print("\t".join(r))
    print(f"# {len(rows)} cases, {sum(r[5]=='agree' for r in rows)} agree, {bad} FALSE-START (probe says starts, it does not)")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
