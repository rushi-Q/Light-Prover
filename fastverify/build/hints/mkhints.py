#!/usr/bin/env python3
"""build/hints/mkhints.py - refresh the B3 `cost-hints` file from the scheduler records of earlier runs.

    python3 -I build/hints/mkhints.py OUT.json.gz SCHED_OUT_OR_RUN_DIR... [--merge-with OLD.json.gz] [--stat median|max]

Each input is a build/sched.py output (`sched.out`) or a fastverify OUT directory (its `log/build-fast/sched.out` and
`log/build-fast/merge/*.out` are read). For every module the LAST successful record (`"event": "module"`, rc 0, no missing
outputs) of each input gives one wall time; across inputs the median (default) or the max is kept. `--merge-with OLD`
keeps OLD's value for modules the inputs do not cover (e.g. the original RH hints for modules a compressed composite did
not touch). Output: `{module: seconds}` (gzip JSON, sorted keys) - the format of build/hints/rh-build-costs.json.gz -
plus a one-line summary on stderr (modules, coverage of each input, total seconds).

Untrusted and order-only, like the hints themselves: `sched.py --cost-hints` uses a value as the module's cost in the
bottom-level priority and in the j1 slack estimate; a wrong or stale value can only cost build time, never change what is
built, exported or checked (build/README.md).
"""
import gzip
import json
import os
import statistics
import sys


def sched_files(p):
    if os.path.isdir(p):
        out = []
        for rel in ("log/build-fast/sched.out", "build-fast/sched.out", "sched.out"):
            f = os.path.join(p, rel)
            if os.path.isfile(f):
                out.append(f)
                break
        md = os.path.join(p, "log", "build-fast", "merge")
        if os.path.isdir(md):
            out += sorted(os.path.join(md, f) for f in os.listdir(md) if f.endswith(".out"))
        return out
    return [p] if os.path.isfile(p) else []


def walls(path):
    """module -> wall of its last successful record in one sched.out (later records replace earlier ones)."""
    w = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for ln in f:
            if not ln.startswith('{"event": "module"'):
                continue
            try:
                r = json.loads(ln)
            except ValueError:
                continue
            m, wall = r.get("module"), r.get("wall")
            if not isinstance(m, str) or not isinstance(wall, (int, float)):
                continue
            if r.get("rc") == 0 and not r.get("missing") and not r.get("error_msg"):
                w[m] = float(wall)
            else:
                w.pop(m, None)   # a later failed record: this input does not vouch for the module
    return w


def main(argv):
    if len(argv) < 2 or argv[0].startswith("-"):
        print(__doc__.strip().splitlines()[2], file=sys.stderr)
        return 2
    out, rest = argv[0], argv[1:]
    old, stat, inputs = None, "median", []
    i = 0
    while i < len(rest):
        a = rest[i]
        if a == "--merge-with":
            old = rest[i + 1]; i += 2; continue
        if a == "--stat":
            stat = rest[i + 1]; i += 2; continue
        inputs.append(a); i += 1
    if stat not in ("median", "max"):
        print("mkhints: --stat median|max", file=sys.stderr)
        return 2
    per_input = []
    for p in inputs:
        files = sched_files(p)
        if not files:
            print(f"mkhints: no sched.out in {p}", file=sys.stderr)
            return 2
        w = {}
        for f in files:
            w.update(walls(f))
        per_input.append((p, w))
    vals = {}
    for _, w in per_input:
        for m, s in w.items():
            vals.setdefault(m, []).append(s)
    hints = {m: round(statistics.median(v) if stat == "median" else max(v), 3) for m, v in vals.items()}
    kept = 0
    if old:
        with gzip.open(old, "rt", encoding="utf-8") as f:
            od = json.load(f)
        for m, s in od.items():
            if m not in hints and isinstance(s, (int, float)):
                hints[m] = s
                kept += 1
    tmp = out + ".tmp"
    with gzip.open(tmp, "wt", encoding="utf-8") as f:
        json.dump(dict(sorted(hints.items())), f)
    os.replace(tmp, out)
    print(f"mkhints: {len(hints)} modules ({len(vals)} from {len(per_input)} input(s): "
          + ", ".join(f"{os.path.basename(p.rstrip('/'))}={len(w)}" for p, w in per_input)
          + (f"; {kept} kept from {os.path.basename(old)}" if old else "")
          + f"); total {sum(hints.values()):.0f} s -> {out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
