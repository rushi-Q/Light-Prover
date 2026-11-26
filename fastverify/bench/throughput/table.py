#!/usr/bin/python3 -I
"""table.py RUNROOT... : one TSV row per run (runq.sh outputs): stage seconds, verdict, export size, build option."""
import json, os, sys

COLS = ["tag", "case", "preset", "mode", "exit", "wall", "verdict", "trust", "preflight", "prepare", "build", "export",
        "check", "export_bytes", "build_opt", "lean", "host"]


def rows(root):
    done = {}
    p = os.path.join(root, "runs", "done.tsv")
    if os.path.exists(p):
        for ln in open(p):
            f = ln.rstrip("\n").split("\t")
            if len(f) >= 8:
                done[f[0]] = f
    for tag, f in sorted(done.items()):
        rj = os.path.join(root, "runs", tag, "result.json")
        try:
            r = json.load(open(rj))
        except (OSError, ValueError):
            r = {}
        ss = r.get("stage_seconds") or {}
        chk = ss.get("checks_total")
        b = r.get("build") or {}
        lean = ""
        for at in b.get("attempts", []):
            st = at.get("stage") or {}
            for u in st.get("unsafe", []) or []:
                if u.startswith("toolchain-T1"):
                    lean = u.split(":", 1)[-1]
        yield {"tag": tag, "case": f[1], "preset": f[2], "mode": f[3], "exit": f[4], "wall": f[5], "host": f[6],
               "verdict": r.get("verdict"), "trust": r.get("trust"), "preflight": ss.get("preflight"),
               "prepare": ss.get("prepare"), "build": ss.get("build"), "export": ss.get("export"), "check": chk,
               "export_bytes": (r.get("export") or {}).get("size"), "build_opt": b.get("option"), "lean": lean}


def main():
    print("\t".join(COLS))
    for root in sys.argv[1:]:
        for r in rows(root):
            print("\t".join("" if r.get(c) is None else str(r.get(c)) for c in COLS))


if __name__ == "__main__":
    main()
