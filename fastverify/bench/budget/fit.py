#!/usr/bin/python3 -I
"""fit.py SIZES.json DIR... : fit peak = a*export_bytes + b*threads + c per stage from cgrun JSONs (least squares, numpy-free).
SIZES.json maps the label used in the run names (sw-<label>.T<t>, lg-<label>.<leg>.T<t>) to the export size in bytes.
Prints the coefficients per stage (check = sw-* runs with memory unlimited; ccmp / plc / grz = lg-* runs) and the
worst relative residual, as JSON and as a table."""
import glob, json, os, re, sys

def solve3(rows):
    """rows: (x1, x2, y) -> least squares for y = a*x1 + b*x2 + c via normal equations (3x3)."""
    n = len(rows)
    if n < 3:
        return None
    S = [[0.0] * 3 for _ in range(3)]; T = [0.0] * 3
    for x1, x2, y in rows:
        v = (x1, x2, 1.0)
        for i in range(3):
            T[i] += v[i] * y
            for j in range(3):
                S[i][j] += v[i] * v[j]
    # gaussian elimination
    M = [S[i] + [T[i]] for i in range(3)]
    for i in range(3):
        p = max(range(i, 3), key=lambda r: abs(M[r][i]))
        M[i], M[p] = M[p], M[i]
        if abs(M[i][i]) < 1e-18:
            return None
        for r in range(3):
            if r != i:
                f = M[r][i] / M[i][i]
                for c in range(i, 4):
                    M[r][c] -= f * M[i][c]
    return [M[i][3] / M[i][i] for i in range(3)]

def main():
    sizes = json.load(open(sys.argv[1]))
    runs = []
    for d in sys.argv[2:]:
        for p in sorted(glob.glob(os.path.join(d, "*.json"))):
            try:
                j = json.load(open(p))
            except Exception:
                continue
            if j.get("exit") not in (0,) or j.get("limits", {}).get("memory_max") not in ("max", None):
                continue
            n = j.get("name", "")
            m = re.match(r"^sw-([A-Za-z0-9]+)\.T(\d+)$", n)
            stage = None
            if m:
                stage, label, t = "check", m.group(1), int(m.group(2))
            else:
                m = re.match(r"^lg-([A-Za-z0-9]+)\.(plc|grz|ccmp)\.T(\d+)$", n)
                if m:
                    label, stage, t = m.group(1), {"plc": "pleanchecker", "grz": "gruszka", "ccmp": "ccmp"}[m.group(2)], int(m.group(3))
            if not stage or label not in sizes:
                continue
            runs.append((stage, label, t, float(sizes[label]), float(j["memory_peak"]), float(j.get("wall_s", 0))))
    out = {}
    for stage in ("check", "ccmp", "pleanchecker", "gruszka"):
        rows = [(b, t, pk) for (s, _l, t, b, pk, _w) in runs if s == stage]
        coef = solve3(rows)
        if not coef:
            continue
        a, b, c = coef
        res = max((abs(a * x1 + b * x2 + c - y) / y for x1, x2, y in rows), default=0)
        out[stage] = {"bytes_per_export_byte": round(a, 3), "bytes_per_thread": int(b), "constant_bytes": int(c),
                      "runs": len(rows), "worst_rel_residual": round(res, 3)}
    print(json.dumps(out, indent=1))
    print()
    print("stage         label   T    export_GB  peak_GB  wall_s")
    for s, l, t, b, pk, w in sorted(runs):
        print(f"{s:13s} {l:7s} {t:3d}  {b/2**30:8.2f}  {pk/2**30:7.2f}  {w:6.1f}")

if __name__ == "__main__":
    main()
