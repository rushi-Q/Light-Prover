#!/usr/bin/python3 -I
"""xtimes.py RUNDIR... : per case of an xdiff.sh run: export size, official build+export seconds (.secs), official
lake comparator wall (mtime of p-C.cmp minus mtime of p-C.export: the comparator runs right after the export), sound check
wall (wall_s of check-sound's JSON line), verdicts."""
import glob, json, os, sys
for R in sys.argv[1:]:
    print("##", R)
    print("case\texport_MB\tbuild+export_s\tofficial_comparator_s\tcheck_sound_s\tofficial\tsound")
    for row in sorted(glob.glob(os.path.join(R, "row-*.tsv"))):
        f = open(row).read().rstrip("\n").split("\t")
        c = f[0]
        e = os.path.join(R, f"p-{c}.export")
        if not os.path.exists(os.path.join(R, f"p-{c}.cmp")):
            print(f"{c}\t-\t-\t-\t-\t{f[3]}\t{f[6]}"); continue
        mb = os.path.getsize(e) / 1e6
        be = open(e + ".secs").read().strip() if os.path.exists(e + ".secs") else "-"
        cmp_s = os.path.getmtime(os.path.join(R, f"p-{c}.cmp")) - os.path.getmtime(e)
        cs = "-"
        try:
            j = json.loads(open(os.path.join(R, f"p-{c}.cs")).read().strip().splitlines()[-1])
            cs = "%.1f" % j.get("wall_s")
        except Exception:
            pass
        print(f"{c}\t{mb:.0f}\t{float(be):.0f}\t{cmp_s:.0f}\t{cs}\t{f[3]}\t{f[6]}" if be != "-" else
              f"{c}\t{mb:.0f}\t-\t{cmp_s:.0f}\t{cs}\t{f[3]}\t{f[6]}")
