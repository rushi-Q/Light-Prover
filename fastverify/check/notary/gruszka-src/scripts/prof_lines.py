# Source lines of the samples inside one function (self time), from a
# samply profile saved with --unstable-presymbolicate. Needs a dSYM next to
# the binary (dsymutil BIN). Usage: prof_lines.py PROFILE.json.gz BIN FUNC [N]
import json, gzip, sys, collections, bisect, subprocess
p = json.load(gzip.open(sys.argv[1]))
syms = json.load(open(sys.argv[1].replace(".json.gz", ".json.syms.json")))
binp, func = sys.argv[2], sys.argv[3]
N = int(sys.argv[4]) if len(sys.argv) > 4 else 40
st = syms["string_table"]
libsyms = {}
for d in syms["data"]:
    libsyms[d["debug_name"]] = sorted((x["rva"], x["size"], st[x["symbol"]]) for x in d["symbol_table"])
libs = p["libs"]
th = max(p["threads"], key=lambda x: x["samples"]["length"])
ft, fr, stk, res = th["funcTable"], th["frameTable"], th["stackTable"], th["resourceTable"]
cnt = collections.Counter(); tot = 0; infn = 0
for s in th["samples"]["stack"]:
    if s is None: continue
    tot += 1
    f = stk["frame"][s]
    addr = fr["address"][f]
    fn = fr["func"][f]
    r = ft["resource"][fn]
    if r is None or r < 0 or addr < 0: continue
    lib = libs[res["lib"][r]]
    ent = libsyms.get(lib["debugName"])
    if not ent: continue
    i = bisect.bisect_right(ent, (addr, 1 << 62, "")) - 1
    if i < 0 or func not in ent[i][2]: continue
    infn += 1
    cnt[addr] += 1
print("samples", tot, "in", func, infn)
top = cnt.most_common(N)
addrs = ["0x%x" % (0x100000000 + a) for a, _ in top]
out = subprocess.run(["atos", "-o", binp, "-l", "0x100000000"] + addrs, capture_output=True, text=True).stdout.split("\n")
bylines = collections.Counter()
for (a, c), line in zip(top, out):
    print("%5.2f%%  %s  %s" % (100 * c / tot, hex(a), line[-90:]))
# all addresses grouped by source line
alla = list(cnt.items())
# with -i atos prints the inlined frames innermost first, a blank line after each address
out = subprocess.run(["atos", "-i", "-o", binp, "-l", "0x100000000"] + ["0x%x" % (0x100000000 + a) for a, _ in alla], capture_output=True, text=True).stdout.split("\n\n")
for (a, c), block in zip(alla, out):
    fs = [l for l in block.split("\n") if l.strip()]
    def short(l):
        name = l.split(" (in ")[0]
        name = name.split("::")[-1][:40]
        loc = l.rsplit("(", 1)[-1].rstrip(")")
        return name + "@" + loc
    k = " < ".join(short(l) for l in fs[:3])
    bylines[k] += c
print("== by line")
for k, c in bylines.most_common(N):
    print("%5.2f%%  %s" % (100 * c / tot, k[-80:]))
