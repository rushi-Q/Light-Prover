# Self and inclusive sample counts per function from a samply profile
# (saved with --unstable-presymbolicate). Usage: prof.py PROFILE.json.gz [N]
import json, gzip, sys, collections, bisect
p = json.load(gzip.open(sys.argv[1]))
syms = json.load(open(sys.argv[1].replace(".json.gz", ".json.syms.json")))
st = syms["string_table"]
# per library: sorted (rva, size, name)
libsyms = {}
for d in syms["data"]:
    ent = sorted((x["rva"], x["size"], st[x["symbol"]]) for x in d["symbol_table"])
    libsyms[d["debug_name"]] = ent
libs = p["libs"]
th = max(p["threads"], key=lambda x: x["samples"]["length"])
ft, fr, stk, res = th["funcTable"], th["frameTable"], th["stackTable"], th["resourceTable"]
def frame_name(f):
    addr = fr["address"][f]
    fn = fr["func"][f]
    r = ft["resource"][fn]
    if r is None or r < 0: return th["stringArray"][ft["name"][fn]]
    lib = libs[res["lib"][r]]
    ent = libsyms.get(lib["debugName"])
    if not ent or addr < 0: return th["stringArray"][ft["name"][fn]]
    i = bisect.bisect_right(ent, (addr, 1 << 62, "")) - 1
    return ent[i][2] if i >= 0 else hex(addr)
names = [frame_name(f) for f in range(fr["length"])]
selfc = collections.Counter(); incl = collections.Counter()
for s in th["samples"]["stack"]:
    if s is None: continue
    selfc[names[stk["frame"][s]]] += 1
    seen = set(); x = s
    while x is not None:
        n = names[stk["frame"][x]]
        if n not in seen: incl[n] += 1; seen.add(n)
        x = stk["prefix"][x]
tot = sum(selfc.values()); N = int(sys.argv[2]) if len(sys.argv) > 2 else 30
short = lambda n: n.replace("gruszka::", "").replace("<tc::Worker>::", "W::")[:110]
print("samples", tot); print("== self")
for n, c in selfc.most_common(N): print("%5.1f%%  %s" % (100 * c / tot, short(n)))
print("== inclusive")
for n, c in incl.most_common(N): print("%5.1f%%  %s" % (100 * c / tot, short(n)))
