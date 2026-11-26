#!/usr/bin/python3 -I
"""mkcase.py BASE_SOLUTION OUT_SOLUTION CASE -- notary test inputs: the base export (a pinned official export, e.g.
checkA/v3/selftest/good.export, judged with ITS challenge + comparator.json) plus the CASE's extra records, with fresh
name / level / expression indices above the base's (placeholders n0.., l1.., e0.. below)."""
import json, re, sys

EXTRA = {
    # B := A ; A := Prop, B declared first (declaration order: the official reader accepts both orders)
    "order-ba": ['{"in":n0,"str":{"pre":0,"str":"F6A"}}', '{"in":n1,"str":{"pre":0,"str":"F6B"}}',
                 '{"il":l1,"succ":0}', '{"ie":e0,"sort":l1}', '{"ie":e1,"sort":0}', '{"const":{"name":n0,"us":[]},"ie":e2}',
                 '{"def":{"all":[n1],"hints":"opaque","levelParams":[],"name":n1,"safety":"safe","type":e0,"value":e2}}',
                 '{"def":{"all":[n0],"hints":"opaque","levelParams":[],"name":n0,"safety":"safe","type":e0,"value":e1}}'],
    "order-ab": ['{"in":n0,"str":{"pre":0,"str":"F6A"}}', '{"in":n1,"str":{"pre":0,"str":"F6B"}}',
                 '{"il":l1,"succ":0}', '{"ie":e0,"sort":l1}', '{"ie":e1,"sort":0}', '{"const":{"name":n0,"us":[]},"ie":e2}',
                 '{"def":{"all":[n0],"hints":"opaque","levelParams":[],"name":n0,"safety":"safe","type":e0,"value":e1}}',
                 '{"def":{"all":[n1],"hints":"opaque","levelParams":[],"name":n1,"safety":"safe","type":e0,"value":e2}}'],
}
for tag, h in (("regular-2p32", 4294967296), ("regular-2p33m1", 8589934591), ("regular-max", 4294967295),
               ("regular-2p64", 18446744073709551616)):
    EXTRA[tag] = ['{"in":n0,"str":{"pre":0,"str":"F6D"}}', '{"il":l1,"succ":0}', '{"ie":e0,"sort":l1}', '{"ie":e1,"sort":0}',
                  '{"def":{"all":[n0],"hints":{"regular":%d},"levelParams":[],"name":n0,"safety":"safe","type":e0,"value":e1}}' % h]

def main():
    base, out, case = sys.argv[1:4]
    mx = {"in": 0, "il": 0, "ie": -1}
    lines = open(base, encoding="utf-8").read().split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    for ln in lines[1:]:
        m = re.search(r'"(in|il|ie)":(\d+)', ln)
        if m:
            mx[m.group(1)] = max(mx[m.group(1)], int(m.group(2)))
    def sub(s):
        s = re.sub(r'\bn(\d+)\b', lambda m: str(mx["in"] + 1 + int(m.group(1))), s)
        s = re.sub(r'\bl(\d+)\b', lambda m: str(mx["il"] + int(m.group(1))), s)
        return re.sub(r'\be(\d+)\b', lambda m: str(mx["ie"] + 1 + int(m.group(1))), s)
    extra = [sub(x) for x in EXTRA[case]]
    for x in extra:
        json.loads(x)
    with open(out, "w", encoding="utf-8") as f:
        f.write("\n".join(lines + extra) + "\n")
main()
