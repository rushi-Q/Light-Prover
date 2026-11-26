#!/usr/bin/python3 -I
"""mk_kernel_issue_exports.py GOOD_EXPORT OUTDIR - writes four crafted exports (shaped after Lean issues 16489 / 15100 / 15101;
the crafting part copied verbatim; only the output differs: files instead of a temp dir) next to an honest control copy:
16489_loose_bvar_normal, 16489_loose_bvar_unsafe_ctor, 15101_fake_quotInfo, 15100_wrong_induct_unsafe_ctor, honest_control."""
import json, os, sys


def main(good, out):
    os.makedirs(out, exist_ok=True)
    good_lines = open(good, encoding="utf-8").read().splitlines()
    max_in = max((json.loads(l).get("in", 0) for l in good_lines[1:]), default=0)
    max_ie = max((json.loads(l).get("ie", 0) for l in good_lines[1:]), default=0)

    def make_16489(ctor_unsafe):
        n1, n2, n3, n4 = max_in + 1, max_in + 2, max_in + 3, max_in + 4
        e0, e1, e2, e3, e4, e5, e6 = [max_ie + k for k in range(1, 8)]
        return good_lines + [
            json.dumps({"in": n1, "str": {"pre": 0, "str": "Bad16489"}}),
            json.dumps({"in": n2, "str": {"pre": n1, "str": "mk"}}),
            json.dumps({"in": n3, "str": {"pre": 0, "str": "a"}}),
            json.dumps({"in": n4, "str": {"pre": 0, "str": "x"}}),
            json.dumps({"ie": e0, "sort": 0}),
            json.dumps({"const": {"name": n1, "us": []}, "ie": e1}),
            json.dumps({"bvar": 1, "ie": e2}),
            json.dumps({"forallE": {"binderInfo": "default", "body": e0, "name": n3, "type": e0}, "ie": e3}),
            json.dumps({"app": {"arg": e2, "fn": e1}, "ie": e4}),
            json.dumps({"forallE": {"binderInfo": "default", "body": e4, "name": n4, "type": e2}, "ie": e5}),
            json.dumps({"forallE": {"binderInfo": "default", "body": e5, "name": n3, "type": e0}, "ie": e6}),
            json.dumps({"inductive": {
                "types": [{"name": n1, "levelParams": [], "type": e3, "numParams": 1, "numIndices": 0,
                           "all": [n1], "ctors": [n2], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
                "ctors": [{"name": n2, "levelParams": [], "type": e6, "induct": n1, "cidx": 0,
                           "numParams": 1, "numFields": 1, "isUnsafe": ctor_unsafe}],
                "recs": [],
            }}),
        ]

    c_15101 = good_lines + [
        json.dumps({"in": max_in + 1, "str": {"pre": 0, "str": "FakeQuot"}}),
        json.dumps({"ie": max_ie + 1, "sort": 0}),
        json.dumps({"quot": {"name": max_in + 1, "levelParams": [], "type": max_ie + 1, "kind": "type"}}),
    ]

    n1, n2, n3 = max_in + 1, max_in + 2, max_in + 3
    e0, e1 = max_ie + 1, max_ie + 2
    c_15100 = good_lines + [
        json.dumps({"in": n1, "str": {"pre": 0, "str": "IndA"}}),
        json.dumps({"in": n2, "str": {"pre": n1, "str": "mk"}}),
        json.dumps({"in": n3, "str": {"pre": 0, "str": "OtherInd"}}),
        json.dumps({"ie": e0, "sort": 0}),
        json.dumps({"const": {"name": n1, "us": []}, "ie": e1}),
        json.dumps({"inductive": {
            "types": [{"name": n1, "levelParams": [], "type": e0, "numParams": 0, "numIndices": 0,
                       "all": [n1], "ctors": [n2], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": n2, "levelParams": [], "type": e1, "induct": n3, "cidx": 99,
                       "numParams": 0, "numFields": 0, "isUnsafe": True}],
            "recs": [],
        }}),
    ]
    cases = [("16489_loose_bvar_normal", make_16489(False)), ("16489_loose_bvar_unsafe_ctor", make_16489(True)),
             ("15101_fake_quotInfo", c_15101), ("15100_wrong_induct_unsafe_ctor", c_15100), ("honest_control", good_lines)]
    for cname, clines in cases:
        open(os.path.join(out, cname + ".export"), "w", encoding="utf-8").write("\n".join(clines) + "\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
