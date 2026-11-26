#!/usr/bin/python3 -I
"""mk_c2_stream.py GOOD_EXPORT OUTDIR : crafted exports that exercise the C2 checks of
STREAMING walks (the ultra-low-memory leg PChk/LowMem.lean, the warm daemon) on paths that do not decline to the official
fallback, built on top of the self-test good.export (lean4export 3.1 NDJSON):
  c2s_isrec_forged        : `inductive IndA : Prop | mk` whose inductive-type record says isRec=true (the kernel: false)
  c2s_unsafe_rec_before   : an UNSAFE axiom record named IndA.rec placed BEFORE the honest IndA block (whose recs list is
                            empty, so the kernel generates IndA.rec itself; the unsafe record is never replayed)
  c2s_deferred_forged_ctor: IndA's type is `Later` (a def `Later : Type := Prop` placed AFTER the block, so streaming walks
                            defer the block); its constructor record is unsafe with induct=OtherInd, cidx=99
  c2s_deferred_control    : the same deferred block with an honest constructor record (CONTROL: must be ACCEPTED)
  c2s_streamed_control    : the honest IndA block (recs []), in order (CONTROL: must be ACCEPTED)"""
import json, os, sys


def main(good, out):
    os.makedirs(out, exist_ok=True)
    base = open(good, encoding="utf-8").read().splitlines()
    max_in = max((json.loads(l).get("in", 0) for l in base[1:]), default=0)
    max_ie = max((json.loads(l).get("ie", 0) for l in base[1:]), default=0)
    N = {k: max_in + i for i, k in enumerate(["IndA", "IndA.mk", "OtherInd", "Later", "IndA.rec"], start=1)}
    names = [json.dumps({"in": N["IndA"], "str": {"pre": 0, "str": "IndA"}}),
             json.dumps({"in": N["IndA.mk"], "str": {"pre": N["IndA"], "str": "mk"}}),
             json.dumps({"in": N["OtherInd"], "str": {"pre": 0, "str": "OtherInd"}}),
             json.dumps({"in": N["Later"], "str": {"pre": 0, "str": "Later"}}),
             json.dumps({"in": N["IndA.rec"], "str": {"pre": N["IndA"], "str": "rec"}})]
    E = {k: max_ie + i for i, k in enumerate(["prop", "constA", "type1", "constLater"], start=1)}
    # level 1 = succ zero: find an existing level id for `succ 0` in the base, else add one
    il1 = None
    for l in base[1:]:
        o = json.loads(l)
        if "il" in o and o.get("succ") == 0:
            il1 = o["il"]; break
    extra_lv = []
    if il1 is None:
        max_il = max((json.loads(l).get("il", 0) for l in base[1:]), default=0)
        il1 = max_il + 1
        extra_lv = [json.dumps({"il": il1, "succ": 0})]
    exprs = extra_lv + [json.dumps({"ie": E["prop"], "sort": 0}),
                        json.dumps({"ie": E["constA"], "const": {"name": N["IndA"], "us": []}}),
                        json.dumps({"ie": E["type1"], "sort": il1}),
                        json.dumps({"ie": E["constLater"], "const": {"name": N["Later"], "us": []}})]

    def ind(type_e, is_rec=False, ctor_unsafe=False, induct="IndA", cidx=0):
        return json.dumps({"inductive": {
            "types": [{"name": N["IndA"], "levelParams": [], "type": type_e, "numParams": 0, "numIndices": 0,
                       "all": [N["IndA"]], "ctors": [N["IndA.mk"]], "numNested": 0, "isRec": is_rec,
                       "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": N["IndA.mk"], "levelParams": [], "type": E["constA"], "induct": N[induct], "cidx": cidx,
                       "numParams": 0, "numFields": 0, "isUnsafe": ctor_unsafe}],
            "recs": []}})
    later = json.dumps({"def": {"all": [N["Later"]], "hints": {"regular": 1}, "levelParams": [], "name": N["Later"],
                                "safety": "safe", "type": E["type1"], "value": E["prop"]}})
    unsafe_rec = json.dumps({"axiom": {"isUnsafe": True, "levelParams": [], "name": N["IndA.rec"], "type": E["prop"]}})
    cases = {
        "c2s_isrec_forged": base + names + exprs + [ind(E["prop"], is_rec=True)],
        "c2s_unsafe_rec_before": base + names + exprs + [unsafe_rec, ind(E["prop"])],
        "c2s_deferred_forged_ctor": base + names + exprs + [ind(E["constLater"], ctor_unsafe=True, induct="OtherInd", cidx=99), later],
        "c2s_deferred_control": base + names + exprs + [ind(E["constLater"]), later],
        "c2s_streamed_control": base + names + exprs + [ind(E["prop"])],
    }
    for k, lines in cases.items():
        open(os.path.join(out, k + ".export"), "w", encoding="utf-8").write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
