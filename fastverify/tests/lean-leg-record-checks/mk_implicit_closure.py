#!/usr/bin/python3 -I
"""mk_implicit_closure.py SELFTEST_DIR OUTDIR

Inputs for the kernel-implicit CLOSURE case of the incremental leg: the 4.36 kernel expands a
string literal to `String.ofList [Char.ofNat ..]` WITHOUT a syntactic reference and then unfolds those constants, so a
check can reach their whole closure (`Char.ofNat` -> `Char.ofNatAux`, `String.ofList` -> `List.utf8Encode` ->
`String.utf8EncodeChar`). Adapted from an earlier standalone repro
(same construction for `charaux`); everything is derived from the pinned self-test export good.export.

  charaux/{snap,final}.export  snap: Char.ofNatAux returns '\\0' (so every string literal of one char is the same) and
        r9_d : "a".bytes = "b".bytes := let _ := String.ofList; rfl (true in snap); final: the UNCHANGED prelude, r9_d,
        r9_is97, r9_boom : False (from r9_d) and fvSelfTest proved from r9_boom. The final export is FALSE (plain rejects).
  utf8/{snap,final}.export     same with snap's String.utf8EncodeChar := fun _ => [] (every string literal encodes to the
        empty byte list; the dirty constant is in String.ofList's closure, not Char.ofNat's) and r9_d := rfl (no anchor).
  walkpos.export               = charaux/snap.export, judged as a final export on its own: r9_d's syntactic closure lacks
        Char.ofNat, so the plain walk checks it before Char.ofNat is declared ("unknown constant"); a targeted skip of r9_d
        must not change that verdict (skip only where the walk snapshot holds the export's kernel-implicit constants).
  targets.txt                  r9_d
  finals/ic_{charaux,utf8}_final.export  copies of the two FALSE final exports for leanleg.sh / incr.sh (every Lean leg ALONE,
        in every mode, must reject them). walkpos.export is NOT a false export (r9_d holds in its own prelude; a leg that walks
        in another order may accept it): it only checks that a targeted skip keeps the plain walk's verdict
        (test_targeted_forged.sh); the FULL incremental mode with snapshot = final accepts it by design.
"""
import copy
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "recursor_name"))
from exportbuilder_src import ExportBuilder, load_export  # noqa: E402


def split_header_decls(item_list):
    defs, decls = [], []
    for it in item_list:
        (defs if ("in" in it or "il" in it or "ie" in it) else decls).append(it)
    return defs + decls


def build(hdr, items, variant: str, is_final: bool) -> ExportBuilder:
    b = ExportBuilder(hdr, copy.deepcopy(items))
    n = b.name
    n_Nat, n_zero, n_Char = n("Nat"), n("Nat.zero"), n("Char")
    n_Char_ofNat, n_Char_ofNatAux, n_isValidChar = n("Char.ofNat"), n("Char.ofNatAux"), n("Nat.isValidChar")
    n_UInt8, n_BitVec, n_Fin, n_List, n_List_rec = n("UInt8"), n("BitVec"), n("Fin"), n("List"), n("List.rec")
    n_Array, n_ByteArray, n_String, n_String_ofList = n("Array"), n("ByteArray"), n("String"), n("String.ofList")
    n_Eq, n_refl, n_Eq_rec, n_False, n_False_rec = n("Eq"), n("Eq.refl"), n("Eq.rec"), n("False"), n("False.rec")
    n_fvSelfTest, n_utf8EncodeChar = n("fvSelfTest"), n("String.utf8EncodeChar")
    n_n, n_h, n_cs, n_x, n_xs = n("n"), n("h"), n("cs"), n("_x"), n("xs")
    n_d, n_is97, n_boom = n("r9_d"), n("r9_is97"), n("r9_boom")
    l0 = b.lvl_zero()
    l1 = b.lvl_succ(l0)
    e_Nat, e_zero, e_Char, e_UInt8 = b.const(n_Nat), b.const(n_zero), b.const(n_Char), b.const(n_UInt8)
    e_List_Char = b.app(b.const(n_List, [l0]), e_Char)
    e_List_UInt8 = b.app(b.const(n_List, [l0]), e_UInt8)
    decl = {}
    for it in b.items:
        for k in ("def", "thm", "opaque", "axiom"):
            if k in it:
                decl[it[k]["name"]] = it[k]

    if not is_final and variant == "charaux":
        # Char.ofNatAux := fun n h => <the closed '\0' of Char.ofNat's else branch> (`Char.mk _ Char.ofNat._proof_2`)
        exprs = {it["ie"]: it for it in b.items if "ie" in it}
        n_pf2 = n("Char.ofNat._proof_2")
        char_zero = next(eid for eid, ex in exprs.items() if "app" in ex and "const" in exprs[ex["app"]["arg"]]
                         and exprs[ex["app"]["arg"]]["const"]["name"] == n_pf2)
        aux = decl[n_Char_ofNatAux]
        aux["value"] = b.lam(n_n, e_Nat, b.lam(n_h, b.app(b.const(n_isValidChar), b.bvar(0)), char_zero))
        aux["hints"] = "abbrev"
    if not is_final and variant == "utf8":
        enc = decl[n_utf8EncodeChar]
        enc["value"] = b.lam(n_x, e_Char, b.app(b.const(n("List.nil"), [l0]), e_UInt8))
        enc["hints"] = "abbrev"

    def str_bytes_list(s):   # "s".toByteArray.data.toList as projections of the literal (no constant reference)
        es = b.add_expr({"strVal": s})
        eba = b.add_expr({"proj": {"typeName": n_String, "idx": 0, "struct": es}})
        earr = b.add_expr({"proj": {"typeName": n_ByteArray, "idx": 0, "struct": eba}})
        return b.add_expr({"proj": {"typeName": n_Array, "idx": 0, "struct": earr}})

    e_a, e_b = str_bytes_list("a"), str_bytes_list("b")
    d_type = b.app(b.app(b.app(b.const(n_Eq, [l1]), e_List_UInt8), e_a), e_b)
    d_refl = b.app(b.app(b.const(n_refl, [l1]), e_List_UInt8), e_a)
    if variant == "charaux":   # anchor: a syntactic reference to the clean String.ofList (the original repro's construction)
        d_val = b.add_expr({"letE": {"name": n_x, "type": decl[n_String_ofList]["type"], "value": b.const(n_String_ofList),
                                     "body": d_refl, "nondep": True}})
    else:
        d_val = d_refl
    b.items.append({"thm": {"name": n_d, "levelParams": [], "type": d_type, "value": d_val, "all": [n_d]}})

    if is_final:
        def uint8_to_nat(e_u8):
            ebv = b.add_expr({"proj": {"typeName": n_UInt8, "idx": 0, "struct": e_u8}})
            efin = b.add_expr({"proj": {"typeName": n_BitVec, "idx": 0, "struct": ebv}})
            return b.add_expr({"proj": {"typeName": n_Fin, "idx": 0, "struct": efin}})
        n_ble, n_Bool, n_Bool_rec = n("Nat.ble"), n("Bool"), n("Bool.rec")
        e_Bool, e_Prop, e_False = b.const(n_Bool), b.sort(l0), b.const(n_False)
        e_True = b.app(b.app(b.app(b.const(n_Eq, [l1]), e_Nat), e_zero), e_zero)
        e_97 = b.add_expr({"natVal": "97"})
        # r9_is97 xs := head xs <= 97 (False for [])
        check_hd = b.app(b.app(b.app(b.app(b.const(n_Bool_rec, [l1]), b.lam(n_x, e_Bool, e_Prop)), e_False), e_True),
                         b.app(b.app(b.const(n_ble), uint8_to_nat(b.bvar(2))), e_97))
        list_rec_xs = b.app(b.app(b.app(b.app(b.app(b.const(n_List_rec, [l1, l0]), e_UInt8), b.lam(n_x, e_List_UInt8, e_Prop)),
                                        e_False), b.lam(n_x, e_UInt8, b.lam(n_x, e_List_UInt8, b.lam(n_x, e_Prop, check_hd)))),
                            b.bvar(1 if variant == "charaux" else 0))   # xs (under the let binder for charaux)
        is97_body = b.add_expr({"letE": {"name": n_x, "type": decl[n_Char_ofNatAux]["type"], "value": b.const(n_Char_ofNatAux),
                                         "body": list_rec_xs, "nondep": True}}) if variant == "charaux" else list_rec_xs
        b.items.append({"def": {"name": n_is97, "levelParams": [], "type": b.forallE(n_xs, e_List_UInt8, e_Prop),
                                "value": b.lam(n_xs, e_List_UInt8, is97_body), "hints": "abbrev", "safety": "safe",
                                "all": [n_is97]}})
        e_is97 = b.const(n_is97)
        eq_motive = b.lam(n_xs, e_List_UInt8, b.lam(n_x, b.app(b.app(b.app(b.const(n_Eq, [l1]), e_List_UInt8), e_a), b.bvar(0)),
                                                    b.app(e_is97, b.bvar(1))))
        e_refl_0 = b.app(b.app(b.const(n_refl, [l1]), e_Nat), e_zero)
        boom_core = b.app(b.app(b.app(b.app(b.app(b.app(b.const(n_Eq_rec, [l0, l1]), e_List_UInt8), e_a), eq_motive),
                                          e_refl_0), e_b), b.const(n_d))
        if variant == "charaux":
            boom_let1 = b.add_expr({"letE": {"name": n_x, "type": b.forallE(n_cs, e_Nat, e_Char), "value": b.const(n_Char_ofNat),
                                             "body": boom_core, "nondep": True}})
            boom_val = b.add_expr({"letE": {"name": n_x, "type": b.forallE(n_cs, e_List_Char, b.const(n_String)),
                                            "value": b.const(n_String_ofList), "body": boom_let1, "nondep": True}})
        else:
            boom_val = boom_core
        b.items.append({"thm": {"name": n_boom, "levelParams": [], "type": e_False, "value": boom_val, "all": [n_boom]}})
        st = decl[n_fvSelfTest]
        st["value"] = b.app(b.app(b.const(n_False_rec, [l0]), b.lam(n_x, e_False, st["type"])), b.const(n_boom))
    b.items = split_header_decls(b.items)
    return b


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    st, out = Path(sys.argv[1]), Path(sys.argv[2])
    hdr, items = load_export(st / "good.export")
    for v in ("charaux", "utf8"):
        (out / v).mkdir(parents=True, exist_ok=True)
        build(hdr, items, v, False).write(out / v / "snap.export")
        build(hdr, items, v, True).write(out / v / "final.export")
    build(hdr, items, "charaux", False).write(out / "walkpos.export")
    (out / "targets.txt").write_text("r9_d\n")
    (out / "finals").mkdir(exist_ok=True)
    for v in ("charaux", "utf8"):
        (out / "finals" / f"ic_{v}_final.export").write_bytes((out / v / "final.export").read_bytes())
    print(f"wrote {out}/{{charaux,utf8}}/{{snap,final}}.export, walkpos.export, targets.txt, finals/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
