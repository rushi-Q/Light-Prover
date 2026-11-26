#!/usr/bin/python3 -I
"""certify_defdedup.py EDITS_TSV IBUILD_TSV IMPORTS_JSON OUT_TSV

Filters a DEFDEDUP.hybrid edits TSV using real L1 `ibuild.py` cone verification results:
  - Drops ALL edits in any edited module that had `rc != 0`.
  - If any direct importer `imp_mod` had `rc != 0`, drops ALL edits in every edited dependency `dep` of `imp_mod`!
  - Drops any cross-module `subst` in user modules targeting a dropped declaring module's deleted decl, and prunes
    any orphaned `insert_before` imports!
  - Guarantees 0 edited failures and 0 direct-importer failures on the verified cone.
"""
import argparse
import collections
import json
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("edits")
    ap.add_argument("ibuild_tsv")
    ap.add_argument("imports_json")
    ap.add_argument("out")
    a = ap.parse_args()

    imp_raw = json.load(open(a.imports_json))
    imp = {m: set(v.get("imports", ())) for m, v in imp_raw.items()}

    edits = [ln.rstrip("\n").split("\t", 5) for ln in open(a.edits, encoding="utf-8") if ln.strip()]
    edited_mods = {e[0] for e in edits}

    # Also track added imports per module so importer failures trace through added imports too
    for e in edits:
        if e[3] == "insert_before":
            for il in e[5].split("\\n"):
                if il.startswith("import "):
                    imp.setdefault(e[0], set()).add(il.split()[1])

    rc_map = {}
    for ln in open(a.ibuild_tsv, encoding="utf-8"):
        p = ln.rstrip("\n").split("\t")
        if len(p) >= 2:
            rc_map[p[0]] = int(p[1])

    bad_edited = {m for m in edited_mods if rc_map.get(m, -1) != 0}
    bad_importers = {m for m, rc in rc_map.items() if m not in edited_mods and rc != 0}

    # Any edited module imported by a failing importer is also dropped!
    dropped_by_importer = set()
    for im in bad_importers:
        for dep in imp.get(im, ()):
            if dep in edited_mods:
                dropped_by_importer.add(dep)

    drop_mods = bad_edited | dropped_by_importer

    # If a dropped declaring module had a deleted decl redirected across modules, drop its cross-module substs too
    dropped_subst_olds = set()
    for e in edits:
        if e[0] in drop_mods and e[3] == "subst":
            dropped_subst_olds.add(e[5].split(" ", 1)[0])

    # Keep remaining edits and prune any insert_before whose module no longer has any non-insert_before edit
    kept_non_imp = []
    kept_mods_with_edit = set()
    for e in edits:
        if e[0] in drop_mods:
            continue
        if e[3] == "insert_before":
            continue
        if e[3] == "subst" and e[5].split(" ", 1)[0] in dropped_subst_olds:
            continue
        kept_non_imp.append(e)
        kept_mods_with_edit.add(e[0])

    out = []
    stats = collections.Counter()
    for e in edits:
        if e[0] in drop_mods:
            stats["dropped_mod_edits"] += 1
            continue
        if e[3] == "insert_before":
            if e[0] not in kept_mods_with_edit:
                stats["dropped_orphan_imp"] += 1
                continue
            out.append(e)
            stats["kept_insert_before"] += 1
        elif e[3] == "subst" and e[5].split(" ", 1)[0] in dropped_subst_olds:
            stats["dropped_xmod_subst"] += 1
        else:
            out.append(e)
            stats["kept_" + e[3]] += 1

    with open(a.out, "w", encoding="utf-8") as fo:
        for e in out:
            fo.write("\t".join(e) + "\n")

    lines_del = sum(int(e[2]) - int(e[1]) + 1 for e in out if e[3] == "delete")
    lines_rep = sum(max(0, (int(e[2]) - int(e[1]) + 1) - 1) for e in out if e[3] == "replace")
    kept_mods = {e[0] for e in out}
    print(
        json.dumps(
            {
                "input_edits": len(edits),
                "output_edits": len(out),
                "input_edited_mods": len(edited_mods),
                "bad_edited_mods": len(bad_edited),
                "bad_importers": len(bad_importers),
                "dropped_by_importer": len(dropped_by_importer),
                "certified_edited_mods": len(kept_mods),
                "verified_importers_ok": sum(1 for m, rc in rc_map.items() if m not in edited_mods and rc == 0),
                "lines_deleted_decls": lines_del,
                "lines_saved_aliases": lines_rep,
                "stats": dict(stats),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
