#!/usr/bin/env python3
"""Filter autoshorten edits.tsv to prevent cross-module `grind` `._proof_*` collisions.

Why this exists (G2 finding on rh-miniF / RH):
  When two sibling modules both declare a theorem with the same fully-qualified name
  `<namespace>.<name>` (e.g., `isMultiHomogIdeal_sup_span` in
  `EqSumMultihomogeneousComponents` and `ExistsPrimeFiltrationOfIsMultiHomogIdeal`),
  rewriting both proofs with `grind` causes Lean 4 to emit identical auxiliary proof
  constants `<namespace>.<name>._proof_1_1` in both `.olean` files. Each module passes
  standalone kernel-on verification (`apply.py`), yet any diamond importer (such as
  `Main.lean`) fails with `environment already contains '..._proof_1_1'`.

This filter scans all edited modules (and optionally the whole project or `srcmap.tsv`)
for theorem/lemma names declared in >1 module, and allows at most ONE module per
duplicate full name to receive `grind`-introducing edits (dropping the smaller-gain
module's edit).

Usage:
  filter_collisions.py IN_EDITS OUT_EDITS --src-root DIR [--srcmap TSV] [--report JSON]
"""
import argparse
import collections
import json
import os
import re
import sys

DECL_HDR_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|protected|exposed|noncomputable|unsafe|partial|meta|scoped|local)\s+)*"
    r"(theorem|lemma)\s+([^\s:({\[<]+)"
)
GRIND_RE = re.compile(r"\bgrind\b")


def parse_decls_in_file(path: str) -> list[tuple[int, str, bool]]:
    """Return list of (line_1idx, full_name, is_private) for theorems/lemmas in file."""
    out: list[tuple[int, str, bool]] = []
    ns_stack: list[str] = []
    try:
        lines = open(path, "r", encoding="utf-8", errors="replace").read().splitlines()
    except OSError:
        return out
    for idx, raw in enumerate(lines, 1):
        s = raw.strip()
        if s.startswith("namespace "):
            parts = s.split()
            if len(parts) >= 2:
                ns_stack.append(parts[1])
            continue
        if s.startswith("end "):
            parts = s.split()
            if len(parts) >= 2:
                target = parts[1]
                if ns_stack and ns_stack[-1] == target:
                    ns_stack.pop()
                elif target in ns_stack:
                    while ns_stack and ns_stack[-1] != target:
                        ns_stack.pop()
                    if ns_stack:
                        ns_stack.pop()
            continue
        m = DECL_HDR_RE.match(raw)
        if m:
            short = m.group(2)
            is_priv = bool(re.search(r"\bprivate\b", raw[:m.start(1)]))
            if short.startswith("_root_."):
                full = short[len("_root_."):]
            elif ns_stack:
                full = ".".join(ns_stack) + "." + short
            else:
                full = short
            out.append((idx, full, is_priv))
    return out


def enclosing_decl(decls: list[tuple[int, str, bool]], line_1idx: int) -> tuple[str, bool]:
    best_name, best_priv = "", False
    for ln, full, priv in decls:
        if ln <= line_1idx:
            best_name, best_priv = full, priv
        else:
            break
    return best_name, best_priv


def resolve_path(src_root: str, mod: str) -> str:
    rel = mod.replace(".", "/") + ".lean"
    p = os.path.join(src_root, rel)
    if os.path.exists(p):
        return p
    p2 = os.path.join(src_root, "src", rel)
    return p2 if os.path.exists(p2) else p


def main() -> int:
    ap = argparse.ArgumentParser(description="Filter cross-module grind ._proof_* collisions.")
    ap.add_argument("in_edits", help="Input headerless edits.tsv")
    ap.add_argument("out_edits", help="Output filtered edits.tsv")
    ap.add_argument("--src-root", required=True, help="Root of Lean source tree")
    ap.add_argument("--srcmap", help="Optional srcmap.tsv (name\\tmodule\\tkw...) for whole-repo duplicate-name scan")
    ap.add_argument("--scan-all", action="store_true", help="Walk entire --src-root to find duplicate names (use for medium repos)")
    ap.add_argument("--report", help="Optional JSON report path")
    args = ap.parse_args()

    raw_lines = [l for l in open(args.in_edits, "r", encoding="utf-8") if l.strip()]
    parsed = []
    edited_mods: set[str] = set()
    for l in raw_lines:
        parts = l.rstrip("\n").split("\t")
        if len(parts) >= 6 and parts[1].isdigit():
            edited_mods.add(parts[0])
            parsed.append((l, parts))
        else:
            parsed.append((l, None))

    # Map full_name -> set of modules declaring it
    name_mods: dict[str, set[str]] = collections.defaultdict(set)
    mod_decls: dict[str, list[tuple[int, str, bool]]] = {}

    if args.srcmap and os.path.exists(args.srcmap):
        with open(args.srcmap, "r", encoding="utf-8", errors="replace") as fh:
            hdr = fh.readline()
            for l in fh:
                p = l.rstrip("\n").split("\t")
                if len(p) >= 3 and p[2] in ("theorem", "lemma"):
                    name_mods[p[0]].add(p[1])

    if args.scan_all:
        for d, dirs, fs in os.walk(args.src_root):
            dirs[:] = [x for x in dirs if x not in (".lake", ".git")]
            for fn in fs:
                if fn.endswith(".lean"):
                    p = os.path.join(d, fn)
                    rel = os.path.relpath(p, args.src_root)
                    if rel.startswith("src/"):
                        rel = rel[4:]
                    mod = rel[:-5].replace(os.sep, ".")
                    decls = parse_decls_in_file(p)
                    if mod in edited_mods:
                        mod_decls[mod] = decls
                    for _, full, _ in decls:
                        name_mods[full].add(mod)

    for mod in sorted(edited_mods):
        if mod not in mod_decls:
            decls = parse_decls_in_file(resolve_path(args.src_root, mod))
            mod_decls[mod] = decls
            for _, full, _ in decls:
                name_mods[full].add(mod)

    # Identify all grind edits inside a duplicate-named theorem
    # Keep at most ONE module per duplicate name (preferring the module with higher total gain on that name)
    dup_grind_by_name: dict[str, dict[str, int]] = collections.defaultdict(lambda: collections.Counter())
    edit_meta: list[tuple[str, bool, str]] = []
    for l, parts in parsed:
        if parts is None:
            edit_meta.append(("", False, ""))
            continue
        mod, s, e, rep = parts[0], int(parts[1]), int(parts[2]), parts[5]
        has_grind = bool(GRIND_RE.search(rep))
        full, _ = enclosing_decl(mod_decls.get(mod, []), s)
        is_dup = bool(full and len(name_mods.get(full, set())) > 1)
        if has_grind and is_dup:
            gain = max(0, (e - s + 1) - (rep.count("\\n") + 1))
            dup_grind_by_name[full][mod] += max(1, gain)
        edit_meta.append((full, has_grind and is_dup, mod))

    # Choose the single winning module per duplicate name (if >1 module edits it with grind;
    # or if --srcmap/--scan-all showed another module already has that theorem name, drop all but 1,
    # or drop when >=2 edited modules use grind on the same name).
    winner_for_name: dict[str, str] = {}
    for full, mod_gains in dup_grind_by_name.items():
        if len(mod_gains) >= 2:
            # Deterministic winner: highest gain, tie-break alphabetically
            winner_for_name[full] = sorted(mod_gains.items(), key=lambda kv: (-kv[1], kv[0]))[0][0]

    kept = 0
    dropped = []
    with open(args.out_edits, "w", encoding="utf-8") as fout:
        for (l, parts), (full, is_dup_grind, mod) in zip(parsed, edit_meta):
            if is_dup_grind and full in winner_for_name and mod != winner_for_name[full]:
                dropped.append({
                    "module": mod,
                    "start": parts[1],
                    "decl": full,
                    "kept_module": winner_for_name[full],
                })
                continue
            fout.write(l)
            kept += 1

    rep = {
        "input_edits": len(raw_lines),
        "kept_edits": kept,
        "dropped_collisions": len(dropped),
        "colliding_names": len(winner_for_name),
        "dropped_details": dropped[:50],
    }
    if args.report:
        with open(args.report, "w", encoding="utf-8") as rf:
            json.dump(rep, rf, indent=2)
    print(
        f"filter_collisions: kept={kept} dropped={len(dropped)} colliding_names={len(winner_for_name)}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
