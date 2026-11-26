#!/usr/bin/env python3
"""Filter autoshorten (or general edits.tsv) against a challenge's statement closure.

Why this exists (G2 finding on Cedar):
  In code formalizations (e.g. Cedar), theorems proved inside the repository can be
  referenced inside model definitions (such as well-founded recursion termination
  proofs like `List.sizeOf_snd_lt_sizeOf_list`). Those theorems enter
  `challenge.export` (the statement closure), and `lake comparator` (`compareAt`)
  checks ALL constants in `challenge.export` -- including theorem proof values and
  auxiliary `_proof_*` lemmas. Even a kernel-valid proof rewrite that passes
  per-module verification (`apply.py`) will be REJECTED by `compareAt` if it
  rewrites a theorem inside `challenge.export`!

Usage:
  filter_challenge.py IN_EDITS OUT_EDITS \\
      [--challenge-export PATH] [--comparator-json PATH] \\
      [--exclude-modules MOD1,MOD2,...] [--report PATH]

Supports both lean4export v3.1.0 NDJSON (`challenge.export`) and legacy text format.
Matches declaration names by exact name and by dotted prefix (e.g. `Foo._proof_1`
when `Foo` is in the edit, or `Foo` when `Foo._proof_1` is in the challenge).
"""
import argparse
import json
import os
import re
import sys

DECL_KEYS = ("thm", "def", "axiom", "opaque", "inductive", "ctor", "rec", "quot")
DECL_HDR_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|protected|exposed|noncomputable|unsafe|partial|meta|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example)\s+([^\s:({\[<]+)"
)


def parse_challenge_export(path: str) -> set[str]:
    """Extract all declared constant names from a lean4export file (NDJSON or text)."""
    names_by_id: dict[int, str] = {0: ""}
    declared: set[str] = set()
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        first = f.readline()
        if not first:
            return declared
        is_json = first.lstrip().startswith("{")

        def handle_json_line(line: str) -> None:
            line = line.strip()
            if not line:
                return
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                return
            if "in" in obj:
                idx = obj["in"]
                if "str" in obj:
                    pre = names_by_id.get(obj["str"]["pre"], "")
                    s = obj["str"]["str"]
                    names_by_id[idx] = f"{pre}.{s}" if pre else s
                elif "num" in obj:
                    pre = names_by_id.get(obj["num"]["pre"], "")
                    n = obj["num"]["i"]
                    names_by_id[idx] = f"{pre}.{n}" if pre else str(n)
                return
            for k in DECL_KEYS:
                if k in obj:
                    val = obj[k]
                    if isinstance(val, dict) and "name" in val:
                        nm = names_by_id.get(val["name"], "")
                        if nm:
                            declared.add(nm)
                    break

        def handle_text_line(line: str) -> None:
            parts = line.split()
            if len(parts) < 3:
                return
            tag = parts[1]
            if tag == "#NS":
                idx = int(parts[0])
                pre = names_by_id.get(int(parts[2]), "")
                s = parts[3] if len(parts) > 3 else ""
                names_by_id[idx] = f"{pre}.{s}" if pre else s
            elif tag == "#NI":
                idx = int(parts[0])
                pre = names_by_id.get(int(parts[2]), "")
                n = parts[3] if len(parts) > 3 else "0"
                names_by_id[idx] = f"{pre}.{n}" if pre else n
            elif tag in ("#DEF", "#THM", "#AX", "#OPAQ", "#IND", "#CTOR", "#REC", "#QUOT"):
                nm = names_by_id.get(int(parts[2]), "")
                if nm:
                    declared.add(nm)

        if is_json:
            handle_json_line(first)
            for line in f:
                handle_json_line(line)
        else:
            handle_text_line(first)
            for line in f:
                handle_text_line(line)
    return declared


def parse_comparator_json(path: str) -> tuple[set[str], set[str]]:
    """Return (definition_names, theorem_names) from comparator.json."""
    data = json.load(open(path, "r", encoding="utf-8"))
    defs = {nm for nm in (data.get("definition_names", []) or []) if isinstance(nm, str)}
    thms = {nm for nm in (data.get("theorem_names", []) or []) if isinstance(nm, str)}
    return defs, thms


def find_enclosing_decl(src_lines: list[str], line_1idx: int) -> tuple[str, str]:
    """Return (short_name, active_namespace) for the enclosing declaration above line_1idx."""
    ns_stack: list[str] = []
    # Track namespace/end up to the enclosing declaration line
    decl_line = -1
    decl_short = ""
    for i in range(min(line_1idx, len(src_lines)) - 1, -1, -1):
        m = DECL_HDR_RE.match(src_lines[i])
        if m:
            decl_line = i
            decl_short = m.group(1)
            break
    if decl_line < 0:
        return "", ""
    # Compute active namespace stack up to decl_line
    for i in range(decl_line):
        s = src_lines[i].strip()
        if s.startswith("namespace "):
            parts = s.split()
            if len(parts) >= 2:
                ns_stack.append(parts[1])
        elif s.startswith("end "):
            parts = s.split()
            if len(parts) >= 2 and ns_stack and ns_stack[-1] == parts[1]:
                ns_stack.pop()
            elif len(parts) >= 2 and parts[1] in ns_stack:
                while ns_stack and ns_stack[-1] != parts[1]:
                    ns_stack.pop()
                if ns_stack:
                    ns_stack.pop()
    ns = ".".join(ns_stack)
    return decl_short, ns


def candidate_decl_names(decl_short: str, ns: str) -> set[str]:
    cands = set()
    if not decl_short:
        return cands
    if decl_short.startswith("_root_."):
        cands.add(decl_short[len("_root_."):])
    else:
        cands.add(decl_short)
        if ns:
            cands.add(f"{ns}.{decl_short}")
            parts = ns.split(".")
            for k in range(1, len(parts)):
                cands.add(".".join(parts[:k]) + "." + decl_short)
    return cands


def matches_pinned(cands: set[str], pinned: set[str], pinned_bases: set[str]) -> str | None:
    for c in cands:
        if c in pinned:
            return c
        if c in pinned_bases:
            return c
    return None


def main() -> int:
    ap = argparse.ArgumentParser(description="Filter edits.tsv against challenge statement closure.")
    ap.add_argument("in_edits", help="Input edits.tsv")
    ap.add_argument("out_edits", help="Output filtered edits.tsv")
    ap.add_argument("--challenge-export", help="Path to challenge.export (lean4export NDJSON or text)")
    ap.add_argument("--comparator-json", help="Path to comparator.json (optional additional pins)")
    ap.add_argument("--src-root", help="Source tree root (needed when edits lack decl name in comment/col)")
    ap.add_argument("--exclude-modules", default="", help="Comma-separated module names to drop entirely")
    ap.add_argument("--report", help="Optional JSON summary report path")
    args = ap.parse_args()

    pinned: set[str] = set()
    target_thms: set[str] = set()
    if args.challenge_export:
        pinned |= parse_challenge_export(args.challenge_export)
    if args.comparator_json:
        comp_defs, comp_thms = parse_comparator_json(args.comparator_json)
        pinned |= comp_defs
        target_thms = comp_thms
        # Target theorems in comparator.json are obligations whose *statements* are checked
        # (their proofs are free to be rewritten by autoshorten); only non-target constants
        # inside challenge.export (definitions + helper theorems used in definition bodies)
        # have their values pinned by compareAt.
        pinned -= target_thms

    # Also record base decl names of any `_proof_*` / `._*` aux constants in pinned
    pinned_bases: set[str] = set()
    for nm in pinned:
        if "._" in nm:
            base = nm.split("._", 1)[0]
            if base not in target_thms:
                pinned_bases.add(base)

    excl_mods = {m.strip() for m in args.exclude_modules.split(",") if m.strip()}
    src_cache: dict[str, list[str]] = {}

    def get_src_lines(mod: str) -> list[str]:
        if mod in src_cache:
            return src_cache[mod]
        if not args.src_root:
            src_cache[mod] = []
            return []
        rel = mod.replace(".", "/") + ".lean"
        p = os.path.join(args.src_root, rel)
        if not os.path.exists(p):
            p2 = os.path.join(args.src_root, "src", rel)
            if os.path.exists(p2):
                p = p2
        try:
            lines = open(p, "r", encoding="utf-8", errors="replace").read().splitlines()
        except OSError:
            lines = []
        src_cache[mod] = lines
        return lines

    kept = 0
    dropped_mod = 0
    dropped_pin = 0
    dropped_pins_detail: list[dict] = []

    with open(args.in_edits, "r", encoding="utf-8") as fin, open(args.out_edits, "w", encoding="utf-8") as fout:
        first = fin.readline()
        if not first:
            return 0
        first_parts = first.rstrip("\n").split("\t")
        has_header = False
        if len(first_parts) >= 2:
            if first_parts[0] == "module" or (not first_parts[1].isdigit()):
                has_header = True
        if has_header:
            fout.write(first)
            cols = first_parts
            ix = {k: i for i, k in enumerate(cols)}
            mod_i = ix.get("module", 0)
            start_i = ix.get("start", 1)
            decl_i = ix.get("decl") if "decl" in ix else ix.get("name")
            reason_i = ix.get("reason", 4)
            lines_iter = fin
        else:
            # Standard headerless apply_edits.py format:
            # module \t start \t end \t kind \t reason \t replacement
            mod_i, start_i, decl_i, reason_i = 0, 1, None, 4
            lines_iter = [first] + list(fin)

        for line in lines_iter:
            if not line.strip():
                continue
            parts = line.rstrip("\n").split("\t")
            mod = parts[mod_i] if mod_i < len(parts) else ""
            if mod in excl_mods:
                dropped_mod += 1
                continue

            cands: set[str] = set()
            if decl_i is not None and decl_i < len(parts) and parts[decl_i]:
                cands.add(parts[decl_i])
            if reason_i is not None and reason_i < len(parts):
                # Some edit formats embed `decl=Foo.bar` in reason
                m = re.search(r"(?:^|[;,\s])decl=([^\s;,]+)", parts[reason_i])
                if m:
                    cands.add(m.group(1))
            if args.src_root and start_i < len(parts):
                try:
                    ln = int(parts[start_i])
                except ValueError:
                    ln = 0
                if ln > 0:
                    short, ns = find_enclosing_decl(get_src_lines(mod), ln)
                    cands |= candidate_decl_names(short, ns)

            hit = matches_pinned(cands, pinned, pinned_bases)
            if hit:
                dropped_pin += 1
                dropped_pins_detail.append({
                    "module": mod,
                    "start": parts[start_i] if start_i < len(parts) else "",
                    "matched_pin": hit,
                })
                continue

            fout.write(line)
            kept += 1

    summary = {
        "pinned_constants": len(pinned),
        "pinned_bases": len(pinned_bases),
        "excluded_modules": sorted(excl_mods),
        "kept_edits": kept,
        "dropped_by_module": dropped_mod,
        "dropped_by_challenge_pin": dropped_pin,
        "dropped_pins": dropped_pins_detail,
    }
    if args.report:
        with open(args.report, "w", encoding="utf-8") as rf:
            json.dump(summary, rf, indent=2)
    print(
        f"filter_challenge: pinned={len(pinned)} kept={kept} "
        f"dropped_mod={dropped_mod} dropped_pin={dropped_pin}",
        file=sys.stderr,
    )
    if dropped_pins_detail:
        uniq = sorted({d["matched_pin"] for d in dropped_pins_detail})
        print(f"  dropped pinned decls ({len(uniq)}): {', '.join(uniq[:20])}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
