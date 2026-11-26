#!/bin/bash
# publish-preset.sh — Staged, additive, default-off wiring of `--preset notary` (check option CN)
# into fastverify/config/components.json and fastverify/lib/fastverify.py.
#
# Run this only after every soundness suite of tests/sound-gates (arena, suitex, cmpx, mathlib, threads,
# RH honest + M1-M4) has 0 FAIL.
#
# Usage:
#   publish-preset.sh --dry-run    # print exact unified diffs without touching live files
#   publish-preset.sh --apply      # apply atomically (refuses if already applied or unexpected context)
set -euo pipefail
MODE=${1:---dry-run}
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../.." && pwd)

/usr/bin/python3 -I - "$FV" "$MODE" <<'PY'
import difflib, json, os, sys

fv, mode = sys.argv[1], sys.argv[2]
if mode not in ("--dry-run", "--apply"):
    sys.exit("usage: publish-preset.sh [--dry-run|--apply]")

# 1. config/components.json: add stages.checkNotary and check_options.CN (purely additive)
cfg_path = os.path.join(fv, "config", "components.json")
cfg_old = open(cfg_path, encoding="utf-8").read()
cfg = json.loads(cfg_old)
if "checkNotary" not in cfg.get("stages", {}):
    cfg["stages"]["checkNotary"] = "check/notary/check-notary.sh"
if "CN" not in cfg.get("check_options", {}):
    cfg["check_options"]["CN"] = {
        "script": "check/notary/check-notary.sh",
        "args": [],
        "what": "NOTARY check (additive): unmodified official Lean 4.36 release libs + runtime 3-leg canonical SHA-256 digest cross-check (ccmp-notary == pleanchecker-notary == gruszka-r7) + selectable vetted second kernels"
    }
cfg_new = json.dumps(cfg, indent=2, ensure_ascii=False) + "\n"

# 2. lib/fastverify.py: additive CN check option + --preset notary + --notary-kernels (zero touch to CS / sound / sound-auto)
fv_path = os.path.join(fv, "lib", "fastverify.py")
fv_old = open(fv_path, encoding="utf-8").read()
fv_new = fv_old

def sub_once(text, target, repl, label):
    if repl in text:
        return text
    cnt = text.count(target)
    if cnt != 1:
        sys.exit(f"REFUSE: {label} expected 1 occurrence, found {cnt}")
    return text.replace(target, repl, 1)

# 2a. CHECK_OPTS: register CN
fv_new = sub_once(
    fv_new,
    '    "CS": ("sound", "SOUND check (GOAL S1): official judge code (compareAt + checkAxioms) + official 4.36 kernel libraries "\n'
    '                    "(parallel Lean.Replay walk) + an independent second kernel (gruszka); no equivalence gates"),\n}',
    '    "CS": ("sound", "SOUND check (GOAL S1): official judge code (compareAt + checkAxioms) + official 4.36 kernel libraries "\n'
    '                    "(parallel Lean.Replay walk) + an independent second kernel (gruszka); no equivalence gates"),\n'
    '    "CN": ("notary", "NOTARY check: unmodified official Lean 4.36 release libraries + runtime 3-leg "\n'
    '                     "canonical env SHA-256 digest cross-check + selectable vetted second kernels"),\n}',
    "CHECK_OPTS CN"
)

# 2b. FAST_PRIORITY: put CN right before CS (only active when CN is explicitly selected)
fv_new = sub_once(
    fv_new,
    'FAST_PRIORITY = ("CS", "C1", "C2", "C3", "C4")',
    'FAST_PRIORITY = ("CN", "CS", "C1", "C2", "C3", "C4")',
    "FAST_PRIORITY CN"
)

# 2c. PRESETS: add default-off "notary" preset (official B0 + E0 + CN for maximum offline assurance)
fv_new = sub_once(
    fv_new,
    '    "sound-auto": {"build": "B3", "export": "E1", "check": ["CS"], "unsafe": [], "auto": True},\n}',
    '    "sound-auto": {"build": "B3", "export": "E1", "check": ["CS"], "unsafe": [], "auto": True},\n'
    '    # notary (additive, default-off): maximum offline assurance — official build/export (B0+E0) +\n'
    '    # unmodified official Lean 4.36 release kernel libraries + runtime 3-leg canonical SHA-256 digest cross-check\n'
    '    # (ccmp-notary == pleanchecker-notary == gruszka-r7) + optional extra bundled kernels (--notary-kernels).\n'
    '    "notary": {"build": "B0", "export": "E0", "check": ["CN"], "unsafe": []},\n}',
    "PRESETS notary"
)

# 2d. check(): pass --private-inputs and optional --kernels to CN (without touching CS behavior!)
fv_new = sub_once(
    fv_new,
    '            if opt == "CS":\n'
    '                # check-sound v2 (D08): the export the orchestrator judges is PRIVATE - written by the package\'s own sandboxed\n'
    '                # exporter (exited) into OUT / --export-dir, or (export-in) the private copy made into OUT above - so\n'
    '                # assert it: an export > 4 GiB is then hard-linked instead of copied a second time by the check\n'
    '                argv += ["--private-inputs"]',
    '            if opt == "CS":\n'
    '                # check-sound v2 (D08): the export the orchestrator judges is PRIVATE - written by the package\'s own sandboxed\n'
    '                # exporter (exited) into OUT / --export-dir, or (export-in) the private copy made into OUT above - so\n'
    '                # assert it: an export > 4 GiB is then hard-linked instead of copied a second time by the check\n'
    '                argv += ["--private-inputs"]\n'
    '            if opt == "CN":\n'
    '                argv += ["--private-inputs"]\n'
    '                if getattr(self.a, "notary_kernels", None):\n'
    '                    argv += ["--kernels", self.a.notary_kernels]',
    "check() CN args"
)

# 2e. decide_notary(): parallel to decide_sound(), never alters decide_sound()
fv_new = sub_once(
    fv_new,
    '    def decide(self):\n'
    '        if getattr(self.a, "modulo_frontier", None) and getattr(self.a, "sound", False):\n'
    '            return self.decide_frontier()\n'
    '        if getattr(self.a, "sound", False):\n'
    '            return self.decide_sound()',
    '    def decide_notary(self):\n'
    '        """NOTARY mode (check CN selected): identical trust posture to SOUND mode, strengthened with\n'
    '        unmodified official Lean 4.36 release kernel libraries (zero PGO/ThinLTO), runtime 3-leg canonical env\n'
    '        SHA-256 digest cross-check (ccmp-notary == pleanchecker-notary == gruszka-r7), and selectable vetted kernels."""\n'
    '        r = self.res\n'
    '        ch = dict(r["checks"])\n'
    '        cn = ch.get("notary") or {"verdict": "NOT_RUN"}\n'
    '        others = {k: v for k, v in ch.items() if k != "notary"}\n'
    '        rej = [k for k, v in others.items() if v.get("verdict") == "REJECTED"]\n'
    '        if cn["verdict"] == "ACCEPTED" and not rej:\n'
    '            v = "ACCEPTED"\n'
    '        elif cn["verdict"] == "REJECTED" or rej:\n'
    '            v = "REJECTED"\n'
    '        else:\n'
    '            v = "DECLINED"\n'
    '        r["verdict_fast"] = v\n'
    '        r["verdict_official"] = (ch.get("official") or {}).get("verdict", "NOT_RUN")\n'
    '        r["verdict_fast_basis"] = {"policy": "notary", "accepted_by": ["notary"] if cn["verdict"] == "ACCEPTED" else [],\n'
    '                                   "rejected_by": (["notary"] if cn["verdict"] == "REJECTED" else []) + rej,\n'
    '                                   "declined_or_not_run": [k for k, x in ch.items()\n'
    '                                                           if x.get("verdict") not in ("ACCEPTED", "REJECTED")]}\n'
    '        r["verdict"] = v\n'
    '        stage = cn.get("stage") if isinstance(cn.get("stage"), dict) else {}\n'
    '        ce = (r.get("inputs") or {}).get("challenge_export") or {}\n'
    '        e = r.get("export") or {}\n'
    '        b = r.get("build") or {}\n'
    '        r["trust"] = "notary"\n'
    '        r["unsafe_reasons"] = []\n'
    '        r["soundness"] = {\n'
    '            "claim": "ACCEPTED only if every check of GOAL S1 and of the notary design passed: unmodified official Lean 4.36 release "\n'
    '                     "kernel libraries (ccmp-notary + pleanchecker-notary) + independent kernel(s) + runtime 3-leg "\n'
    '                     "canonical environment SHA-256 digest equality across ccmp, Lean replay, and gruszka-r7",\n'
    '            "trusted": {"challenge_export": {"sha256": ce.get("sha256"), "source": ce.get("source"),\n'
    '                                             "pinned_sha256": getattr(self.a, "challenge_sha256", None),\n'
    '                                             "pin_ok": (None if not getattr(self.a, "challenge_sha256", None)\n'
    '                                                        else ce.get("sha256") == self.a.challenge_sha256)},\n'
    '                        "check": {"option": "CN", "verdict": cn.get("verdict"), "basis": stage.get("basis"),\n'
    '                                  "binaries_sha256": stage.get("binaries_sha256"), "version": stage.get("version"),\n'
    '                                  "kernels": stage.get("kernels"), "r7_digest": stage.get("r7_digest"),\n'
    '                                  "reason": stage.get("reason")}},\n'
    '            "untrusted": {"build": {"option": b.get("option"), "mode": b.get("mode")},\n'
    '                          "export": {"option": e.get("option"), "mode": e.get("mode"), "sha256": e.get("sha256"),\n'
    '                                     "size": e.get("size")}},\n'
    '        }\n'
    '        if v == "ACCEPTED":\n'
    '            r["verdict_basis"] = "NOTARY: " + (stage.get("basis") or "trusted check CN accepted")\n'
    '        elif v == "REJECTED":\n'
    '            r["verdict_basis"] = "NOTARY: rejected by " + ", ".join(r["verdict_fast_basis"]["rejected_by"]) + (\n'
    '                f" ({stage.get(\'reason\')})" if stage.get("reason") else "")\n'
    '        else:\n'
    '            r["verdict_basis"] = f"NOTARY: no verdict (trusted check: {cn.get(\'verdict\')}; {stage.get(\'reason\')})"\n'
    '        off = ch.get("official")\n'
    '        if off and off.get("verdict") in ("ACCEPTED", "REJECTED") and v in ("ACCEPTED", "REJECTED"):\n'
    '            r["agreement"] = off["verdict"] == v\n'
    '\n'
    '    def decide(self):\n'
    '        if getattr(self.a, "notary", False):\n'
    '            return self.decide_notary()\n'
    '        if getattr(self.a, "modulo_frontier", None) and getattr(self.a, "sound", False):\n'
    '            return self.decide_frontier()\n'
    '        if getattr(self.a, "sound", False):\n'
    '            return self.decide_sound()',
    "decide_notary()"
)

# 2f. CLI arg --notary-kernels + a.notary flag (require --challenge-sha256 on --from-export just like sound mode)
fv_new = sub_once(
    fv_new,
    '    ap.add_argument("--confirm-reject", action="store_true",',
    '    ap.add_argument("--notary-kernels", default=None, metavar="LIST",\n'
    '                    help="with --preset notary / --check CN: comma-separated second kernels "\n'
    '                         "(subset of gruszka,con-ron,con-leche,nanoda; default: gruszka)")\n'
    '    ap.add_argument("--confirm-reject", action="store_true",',
    "CLI --notary-kernels"
)

fv_new = sub_once(
    fv_new,
    '    a.sound = "CS" in a.checks   # SOUND mode: CS decides (decide_sound), build/export are untrusted',
    '    a.sound = "CS" in a.checks   # SOUND mode: CS decides (decide_sound), build/export are untrusted\n'
    '    a.notary = "CN" in a.checks  # NOTARY mode (additive): CN decides (decide_notary)',
    "a.notary flag"
)

# Ensure challenge-sha256 requirement in notary mode matches sound mode
fv_new = sub_once(
    fv_new,
    'if getattr(a, "sound", False) and info.get("source") == "given" and not getattr(a, "challenge_sha256", None):',
    'if (getattr(a, "sound", False) or getattr(a, "notary", False)) and info.get("source") == "given" and not getattr(a, "challenge_sha256", None):',
    "notary challenge_sha256 check"
)

for path, old, new in ((cfg_path, cfg_old, cfg_new), (fv_path, fv_old, fv_new)):
    diff = "".join(difflib.unified_diff(
        old.splitlines(keepends=True), new.splitlines(keepends=True),
        fromfile=f"a/{os.path.relpath(path, fv)}", tofile=f"b/{os.path.relpath(path, fv)}"
    ))
    print(diff if diff else f"(no change for {path})")
    if mode == "--apply" and diff:
        tmp = path + f".tmp.{os.getpid()}"
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(new)
        os.replace(tmp, path)
        print(f"APPLIED -> {path}")
PY
