#!/bin/bash
# tests/package/run.sh [WORKDIR]   -- orchestrator-level regression tests of bin/fastverify, ~1 min, any host.
# Each case prints "PASS|FAIL <name>: <what>"; last line "RESULT: PASS|FAIL"; exit 0 iff all pass.
# Covers the package-level fixes: 067 (OUT must be empty: state never reused), 066 (shipped PROJECT/.lake ignored),
# 016 (caller environment cannot influence the run: bin/fastverify runs under env -i), 036/001 (a component that is not
# pinned / cannot start makes the run refuse instead of silently degrading), refusals instead of verdicts for inputs the
# package cannot judge exactly (unsupported toolchain, special files, symlinks leaving the project, export-targets.txt
# inconsistent with comparator.json, dependency revision mismatch, OUT inside PROJECT, an unconfigured package copy),
# official verdicts on toy projects, the option menu (preset reference, the retired preset fast-exact is refused, the
# former default combination without check A = C3,C0, C4 = UNSAFE trust label, unsafe build options need B3). 20 cases,
# ~3 min. Run it from a frozen snapshot: a stage script replaced during a run makes that run end in ERROR by design
# (end-of-run re-verification). (Check A = C1/C2 and the presets fast-exact/default were retired: cases 12,
# 16 and 18 used them; tests/package/retired-checkA.sh covers every retired option.)
set -u
T=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=$(cd "$T/../.." && pwd); FV=$PKG/bin/fastverify
W=${1:-${TMPDIR:-/tmp}/$USER-fvpkg-$$}; rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
# inputs shipped with the repository: the X011 / X002 toy snapshots of tests 011 / 002, and data/ (SHA256SUMS)
X011=$PKG/tests/011-pipeline-ignores-the-project-lakefile-ha/x
X002=$PKG/tests/002-run-sh-and-with-kernel-sh-path-no-challe/x
(cd "$T/data" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: tests/package/data does not match SHA256SUMS"; echo "RESULT: FAIL (1)"; exit 1; }
# the trusted Mathlib workspace (only row 11 needs it): $FV_PACKAGES, else <repository root>/verify/challenge
WS=${FV_PACKAGES:-$(dirname "$PKG")/verify/challenge}
FAILS=0; SKIPS=0
ok() { echo "PASS $1: $2"; }
bad() { echo "FAIL $1: $2"; FAILS=$((FAILS+1)); }
skip() { echo "SKIP $1: $2"; SKIPS=$((SKIPS+1)); }   # neither PASS nor FAIL
verdict() { /usr/bin/python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r.get("verdict"), "|", r.get("verdict_basis"))' "$1/result.json" 2>/dev/null; }

# toy project + challenge (no dependencies): X011 case b (honest) and case a (warningAsError + sorry)
CH=$W/challenge; cp -a "$X011/challenge" "$CH"
P_OK=$W/p-ok; cp -a "$X011/proj/b" "$P_OK"
P_BAD=$W/p-bad; cp -a "$X011/proj/a" "$P_BAD"

# 1. honest toy: ACCEPTED by the official comparator, exit 0
"$FV" "$P_OK" "$CH" "$W/o1" --check official > "$W/o1.log" 2>&1; rc=$?
v=$(verdict "$W/o1"); [ $rc = 0 ] && [[ "$v" == ACCEPTED* ]] && ok official-accept "rc=$rc $v" || bad official-accept "rc=$rc $v"
# 2. build failure: REJECTED, exit 1
"$FV" "$P_BAD" "$CH" "$W/o2" --check official > "$W/o2.log" 2>&1; rc=$?
v=$(verdict "$W/o2"); [ $rc = 1 ] && [[ "$v" == REJECTED* ]] && ok build-reject "rc=$rc $v" || bad build-reject "rc=$rc $v"
# 3. (067) OUT not empty -> refuse, nothing overwritten
mkdir -p "$W/o3"; echo keep > "$W/o3/marker"
"$FV" "$P_OK" "$CH" "$W/o3" --check official > "$W/o3.log" 2>&1; rc=$?
[ $rc = 2 ] && [ "$(cat "$W/o3/marker")" = keep ] && [ ! -e "$W/o3/result.json" ] && ok out-not-empty "rc=$rc" || bad out-not-empty "rc=$rc"
# 4. (066) shipped .lake/build of a DIFFERENT (failing) source is ignored: p-bad sources + p-ok's built .lake -> still REJECTED
P_SHIP=$W/p-ship; cp -a "$P_BAD" "$P_SHIP"; mkdir -p "$P_SHIP/.lake/build/lib/lean"; echo garbage > "$P_SHIP/.lake/build/lib/lean/Main.olean"
"$FV" "$P_SHIP" "$CH" "$W/o4" --check official > "$W/o4.log" 2>&1; rc=$?
v=$(verdict "$W/o4"); [ $rc = 1 ] && ok shipped-lake-ignored "rc=$rc $v" || bad shipped-lake-ignored "rc=$rc $v"
# 5. (016) a polluted caller environment changes nothing (same verdict, same export sha)
env KC_AXIOMS=sorryAx KC_THEOREMS=x CCMP_LEANCHECKER=/bin/true LEAN_PATH=/nonexistent LEAN_ABORT_ON_PANIC=0 \
    PYTHONPATH=/nonexistent PYTHONSTARTUP=/nonexistent PATH=/nonexistent:$PATH HOME=/nonexistent \
    "$FV" "$P_OK" "$CH" "$W/o5" --check official > "$W/o5.log" 2>&1; rc=$?
s1=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["export"].get("sha256"))' "$W/o1/result.json" 2>/dev/null)
s5=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["export"].get("sha256"))' "$W/o5/result.json" 2>/dev/null)
[ $rc = 0 ] && [ -n "$s1" ] && [ "$s1" = "$s5" ] && ok env-pollution "rc=$rc sha=${s5:0:16}" || bad env-pollution "rc=$rc $s1 vs $s5"
# 6. unsupported toolchain -> ERROR (exit 2), not a verdict
P_TC=$W/p-tc; cp -a "$P_OK" "$P_TC"; echo "leanprover/lean4:v4.34.0" > "$P_TC/lean-toolchain"
CH_TC=$W/challenge-tc; cp -a "$CH" "$CH_TC"; echo "leanprover/lean4:v4.34.0" > "$CH_TC/lean-toolchain"
"$FV" "$P_TC" "$CH_TC" "$W/o6" --check official > "$W/o6.log" 2>&1; rc=$?
v=$(verdict "$W/o6"); [ $rc = 2 ] && [[ "$v" == ERROR* ]] && ok unsupported-toolchain "rc=$rc $v" || bad unsupported-toolchain "rc=$rc $v"
# 7. project/challenge toolchain mismatch -> ERROR
"$FV" "$P_TC" "$CH" "$W/o7" --check official > "$W/o7.log" 2>&1; rc=$?
[ $rc = 2 ] && ok toolchain-mismatch "rc=$rc $(verdict "$W/o7")" || bad toolchain-mismatch "rc=$rc"
# 8. a FIFO in the project -> ERROR (the copy would hang)
P_FIFO=$W/p-fifo; cp -a "$P_OK" "$P_FIFO"; mkfifo "$P_FIFO/src/pipe"
timeout 300 "$FV" "$P_FIFO" "$CH" "$W/o8" --check official > "$W/o8.log" 2>&1; rc=$?
[ $rc = 2 ] && ok special-file "rc=$rc $(verdict "$W/o8")" || bad special-file "rc=$rc"
# 9. a symlink leaving the project -> ERROR
P_LNK=$W/p-lnk; cp -a "$P_OK" "$P_LNK"; ln -s /etc/hostname "$P_LNK/src/Leak.lean"
"$FV" "$P_LNK" "$CH" "$W/o9" --check official > "$W/o9.log" 2>&1; rc=$?
[ $rc = 2 ] && ok symlink-outside "rc=$rc $(verdict "$W/o9")" || bad symlink-outside "rc=$rc"
# 10. export-targets.txt inconsistent with comparator.json -> ERROR
CH_T=$W/challenge-t; cp -a "$CH" "$CH_T"; sed -i 's/riemannHypothesis//' "$CH_T/export-targets.txt"
"$FV" "$P_OK" "$CH_T" "$W/o10" --check official > "$W/o10.log" 2>&1; rc=$?
[ $rc = 2 ] && ok targets-inconsistent "rc=$rc $(verdict "$W/o10")" || bad targets-inconsistent "rc=$rc"
# 11. dependency at a revision the trusted workspace does not have -> ERROR (no network, no guessing)
if [ -f "$WS/lake-manifest.json" ] && [ -d "$WS/.lake/packages" ]; then
P_DEP=$W/p-dep; cp -a "$P_OK" "$P_DEP"
/usr/bin/python3 -I - "$P_DEP/lake-manifest.json" "$WS/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[2]))
m["packages"][0]["rev"] = "0" * 40
json.dump(m, open(sys.argv[1], "w"), indent=1)
PY
"$FV" "$P_DEP" "$CH" "$W/o11" --check official --packages "$WS" > "$W/o11.log" 2>&1; rc=$?
[ $rc = 2 ] && grep -q "differs\|rev" "$W/o11.log" && ok dependency-mismatch "rc=$rc $(verdict "$W/o11")" || bad dependency-mismatch "rc=$rc"
else
  skip dependency-mismatch "no trusted Mathlib workspace at $WS (set FV_PACKAGES)"
fi
# 12. (036/001) --require-fast refuses when a fast component is not usable, instead of silently degrading (fast check: C3)
"$FV" "$P_OK" "$CH" "$W/o12" --check C3 --require-fast --build official > "$W/o12.log" 2>&1; rc=$?
pf=$("$FV" "$P_OK" "$CH" "$W/o12pf" --check C3 --build official --preflight-only 2>/dev/null | tail -1)
if [[ "$pf" == *"preflight OK"* ]]; then
  [ $rc != 2 ] && ok require-fast "checkB usable: run rc=$rc" || bad require-fast "checkB usable but refused"
else
  [ $rc = 2 ] && ok require-fast "checkB not usable here -> refused (rc=$rc)" || bad require-fast "rc=$rc although: $pf"
fi
# 13. --export with a crafted wrong-statement export (X002): official REJECTED
TOY=$X002/toy/wrongstmt
CH_E=$W/challenge-e; mkdir -p "$CH_E"; cp "$TOY/challenge.export" "$CH_E/"; cp "$T/data/comparator-rh.json" "$CH_E/comparator.json"
"$FV" - "$CH_E" "$W/o13" --export "$TOY/solution.export" --check official > "$W/o13.log" 2>&1; rc=$?
v=$(verdict "$W/o13"); [ $rc = 1 ] && [[ "$v" == REJECTED* ]] && ok export-mode-reject "rc=$rc $v" || bad export-mode-reject "rc=$rc $v"

# 14. OUT inside PROJECT (the copy would recurse) -> refuse
P_IN=$W/p-in; cp -a "$P_OK" "$P_IN"
"$FV" "$P_IN" "$CH" "$P_IN/out" --check official > "$W/o14.log" 2>&1; rc=$?
[ $rc = 2 ] && [ ! -e "$P_IN/out/result.json" ] && ok out-inside-project "rc=$rc" || bad out-inside-project "rc=$rc"

# 15-19. the option menu: presets and trust labels on the honest toy
tr() { /usr/bin/python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r.get("verdict"), r.get("trust"), r["build"].get("option"), r["export"].get("option"), ",".join(k+":"+str(v.get("verdict")) for k,v in sorted(r["checks"].items())))' "$1/result.json" 2>/dev/null; }
"$FV" "$P_OK" "$CH" "$W/o15" --preset reference > "$W/o15.log" 2>&1; rc=$?; v=$(tr "$W/o15")
[ $rc = 0 ] && [[ "$v" == "ACCEPTED official B0 E0 official:ACCEPTED" ]] && ok preset-reference "$v" || bad preset-reference "rc=$rc $v"
"$FV" "$P_OK" "$CH" "$W/o16" --preset fast-exact --build B1 > "$W/o16.log" 2>&1; rc=$?   # retired: refused
[ $rc = 2 ] && [ ! -e "$W/o16" ] && grep -q -- "--preset sound" "$W/o16.log" && ok preset-fast-exact-retired "rc=$rc refused" || bad preset-fast-exact-retired "rc=$rc $(tail -1 "$W/o16.log" | cut -c1-200)"
"$FV" "$P_OK" "$CH" "$W/o17" --check C4 --build B1 > "$W/o17.log" 2>&1; rc=$?; v=$(tr "$W/o17")
[[ "$v" == *" UNSAFE "* ]] && ok check-C4-unsafe "rc=$rc $v" || bad check-C4-unsafe "rc=$rc $v"
"$FV" "$P_OK" "$CH" "$W/o18" --check C3,C0 --build B1 > "$W/o18.log" 2>&1; rc=$?; v=$(tr "$W/o18")   # former default minus C1
[ $rc = 0 ] && [[ "$v" == "ACCEPTED official "* ]] && ok default-combination-without-C1 "$v" || bad default-combination-without-C1 "rc=$rc $v"
"$FV" "$P_OK" "$CH" "$W/o19" --check official --unsafe skip-kernel-tc > "$W/o19.log" 2>&1; rc=$?
[ $rc = 2 ] && grep -q "need --build B3" "$W/o19.log" && ok unsafe-needs-B3 "rc=$rc" || bad unsafe-needs-B3 "rc=$rc"

# 20. an unconfigured package copy (components.json = the template with ${...} variables) refuses with exit 2
PC=$W/pkgcopy; mkdir -p "$PC"; cp -a "$PKG/bin" "$PKG/lib" "$PKG/config" "$PC/"
cp "$PKG/config/components.template.json" "$PC/config/components.json"
"$PC/bin/fastverify" "$P_OK" "$CH" "$W/o20" --preset reference > "$W/o20.log" 2>&1; rc=$?
[ $rc = 2 ] && grep -q "configure.py" "$W/o20.log" && ok unconfigured-package "rc=$rc" || bad unconfigured-package "rc=$rc"

echo "RESULT: $([ $FAILS = 0 ] && echo PASS || echo "FAIL ($FAILS)")$([ $SKIPS = 0 ] || echo " ($SKIPS SKIP)")  (work dir $W)"
[ $FAILS = 0 ]
