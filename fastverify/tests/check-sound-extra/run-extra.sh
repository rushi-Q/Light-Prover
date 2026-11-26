#!/bin/bash
# check-sound-extra/run-extra.sh [PKG_ROOT]: three cases that kill check-sound.sh mutants surviving check/sound/test/run.sh.
#  1 env-pollution-tmpdir-good : TMPDIR / BASH_ENV of the caller must not matter (the env -i re-exec; SH-0001/SH-0003 survive
#                                run.sh's env-pollution case because runj's own env -i already clears those variables)
#  2 basis-recorded-accept     : the ACCEPTED JSON names its verdict basis (SH-0331 deletes BASIS= and survives)
#  4 empty-targets-config      : a comparator config naming no theorem and no definition must give no verdict (ccmp's
#                                'nothing to check' refusal -> exit 2 -> check-sound line 500; CCmp-0048 drops the refusal and
#                                then ACCEPTS any kernel-valid export: it survives every soundness-suite corpus)
#  3 pin-changed-during-run    : a pinned file replaced/changed DURING the run (here: appended to by an outside process while
#                                the second kernel runs) -> no verdict (end-of-run re-hash; SH-0329/SH-0330 survive run.sh)
set -u
PKG=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
H=$PKG/check/sound; CS=$H/check-sound.sh
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$H/pins.env"; }
GOOD=$(pin selftest_good); CHAL=$(pin selftest_challenge); CFG=$(pin selftest_comparator)
W=$(mktemp -d "${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}/checkSound-extra.XXXXXX") || exit 2; trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
pass=0; fail=0
res() { if [ "$2" = ok ]; then echo "PASS $1: $3"; pass=$((pass+1)); else echo "FAIL $1: $3"; fail=$((fail+1)); fi; }
# 1
env TMPDIR=/nonexistent/tmp BASH_ENV=/nonexistent/tmp/env "$CS" "$GOOD" "$CHAL" "$CFG" --threads 4 > "$W/o1" 2>&1; rc=$?
[ "$rc" = 0 ] && res env-pollution-tmpdir-good ok "exit 0" || res env-pollution-tmpdir-good bad "expected exit 0, got $rc :: $(tail -1 "$W/o1" | cut -c1-200)"
# 2
"$CS" "$GOOD" "$CHAL" "$CFG" --threads 4 > "$W/o2" 2>&1; rc=$?
if [ "$rc" = 0 ] && tail -1 "$W/o2" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); b=j.get("basis") or ""; sys.exit(0 if ("gruszka" in b and "kernel" in b and "comparator" in b) else 1)'; then
  res basis-recorded-accept ok "basis present"; else res basis-recorded-accept bad "exit $rc, basis: $(tail -1 "$W/o2" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("basis"))' 2>&1 | cut -c1-120)"; fi
# 3 package copy whose gruszka pin is a wrapper that waits 4 s on the judged export (then runs the real gruszka)
d=$W/pkg; mkdir -p "$d/check" "$d/lib" "$d/config"; cp -r "$H" "$d/check/sound"; [ -d "$PKG/check/xversion" ] && cp -r "$PKG/check/xversion" "$d/check/xversion"; cp "$PKG/lib/toolchain.py" "$d/lib/"; cp -r "$PKG/toolchains" "$d/"; cp "$PKG/config/components.json" "$d/config/"
printf '#!/bin/sh\ncase "$1" in */solution.export) sleep 4;; esac\nexec "%s" "$@"\n' "$(pin gruszka)" > "$d/slow-kernel"; chmod 755 "$d/slow-kernel"
s=$(sha256sum "$d/slow-kernel" | cut -d' ' -f1)
awk -v p="$d/slow-kernel" -v s="$s" '$1=="PIN" && $2=="gruszka" {print "PIN gruszka " s " " p; next} {print}' "$H/pins.env" > "$d/check/sound/pins.env"
( sleep 2; echo "# changed during the run" >> "$d/slow-kernel" ) &
"$d/check/sound/check-sound.sh" "$GOOD" "$CHAL" "$CFG" --threads 4 > "$W/o3" 2>&1; rc=$?; wait
if [ "$rc" = 2 ] && grep -q 'changed during the run' "$W/o3"; then res pin-changed-during-run ok "exit 2 (pinned file changed)"; else res pin-changed-during-run bad "expected exit 2 + 'changed during the run', got $rc :: $(tail -1 "$W/o3" | cut -c1-200)"; fi
# 4
printf '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":[],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}' > "$W/empty.json"
"$CS" "$GOOD" "$CHAL" "$W/empty.json" --threads 4 > "$W/o4" 2>&1; rc=$?
[ "$rc" = 2 ] && res empty-targets-config ok "exit 2 :: $(tail -1 "$W/o4" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read())["reason"][:100])')" || res empty-targets-config bad "expected exit 2, got $rc :: $(tail -1 "$W/o4" | cut -c1-200)"
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]
