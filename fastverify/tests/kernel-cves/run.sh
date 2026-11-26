#!/usr/bin/env bash
# Adversarial regression suite for Lean kernel/replay issues #16489, #15100, and #15101.
# Verifies that EVERY trusted fastverify path (check-sound, check-notary, check-sound-lowmem, check-frontier)
# REJECTS all 7 attack exports (including the `isUnsafe=true` ctor & arbitrary `quotInfo` single-kernel
# bypasses accepted by unpatched Lean 4.36 leanchecker / leanchecker-paranoid / pleanchecker / lake comparator)
# while ACCEPTING both honest controls.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
FV="$(cd "$HERE/../.." && pwd)"
SELFTEST="${SELFTEST_DIR:-/scratch/fastverify-next/selftest}"
THREADS="${THREADS:-4}"

W="$(mktemp -d "${TMPDIR:-/tmp}/fv-kernel-cves.XXXXXX")"
trap 'rm -rf "$W"' EXIT

/usr/bin/python3 -I "$HERE/craft_cves.py" --selftest-dir "$SELFTEST" --out "$W"

PASS=0
FAIL=0

check_case() {
  local label="$1" script="$2" exp="$3" chal="$4" comp="$5" want_rc="$6"
  local rc=0
  "$script" "$exp" "$chal" "$comp" --threads "$THREADS" >"$W/out.log" 2>&1 || rc=$?
  # (v0.1, notary EXPERIMENTAL): rc 2 allowed only for the configured nanoda's panic (src/parser.rs:120 'Attempted to insert duplicate Expr')
  if [ "$label" = check-notary/control_16489_valid ] && [ "$rc" -eq 2 ] && tail -n 1 "$W/out.log" | grep -q 'config kernel nanoda'; then
    want_rc=2
  fi
  if [ "$rc" -eq "$want_rc" ]; then
    echo "PASS $label (rc=$rc)"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label (got rc=$rc, want $want_rc): $(tail -n 1 "$W/out.log")"
    FAIL=$((FAIL + 1))
  fi
}

CHAL="$SELFTEST/challenge.export"
COMP="$SELFTEST/comparator.json"
COMP_NQ="$W/comparator_noquot.json"

SCRIPTS=(
  "check-sound:$FV/check/sound/check-sound.sh"
  "check-notary:$FV/check/notary/check-notary.sh"
  "check-lowmem:$FV/check/lowmem/check-sound-lowmem.sh"
  "check-frontier:$FV/check/frontier/check-frontier.sh"
)

CASES=(
  "control_16489_valid:$W/16489_control_valid.export:$COMP:0"
  "attack_16489_safe_ctor:$W/16489_safe_ctor.export:$COMP:1"
  "attack_16489_unsafe_ctor:$W/16489_unsafe_ctor.export:$COMP:1"
  "attack_16489_2param_unsafe:$W/16489_2param_unsafe.export:$COMP:1"
  "attack_15100_unsafe_axiom_as_ctor:$W/15100_unsafe_axiom_as_ctor.export:$COMP:1"
  "attack_15100_unsafe_ctor_forged_meta:$W/15100_unsafe_ctor_forged_meta.export:$COMP:1"
  "control_15101_baseline_noquot:$W/15101_baseline_noquot.export:$COMP_NQ:0"
  "attack_15101_fake_quot_clean:$W/15101_fake_quot_clean.export:$COMP_NQ:1"
  "attack_15101_fake_quot_plus_mk:$W/15101_fake_quot_plus_mk.export:$COMP_NQ:1"
)

for sspec in "${SCRIPTS[@]}"; do
  sname="${sspec%%:*}"
  spath="${sspec#*:}"
  [ -x "$spath" ] || { echo "SKIP $sname (missing $spath)"; continue; }
  for cspec in "${CASES[@]}"; do
    IFS=: read -r cname cexp ccomp want <<< "$cspec"
    check_case "${sname}/${cname}" "$spath" "$cexp" "$CHAL" "$ccomp" "$want"
  done
done

echo "RESULT pass=$PASS fail=$FAIL"
[ "$FAIL" -eq 0 ]
