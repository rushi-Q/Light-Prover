#!/bin/bash
# option_matrix.sh [GROUP...] : run the regression tests once per MENU OPTION of the package (one entry point, a menu of
# options per stage, tests per option) and write the matrix to $FV_TEST_WORK/OPTIONS.md (tools/mk_options.py). Groups (default: all exact ones + all unsafe ones):
#   reference   --preset reference (B0+E0+C0)               all e2e/generality tests        must PASS
#   b2          --build B2 --check C3,C0                    all e2e/generality tests        must PASS
#   e0          --export E0 --check C3,C0                   exporter-relevant e2e tests     must PASS
#   unsafe-<opt> --build B3 --unsafe <opt> --check C3,C0    the findings that <opt> breaks + controls (UNSAFE-FAIL expected)
#   c3, c4, c4io       --check C3 / C4 / C4 + --unsafe ignore-order (no C0)   e2e tests (C4/C4io UNSAFE)
# (The groups fastexact = --preset fast-exact and c2 = --check C2, and C1 inside the old default '--check both', were
# dropped when check A (C1/C2) was retired; those options are refused since.)
# Export-level tests already run every check option (C3/C4 variants) in every suite run. Needs what run_all.sh needs
# (official toolchains, a work directory: FV_TEST_WORK), e.g.
#   FV_TEST_WORK=/local/disk/fvtests fastverify/tests/tools/option_matrix.sh
{ # whole script parsed before it runs
set -u
[ -n "${FV_TEST_WORK:-}" ] || { echo "option_matrix.sh: set FV_TEST_WORK (the work directory of the run_all.sh runs)" >&2; exit 2; }
T=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); R=$T/run_all.sh; J=${J:-12}
# e2e + generality tests, heavy ones (015 057: Mathlib natives / 7.6 GB workspace copies) excluded unless HEAVY=1
E2E=$(cd "$T" && for r in [0-9][0-9][0-9]-*/REPRO lake-config/REPRO challenge-config/REPRO odd-layouts/REPRO challenge-variants/REPRO; do d=$(dirname "$r"); { [ "${HEAVY:-0}" = 1 ] || ! grep -q '^# heavy' "$d/test.sh"; } && case $d in [0-9][0-9][0-9]-*) echo "${d:0:3}";; *) echo "$d";; esac; done | tr '\n' ' ')
run() { local label=$1 args=$2 ids=$3 unsafe=${4:-}; echo "=== option run $label: --fv-args '$args' ids: $ids"
  bash "$R" --jobs "$J" --label "opt-$label" --fv-args "$args" $unsafe $ids 2>&1 | grep -E '^(SUMMARY|results:)'; }
G=${*:-reference b2 e0 c3 c4 c4io unsafe-skip-kernel-tc unsafe-deny-line unsafe-linter-off unsafe-retries unsafe-toolchain-T1}
for g in $G; do case $g in
  reference) run reference "--preset reference" "$E2E";;
  b2)        run b2 "--build B2 --check C3,C0" "$E2E";;
  e0)        run e0 "--export E0 --check C3,C0" "008 010 030 lake-config challenge-config odd-layouts";;
  c3)        run c3 "--check C3" "$E2E";;
  c4)        run c4 "--check C4" "$E2E" --unsafe-run;;
  c4io)      run c4io "--check C4 --unsafe ignore-order" "$E2E" --unsafe-run;;
  unsafe-skip-kernel-tc) run unsafe-skip-kernel-tc "--build B3 --unsafe skip-kernel-tc --check C3,C0" "007 017 030 038 challenge-config" --unsafe-run;;
  unsafe-deny-line)      run unsafe-deny-line "--build B3 --unsafe deny-line --check C3,C0" "021 023 025 028 challenge-config" --unsafe-run;;
  unsafe-linter-off)     run unsafe-linter-off "--build B3 --unsafe linter-off --check C3,C0" "022 challenge-config" --unsafe-run;;
  unsafe-retries)        run unsafe-retries "--build B3 --unsafe retries --check C3,C0" "062 challenge-config" --unsafe-run;;
  unsafe-native-pkg)     run unsafe-native-pkg "--build B3 --unsafe native-pkg --check C3,C0" "015 057" --unsafe-run;;
  unsafe-toolchain-T1)   run unsafe-toolchain-T1 "--build B3 --unsafe toolchain-T1 --check C3,C0" "004 014 020 040 061 challenge-config" --unsafe-run;;
  *) echo "unknown group $g";; esac; done
python3 -I "$T/tools/mk_options.py" "$FV_TEST_WORK/OPTIONS.md"
exit 0
}
