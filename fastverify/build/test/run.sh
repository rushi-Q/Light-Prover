#!/bin/bash
# build/test/run.sh [WORK] : component test of the fast build stage (no Mathlib needed, ~1 min, any host)
#   projects/libs-options   two libs, package + lib leanOptions, moreLeanArgs            -> SAME (every artifact byte-identical)
#   projects/module-system  public/private/import all/meta imports + non-module importer -> SAME (setup.json importArts exact)
#   projects/self-modifying module A rewrites B.lean while the build runs               -> DECLINED (sources changed)
#   projects/olean-tamper   module B appends to A.olean after A was built               -> DECLINED (outputs changed)
#   projects/modify-restore A rewrites B.lean before B compiles, C restores it          -> DECLINED (per-module source check)
#   projects/env-probe      prints LEAN_PATH, cwd, argv, child env as an error         -> identical message in both builds
#   projects/fast-exact     with_unfolding_all exact forms; B3 --unsafe fast-exact      -> SAME + plugin decision log
# and the menu options: --preset B2 (early release) SAME/DECLINED as B1; --unsafe ... runs and is marked "exact": false
# The crafted attack projects (78 dirs, need the Mathlib workspace) are run with cmp_official.sh.
# Prints PASS/FAIL per case and 'RESULT: PASS|FAIL'; exit 0 iff all pass.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
W=${1:-/tmp/fv-buildtest-$$}; mkdir -p "$W"
# the test projects have no dependencies (manifest.py binds nothing): an existing workspace, else an empty one in W
# (never create $FV_PACKAGES: an empty directory there would look like a workspace to later tests)
if [ -d "${FV_PACKAGES:-}" ]; then WS=$FV_PACKAGES; else WS=$W/no-packages; mkdir -p "$WS"; fi
fail=0
check() { # name expected [build.sh args...]
  local n=$1 e=$2; shift 2
  local out; out=$(FASTARGS="$*" "$H/cmp_official.sh" "$H/projects/$n" "$W/$n${1:+-$(echo "$*" | tr -c 'A-Za-z0-9\n' _)}" "$WS" 2>&1 | tail -1)
  case "$out" in "CMP: $e"*) echo "PASS $n ${*:-B1}: $out";; *) echo "FAIL $n ${*:-B1}: expected $e, got: $out"; fail=1;; esac
}
check libs-options SAME
check module-system SAME
check self-modifying DECLINED
check olean-tamper DECLINED
check modify-restore DECLINED
# env-probe: the module reports (as an error message) what lean sees: LEAN_PATH, cwd, its own argv and the full
# environment of a child process; both builds fail with that message, which must be identical (finding 069 class)
check env-probe SAME
# official-build.sh passes --threads to lake as LEAN_NUM_THREADS (documented in docs/reference/options.md, B0), which a
# plain `lake build` does not set and build.sh does not either: that one variable is left out of the comparison
off=$(grep -o 'PROBE.*' "$W/env-probe/log-off/build.log" | head -1 | sed 's/ \[[0-9.]*m\?s\]$//; s/ENV=LEAN_NUM_THREADS=[0-9]*;/ENV=/; s/;LEAN_NUM_THREADS=[0-9]*;/;/')
fast=$(/usr/bin/python3 -I -c 'import json,sys
for l in open(sys.argv[1]):
    if l.startswith("{"):
        r=json.loads(l)
        for ln in r.get("stdout_head","").split("\n"):
            if "PROBE" in ln: print(json.loads(ln)["data"])' "$W/env-probe/log-fast/sched.out" | head -1)
if [ -n "$off" ] && [ "$off" = "$fast" ]; then echo "PASS env-probe: lean's LEAN_PATH/cwd/argv/environment identical under lake build and build.sh"
else echo "FAIL env-probe: official '$(echo "$off" | cut -c1-200)' vs fast '$(echo "$fast" | cut -c1-200)'"; fail=1; fi
# menu: B2 (early release) must be exact too; B3 (unsafe) must run and be marked exact:false
check libs-options SAME --preset B2
check module-system SAME --preset B2
check olean-tamper DECLINED --preset B2
b3=$(FASTARGS="--preset B3 --unsafe skip-kernel-tc,linter-off,retries" "$H/cmp_official.sh" "$H/projects/libs-options" "$W/b3" "$WS" 2>&1 | tail -1)
if grep -q '"exact": false' "$W/b3/fast.json" && grep -q '"status": "BUILT"' "$W/b3/fast.json"; then echo "PASS libs-options B3: built, marked exact:false ($b3)"
else echo "FAIL libs-options B3: $(cat "$W/b3/fast.json" | tail -1 | cut -c1-200)"; fail=1; fi
# B3 item fast-exact (sound mode; plugins/LightFastExact.lean): a toy with every form the plugin handles or
# declines (inner fast path, inner+outer, kernel says no -> coercion by the official tactic, metavariables -> official
# tactic, typed ascription) -> every artifact byte-identical to the official lake build; plus the plugin's decision log
check fast-exact SAME --preset B3 --unsafe fast-exact,skip-kernel-tc
fxd=$(ls -d "$W"/fast-exact-*preset_B3* 2>/dev/null | head -1)
fxlog=$(cd "$H/projects/fast-exact" && env -i PATH=/usr/bin:/bin LIGHT_FASTEXACT_DEBUG=1 \
  "${FV_TC:-${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}}/bin/lean" --plugin="$fxd/log-fast/fastexact/libLightFastExact.so" \
  src/FX/A.lean 2>&1)
nok=$(echo "$fxlog" | grep -c '^fx: ok'); nout=$(echo "$fxlog" | grep -c '^fx-outer: ok')
nno=$(echo "$fxlog" | grep -c 'KERNEL-NO'); nfb=$(echo "$fxlog" | grep -c 'fallback to the official')
if [ "$nok" -ge 3 ] && [ "$nout" = 1 ] && [ "$nno" = 1 ] && [ "$nfb" = 2 ]; then
  echo "PASS fast-exact plugin decisions: $nok inner fast, $nout outer fast, $nno kernel-no, $nfb official fallbacks"
else echo "FAIL fast-exact plugin decisions: ok=$nok outer=$nout kernel-no=$nno fallback=$nfb: $(echo "$fxlog" | head -5 | tr '\n' ' ' | cut -c1-300)"; fail=1; fi
[ $fail = 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL"
exit $fail
