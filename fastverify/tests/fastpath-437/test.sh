#!/bin/bash
# tests/fastpath-437/test.sh [WORK]  -- the fast build + export path on Lean 4.37.0-rc1 (or FV_RELEASE=4.36.0)
# (component test, no Mathlib, ~4 min, any test host with the 4.37.0-rc1 toolchain in
# config/components.json):
#   (1) build: two build-test projects (libs-options; module-system with public/private/import all/meta imports) switched
#       to 4.37.0-rc1, built by build.sh --preset B3 --unsafe sound-fast-path (Planner435.lean, Lake 4.37 port) and by the
#       sandboxed official 4.37 `lake build`: every artifact byte-identical (build/test/cmp_official.sh) -> PASS;
#   (2) the exact presets still DECLINE for 4.37 (B1: exactness not claimed yet);
#   (3) the measured --preset sound item list (toolchain-T1 of 4.33.1 trees, zygote, merge, fast-exact, premise-off, ...)
#       builds a 4.37 project: toolchain-T1 is "not applicable" (no tree of this release), the zygote items are dropped,
#       the build is never done with a lean of another release;
#   (4) export: export.sh --verify on the module-system build: the 4.37 native exporter (components.json natives_other)
#       runs and is byte-identical to the release's bundled leanexport.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FV_PKG:-$(cd "$H/../.." && pwd)}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/fastpath-437.XXXXXX")}; rm -rf "$W"; mkdir -p "$W/ws"; W=$(readlink -f "$W")
R=${FV_RELEASE:-4.37.0-rc1}; fail=0   # FV_RELEASE=4.36.0: the same checks for 4.36.0 (Planner435 + the 4.36 native exporter)
TC=$(python3 -I -c 'import json,sys; t=json.load(open(sys.argv[1]))["lean_toolchains"].get("leanprover/lean4:v"+sys.argv[2]); print(t["prefix"] if t else "")' "$FV/config/components.json" "$R")
if [ -z "$TC" ] || [ ! -x "$TC/bin/lean" ]; then echo "SKIP: $R not in config/components.json (tools/addrelease.py) or not installed here"; echo "RESULT: SKIP"; exit 0; fi
for p in libs-options module-system; do
  rm -rf "$W/src-$p"; cp -a "$FV/build/test/projects/$p" "$W/src-$p"; echo "leanprover/lean4:v$R" > "$W/src-$p/lean-toolchain"
  out=$(FASTARGS="--preset B3 --unsafe sound-fast-path" "$FV/build/test/cmp_official.sh" "$W/src-$p" "$W/w-$p" "$W/ws" "$TC" 2>&1 | tail -1)
  case "$out" in "CMP: SAME"*) echo "PASS $p B3 sound-fast-path: $out";; *) echo "FAIL $p B3: $out"; fail=1;; esac
done
out=$(FASTARGS="" "$FV/build/test/cmp_official.sh" "$W/src-libs-options" "$W/w-b1" "$W/ws" "$TC" 2>&1 | tail -1)
case "$out" in "CMP: DECLINED"*"sound build only"*) echo "PASS B1 declines for $R (exactness not claimed)";; *) echo "FAIL B1: $out"; fail=1;; esac
FULL="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,merge,check-tail"
rm -rf "$W/full"; mkdir -p "$W/full"; cp -a "$W/src-module-system" "$W/full/proj"; rm -rf "$W/full/proj/.lake"
"$FV/build/build.sh" "$W/full/proj" "$W/ws" "$TC" --log "$W/full/log" --threads 8 --preset B3 --unsafe "$FULL" > "$W/full/fast.json" 2> "$W/full/fast.err"; frc=$?
if [ $frc = 0 ] && grep -q '"toolchain-T1:not-applicable(release)"' "$W/full/fast.json" && grep -q 'zygote items dropped' "$W/full/fast.err" \
   && ! grep -q '"zygote"' "$W/full/fast.json" && ! grep -rq -- '--lean /scratch/fastverify-next/tc' "$W/full/log/sched.out" 2>/dev/null; then
  echo "PASS sound item list on $R: built with the official $R lean (T1 not applicable, zygote dropped)"
else echo "FAIL sound item list on $R: exit $frc $(tail -1 "$W/full/fast.json" | cut -c1-300)"; fail=1; fi
P=$W/w-module-system/proj
printf 'Nat.add\nList\n' > "$W/tg.txt"
"$FV/export/export.sh" --lean-path "$P/.lake/build/lib/lean:$TC/lib/lean" --module Top --targets-file "$W/tg.txt" --toolchain "$TC" \
   --project "$P" --out "$W/exp/out.export" --threads 4 --verify --json "$W/exp.json" > /dev/null 2>&1; erc=$?
ex=$(python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j.get("exporter"), j.get("verify"), (j.get("native") or {}).get("decline_reason"))' "$W/exp.json" 2>/dev/null)
case "$erc $ex" in "0 native identical"*) echo "PASS $R export: native exporter for $R, identical to the bundled leanexport";; *) echo "FAIL $R export: rc=$erc $ex"; fail=1;; esac
[ $fail = 0 ] && { echo "RESULT: PASS"; exit 0; } || { echo "RESULT: FAIL"; exit 1; }
