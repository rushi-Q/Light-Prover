#!/bin/bash
# tests/ci-chain/run.sh [WORKDIR]  (kind: component, sound mode + CI tools; ~4 min, no Mathlib)
# History c0..c4 of x/c0 (libs Tiny (Tiny.A <- Tiny.B <- Solution) + Solution + Extra (Extra.X, outside the closure)):
#   c1 = c0 + new module Extra.Y          c2 = c1 with Extra.X ill-typed (outside the solution's closure)
#   c3 = c2 + a valid proof edit in Tiny.A   c4 = c3 with 'sorry' in Tiny.B
# Cases:
#   cold-clos        c0 --preset sound + closure-only + importarts-empty (no merge) --keep-work: ACCEPTED, plan = 3 of 4 modules
#   snd-clos c1..c4  tools/ci/sound-incr.sh --closure-only chain: ACC (0 dirty), ACC (0 dirty: Extra.X never built),
#                    ACC (Tiny.A + importers rebuilt), REJ (sorryAx); every rebuild re-planned with --import-arts-empty
#   off-sol c0..c4   tools/ci/official-incr.sh --solution-only (= the 4.36 lake comparator build set): ACC ACC ACC ACC REJ
#                    -> per-commit verdicts equal to the sound chain's (test oracle)
#   off-def c0..c2   tools/ci/official-incr.sh default targets: ACC ACC REJ (the broken Extra.X rejects)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/a05-ci.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"; fails=0; T=${EVAL_THREADS:-8}
WS=${FV_PACKAGES:-$(dirname "$FV")/verify/challenge}
row() { echo "$1 $2: $3"; [ "$1" = FAIL ] && fails=$((fails+1)); return 0; }
# rows of the experimental incremental CI chain (commits 1-4 through sound-incr.sh) run only with FV_TEST_EXPERIMENTAL=1
xrow() { if [ "${FV_TEST_EXPERIMENTAL:-0}" = 1 ]; then row "$@"; else echo "SKIP $2: experimental incremental CI chain (not part of the stable release)"; fi; }
# incr-reverify.sh (under sound-incr.sh) takes the official 4.33.1 toolchain from INCR_TC (default $HOME/.elan/...): give
# it the one this package registered (config/components.json), so the rows do not depend on HOME
[ -n "${INCR_TC:-}" ] || INCR_TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
[ -n "${INCR_TC:-}" ] && export INCR_TC
# ---- history
for i in 0 1 2 3 4; do cp -r "$H/x/c0" "$W/c$i"; done
for i in 1 2 3 4; do echo 'theorem extraY : True := trivial' > "$W/c$i/Extra/Y.lean"; done
for i in 2 3 4; do echo 'theorem extraX : (1 : Nat) + 1 = 3 := rfl' > "$W/c$i/Extra/X.lean"; done
for i in 3 4; do printf 'theorem tinyA (n : Nat) : n + 0 = n := by\n  simp\n' > "$W/c$i/Tiny/A.lean"; done
printf 'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  sorry\n' > "$W/c4/Tiny/B.lean"
mkdir -p "$W/R/commits"; for i in 0 1 2 3 4; do ln -s "$W/c$i" "$W/R/commits/00$i-c$i"; done
# ---- cold base (builds the challenge officially), then pin
cp -r "$H/x/challenge" "$W/ch0"
U="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path=importarts-empty,cost-hints,native-pkg,check-tail,closure-only"
"$FV/bin/fastverify" "$W/c0" "$W/ch0" "$W/base" --preset sound --unsafe "$U" --threads "$T" --keep-work --packages "$WS" > "$W/base.log" 2>&1
rc=$?; m=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).readline())["nmods"])' "$W/base/log/build-fast/plan.jsonl" 2>/dev/null)
[ $rc = 0 ] && [ "$m" = 3 ] && row PASS cold-clos "ACCEPTED, closure 3 modules" || row FAIL cold-clos "exit $rc, closure modules '$m'"
mkdir -p "$W/R/challenge"; cp "$H/x/challenge/comparator.json" "$W/R/challenge/"; cp "$W/base/challenge.export" "$W/R/challenge/"
sha256sum "$W/R/challenge/challenge.export" > "$W/R/challenge/challenge.export.sha256"
python3 -I -c 'import sys; print("\n".join(open(sys.argv[1]).read().split()))' "$W/base/log/export-targets.txt" > "$W/R/targets.txt"
# ---- chains
export R=$W/R WS FV T
# incr-reverify.sh (under sound-incr.sh) needs the caller's comparator pin too; the per-commit dirty / import-arts rows
# exercise the EXPERIMENTAL incremental machinery, so that is requested where the package has the flag
CPIN=$(sha256sum < "$W/R/challenge/comparator.json" | cut -c1-64)
XINC=(); grep -q -- '--experimental-incremental' "$FV/tools/incr/incr-reverify.sh" && XINC=(--experimental-incremental)
BASE=$W/base TSV=$W/snd.tsv bash "$FV/tools/ci/ci-chain.sh" snd-clos 1 4 --comparator-sha256 "$CPIN" "${XINC[@]}" > "$W/snd.log" 2>&1
TSV=$W/sol.tsv bash "$FV/tools/ci/ci-chain.sh" off-sol 0 4 > "$W/sol.log" 2>&1
TSV=$W/def.tsv bash "$FV/tools/ci/ci-chain.sh" off-incr 0 2 > "$W/def.log" 2>&1
col() { cut -f3 "$1" | tr '\n' ' ' | sed 's/ $//'; }
# the EXPERIMENTAL incremental machinery reports its ACCEPTED / REJECTED as NO VERDICT (exit 2) + "provisional": that
# counts here as the machinery's own exit 0 / 1 (the rows test the machinery, not a counted verdict)
sndx() { local out=""; for f in "$W"/R/ci/snd-clos/00[1-4]-*/summary.json; do
    out="$out $(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); e=r.get("exit"); p=r.get("provisional")
print({"ACCEPTED": 0, "REJECTED": 1}.get(p, e) if e == 2 else e)' "$f" 2>/dev/null || echo x)"; done; echo "${out# }"; }
s=$(col "$W/snd.tsv"); [ ${#XINC[@]} -gt 0 ] && s=$(sndx); o=$(col "$W/sol.tsv"); d=$(col "$W/def.tsv")
[ "$s" = "0 0 0 1" ] && xrow PASS snd-clos "exits $s" || xrow FAIL snd-clos "exits '$s' (want 0 0 0 1)"
[ "$o" = "0 0 0 0 1" ] && row PASS off-sol "exits $o" || row FAIL off-sol "exits '$o' (want 0 0 0 0 1)"
[ "$(echo "$o" | cut -d' ' -f2-)" = "$s" ] && xrow PASS oracle "sound chain = lake-comparator build set on c1..c4" || xrow FAIL oracle "sound '$s' vs official '$o'"
[ "$d" = "0 0 1" ] && row PASS off-def "exits $d (Extra.X outside the closure rejects with default targets)" || row FAIL off-def "exits '$d' (want 0 0 1)"
dz=$(python3 -I - "$W/R/ci/snd-clos" <<'PY'
import glob, json, sys
out = []
for d in sorted(glob.glob(sys.argv[1] + "/00[1-4]-*/summary.json")):
    a = json.load(open(d))["attempts"][-1]; out.append(f"{a.get('dirty')}")
print(" ".join(out))
PY
)
case "$dz" in "0 0 "[1-3]" "*) xrow PASS dirty "dirty per commit: $dz (Extra.* never rebuilt)";; *) xrow FAIL dirty "dirty per commit: '$dz'";; esac
ia=$(grep -l '"import_arts_empty": true' "$W"/R/ci/snd-clos/00*/a*/build.json 2>/dev/null | wc -l)
[ "$ia" -ge 3 ] && row PASS import-arts-empty "re-planned with --import-arts-empty in $ia attempts" || row FAIL import-arts-empty "only $ia attempts"
for x in "$W"/base/solution.export "$W"/R/ci/snd-clos/*/a*/solution.export; do E=$(readlink -f "$x"); case "$E" in /dev/shm/*) rm -rf "$(dirname "$E")";; esac; done
[ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"
echo "RESULT $([ $fails = 0 ] && echo PASS || echo FAIL) fails=$fails"
[ $fails = 0 ]
