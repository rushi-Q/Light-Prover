#!/bin/bash
# tests/reference-release/run.sh [WORKDIR] -- regression test: --preset reference judges with the challenge's own release (HIGH):
# `bin/fastverify --preset reference` (C0) always ran the Lean 4.36 lake comparator, and the cross-version gate ran only
# for sound/notary, so on a Lean 4.37.0-rc1 challenge whose config lists a non-sorried definition hole it ACCEPTED with
# trust "official" - from a caller-given export (part 1: a proof of False) and from a real 4.37 source build (part 2) -
# while the challenge's own release comparator (official 4.37.0-rc1 lake comparator) REJECTS; and decide() tested
# export.mode == "given" while the given path writes "given (private copy)", so a caller-given export lost its caveat.
# Reproduction inputs in data/ (SHA256SUMS):
# part 1 = chal37_canon / comparator_shl / sol37_prove_false (as in tests/cross-version-regress), part 2 = chal37_full + Sol3/M3.
# control436 = copies of tests/definition-hole/x (4.36.0 Challenge / SolutionHonest / comparator.json).
# Rows:
#   part1/c0-direct: check/official/check.sh -> REJECTED by the 4.37.0-rc1 comparator ("not sorried")
#   part1/reference-from-export: bin/fastverify --preset reference --from-export -> REJECTED (exit 1), basis names Lean
#     4.37.0-rc1, trust UNSAFE with the "export given by the caller" reason
#   part1/sound-control: --preset sound -> REJECTED (unchanged)
#   part2/reference-source-build: B0 + E0 + C0 on the real 4.37 project -> REJECTED (exit 1), basis Lean 4.37.0-rc1
#   part2/fv-verify-reference: bin/fv verify --preset reference -> not accepted (REJECTED, or refused by the client-path policy)
#   control/437-honest: a tiny 4.37 challenge + honest proof, --preset reference -> ACCEPTED by the 4.37 comparator
#   control/433-gate-*: the 4.33.1 self-test (no comparator of its own) -> the 4.36.0 comparator after the cross-version
#     gate: good ACCEPTED, bad REJECTED; a caller-given good export under --preset reference -> ACCEPTED but trust UNSAFE
#   control/436-own: a 4.36.0 challenge -> the pinned 4.36.0 comparator, unchanged (honest pair ACCEPTED, no gate);
#   control/436-wrong-githash: meta names 4.36.0 with a githash that is not the pinned release -> ERROR (exit 2)
#   control/unknown-release, control/no-meta: a challenge naming Lean 4.99.0 / no meta line -> ERROR (exit 2)
# Untrusted code is built only inside bin/fastverify's bwrap sandbox. Needs the 4.36.0 and 4.37.0-rc1 toolchains (else the
# rows that need them SKIP). Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/reference-release.XXXXXX") || exit 2
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
(cd "$HERE/data" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
cp -a "$HERE/data/." "$W/"; chmod -R u+w "$W"
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
rj() { python3 -I -c 'import json,sys
try: d=json.load(open(sys.argv[1]))
except Exception: print("none"); sys.exit()
print("%s|%s|%s|%s" % (d.get("verdict"), d.get("trust"), d.get("verdict_basis"), " ;; ".join(d.get("unsafe_reasons") or [])))' "$1"; }
TC37=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.37.0-rc1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
HAVE37=0; [ -n "$TC37" ] && [ -x "$TC37/bin/lake" ] && HAVE37=1

# ---------------- part 1: caller-given export (proof of False through a non-sorried definition hole) ----------------
mkdir -p "$W/p1/chal" "$W/p1/proj"
cp "$W/part1/chal37_canon.export" "$W/p1/chal/challenge.export"; cp "$W/part1/comparator_shl.json" "$W/p1/chal/comparator.json"
if [ "$HAVE37" = 1 ]; then
  "$FV/check/official/check.sh" "$W/part1/sol37_prove_false.export" "$W/p1/chal/challenge.export" "$W/p1/chal/comparator.json" \
    --json "$W/p1/c0.json" > /dev/null 2>&1; rc=$?
  v=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["verdict"], "|", d.get("tool"), "|", d.get("detail","")[:80])' "$W/p1/c0.json" 2>/dev/null)
  case "$rc|$v" in "1|REJECTED | "*"4.37.0-rc1"*"not sorried"*) ok part1/c0-direct "$v";; *) ko part1/c0-direct "exit $rc: $v";; esac
  "$FV/bin/fastverify" "$W/p1/proj" "$W/p1/chal" "$W/p1/out" --from-export "$W/part1/sol37_prove_false.export" --preset reference \
    > "$W/p1/ref.log" 2>&1; rc=$?
  v=$(rj "$W/p1/out/result.json")
  case "$rc|$v" in "1|REJECTED|UNSAFE|"*"4.37.0-rc1"*"export given by the caller"*) ok part1/reference-from-export "exit 1: $(echo "$v" | cut -c1-140)";;
    *) ko part1/reference-from-export "exit $rc: $(echo "$v" | cut -c1-220)";; esac
  CSHA=$(sha256sum "$W/p1/chal/challenge.export" | cut -d' ' -f1)
  "$FV/bin/fastverify" "$W/p1/proj" "$W/p1/chal" "$W/p1/out_s" --from-export "$W/part1/sol37_prove_false.export" --preset sound \
    --challenge-sha256 "$CSHA" --comparator-sha256 "$(sha256sum "$W/p1/chal/comparator.json" | cut -d' ' -f1)" > "$W/p1/sound.log" 2>&1; rc=$?
  [ "$rc" = 1 ] && ok part1/sound-control "exit 1 REJECTED" || ko part1/sound-control "exit $rc"
else echo "SKIP part1: no Lean 4.37.0-rc1 toolchain"; fi

# ---------------- part 2: a real 4.37.0-rc1 source build, no crafted export ----------------
if [ "$HAVE37" = 1 ]; then
  "$FV/bin/fastverify" "$W/part2/proj" "$W/part2/chal" "$W/p2out" --preset reference --threads 8 > "$W/p2.log" 2>&1; rc=$?
  v=$(rj "$W/p2out/result.json")
  case "$rc|$v" in "1|REJECTED|official|"*"4.37.0-rc1"*) ok part2/reference-source-build "exit 1: $(echo "$v" | cut -c1-140)";;
    *) ko part2/reference-source-build "exit $rc: $(echo "$v" | cut -c1-220) $(tail -c 200 "$W/p2.log")";; esac
  CSHA2=$(sha256sum "$W/part2/chal/challenge.export" | cut -d' ' -f1); CFG2=$(sha256sum "$W/part2/chal/comparator.json" | cut -d' ' -f1)
  "$FV/bin/fv" verify "$W/part2/proj" --challenge "$W/part2/chal" --challenge-sha256 "$CSHA2" --comparator-sha256 "$CFG2" \
    --preset reference --threads 8 --json > "$W/p2fv.json" 2> "$W/p2fv.err"; rc=$?
  v=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["verdict"], d["accepted"], d["reward"])' "$W/p2fv.json" 2>/dev/null)
  case "$rc|$v" in 0\|*|*" True "*|ACCEPTED*) ko part2/fv-verify-reference "exit $rc '$v' (counted as an acceptance)";;
    *) ok part2/fv-verify-reference "exit $rc '$v'";; esac
  # positive control: a tiny honest 4.37.0-rc1 project is ACCEPTED by the 4.37 comparator
  for d in c437 p437; do
    mkdir -p "$W/$d"; printf 'leanprover/lean4:v4.37.0-rc1\n' > "$W/$d/lean-toolchain"
    printf 'name = "M"\ndefaultTargets = ["M"]\n\n[[lean_lib]]\nname = "M"\n' > "$W/$d/lakefile.toml"
    printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$W/$d/lake-manifest.json"
  done
  printf 'theorem two_eq : 1 + 1 = 2 := by sorry\n' > "$W/c437/M.lean"; printf 'theorem two_eq : 1 + 1 = 2 := rfl\n' > "$W/p437/M.lean"
  printf '{"challenge_module":"M","solution_module":"M","theorem_names":["two_eq"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' > "$W/c437/comparator.json"
  "$FV/bin/fastverify" "$W/p437" "$W/c437" "$W/p437out" --preset reference --threads 8 > "$W/p437.log" 2>&1; rc=$?
  v=$(rj "$W/p437out/result.json")
  case "$rc|$v" in "0|ACCEPTED|official|"*"4.37.0-rc1"*) ok control/437-honest "exit 0: $(echo "$v" | cut -c1-120)";;
    *) ko control/437-honest "exit $rc: $(echo "$v" | cut -c1-200) $(tail -c 200 "$W/p437.log")";; esac
else echo "SKIP part2 / control 437: no Lean 4.37.0-rc1 toolchain"; fi

# ---------------- controls: 4.33.1 (gate path), given-export caveat, unknown release / no meta ----------------
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$FV/check/sound/pins.env"; }
SC=$(pin selftest_challenge); SG=$(pin selftest_good); SB=$(pin selftest_bad); SCF=$(pin selftest_comparator)
for x in good bad; do
  f=$SG; want=ACCEPTED; wrc=0; [ $x = bad ] && { f=$SB; want=REJECTED; wrc=1; }
  "$FV/check/official/check.sh" "$f" "$SC" "$SCF" --json "$W/st_$x.json" > /dev/null 2>&1; rc=$?
  v=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["verdict"], "|", d.get("tool"))' "$W/st_$x.json" 2>/dev/null)
  case "$rc|$v" in "$wrc|$want | "*"4.36.0"*) ok "control/433-gate-$x" "$v";; *) ko "control/433-gate-$x" "exit $rc: $v";; esac
done
mkdir -p "$W/st/chal" "$W/st/proj"; cp "$SC" "$W/st/chal/challenge.export"; cp "$SCF" "$W/st/chal/comparator.json"
"$FV/bin/fastverify" "$W/st/proj" "$W/st/chal" "$W/st/out" --from-export "$SG" --preset reference > "$W/st.log" 2>&1; rc=$?
v=$(rj "$W/st/out/result.json")
case "$rc|$v" in "0|ACCEPTED|UNSAFE|"*"export given by the caller"*) ok control/given-export-caveat "exit 0, trust UNSAFE (caller's export)";;
  *) ko control/given-export-caveat "exit $rc: $(echo "$v" | cut -c1-200)";; esac
python3 -I - "$SC" "$W/fake499.export" "$W/nometa.export" <<'PY'
import sys
src = open(sys.argv[1], "rb").read().split(b"\n", 1)
open(sys.argv[2], "wb").write(src[0].replace(b'"version":"4.33.1"', b'"version":"4.99.0"') + b"\n" + src[1])
open(sys.argv[3], "wb").write(src[1])
PY
# the 4.36.0 path is unchanged: a 4.36.0 challenge (tests/definition-hole fixtures, copied) is judged by the pinned
# 4.36.0 comparator directly (no gate); a challenge whose meta names 4.36.0 with another githash -> ERROR
"$FV/check/official/check.sh" "$W/control436/SolutionHonest.export" "$W/control436/Challenge.export" "$W/control436/comparator.json" \
  --json "$W/c436.json" > /dev/null 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["verdict"], "|", d.get("tool"))' "$W/c436.json" 2>/dev/null)
case "$rc|$v" in "0|ACCEPTED | lake comparator (Lean 4.36.0, unmodified)") ok control/436-own "$v";; *) ko control/436-own "exit $rc: $v";; esac
python3 -I - "$W/control436/Challenge.export" "$W/gh436.export" <<'PY'
import sys
src = open(sys.argv[1], "rb").read().split(b"\n", 1)
assert b"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9" in src[0]
open(sys.argv[2], "wb").write(src[0].replace(b"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9", b"0" * 40) + b"\n" + src[1])
PY
"$FV/check/official/check.sh" "$W/control436/SolutionHonest.export" "$W/gh436.export" "$W/control436/comparator.json" \
  --json "$W/gh436.json" > /dev/null 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["verdict"], "|", d.get("detail","")[:100])' "$W/gh436.json" 2>/dev/null)
case "$rc|$v" in "2|ERROR | "*"githash"*) ok control/436-wrong-githash "exit 2: $v";; *) ko control/436-wrong-githash "exit $rc: $v";; esac
for c in unknown-release:fake499 no-meta:nometa; do
  n=${c%%:*}; f=${c#*:}
  "$FV/check/official/check.sh" "$SG" "$W/$f.export" "$SCF" --json "$W/$f.json" > /dev/null 2>&1; rc=$?
  v=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["verdict"], "|", d.get("detail","")[:100])' "$W/$f.json" 2>/dev/null)
  case "$rc|$v" in "2|ERROR | "*) ok "control/$n" "exit 2: $v";; *) ko "control/$n" "exit $rc: $v";; esac
done
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
