#!/bin/bash
# tests/build-kill/run.sh [WORKDIR] - regression test: a killed lean of the official build must give no verdict:
#   a `lean` of the OFFICIAL build (B0 = the final fallback of every preset) killed from outside - what the kernel's OOM
#   killer does under a memory limit - made `lake build` exit 1 with "error: Lean exited with code 137" and
#   build/official-build.sh reported FAILED, so bin/fastverify gave the verdict REJECTED for a valid project.
#   Expected after the fix: ERROR (no verdict, exit 2) with the reason "a lean process was killed from outside".
# Case: a one-module project importing Mathlib (the `lean` lives ~15-30 s) against a challenge of the same statement;
#   `--preset sound --build B0 --threads 4`; the test SIGKILLs the first `lean` of the run's build 3 s after it appears.
#   Control: the same run without the kill must be ACCEPTED (skipped with QUICK=1).
# Needs the trusted Mathlib workspace (FV_PACKAGES, default $LIGHT_LEAN/verify/challenge) and ~1 min on a test host.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FASTVERIFY:-$(cd "$H/../.." && pwd)}
LL=${LIGHT_LEAN:-$(dirname "$FV")}
WS=${FV_PACKAGES:-$LL/verify/challenge}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-kill.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"
pass=0; fail=0
ok()  { pass=$((pass+1)); echo "PASS $1"; }
bad() { fail=$((fail+1)); echo "FAIL $1: $2"; }
[ -d "$WS/.lake/packages/mathlib" ] || { echo "SKIP: no trusted workspace at $WS"; exit 0; }
REV=$(python3 -I -c 'import json,sys; print([p["rev"] for p in json.load(open(sys.argv[1]))["packages"] if p["name"]=="mathlib"][0])' "$WS/lake-manifest.json")
URL=$(python3 -I -c 'import json,sys; print([p["url"] for p in json.load(open(sys.argv[1]))["packages"] if p["name"]=="mathlib"][0])' "$WS/lake-manifest.json")
mk() { # mk DIR NAME MODULE PROOF
  local d=$1 n=$2 m=$3 pf=$4
  mkdir -p "$d"
  printf 'name = "%s"\ndefaultTargets = ["%s"]\n\n[[require]]\nname = "mathlib"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "%s"\n' "$n" "$m" "$URL" "$REV" "$m" > "$d/lakefile.toml"
  python3 -I -c 'import json,sys; m=json.load(open(sys.argv[1])); m["name"]=sys.argv[3]; json.dump(m, open(sys.argv[2],"w"), indent=1)' "$WS/lake-manifest.json" "$d/lake-manifest.json" "$n"
  cp "$WS/lean-toolchain" "$d/lean-toolchain"
  printf 'import Mathlib\n\ntheorem kill_target (n : Nat) : n + 0 = n := %s\n' "$pf" > "$d/$m.lean"
}
mk "$W/proj" killproj Solution "by simp"
mk "$W/chal" killchal Challenge "sorry"
printf '{"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["kill_target"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}\n' > "$W/chal/comparator.json"
run() { # run OUT kill?  -> prints "verdict | basis"; the exit code goes to OUT.rc
  local out=$1 kill=$2
  rm -rf "$out"
  ( env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$W/proj" "$W/chal" "$out" --preset sound --build B0 --threads 4 --packages "$WS" > "$out.log" 2>&1; echo "rc=$?" >> "$out.log" ) &
  local fvpid=$!
  if [ "$kill" = 1 ]; then
    local i victim=
    for i in $(seq 1 900); do victim=$(pgrep -f "lean .*$out/work/proj/" | head -1); [ -n "$victim" ] && break; sleep 0.2; done
    sleep 3
    victim=$(pgrep -f "lean .*$out/work/proj/" | head -1)
    if [ -n "$victim" ]; then kill -9 "$victim"; echo "  killed lean $victim" >> "$out.log"; else echo "  no lean to kill" >> "$out.log"; fi
  fi
  wait $fvpid
  sed -n 's/^rc=//p' "$out.log" | tail -1 > "$out.rc"
  python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["verdict"], "|", r["verdict_basis"][:160])' "$out/result.json" 2>/dev/null || echo "none | no result.json"
}
V=$(run "$W/kill" 1); RC=$(cat "$W/kill.rc")
echo "  killed run: exit $RC verdict $V"
case "$V" in
  ERROR*killed\ from\ outside*|ERROR*) [ "$RC" = 2 ] && ok "lean killed during the official build -> ERROR (no verdict), exit 2" || bad "exit code" "exit $RC, verdict $V";;
  REJECTED*) bad "killed-lean regression: a killed lean became REJECTED" "$V";;
  *) bad "unexpected outcome" "exit $RC, verdict $V (did the kill happen? $(grep -c 'killed lean' "$W/kill.log"))";;
esac
if [ "${QUICK:-0}" != 1 ]; then
  V=$(run "$W/ctl" 0); RC=$(cat "$W/ctl.rc"); echo "  control run: exit $RC verdict $V"
  case "$V" in ACCEPTED*) ok "control without kill -> ACCEPTED";; *) bad "control" "exit $RC, verdict $V";; esac
fi
# ENOSPC: the official build's log of an earlier run (community main 9c9f665e on Lean 4.37.0-rc1, 122,149 of
# 146,883 modules) ended with ENOSPC; the classifier of build/official-build.sh must turn that into ERROR, not FAILED/REJECTED.
# The condition cannot be produced here without root (no tmpfs / quota), so the archived excerpt is checked against the
# script's own pattern, and the script must contain that classification.
EX="$H/enospc-excerpt.log"
if grep -qE "resource exhausted \(error code: 28|[Nn]o space left on device" "$EX" && grep -q 'ran out of disk space (ENOSPC)' "$FV/build/official-build.sh" \
   && grep -qE 'resource exhausted .*error code: 28' "$FV/build/official-build.sh"; then
  ok "ENOSPC in the official build log is classified as a host failure (ERROR) by build/official-build.sh"
else
  bad "ENOSPC regression: build/official-build.sh does not classify ENOSPC ('resource exhausted (error code: 28)') as ERROR" "excerpt $EX"
fi
echo "RESULT: $pass PASS, $fail FAIL"
[ $fail = 0 ]
