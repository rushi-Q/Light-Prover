#!/bin/bash
# check/sound/test/run.sh — regression test of the sound check (option CS). ~1 min on any host with the pinned binaries.
# Every case prints 'PASS|FAIL <case>: ...'; last line 'RESULT pass=N fail=M'; exit 0 iff all PASS.
# Inputs: only the tiny self-test exports pinned in check/sound/pins.env (+ mutants derived from them here).
# Cases: preflight; good -> ACCEPTED; extra axiom -> REJECTED; kernel-invalid proof (statement unchanged) -> REJECTED;
# changed statement -> REJECTED (compareAt); missing declaration -> REJECTED; missing target -> REJECTED; config with
# nanoda / Lean-only config -> gruszka attached either way; second kernel that cannot decide -> DECLINED (never ACCEPTED);
# second kernel that rejects -> REJECTED; pinned binary with a wrong sha256 -> DECLINED; environment pollution ignored;
# non-regular input -> DECLINED.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); CS=$H/check-sound.sh
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$H/pins.env"; }
GOOD=$(pin selftest_good); BAD=$(pin selftest_bad); CHAL=$(pin selftest_challenge); CFG=$(pin selftest_comparator)
# not under /tmp, /home, /var, /run: the official kernel sandbox hides those (the fake kernels below must stay visible)
# the work directory must stay visible inside the kernel sandboxes (they hide /tmp, /home, /root, /var, /run):
# CHECK_SOUND_TEST_DIR if set, else a visible default (tests/lib/visible_workdir.sh); SKIP only if there is none
. "$H/../../tests/lib/visible_workdir.sh"
fv_visible_workdir check-sound "${CHECK_SOUND_TEST_DIR:-}" || { echo "SKIP all rows: $FV_WORKDIR_WHY"; echo "RESULT pass=0 fail=0 (SKIP)"; exit 0; }
CSD=$FV_WORKDIR
W=$(mktemp -d "$CSD/checkSound-test.XXXXXX") || exit 2; trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
fails=0; passes=0
ex() {  # ex NAME EXPECTED_EXIT SCRIPT [ENV...] -- ARGS...
  local name=$1 want=$2 script=$3; shift 3
  local envs=(); while [ "$1" != -- ]; do envs+=("$1"); shift; done; shift
  local got
  env "${envs[@]}" "$script" "$@" > "$W/out" 2> "$W/err"; got=$?
  if [ "$got" = "$want" ] && tail -1 "$W/out" | python3 -I -c 'import json,sys; json.loads(sys.stdin.read())' 2>/dev/null; then
    echo "PASS $name: exit $got :: $(tail -1 "$W/out" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("reason","")[:150])')"
    passes=$((passes+1))
  else
    echo "FAIL $name: expected $want got $got :: $(tail -1 "$W/out" | cut -c1-300)"; fails=$((fails+1))
  fi
}
# ---- mutants of the good export (fvSelfTest : 2 + 2 = 4, value `rfl`) ----
# kernel-invalid: value of fvSelfTest := rfl 2 (type 2 = 2, not defeq to 2 + 2 = 4); statement unchanged
sed 's/^{"app":{"arg":518,"fn":526},"ie":527}$/{"app":{"arg":512,"fn":526},"ie":527}/' "$GOOD" > "$W/kernel-bad.export"
cmp -s "$GOOD" "$W/kernel-bad.export" && { echo "FAIL setup: kernel mutant identical"; fails=$((fails+1)); }
# changed statement: 2 + 2 = 4 -> 2 + 2 = 5 in the type AND the proof (kernel-invalid too; compareAt must catch it first)
sed 's/^{"ie":520,"natVal":"4"}$/{"ie":520,"natVal":"5"}/' "$GOOD" > "$W/stmt-bad.export"
cmp -s "$GOOD" "$W/stmt-bad.export" && { echo "FAIL setup: statement mutant identical"; fails=$((fails+1)); }
# missing declaration: drop the definition of semiOutParam (a kernel primitive target) -> must not be accepted
grep -v '^{"def":{"all":\[2880\]' "$GOOD" > "$W/missing.export"
cfg() { printf '%s' "$1" > "$W/$2"; echo "$W/$2"; }
LEANONLY=$(cfg '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":["fvSelfTest"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}' lo.json)
NANODA=$(cfg '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":["fvSelfTest"],"permitted_axioms":["propext","Quot.sound","Classical.choice"],"enable_nanoda":true}' en.json)
MISSINGT=$(cfg '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":["fvSelfTest","fvNoSuchTheorem"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}' mt.json)
ex preflight 0 "$CS" -- --preflight
ex good-accept 0 "$CS" -- "$GOOD" "$CHAL" "$CFG" --threads 4
ex good-leanonly-config 0 "$CS" -- "$GOOD" "$CHAL" "$LEANONLY" --threads 4
ex good-enable-nanoda-config 0 "$CS" -- "$GOOD" "$CHAL" "$NANODA" --threads 4
ex good-1-thread 0 "$CS" -- "$GOOD" "$CHAL" "$CFG" --threads 1
ex bad-axiom-reject 1 "$CS" -- "$BAD" "$CHAL" "$CFG" --threads 4
ex kernel-invalid-reject 1 "$CS" -- "$W/kernel-bad.export" "$CHAL" "$CFG" --threads 4
ex statement-changed-reject 1 "$CS" -- "$W/stmt-bad.export" "$CHAL" "$CFG" --threads 4
ex missing-declaration-reject 1 "$CS" -- "$W/missing.export" "$CHAL" "$CFG" --threads 4
ex missing-target-reject 1 "$CS" -- "$GOOD" "$CHAL" "$MISSINGT" --threads 4
ex env-pollution-bad 1 "$CS" CCMP_LEANCHECKER=/bin/true LEAN_ABORT_ON_PANIC=0 LD_LIBRARY_PATH=/nonexistent \
   LEAN_STACK_SIZE_KB=1 PATH=/nonexistent:/usr/bin:/bin -- "$BAD" "$CHAL" "$CFG" --threads 4
ex no-challenge 2 "$CS" -- "$GOOD" "" "$CFG" --threads 4
mkfifo "$W/fifo"
ex fifo-input 2 "$CS" -- "$W/fifo" "$CHAL" "$CFG" --threads 4
ex bad-threads 2 "$CS" -- "$GOOD" "$CHAL" "$CFG" --threads 0
# ---- package copies with a fake second kernel (its sha256 pinned in the copy's pins.env): it behaves like gruszka on
# the self-test exports (so the self-test passes) and exits CODE on the judged export ----
fake() {  # fake NAME CODE -> path of the copy's check-sound.sh
  local d=$W/pkg-$1; mkdir -p "$d/check" "$d/lib" "$d/config"
  cp -r "$H" "$d/check/sound"; cp -r "$H/../xversion" "$d/check/"; cp "$H/../../lib/toolchain.py" "$d/lib/"; cp -r "$H/../../toolchains" "$d/"
  cp "$H/../../config/components.json" "$d/config/"
  printf '#!/bin/sh\ncase "$1" in */solution.export) echo "fake second kernel: exit %s" >&2; exit %s;; esac\nexec "%s" "$@"\n' \
    "$2" "$2" "$(pin gruszka)" > "$d/fake-kernel"; chmod 755 "$d/fake-kernel"
  local s; s=$(sha256sum "$d/fake-kernel" | cut -d' ' -f1)
  awk -v p="$d/fake-kernel" -v s="$s" '$1=="PIN" && $2=="gruszka" {print "PIN gruszka " s " " p; next} {print}' "$H/pins.env" > "$d/check/sound/pins.env"
  echo "$d/check/sound/check-sound.sh"
}
# second kernel cannot decide (exit 2) while the official kernel accepts -> no verdict (never ACCEPTED)
ex second-kernel-declines 2 "$(fake decl 2)" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# second kernel rejects while the official kernel accepts -> REJECTED
ex second-kernel-rejects 1 "$(fake rej 1)" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# second kernel crashes (exit 134) -> no verdict
ex second-kernel-crashes 2 "$(fake crash 134)" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# second kernel "accepts" an export with a forbidden axiom -> still REJECTED (checkAxioms is independent of the kernels)
ex second-kernel-accepts-axiom 1 "$(fake acc 0)" -- "$BAD" "$CHAL" "$CFG" --threads 4
# second kernel "accepts" a kernel-invalid export -> still REJECTED (the official kernel must accept too)
ex second-kernel-accepts-invalid 1 "$(fake acc2 0)" -- "$W/kernel-bad.export" "$CHAL" "$CFG" --threads 4
# a second kernel that fails the self-test (it rejects the good self-test export) but accepts the judged export ->
# DECLINED: the self-test runs concurrently with the judge, and the verdict still requires it
fakest() {
  local d=$W/pkg-st; mkdir -p "$d/check" "$d/lib" "$d/config"
  cp -r "$H" "$d/check/sound"; cp -r "$H/../xversion" "$d/check/"; cp "$H/../../lib/toolchain.py" "$d/lib/"; cp -r "$H/../../toolchains" "$d/"
  cp "$H/../../config/components.json" "$d/config/"
  printf '#!/bin/sh\ncase "$1" in */solution.export) exec "%s" "$@";; esac\necho "fake: fail the self-test" >&2; exit 1\n' \
    "$(pin gruszka)" > "$d/fake-kernel"; chmod 755 "$d/fake-kernel"
  local s; s=$(sha256sum "$d/fake-kernel" | cut -d' ' -f1)
  awk -v p="$d/fake-kernel" -v s="$s" '$1=="PIN" && $2=="gruszka" {print "PIN gruszka " s " " p; next} {print}' "$H/pins.env" > "$d/check/sound/pins.env"
  echo "$d/check/sound/check-sound.sh"
}
ex selftest-fails-judge-accepts 2 "$(fakest)" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# ---- fake official-kernel legs (pleanchecker pin replaced by a wrapper; self-test exports go to the real binary) ----
fakeplc() {  # fakeplc NAME SCRIPT_BODY_FOR_THE_JUDGED_EXPORT -> path of the copy's check-sound.sh
  local d=$W/pkg-plc-$1; mkdir -p "$d/check" "$d/lib" "$d/config"
  cp -r "$H" "$d/check/sound"; cp -r "$H/../xversion" "$d/check/"; cp "$H/../../lib/toolchain.py" "$d/lib/"; cp -r "$H/../../toolchains" "$d/"
  cp "$H/../../config/components.json" "$d/config/"
  { printf '#!/bin/sh\nREAL="%s"\nfor a do case "$a" in */solution.export) JUDGED=1;; esac; done\n' "$(pin pleanchecker)"
    printf '[ -n "${JUDGED:-}" ] || exec "$REAL" "$@"\n%s\n' "$2"; } > "$d/fake-plc"; chmod 755 "$d/fake-plc"
  local s; s=$(sha256sum "$d/fake-plc" | cut -d' ' -f1)
  awk -v p="$d/fake-plc" -v s="$s" '$1=="PIN" && $2=="pleanchecker" {print "PIN pleanchecker " s " " p; next} {print}' "$H/pins.env" > "$d/check/sound/pins.env"
  echo "$d/check/sound/check-sound.sh"
}
# found in a gate run: a dying leg prints a resource message into the shared log while ccmp's own axiom check fails -> REJECTED
ex spurious-thread-msg-axiom-reject 1 "$(fakeplc spur 'echo "terminate called after throwing an instance of lean::exception: failed to create thread: Resource temporarily unavailable" >&2; exec "$REAL" "$@"')" -- "$BAD" "$CHAL" "$CFG" --threads 4
# ... and the same message on an otherwise good export: the Lean leg still accepts -> ACCEPTED (messages are not verdicts)
ex spurious-thread-msg-good-accept 0 "$(fakeplc spur2 'echo "failed to create thread: Resource temporarily unavailable" >&2; exec "$REAL" "$@"')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# the official-kernel leg is SIGKILLed (OOM killer) -> no verdict
ex lean-leg-killed 2 "$(fakeplc kill 'kill -9 $$')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# the official-kernel leg runs out of stack (deep recursion, exit 1) -> no verdict (our stack is smaller than the official one)
ex lean-leg-deep-recursion 2 "$(fakeplc deep 'echo "(kernel) deep recursion detected" >&2; exit 1')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# the official-kernel leg exits 1 (a rejection) -> REJECTED even if gruszka accepts
ex lean-leg-rejects 1 "$(fakeplc rej 'echo "fake: kernel exception" >&2; exit 1')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# a pinned binary that does not match its sha256 -> DECLINED
D=$W/pkg-sha; mkdir -p "$D/check" "$D/lib" "$D/config"; cp -r "$H" "$D/check/sound"; cp -r "$H/../xversion" "$D/check/"; cp "$H/../../lib/toolchain.py" "$D/lib/"
cp -r "$H/../../toolchains" "$D/"; cp "$H/../../config/components.json" "$D/config/"
sed -i 's/^PIN ccmp [0-9a-f]*/PIN ccmp 0000000000000000000000000000000000000000000000000000000000000000/' "$D/check/sound/pins.env"
ex wrong-pin-sha 2 "$D/check/sound/check-sound.sh" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# ---- v2 (check/sound/README.md): leg-scoped verdict (a leg's output cannot steer the decision), recorded leg status, private inputs ----
exj() {  # exj NAME EXPECTED_EXIT PY_PREDICATE SCRIPT -- ARGS... : like ex, plus a Python predicate over the result JSON `j`
  local name=$1 want=$2 pred=$3 script=$4; shift 5
  local got; "$script" "$@" > "$W/out" 2> "$W/err"; got=$?
  if [ "$got" = "$want" ] && tail -1 "$W/out" | python3 -I -c "import json,sys; j=json.loads(sys.stdin.read()); sys.exit(0 if ($pred) else 1)" 2>/dev/null; then
    echo "PASS $name: exit $got :: $(tail -1 "$W/out" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("reason","")[:120])')"; passes=$((passes+1))
  else
    echo "FAIL $name: expected $want + [$pred] got $got :: $(tail -1 "$W/out" | cut -c1-500)"; fails=$((fails+1))
  fi
}
fakek2() {  # fakek2 NAME SCRIPT_BODY_FOR_THE_JUDGED_EXPORT -> path of the copy's check-sound.sh (self-test exports: real gruszka)
  local d=$W/pkg-k2-$1; mkdir -p "$d/check" "$d/lib" "$d/config"
  cp -r "$H" "$d/check/sound"; cp -r "$H/../xversion" "$d/check/"; cp "$H/../../lib/toolchain.py" "$d/lib/"; cp -r "$H/../../toolchains" "$d/"
  cp "$H/../../config/components.json" "$d/config/"
  { printf '#!/bin/sh\nREAL="%s"\ncase "$1" in */solution.export) ;; *) exec "$REAL" "$@";; esac\n%s\n' "$(pin gruszka)" "$2"; } > "$d/fake-k2"; chmod 755 "$d/fake-k2"
  local s; s=$(sha256sum "$d/fake-k2" | cut -d' ' -f1)
  awk -v p="$d/fake-k2" -v s="$s" '$1=="PIN" && $2=="gruszka" {print "PIN gruszka " s " " p; next} {print}' "$H/pins.env" > "$d/check/sound/pins.env"
  echo "$d/check/sound/check-sound.sh"
}
# the result JSON records each leg's own exit status (written by the trusted wrapper), ccmp's leg times and the input handling
exj v2-legs-recorded-accept 0 'j["legs"]["lean"]["rc"]==0 and j["legs"]["k2"]["rc"]==0 and j["legs"]["lean"]["ms"] is not None and j["legs"]["k2"]["ms"] is not None and j["compare_ms"] is not None and j["inputs"]["export"]["private"]=="copy" and j["inputs"]["challenge"]["private"]=="copy" and j["private_inputs_asserted"]==0 and j["wiring"].startswith("check-sound-v2")' "$CS" -- "$GOOD" "$CHAL" "$CFG" --threads 4
exj v2-legs-recorded-reject 1 'j["legs"]["lean"]["rc"]==1 and "rejects the solution" in (j["legs"]["lean"]["message"] or "")' "$CS" -- "$W/kernel-bad.export" "$CHAL" "$CFG" --threads 4
# a (hostile) Lean leg prints the judge's own lines - a fake first error line, both acceptance lines, the success line - and
# then rejects: REJECTED (v1 read the first 'error:' line of the shared log and gave no verdict)
ex v2-inject-fake-judge-lines-reject 1 "$(fakeplc inj1 'echo "error: Lean default exited with 2"; echo "Lean default kernel accepts the solution"; echo "gruszka (second kernel) kernel accepts the solution"; echo "Your solution is okay!"; exit 1')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# resource / stack words inside a rejection message (e.g. in a declaration name) do not turn the rejection into no verdict
ex v2-inject-stack-words-in-name-reject 1 "$(fakeplc inj2 'echo "Lean default kernel rejects the solution: while replaying declaration '"'"'«x Stack overflow detected»'"'"':"; echo "(kernel) unknown constant '"'"'«out of memory (kernel) deep recursion»'"'"'"; echo "failed to create thread: Resource temporarily unavailable" >&2; exit 1')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# the real deep-recursion format of the Lean leg (Par.lean "while replaying declaration" + Kernel.Exception.deepRecursion) -> no verdict
ex v2-deep-recursion-real-format-declines 2 "$(fakeplc deep2 'echo "Lean default kernel rejects the solution: while replaying declaration '"'"'foo'"'"':"; echo "(kernel) deep recursion detected"; exit 1')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# a second kernel that prints the judge's "Lean default kernel rejected the solution" and a fake error line, then cannot decide,
# while the official kernel accepts -> no verdict (v1 could read those lines from the shared log and REJECT a valid export)
ex v2-inject-second-kernel-fake-lines-declines 2 "$(fakek2 inj3 'echo "Lean default kernel rejected the solution"; echo "error: Lean default exited with 1"; exit 2')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# ... and a second kernel printing the acceptance + success lines but exiting 2 -> no verdict, never ACCEPTED
ex v2-inject-second-kernel-fake-accept-declines 2 "$(fakek2 inj4 'echo "gruszka (second kernel) kernel accepts the solution"; echo "Your solution is okay!"; exit 2')" -- "$GOOD" "$CHAL" "$CFG" --threads 4
# --keep-config-kernels: the challenge's own kernels stay as extra legs (veto only), each through a wrapper of its own
exj v2-keep-config-nanoda-accept 0 'j["legs"]["kept-0"]["name"]=="nanoda" and j["legs"]["kept-0"]["rc"]==0' "$CS" -- "$GOOD" "$CHAL" "$NANODA" --threads 4 --keep-config-kernels
KREJ=$W/kept-reject.sh; printf '#!/bin/sh\necho "fake kept kernel: reject" >&2; exit 1\n' > "$KREJ"; chmod 755 "$KREJ"
KEPT1=$(cfg "{\"challenge_module\":\"Challenge\",\"solution_module\":\"Main\",\"theorem_names\":[\"fvSelfTest\"],\"permitted_axioms\":[\"propext\",\"Quot.sound\",\"Classical.choice\"],\"external_kernels\":{\"myk\":[\"$KREJ\"]}}" kept1.json)
ex v2-keep-config-kernel-rejects 1 "$CS" -- "$GOOD" "$CHAL" "$KEPT1" --threads 4 --keep-config-kernels
KDEC=$W/kept-decline.sh; printf '#!/bin/sh\necho "Your solution is okay!"; echo "myk kernel accepts the solution"; echo "Lean default kernel accepts the solution"; exit 2\n' > "$KDEC"; chmod 755 "$KDEC"
KEPT2=$(cfg "{\"challenge_module\":\"Challenge\",\"solution_module\":\"Main\",\"theorem_names\":[\"fvSelfTest\"],\"permitted_axioms\":[\"propext\",\"Quot.sound\",\"Classical.choice\"],\"external_kernels\":{\"myk\":[\"$KDEC\"]}}" kept2.json)
ex v2-keep-config-kernel-declines 2 "$CS" -- "$GOOD" "$CHAL" "$KEPT2" --threads 4 --keep-config-kernels
# private inputs: an export > 4 GiB is COPIED by default (own inode) and hard-LINKED only with --private-inputs (same filesystem);
# BIG = the good export followed by a 4 GiB hole (sparse; not a valid export: never ACCEPTED, exit 1 or 2 depending on which leg fails first)
BIG=$W/big.export; cp "$GOOD" "$BIG"; chmod u+w "$BIG"; truncate -s 4294967297 "$BIG"   # the pinned export is read-only: chmod before truncate
exj2() {  # like exj, EXPECTED_EXIT is a set of digits
  local name=$1 want=$2 pred=$3 script=$4; shift 5
  local got; "$script" "$@" > "$W/out" 2> "$W/err"; got=$?
  if case "$got" in [$want]) true;; *) false;; esac && tail -1 "$W/out" | python3 -I -c "import json,sys; j=json.loads(sys.stdin.read()); sys.exit(0 if ($pred) else 1)" 2>/dev/null; then
    echo "PASS $name: exit $got :: $(tail -1 "$W/out" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("reason","")[:120])')"; passes=$((passes+1))
  else
    echo "FAIL $name: expected [$want] + [$pred] got $got :: $(tail -1 "$W/out" | cut -c1-500)"; fails=$((fails+1))
  fi
}
exj2 v2-big-export-copied-by-default 12 'j["inputs"]["export"]["private"]=="copy" and j["inputs"]["export"]["size"]==4294967297 and j["private_inputs_asserted"]==0' "$CS" -- "$BIG" "$CHAL" "$CFG" --threads 4 --timeout 600
exj2 v2-big-export-linked-when-asserted 12 'j["inputs"]["export"]["private"]=="link" and j["private_inputs_asserted"]==1' "$CS" -- "$BIG" "$CHAL" "$CFG" --threads 4 --timeout 600 --private-inputs
rm -f "$BIG"
echo "RESULT pass=$passes fail=$fails"
[ "$fails" = 0 ]
