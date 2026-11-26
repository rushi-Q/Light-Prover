#!/bin/bash
# check/sound/test/xk.sh — regression test of the EXTRA VETO-ONLY KERNELS of check-sound.sh v2.3-H (con-leche, nanoda).
# ~3 min on a many-core host (needs the pinned binaries of check/sound/pins.env incl. PIN con_leche / nanoda /
# selftest_kbad). Every case prints 'PASS|FAIL <case>: ...'; last line 'RESULT pass=N fail=M'; exit 0 iff all PASS.
#  Part A  the classification table (check-sound.sh --xk-classify KERNEL LOG RC, the very function the verdict uses) on
#          REAL recorded logs (test/xk-fixtures/: corpus and RH-scale measurements) and on synthetic logs for
#          the paths no corpus produced (OOM, signals, spawn failure, library panic, forged names).
#  Part B  end to end through check-sound.sh with package copies whose pins.env pins MOCK extra kernels: a mock runs the
#          REAL pinned binary on the two self-test exports (so the per-run self-test passes) and, on the judged export,
#          replays a recorded log + exit status, kills itself with a signal, or sleeps. Asserted: exit code, verdict and
#          the per-kernel status in the JSON result.
#  Part C  check-sound-svc.sh (service variant, incl. an integrity-cache hit) on a subset; no extra kernel outlives the
#          judge with --timeout; a kept config kernel cannot reach the extra kernels' records; the one-line default switch
#          and the memory guard of the default-on mode under a cgroup memory limit (cgrun, env CGRUN; skipped if absent).
#  Part E  con-leche's documented false reject of valid official output (xk-fixtures/thmunfold, built from source with the
#          official 4.36 lean + leanexport; skipped without them): default ACCEPTED, --kernel con-leche REJECTED.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); CS=$H/check-sound.sh; FX=$H/test/xk-fixtures
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$H/pins.env"; }
GOOD=$(pin selftest_good); BAD=$(pin selftest_bad); CHAL=$(pin selftest_challenge); CFG=$(pin selftest_comparator)
REALCL=$(pin con_leche); REALNA=$(pin nanoda)
[ -n "$REALCL" ] && [ -n "$REALNA" ] && [ -n "$(pin selftest_kbad)" ] || { echo "FAIL setup: pins.env lacks PIN con_leche/nanoda/selftest_kbad"; echo "RESULT pass=0 fail=1"; exit 1; }
# not under /tmp, /home, /var, /run: the kernel sandboxes hide those (mocks and fixtures must stay visible)
# the work directory must stay visible inside the kernel sandboxes (they hide /tmp, /home, /root, /var, /run):
# CHECK_SOUND_TEST_DIR if set, else a visible default (tests/lib/visible_workdir.sh); SKIP only if there is none
. "$H/../../tests/lib/visible_workdir.sh"
fv_visible_workdir check-sound-xk "${CHECK_SOUND_TEST_DIR:-}" || { echo "SKIP all rows: $FV_WORKDIR_WHY"; echo "RESULT pass=0 fail=0 (SKIP)"; exit 0; }
CSD=$FV_WORKDIR
W=$(mktemp -d "$CSD/checkSound-xk.XXXXXX") || exit 2; trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
cp -r "$FX" "$W/fx"
fails=0; passes=0
pass() { echo "PASS $*"; passes=$((passes+1)); }
fail() { echo "FAIL $*"; fails=$((fails+1)); }

# ---------------- Part A: classification table ----------------
cls() {  # cls CASE KERNEL LOG RC WANT_STATUS [WANT_SUBSTRING_OF_REASON_OR_MESSAGE]
  local name=$1 k=$2 log=$3 rc=$4 want=$5 sub=${6:-} out got ex
  out=$("$CS" --xk-classify "$k" "$log" "$rc" 2>/dev/null); ex=$?
  got=$(printf '%s' "$out" | tail -1 | python3 -I -c 'import json,sys; d=json.loads(sys.stdin.read()); assert d["verdict"]=="NOT_A_VERDICT"; print(d["status"]+"\t"+d["reason"]+" "+d["message"])' 2>/dev/null)
  if [ "$ex" = 2 ] && [ "${got%%	*}" = "$want" ] && { [ -z "$sub" ] || [[ "$got" == *"$sub"* ]]; }; then pass "$(printf '%s' "A:$name: $want :: ${got#*	}" | cut -c1-230)"
  else fail "A:$name: want '$want'${sub:+ ~'$sub'} (exit 2), got exit $ex '$got'"; fi
}
syn() { printf '%b' "$2" > "$W/fx/$1"; echo "$W/fx/$1"; }
F=$W/fx
# con-leche, real logs
cls cl-real-accepted-t22          con-leche "$F/cl-rc0-t22-accepted.log" 0 accepted "accepted 506 declarations"
cls cl-real-invalid-badDef        con-leche "$F/cl-rc1-invalid-arena-badDef.log" 1 rejected "con-leche: invalid:"
cls cl-real-invalid-unknown-const con-leche "$F/cl-rc1-invalid-unknown-constant.log" 1 rejected "unknown constant"
cls cl-real-invalid-thm-unfold    con-leche "$F/cl-rc1-invalid-thm-unfold-good.log" 1 rejected "type mismatch"
# KNOWN FALSE REJECT (documented): official v4.36.0 lean + leanexport output of xk-fixtures/thmunfold/Main.lean, valid for the
# official kernel and gruszka; con-leche treats theorem bodies as opaque -> its own rejection = 'rejected' (why it is opt-in)
cls cl-real-thmunfold-known-false-reject con-leche "$F/cl-rc1-invalid-thmunfold-official-valid.log" 1 rejected "application type mismatch"
cls cl-real-natlimit              con-leche "$F/cl-rc1-natlimit.log" 1 "not decided" "resource limit"
cls cl-real-limit-pow-result-size con-leche "$F/cl-rc1-limit-pow-result-size.log" 1 "not decided" "maximum numeral size"
cls cl-real-limit-pow-32bit       con-leche "$F/cl-rc1-limit-pow-32bit-operand.log" 1 "not decided" "32-bit"
cls cl-real-limit-shift-32bit     con-leche "$F/cl-rc1-limit-shift-32bit-operand.log" 1 "not decided" "32-bit"
cls cl-fuel-exhausted             con-leche "$(syn cl-fuel.log 'con-leche: invalid: resource limit: fuel exhausted: defeq loop [at theorem t, fold position 3] (--verified) t=1.0s\n')" 1 "not decided" "fuel exhausted"
cls cl-fuel-exhausted-bare        con-leche "$(syn cl-fuel2.log 'con-leche: invalid: fuel exhausted: whnf [at theorem t, fold position 3] (--verified) t=1.0s\n')" 1 "not decided" "fuel exhausted"
cls cl-refused-in-name-only       con-leche "$(syn cl-refname.log 'con-leche: invalid: type mismatch in theorem «the kernel refused » [at theorem «the kernel refused », fold position 3]\n')" 1 rejected "type mismatch"
cls cl-real-declined-axiom        con-leche "$F/cl-rc2-declined-axiom.log" 2 "not decided" "non-standard axiom"
cls cl-real-error-parse           con-leche "$F/cl-rc3-error-parse.log" 3 "not decided" "duplicate key"
cls cl-real-accept-line-but-rc1   con-leche "$F/cl-rc0-t22-accepted.log" 1 "not decided" "without con-leche's rejection line"
cls cl-real-invalid-but-rc0       con-leche "$F/cl-rc1-invalid-arena-badDef.log" 0 "not decided" "without con-leche's acceptance line"
# con-leche, synthetic
cls cl-oom-runtime        con-leche "$(syn cl-oom.log 'INTERNAL PANIC: out of memory\n')" 1 "not decided" "out of memory"
cls cl-oom-after-invalid  con-leche "$(syn cl-oom2.log 'con-leche: invalid: type mismatch in theorem t [at theorem t, fold position 3] (--verified) t=0.0s\nINTERNAL PANIC: out of memory\n')" 1 "not decided" "resource"
cls cl-forged-name-same-line con-leche "$(syn cl-forge.log 'con-leche: invalid: type mismatch in theorem «out of memory» [at theorem «out of memory», fold position 3] (--verified) t=0.0s\n')" 1 rejected "type mismatch"
cls cl-deep-recursion-reason con-leche "$(syn cl-deep.log 'con-leche: invalid: deep recursion detected [at theorem t, fold position 3]\n')" 1 "not decided" "resource failure reported"
cls cl-empty-rc1          con-leche "$(syn cl-empty.log '')" 1 "not decided" "(empty log)"
cls cl-abort              con-leche "$(syn cl-abort.log 'Stack overflow detected. Aborting.\n')" 134 "not decided" "SIGABRT"
cls cl-sigkill            con-leche "$F/cl-rc0-t22-accepted.log" 137 "not decided" "SIGKILL"
cls cl-timeout            con-leche "$(syn cl-empty2.log '')" 124 "not decided" "timeout"
cls cl-no-status          con-leche "$F/cl-rc0-t22-accepted.log" "" "not decided" "no exit status"
cls cl-bwrap-failure      con-leche "$(syn cl-bwrap.log 'bwrap: Creating new namespace failed: Operation not permitted\n')" 1 "not decided" "without con-leche's rejection line"
cls cl-accept-wrong-mode  con-leche "$(syn cl-trusted.log 'con-leche: accepted 12 declarations (--trusted)\n')" 0 "not decided"
# nanoda, real logs
cls na-real-accepted-t22-1gib     nanoda "$F/na-rc0-t22-accepted-1gib.log" 0 accepted "no typechecker errors"
cls na-real-reject-tc             nanoda "$F/na-rc101-reject-tc-arena-badDef.log" 101 rejected "src/tc.rs"
cls na-real-reject-inductive      nanoda "$F/na-rc101-reject-inductive.log" 101 rejected "src/inductive.rs"
cls na-real-panic-parser          nanoda "$F/na-rc101-panic-parser.log" 101 "not decided" "src/parser.rs"
cls na-real-error-invalid-block   nanoda "$F/na-rc1-error-invalid-block.log" 1 "not decided" "invalid inductive block"
cls na-real-declined-format       nanoda "$F/na-rc2-declined-format.log" 2 "not decided" "back-reference"
cls na-real-t22-stack-overflow    nanoda "$F/na-rc134-t22-stack-overflow-32mib.log" 134 "not decided" "overflowed its stack"
cls na-real-tc-panic-but-rc134    nanoda "$F/na-rc101-reject-tc-arena-badDef.log" 134 "not decided" "SIGABRT"
# nanoda, synthetic
cls na-no-errors-line     nanoda "$(syn na-ok.log 'Checked 7 declarations with no errors\n')" 0 accepted
cls na-rc0-no-line        nanoda "$(syn na-ok2.log '\n')" 0 "not decided" "without nanoda's success line"
cls na-spawn-failure      nanoda "$(syn na-spawn.log "\nthread 'main' (1) panicked at src/tc.rs:180:29:\nfailed to spawn checking thread 3 with stack_size_bytes=1073741824: Resource temporarily unavailable (os error 11)\n")" 101 "not decided" "failed to spawn"
cls na-library-panic      nanoda "$(syn na-lib.log "\nthread 'thread_2' (6) panicked at /rustc/abc/library/alloc/src/raw_vec/mod.rs:28:5:\ncapacity overflow\n")" 101 "not decided" "outside nanoda's type checker"
cls na-util-panic         nanoda "$(syn na-util.log "\nthread 'thread_0' (4) panicked at src/util.rs:59:9:\nindex 2147483648 exceeds 31-bit capacity\n")" 101 "not decided" "src/util.rs"
cls na-old-panic-format   nanoda "$(syn na-old.log "thread 'thread_0' panicked at src/quot.rs:89:13:\nassertion failed\n")" 101 rejected "src/quot.rs"
cls na-first-panic-decides nanoda "$(syn na-two.log "\nthread 'thread_1' (5) panicked at src/tc.rs:985:71:\nassertion failed: self.def_eq(u, v)\nthread 'main' (1) panicked at src/parser.rs:1:1:\nx\n")" 101 rejected "src/tc.rs"
cls na-forged-name-in-msg nanoda "$(syn na-forge.log "\nthread 'thread_1' (5) panicked at src/tc.rs:213:13:\ninfer_const: declaration \"stack overflow\" depends on \"has overflowed its stack\" which was not found in the environment\n")" 101 rejected "infer_const"
cls na-101-no-panic-line  nanoda "$(syn na-nopanic.log 'something\n')" 101 "not decided" "without a panic location line"
cls na-alloc-abort        nanoda "$(syn na-alloc.log 'memory allocation of 68719476736 bytes failed\n')" 134 "not decided" "memory allocation"
cls na-sigsegv            nanoda "$(syn na-segv.log '')" 139 "not decided" "SIGSEGV"
cls unknown-kernel        con-ron "$F/cl-rc0-t22-accepted.log" 0 "not decided" "unknown extra kernel"

# ---------------- Part B: end to end with mock extra kernels ----------------
# kernel-invalid mutant of the good export (statement unchanged): the official kernel and gruszka reject it
sed 's/^{"app":{"arg":518,"fn":526},"ie":527}$/{"app":{"arg":512,"fn":526},"ie":527}/' "$GOOD" > "$W/kernel-bad.export"
mkpkg() {  # mkpkg NAME -> a package copy (check/sound + what check-sound.sh reads) in $W/pkg-NAME
  local d=$W/pkg-$1; mkdir -p "$d/check" "$d/lib" "$d/config"
  cp -r "$H" "$d/check/sound"; [ -d "$H/../xversion" ] && cp -r "$H/../xversion" "$d/check/"; cp "$H/../../lib/toolchain.py" "$d/lib/"; cp -r "$H/../../toolchains" "$d/"
  cp "$H/../../config/components.json" "$d/config/"; echo "$d"
}
mock() {  # mock PKGDIR KERNEL 'SCENARIO SHELL TEXT' -> writes PKGDIR/mock-KERNEL and pins it in PKGDIR's pins.env
  local d=$1 k=$2 sc=$3 real pn pat s
  case "$k" in con-leche) real=$REALCL; pn=con_leche; pat='*/solution.export';; nanoda) real=$REALNA; pn=nanoda; pat='*/xk-nanoda/nanoda.json';; esac
  printf '#!/bin/sh\nfor a; do L=$a; done\ncase "$L" in %s) %s;; esac\nexec "%s" "$@"\n' "$pat" "$sc" "$real" > "$d/mock-$k"; chmod 755 "$d/mock-$k"
  s=$(sha256sum "$d/mock-$k" | cut -d' ' -f1)
  for f in pins.env pins-437.env; do
    awk -v n="$pn" -v p="$d/mock-$k" -v s="$s" '$1=="PIN" && $2==n {print "PIN " n " " s " " p; next} {print}' "$d/check/sound/$f" > "$d/pins.tmp" && mv "$d/pins.tmp" "$d/check/sound/$f"
  done
}
replay() { printf "cat '%s'; exit %s" "$1" "$2"; }   # scenario: replay a recorded log + exit status
e2e() {  # e2e CASE WANT_EXIT 'KERNEL=STATUS[,KERNEL=STATUS]' SCRIPT ARGS...
  local name=$1 want=$2 spec=$3 script=$4; shift 4
  local got js chk
  "$script" "$@" > "$W/out" 2> "$W/err"; got=$?
  js=$(tail -1 "$W/out")
  chk=$(printf '%s' "$js" | python3 -I -c '
import json, sys
d = json.loads(sys.stdin.read()); spec = sys.argv[1]; bad = []
xk = d.get("extra_kernels") or {}
for item in [x for x in spec.split(",") if x]:
    k, st = item.split("=", 1)
    got = (xk.get(k) or {}).get("status")
    if got != st:
        bad.append("%s=%r (want %r)" % (k, got, st))
v = {0: "ACCEPTED", 1: "REJECTED", 2: "DECLINED"}.get(d.get("exit"))
if d.get("verdict") != v:
    bad.append("verdict %s vs exit %s" % (d.get("verdict"), d.get("exit")))
print(("OK " if not bad else "BAD ") + "; ".join(bad) + " :: " + d.get("reason", "")[:200])' "$spec" 2>&1)
  if [ "$got" = "$want" ] && [ "${chk%% *}" = OK ]; then pass "$(printf '%s' "B:$name: exit $got ${chk#OK }" | cut -c1-260)"
  else fail "B:$name: want exit $want [$spec], got exit $got :: $chk :: $(tail -c 300 "$W/err" | tr '\n' ' ')"; fi
}
A=("$GOOD" "$CHAL" "$CFG" --threads 4)
# B1 baseline: the staged package as it is (real binaries)
e2e real-default-good-both-off 0 "con-leche=off,nanoda=off" "$CS" "${A[@]}"   # installing the delta changes no verdict
e2e real-optin-con-leche-good 0 "con-leche=accepted,nanoda=off" "$CS" "${A[@]}" --kernel con-leche
e2e real-both-required-good 0 "con-leche=accepted,nanoda=accepted" "$CS" "${A[@]}" --require-kernel con-leche --require-kernel nanoda
e2e real-kernel-bad-two-kernel-reject 1 "con-leche=not consulted" "$CS" "$W/kernel-bad.export" "$CHAL" "$CFG" --threads 4 --kernel con-leche
e2e real-axiom-bad 1 "con-leche=off,nanoda=not consulted" "$CS" "$BAD" "$CHAL" "$CFG" --threads 4 --kernel nanoda
e2e real-skip-con-leche 0 "con-leche=off,nanoda=off" "$CS" "${A[@]}" --skip-kernel con-leche
e2e real-skip-vs-require 2 "" "$CS" "${A[@]}" --require-kernel con-leche --skip-kernel con-leche
e2e real-unknown-kernel 2 "" "$CS" "${A[@]}" --kernel con-ron
e2e real-two-names-one-arg 2 "" "$CS" "${A[@]}" --require-kernel "con-leche nanoda"   # one name per option (review finding 4)
e2e real-kjobs-leading-zero 0 "nanoda=accepted" "$CS" "${A[@]}" --require-kernel nanoda --kernel-jobs 08   # decimal (finding 5)
e2e real-grace-leading-zero 0 "nanoda=accepted" "$CS" "${A[@]}" --kernel nanoda --kernel-grace 08   # decimal, not octal (G6)
# --kernel-jobs defaults to the thread count AFTER the ulimit -v cap (G6): 64 threads requested under a 32 GiB address space
# -> T = 8 -> the extra kernel starts with jobs=8 (asserted from the log; the v2.2 two-kernel self-test itself does not run
# under such a limit, so the verdict there is DECLINED either way)
( ulimit -v 33554432; "$CS" "$GOOD" "$CHAL" "$CFG" --threads 64 --kernel nanoda --log "$W/as.log" > /dev/null 2>&1 )
grep -q "threads 64 -> 8" "$W/as.log" && grep -q "extra kernel nanoda started (optional, jobs=8)" "$W/as.log" \
  && pass "C:kjobs-after-address-space-cap: threads 64 -> 8, nanoda jobs=8" \
  || fail "C:kjobs-after-address-space-cap: $(grep -E 'address-space|extra kernel nanoda started' "$W/as.log" | tr '\n' ' ' | cut -c1-200)"
# B2 con-leche mocks (default-on, optional)
P=$(mkpkg clrej); mock "$P" con-leche "$(replay "$F/cl-rc1-invalid-arena-badDef.log" 1)"
e2e cl-rejects-veto 1 "con-leche=rejected" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
e2e cl-rejects-required 1 "con-leche=rejected" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche
e2e cl-rejects-but-skipped 0 "con-leche=off" "$P/check/sound/check-sound.sh" "${A[@]}" --skip-kernel con-leche
e2e cl-rejects-default-off 0 "con-leche=off" "$P/check/sound/check-sound.sh" "${A[@]}"   # opt-in: a rejecting con-leche changes nothing unless enabled
e2e cl-rejects-two-kernel-rejected 1 "con-leche=not consulted" "$P/check/sound/check-sound.sh" "$BAD" "$CHAL" "$CFG" --threads 4 --kernel con-leche
P=$(mkpkg cldecl); mock "$P" con-leche "$(replay "$F/cl-rc2-declined-axiom.log" 2)"
e2e cl-declines-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
e2e cl-declines-required 2 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche
P=$(mkpkg clnat); mock "$P" con-leche "$(replay "$F/cl-rc1-natlimit.log" 1)"
e2e cl-natlimit-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
P=$(mkpkg cloom); mock "$P" con-leche "echo 'INTERNAL PANIC: out of memory' >&2; exit 1"
e2e cl-oom-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
e2e cl-oom-required 2 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche
P=$(mkpkg clabrt); mock "$P" con-leche 'kill -ABRT $$'
e2e cl-abort-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
P=$(mkpkg clkill); mock "$P" con-leche 'kill -KILL $$'
e2e cl-sigkill-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
P=$(mkpkg clslow); mock "$P" con-leche 'sleep 120; exit 1'
e2e cl-slow-grace-timeout 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel-grace 3 --kernel con-leche
e2e cl-slow-required-global-timeout 2 "" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche --timeout 20
P=$(mkpkg clacc); mock "$P" con-leche "$(replay "$F/cl-rc0-t22-accepted.log" 0)"
e2e cl-accepts-kernel-invalid 1 "con-leche=not consulted" "$P/check/sound/check-sound.sh" "$W/kernel-bad.export" "$CHAL" "$CFG" --threads 4 --require-kernel con-leche
e2e cl-accepts-axiom-bad 1 "con-leche=not consulted" "$P/check/sound/check-sound.sh" "$BAD" "$CHAL" "$CFG" --threads 4 --require-kernel con-leche
P=$(mkpkg clnoline); mock "$P" con-leche 'echo "con-leche: something else"; exit 0'
e2e cl-rc0-without-line-required 2 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche
# self-test failures: a mock that accepts EVERYTHING (also selftest_kbad) and one that rejects everything (also selftest_good)
P=$(mkpkg clall); printf '#!/bin/sh\necho "con-leche: accepted 1 declarations (--verified)"; exit 0\n' > "$P/mock-all"; chmod 755 "$P/mock-all"
s=$(sha256sum "$P/mock-all" | cut -d' ' -f1); sed -i "s#^PIN con_leche .*#PIN con_leche $s $P/mock-all#" "$P/check/sound/pins.env"
e2e cl-selftest-fails-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
e2e cl-selftest-fails-required 2 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche
e2e cl-selftest-fails-required-preflight 2 "" "$P/check/sound/check-sound.sh" --preflight --require-kernel con-leche
P=$(mkpkg clnone); printf '#!/bin/sh\necho "con-leche: invalid: type mismatch in theorem x [at theorem x]"; exit 1\n' > "$P/mock-none"; chmod 755 "$P/mock-none"
s=$(sha256sum "$P/mock-none" | cut -d' ' -f1); sed -i "s#^PIN con_leche .*#PIN con_leche $s $P/mock-none#" "$P/check/sound/pins.env"
e2e cl-rejects-all-selftest-fails 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
# pin integrity / configuration
P=$(mkpkg clsha); mock "$P" con-leche "exit 0"; echo "# tampered" >> "$P/mock-con-leche"
e2e cl-wrong-sha256 2 "" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
P=$(mkpkg clmiss); sed -i "s#^PIN con_leche \([0-9a-f]*\) .*#PIN con_leche \1 $W/no-such-con-leche#" "$P/check/sound/pins.env"
e2e cl-missing-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
e2e cl-missing-required 2 "" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche
P=$(mkpkg nopins); grep -vE '^PIN (con_leche|nanoda|selftest_kbad) ' "$H/pins.env" > "$P/check/sound/pins.env"
e2e no-pin-lines-v22-behaviour 0 "con-leche=off,nanoda=off" "$P/check/sound/check-sound.sh" "${A[@]}"
e2e no-pin-lines-optin 0 "con-leche=not configured" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
e2e no-pin-lines-required 2 "" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel nanoda
P=$(mkpkg nokbad); grep -vE '^PIN selftest_kbad ' "$H/pins.env" > "$P/check/sound/pins.env"
e2e no-kbad-optional 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche
e2e no-kbad-required 2 "" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel con-leche
# B3 nanoda mocks (opt-in)
P=$(mkpkg narej); mock "$P" nanoda "$(replay "$F/na-rc101-reject-tc-arena-badDef.log" 101)"
e2e na-off-by-default 0 "nanoda=off" "$P/check/sound/check-sound.sh" "${A[@]}"
e2e na-optin-rejects 1 "nanoda=rejected" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel nanoda
e2e na-required-rejects 1 "nanoda=rejected" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel nanoda
P=$(mkpkg naso); mock "$P" nanoda "$(replay "$F/na-rc134-t22-stack-overflow-32mib.log" 134)"
e2e na-stack-overflow-optional 0 "nanoda=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel nanoda
e2e na-stack-overflow-required 2 "nanoda=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel nanoda
P=$(mkpkg napars); mock "$P" nanoda "$(replay "$F/na-rc101-panic-parser.log" 101)"
e2e na-parser-panic-optional 0 "nanoda=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel nanoda
P=$(mkpkg nasig); mock "$P" nanoda 'kill -SEGV $$'
e2e na-sigsegv-optional 0 "nanoda=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel nanoda
P=$(mkpkg nacfg); mock "$P" nanoda 'grep -q "\"stack_size_bytes\":1073741824" "$L" && grep -q "\"unsafe_permit_all_axioms\":true" "$L" && grep -q "\"nat_extension\":true" "$L" || { echo "Error: config"; exit 1; }'
e2e na-config-has-1gib-stack 0 "nanoda=accepted" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel nanoda
# both: con-leche rejects while nanoda accepts -> REJECTED; nanoda rejects while con-leche declines -> REJECTED
P=$(mkpkg mix1); mock "$P" con-leche "$(replay "$F/cl-rc1-invalid-arena-badDef.log" 1)"
e2e mix-cl-rejects-na-accepts 1 "con-leche=rejected,nanoda=accepted" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel nanoda --kernel con-leche
P=$(mkpkg mix2); mock "$P" con-leche "$(replay "$F/cl-rc2-declined-axiom.log" 2)"; mock "$P" nanoda "$(replay "$F/na-rc101-reject-inductive.log" 101)"
e2e mix-na-rejects-cl-declines 1 "con-leche=not decided,nanoda=rejected" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel nanoda --kernel con-leche

# ---------------- Part C: service variant, memory guard ----------------
P=$(mkpkg svc); mock "$P" con-leche "$(replay "$F/cl-rc1-invalid-arena-badDef.log" 1)"
IC=$W/icache; mkdir -m 700 "$IC"
e2e svc-cl-rejects 1 "con-leche=rejected" "$P/check/sound/check-sound-svc.sh" "${A[@]}" --integrity-cache "$IC" --kernel con-leche
e2e svc-cl-rejects-cache-hit 1 "con-leche=rejected" "$P/check/sound/check-sound-svc.sh" "${A[@]}" --integrity-cache "$IC" --kernel con-leche
echo "# tampered after the integrity record" >> "$P/mock-con-leche"
e2e svc-cl-tampered-after-record 2 "" "$P/check/sound/check-sound-svc.sh" "${A[@]}" --integrity-cache "$IC" --kernel con-leche
e2e svc-real-good 0 "con-leche=accepted" "$H/check-sound-svc.sh" "${A[@]}" --kernel con-leche
leftover() { sleep 2; pgrep -f "sleep $1" | wc -l; }
P=$(mkpkg leak1); mock "$P" con-leche 'sleep 3171; exit 1'
e2e leak-rejected-with-timeout 1 "con-leche=not consulted" "$P/check/sound/check-sound.sh" "$BAD" "$CHAL" "$CFG" --threads 4 --kernel con-leche --timeout 900
n=$(leftover 3171); [ "$n" = 0 ] && pass "C:leak-rejected-with-timeout-no-leftover: 0 processes" || { fail "C:leak-rejected-with-timeout-no-leftover: $n left"; pkill -KILL -f "sleep 3171"; }
P=$(mkpkg leak2); mock "$P" con-leche 'sleep 3172; exit 1'
e2e leak-grace-with-timeout 0 "con-leche=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --kernel con-leche --kernel-grace 3 --timeout 900
n=$(leftover 3172); [ "$n" = 0 ] && pass "C:leak-grace-with-timeout-no-leftover: 0 processes" || { fail "C:leak-grace-with-timeout-no-leftover: $n left"; pkill -KILL -f "sleep 3172"; }
P=$(mkpkg leak3); mock "$P" nanoda 'sleep 3173; exit 0'
e2e leak-required-global-timeout 2 "nanoda=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --require-kernel nanoda --timeout 15
n=$(leftover 3173); [ "$n" = 0 ] && pass "C:leak-required-global-timeout-no-leftover: 0 processes" || { fail "C:leak-required-global-timeout-no-leftover: $n left"; pkill -KILL -f "sleep 3173"; }
# a --keep-config-kernels kernel (inside ccmp's sandbox, $W/tmp writable) plants symlinks where the v2.3-H r2 wrapper used to
# write and tries to write the new record dir $W/xko: the victim outside every sandbox stays untouched, the record is the real one
echo untouched > "$W/victim.txt"
printf '#!/bin/sh
W=$(dirname "$1")
ln -sf "%s" "$W/tmp/leg-con-leche.rc"; ln -sf "%s" "$W/tmp/leg-con-leche.log"
echo 1 > "$W/xko/leg-con-leche.rc" 2>/dev/null; ln -sf "%s" "$W/xko/leg-x" 2>/dev/null
exit 0
' "$W/victim.txt" "$W/victim.txt" "$W/victim.txt" > "$W/evil-kept.sh"; chmod 755 "$W/evil-kept.sh"
python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("enable_nanoda",None); c["external_kernels"]={"evil":[sys.argv[2]]}; json.dump(c,open(sys.argv[3],"w"))' "$CFG" "$W/evil-kept.sh" "$W/evil-cfg.json"
e2e xko-kept-kernel-cannot-reach-records 0 "con-leche=accepted" "$CS" "$GOOD" "$CHAL" "$W/evil-cfg.json" --threads 4 --keep-config-kernels --kernel con-leche
[ "$(cat "$W/victim.txt")" = untouched ] && pass "C:xko-victim-untouched: the file outside every sandbox was not written" || fail "C:xko-victim-untouched: victim now '$(cat "$W/victim.txt")'"
CG=${CGRUN:-$(command -v cgrun 2>/dev/null || echo /usr/local/bin/cgrun)}
PA=$(mkpkg auto); sed -i 's/^XK_CONLECHE_DEFAULT=off /XK_CONLECHE_DEFAULT=auto/' "$PA/check/sound/check-sound.sh"
grep -q '^XK_CONLECHE_DEFAULT=auto' "$PA/check/sound/check-sound.sh" && pass "C:default-switch-is-one-line: XK_CONLECHE_DEFAULT=auto in a copy" || fail "C:default-switch-is-one-line"
e2e switch-auto-default-on 0 "con-leche=accepted" "$PA/check/sound/check-sound.sh" "${A[@]}"
if [ -x "$CG" ] && sudo -n true 2>/dev/null; then
  cgrun_e2e() { local name=$1 want=$2 spec=$3; shift 3; e2e "$name" "$want" "$spec" "$CG" --mem 3G -- "$PA/check/sound/check-sound.sh" "$@"; }
  cgrun_e2e memguard-3g-skips-auto-con-leche 0 "con-leche=skipped (memory)" "${A[@]}"
  cgrun_e2e memguard-3g-forced-con-leche 0 "con-leche=accepted" "${A[@]}" --kernel con-leche
else
  echo "SKIP memory guard (cgrun (CGRUN) or sudo -n not available here)"
fi
# ---------------- Part D: the same wiring with the 4.37.0-rc1 pins (check/sound/pins-437.env) ----------------
P437=$H/pins-437.env
e2e d437-real-good 0 "con-leche=accepted,nanoda=accepted" "$CS" "${A[@]}" --pins "$P437" --kernel nanoda --kernel con-leche
e2e d437-real-kernel-bad 1 "con-leche=not consulted" "$CS" "$W/kernel-bad.export" "$CHAL" "$CFG" --threads 4 --pins "$P437" --kernel con-leche
P=$(mkpkg d437); mock "$P" con-leche "$(replay "$F/cl-rc1-invalid-arena-badDef.log" 1)"; mock "$P" nanoda "$(replay "$F/na-rc134-t22-stack-overflow-32mib.log" 134)"
e2e d437-cl-rejects 1 "con-leche=rejected" "$P/check/sound/check-sound.sh" "${A[@]}" --pins "$P/check/sound/pins-437.env" --kernel con-leche
e2e d437-na-overflow-optional 0 "con-leche=off,nanoda=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --pins "$P/check/sound/pins-437.env" --skip-kernel con-leche --kernel nanoda
e2e d437-na-overflow-required 2 "con-leche=off,nanoda=not decided" "$P/check/sound/check-sound.sh" "${A[@]}" --pins "$P/check/sound/pins-437.env" --skip-kernel con-leche --require-kernel nanoda
# ---------------- Part E: con-leche's documented false reject of valid official output (built here from source) ----------------
T36=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$H/../../config/components.json" 2>/dev/null)
if [ -x "$T36/bin/lean" ] && [ -x "$T36/bin/leanexport" ]; then
  D=$W/thm; mkdir -p "$D"; cp "$FX/thmunfold/Main.lean" "$FX/thmunfold/Challenge.lean" "$D/"
  ( cd "$D" && "$T36/bin/lean" Main.lean -o Main.olean && "$T36/bin/lean" Challenge.lean -o Challenge.olean \
    && PATH=$T36/bin:/usr/bin:/bin LEAN_PATH=$D:$T36/lib/lean "$T36/bin/leanexport" Main > solution.export \
    && PATH=$T36/bin:/usr/bin:/bin LEAN_PATH=$D:$T36/lib/lean "$T36/bin/leanexport" Challenge > challenge.export ) > "$W/thm.log" 2>&1
  if [ -s "$D/solution.export" ] && [ -s "$D/challenge.export" ]; then
    TA=("$D/solution.export" "$D/challenge.export" "$FX/thmunfold/comparator.json" --threads 8)
    e2e thmunfold-default-accepted 0 "con-leche=off,nanoda=off" "$CS" "${TA[@]}"
    e2e thmunfold-con-leche-KNOWN-FALSE-REJECT 1 "con-leche=rejected" "$CS" "${TA[@]}" --kernel con-leche
    grep -q -- "--skip-kernel con-leche gives the two-kernel verdict" "$W/out" && pass "E:thmunfold-reject-reason-names-remedy" || fail "E:thmunfold-reject-reason-names-remedy: $(tail -1 "$W/out" | cut -c1-300)"
    e2e thmunfold-nanoda-accepted 0 "nanoda=accepted" "$CS" "${TA[@]}" --kernel nanoda
  else fail "E:thmunfold-build: $(tail -3 "$W/thm.log" | tr '\n' ' ')"; fi
else
  echo "SKIP Part E (no official 4.36 lean/leanexport at '$T36')"
fi
echo "RESULT pass=$passes fail=$fails"
[ "$fails" = 0 ]
