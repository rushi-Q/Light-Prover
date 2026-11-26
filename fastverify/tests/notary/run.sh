#!/bin/bash
# tests/notary/run.sh -- regression test of the notary checker.
# Every row FAILS on the earlier notary (5e40f06c; most also on 00394f3a) and PASSES now.
# Usage: run.sh            (tests the package this file is in: FV = ../..)
# Needs: the pinned notary binaries / self-test fixtures of FV's check/notary/pins.env, bwrap, /dev/shm.
set -uo pipefail
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../.." && pwd)
NOTARY=$FV/check/notary
CN=$NOTARY/check-notary.sh
D=$HERE/data
( cd "$D" && sha256sum -c --quiet SHA256SUMS ) || { echo "RESULT pass=0 fail=1 (data SHA256SUMS mismatch)"; exit 1; }
W=$(mktemp -d "${NOTARY_TEST_DIR:-/dev/shm}/notary.XXXXXX")
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
. "$HERE/stage.sh"
PASS=0; FAIL=0
ok()   { echo "PASS $1: $2"; PASS=$((PASS+1)); }
skip() { echo "SKIP $1: $2"; }   # neither PASS nor FAIL
bad()  { echo "FAIL $1: $2"; FAIL=$((FAIL+1)); }
# row NAME WANT_RC PRED [TIMEOUT] -- CMD...: PASS iff CMD exits WANT_RC (or any of "0|2") and PRED holds on its last
# stdout line parsed as JSON (j)
row() {
  local name=$1 want=$2 pred=$3 tmo=600; shift 3
  if [ "$1" != -- ]; then tmo=$1; shift; fi; shift
  local out rc last
  out=$(timeout -k 5 "$tmo" "$@" 2>"$W/err.log"); rc=$?
  last=$(printf '%s\n' "$out" | tail -n 1)
  if [[ "|$want|" == *"|$rc|"* ]] && python3 -I -c "import json,os,sys; j=json.loads(sys.argv[1]); sys.exit(0 if ($pred) else 1)" "$last" 2>/dev/null; then
    ok "$name" "rc=$rc :: $(printf '%s' "$last" | cut -c1-200)"
  else
    bad "$name" "want rc=$want pred=[$pred]; got rc=$rc :: $(printf '%s' "$last" | cut -c1-300)"
  fi
}
G=("$SG" "$SC" "$SCFG" --threads 4)

echo "=== gruszka-r7's digest of the candidate is mandatory; the attestation lists who agreed ==="
row con-ron-attests-three-legs "0|2" \
  'j["verdict"]=="DECLINED" or (j["verdict"]=="ACCEPTED" and j["r7_digest"]["attestation"]["env_sha256_v1"]["agreed"]==["ccmp","lean","gruszka"] and j["r7_digest"]["attestation"]["env_strict_sha256_v1"]["agreed"]==["ccmp","lean"] and j["kernels"].split(",")[0]=="gruszka")' \
  -- "$CN" "${G[@]}" --kernels con-ron
row default-attestation 0 \
  'j["verdict"]=="ACCEPTED" and j["r7_digest"]["attestation"]["env_sha256_v1"]["agreed"]==["ccmp","lean","gruszka"] and j["r7_digest"]["strict_matched_legs"]==["ccmp","lean"] and j["r7_digest"]["attestation"]["const_count"]["value"]==584 and type(j["r7_digest"]["legs"]["gruszka"]["const_count"]) is int' \
  -- "$CN" "${G[@]}"
S=$W/s-nogzdigest; mk_stage "$S" gruszka
cat > "$STAGE_DIR/bin/gruszka" <<EOF
#!/bin/sh
"$STAGE_DIR/bin/gruszka.real" "\$@"; rc=\$?
case "\$GRUSZKA_DIGEST_OUT" in */digest-k2.txt) rm -f "\$GRUSZKA_DIGEST_OUT";; esac
exit \$rc
EOF
write_pins
row con-ron-without-gruszka-digest-declines 2 'j["verdict"]=="DECLINED" and "missing or invalid gruszka digest" in j["reason"]' \
  -- "$STAGE_DIR/check-notary.sh" "${G[@]}" --kernels con-ron

echo "=== an official comparator configuration error is never a verdict; the rewrite is reported ==="
for c in config-type cfg-ek-notarray cfg-ek-empty cfg-ek-emptyname cfg-exponent; do   # cfg-ek-emptyname: an empty kernel name
  row "official-config-error-$c" 2 'j["verdict"]=="DECLINED" and "config refused" in j["reason"]' -- "$CN" "$SG" "$SC" "$D/$c.json" --threads 4
done
# (previously this one was DECLINED too, but only through a Python traceback while re-encoding the lone surrogate)
row official-config-error-surrogate-dupkey-refused-cleanly 2 'j["verdict"]=="DECLINED" and "duplicate object key" in j["reason"] and "Traceback" not in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-surrogate-dupkey.json" --threads 4
row keep-config-kernels-nondict-not-dropped 2 'j["verdict"]=="DECLINED" and "external_kernels" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-ek-list.json" --threads 4 --keep-config-kernels
# the challenge's configured kernels are run (Lake's kernel set) and reported (was: dropped by the rewrite)
row rewrite-visible-in-report 0 \
  'j["verdict"]=="ACCEPTED" and j["config_rewrite"]["mode"]=="keep-config-kernels" and j["config_rewrite"]["dropped"]==[] and j["config_rewrite"]["challenge_external_kernels"]==["nanoda"] and "config kernel nanoda" in j["config_rewrite"]["judge_external_kernels"] and j["kernel_status"]["kept-0"]["status"]=="accepted"' \
  -- "$CN" "${G[@]}"

# (as for the five other judges, tests/config-types Part C): official configs the notary must not decline (the
# official 4.36 comparator accepts all three: results/official-comparator-4.36.txt)
row extra-key-1e309-not-infinity 0 'j["verdict"]=="ACCEPTED"' -- "$CN" "$SG" "$SC" "$D/cfg-extra-key-1e309.json" --threads 4
row kept-kernel-empty-argument 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-kept-empty-arg.json" --threads 4 --keep-config-kernels
row kept-kernel-cr-in-name-leg-record 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-kept-cr-name.json" --threads 4 --keep-config-kernels

echo "=== malformed leg evidence is DECLINED (strict digest and status parsing) ==="
S=$W/s-tamper; mk_stage "$S" ccmp plc gruszka
# the three wrappers run the real binary, then apply the edit named in $STAGE_DIR/bin/mode to the digest they wrote
cat > "$STAGE_DIR/bin/edit.sh" <<'EOF'
#!/bin/sh
# edit.sh MODE LEG DIGESTFILE (LEG = ccmp | lean | k2 for the candidate, st-* for self-test files)
m=$1; leg=$2; f=$3
[ -f "$f" ] || exit 0
case "$m:$leg" in
  dup:lean) { echo "env_sha256_v1=0000000000000000000000000000000000000000000000000000000000000000"; cat "$f"; } > "$f.x" && mv "$f.x" "$f";;
  garbage:lean) echo "garbage line" >> "$f";;
  lead0:ccmp|lead0:lean|lead0:k2) sed -i 's/^const_count=/const_count=0/' "$f";;
  neg:ccmp|neg:lean|neg:k2) sed -i 's/^const_count=.*/const_count=-1/' "$f";;
  stdig:st-ccmp-good|stdig:st-lean-good|stdig:st-k2-good) sed -i 's/^env_sha256_v1=./env_sha256_v1=0/' "$f";;
esac
exit 0
EOF
cat > "$STAGE_DIR/bin/ccmp" <<EOF
#!/bin/sh
m=\$(cat "$STAGE_DIR/bin/mode"); for a do last=\$a; done
case "\$m:\$last" in
  badctl-unrelated:"$SB") echo "error: simulated launcher failure"; exit 1;;
  badctl-sleep:"$SB") exec sleep 100000;;
  ccmpio:*/solution.export) mkdir -p "\$CCMP_DIGEST_OUT.tmp";;
esac
"$STAGE_DIR/bin/ccmp.real" "\$@"; rc=\$?
case "\$CCMP_DIGEST_OUT" in
  */digest-ccmp.txt) "$STAGE_DIR/bin/edit.sh" "\$m" ccmp "\$CCMP_DIGEST_OUT";;
  */digest-selftest-ccmp-good.txt) "$STAGE_DIR/bin/edit.sh" "\$m" st-ccmp-good "\$CCMP_DIGEST_OUT";;
  */digest-selftest-ccmp-bad.txt) [ "\$m" = badctl-digest ] && printf 'env_sha256_v1=%064d\nenv_strict_sha256_v1=%064d\nconst_count=1\ndigest_ms=0\n' 0 0 > "\$CCMP_DIGEST_OUT";;
esac
exit \$rc
EOF
cat > "$STAGE_DIR/bin/plc" <<EOF
#!/bin/sh
m=\$(cat "$STAGE_DIR/bin/mode")
case "\$m:\$PCHK_DIGEST_OUT" in leanio:*/digest-lean.txt) mkdir -p "\$PCHK_DIGEST_OUT.tmp";; esac
"$STAGE_DIR/bin/plc.real" "\$@"; rc=\$?
case "\$PCHK_DIGEST_OUT" in
  */digest-lean.txt) "$STAGE_DIR/bin/edit.sh" "\$m" lean "\$PCHK_DIGEST_OUT";;
  */digest-selftest-lean-$(basename "$SG").txt) "$STAGE_DIR/bin/edit.sh" "\$m" st-lean-good "\$PCHK_DIGEST_OUT";;
esac
exit \$rc
EOF
cat > "$STAGE_DIR/bin/gruszka" <<EOF
#!/bin/sh
m=\$(cat "$STAGE_DIR/bin/mode")
"$STAGE_DIR/bin/gruszka.real" "\$@"; rc=\$?
case "\$GRUSZKA_DIGEST_OUT" in
  */digest-k2.txt) "$STAGE_DIR/bin/edit.sh" "\$m" k2 "\$GRUSZKA_DIGEST_OUT"
     case "\$m" in lean-rc-junk|lean-rc-nul)   # damage the Lean leg's recorded status after its wrapper wrote it
       t=\$(dirname "\$GRUSZKA_DIGEST_OUT"); i=0
       while [ ! -s "\$t/leg-lean.rc" ] && [ \$i -lt 300 ]; do sleep 0.1; i=\$((i+1)); done
       if [ "\$m" = lean-rc-junk ]; then printf '0junk\n' > "\$t/leg-lean.rc"; else printf '0\n\000' > "\$t/leg-lean.rc"; fi;;
     lean-rc-symlink)   # the Lean status replaced by a symlink to a file reading "0\n"
       t=\$(dirname "\$GRUSZKA_DIGEST_OUT"); i=0
       while [ ! -s "\$t/leg-lean.rc" ] && [ \$i -lt 300 ]; do sleep 0.1; i=\$((i+1)); done
       printf '0\n' > "\$t/zero.rc"; ln -sf zero.rc "\$t/leg-lean.rc";;
     esac;;
  */digest-selftest-k2-$(basename "$SG").txt) "$STAGE_DIR/bin/edit.sh" "\$m" st-k2-good "\$GRUSZKA_DIGEST_OUT";;
esac
exit \$rc
EOF
write_pins
TS=$STAGE_DIR/check-notary.sh
mode() { echo "$1" > "$STAGE_DIR/bin/mode"; }
mode none
row stage-control-honest-accepts 0 'j["verdict"]=="ACCEPTED" and "-f6" in j["wiring"]' -- "$TS" "${G[@]}"
mode dup
row duplicate-digest-field-declines 2 'j["verdict"]=="DECLINED" and "invalid lean digest" in j["reason"]' -- "$TS" "${G[@]}"
mode garbage
row malformed-digest-line-declines 2 'j["verdict"]=="DECLINED" and "invalid lean digest" in j["reason"]' -- "$TS" "${G[@]}"
mode lead0
row noncanonical-count-declines 2 'j["verdict"]=="DECLINED" and "canonical" in j["reason"]' -- "$TS" "${G[@]}"
mode neg
row negative-count-declines 2 'j["verdict"]=="DECLINED" and "canonical" in j["reason"]' -- "$TS" "${G[@]}"
mode lean-rc-junk
row damaged-status-declines 2 'j["verdict"]=="DECLINED" and "Lean leg recorded exit" in j["reason"]' -- "$TS" "${G[@]}"
mode lean-rc-nul
row status-with-trailing-nul-declines 2 'j["verdict"]=="DECLINED" and "Lean leg recorded exit" in j["reason"]' -- "$TS" "${G[@]}"
mode lean-rc-symlink
row report-status-is-the-gates-status 2 'j["verdict"]=="DECLINED" and "Lean leg recorded exit" in j["reason"] and j["legs"]["lean"]["rc"] is None' -- "$TS" "${G[@]}"

echo "=== the self-test's controls must behave as expected (not just exit 0 / 1) ==="
mode badctl-unrelated
row negative-control-unrelated-failure-declines 2 'j["verdict"]=="DECLINED" and "negative control" in j["reason"]' -- "$TS" "${G[@]}"
mode badctl-digest
row negative-control-digest-declines 2 'j["verdict"]=="DECLINED" and "negative control" in j["reason"] and "digest" in j["reason"]' -- "$TS" "${G[@]}"
mode stdig
row positive-control-unpinned-digest-declines 2 'j["verdict"]=="DECLINED" and "R7_SELFTEST_DIGEST_UNEXPECTED" in j["reason"]' -- "$TS" "${G[@]}"

echo "=== bounded self-test, evidence I/O failures, NDJSON naming, declaration order, 32-bit vetoes ==="
mode badctl-sleep
row selftest-bounded-by-timeout 2 'j["verdict"]=="DECLINED" and "time limit" in j["reason"]' 90 -- "$TS" "${G[@]}" --timeout 5
mode leanio
row lean-digest-io-failure-declines 2 'j["verdict"]=="DECLINED" and "evidence" in j["reason"]' -- "$TS" "${G[@]}"
mode ccmpio
row ccmp-digest-io-failure-declines 2 'j["verdict"]=="DECLINED" and "evidence" in j["reason"]' -- "$TS" "${G[@]}"
mode none
row leading-space-ndjson-not-rejected "0|2" 'j["verdict"] in ("ACCEPTED","DECLINED")' -- "$CN" "$D/good-leading-space.export" "$SC" "$SCFG" --threads 4
row order-unknown-constant-declines 2 'j["verdict"]=="DECLINED" and j["kernel_status"]["gruszka"]["status"]=="not decided" and "unknown constant" in j["kernel_status"]["gruszka"]["message"]' \
  -- "$CN" "$D/order-ba.export" "$SC" "$D/cfg-leanonly.json" --threads 4
row regular-height-ge-2p32-vetoed 2 'j["verdict"]=="DECLINED" and "regular reducibility height 8589934591" in j["reason"]' \
  -- "$CN" "$D/regular-2p33m1.export" "$SC" "$D/cfg-leanonly.json" --threads 4
row veto-scan-proj 2 'j["veto"] is True and "projection index" in j["reasons"][0]' -- "$CN" --veto-scan "$D/veto-proj.txt"
row veto-scan-proj-escaped-key 2 'j["veto"] is True and "projection index" in j["reasons"][0]' -- "$CN" --veto-scan "$D/veto-proj-escaped.txt"
row veto-scan-bvar 2 'j["veto"] is True and "bound variable" in j["reasons"][0]' -- "$CN" --veto-scan "$D/veto-bvar.txt"
row veto-scan-file-with-nul-byte 2 'j["veto"] is True and "regular reducibility height" in j["reasons"][0]' -- "$CN" --veto-scan "$D/veto-nul.txt"
row veto-scan-names-and-literals-pass 2 'j["veto"] is False and j["candidates"]==1' -- "$CN" --veto-scan "$D/veto-none.txt"
# ref_digest.py (the independent oracle): the official reader's schema; an exception is DECLINED, never a traceback
refrow() {  # NAME WANT_RC GREP_PATTERN FILE
  local out rc; out=$(python3 -I "$NOTARY/ref_digest.py" "$4" 2>&1); rc=$?
  if [ "$rc" = "$2" ] && printf '%s\n' "$out" | grep -qE -- "$3" && ! printf '%s\n' "$out" | grep -q Traceback; then ok "$1" "rc=$rc :: $(printf '%s' "$out" | tr '\n' ' ' | cut -c1-160)"
  else bad "$1" "want rc=$2 /$3/; got rc=$rc :: $(printf '%s' "$out" | tr '\n' ' ' | cut -c1-200)"; fi
}
refrow refdigest-duplicate-declaration-declined 2 '^status=DECLINED$' "$D/132_dup_defs.ndjson"
refrow refdigest-regular-height-official-touint32 0 '^env_sha256_v1=aa16bbef8b06ccd0062dd66b65aa485d98664b1036fbda9e529afb8ddf5f8652$' "$D/regular-height.export"
refrow refdigest-nonobject-line-declined 2 '^status=DECLINED$' "$D/ref-nonobject.ndjson"

echo "=== shell-side checks and further items ==="
row unwritable-json-report-declines 2 'j["verdict"]=="DECLINED" and "--json report" in j["reason"]' -- "$CN" "${G[@]}" --json "$W/no-such-dir/report.json"
row threads-02-valid-json 0 'j["verdict"]=="ACCEPTED" and j["threads"]==2' -- "$CN" "$SG" "$SC" "$SCFG" --threads 02
row rejection-basis-claims-no-digest 1 'j["verdict"]=="REJECTED" and "digest verified" not in j["basis"] and j["r7_digest"] is None' -- "$CN" "$SB" "$SC" "$SCFG" --threads 4
# the mock lives in the staged gruszka's bin dir, which the judge binds into its sandbox (a mock under
# /dev/shm alone is hidden by bwrap's --dev /dev and exits 127); the row requires the mock's own exit 1
S=$W/s-mockconron; mk_stage "$S" gruszka
printf '#!/bin/sh\nexec "%s" "$@"\n' "$STAGE_DIR/bin/gruszka.real" > "$STAGE_DIR/bin/gruszka"
cat > "$STAGE_DIR/bin/mock-con-ron" <<'EOF'
#!/bin/sh
echo "con-ron: invalid: simulated broken kernel [at theorem fvSelfTest] (--verified)"
exit 1
EOF
sed -i "s|^CONRON_BIN=\"\$TC36/bin/con-ron\"|CONRON_BIN=\"$STAGE_DIR/bin/mock-con-ron\"|" "$STAGE_DIR/check-notary.sh"
write_pins
row preflight-runs-selected-kernel 2 'j["verdict"]=="DECLINED" and "con-ron (verified) exited with 1" in j["reason"]' -- "$STAGE_DIR/check-notary.sh" --preflight --threads 4 --kernels con-ron
row preflight-reports-kernels-run 0 'j["verdict"]=="PREFLIGHT_OK" and "gruszka,con-ron" in j["reason"] and j["selftest"]["ok"] is True' -- "$CN" --preflight --threads 4 --kernels con-ron

# a symlinked or relative --workdir. The work dir must be visible inside the judge's
# sandbox through the host root (bwrap --ro-bind / /; /tmp and /dev/shm are masked there and hide the problem): /var/tmp
# a setup failure is a FAIL (never a PASS through the checker's /tmp fallback), and the report's
# "workdir" must lie in the requested directory
if [ -z "${NOTARY_TEST_VARTMP:-}" ] && [ ! -w /var/tmp ]; then
  skip symlinked-workdir-accepted "/var/tmp is not writable here (set NOTARY_TEST_VARTMP to a writable directory visible in the judge's sandbox)"
  skip relative-workdir-accepted "/var/tmp is not writable here (set NOTARY_TEST_VARTMP)"
elif VW=$(mktemp -d "${NOTARY_TEST_VARTMP:-/var/tmp}/notary-wd.XXXXXX") && mkdir "$VW/real" "$VW/rel" && ln -s "$VW/real" "$VW/link"; then
  export NOTARY_EXPECT_VWR; NOTARY_EXPECT_VWR=$(realpath -e "$VW")   # the expected path is data (an apostrophe is fine)
  row symlinked-workdir-accepted 0 "j['verdict']=='ACCEPTED' and j['workdir'].startswith(os.environ['NOTARY_EXPECT_VWR'] + '/real/.checkNotary.')" -- "$CN" "${G[@]}" --workdir "$VW/link"
  row relative-workdir-accepted 0 "j['verdict']=='ACCEPTED' and j['workdir'].startswith(os.environ['NOTARY_EXPECT_VWR'] + '/rel/.checkNotary.')" -- bash -c 'cd "$1" || exit 97; shift; exec "$@"' f65 "$VW" "$CN" "${G[@]}" --workdir rel
  rm -rf "$VW"
else
  bad workdir-setup "cannot create the test work dirs under ${NOTARY_TEST_VARTMP:-/var/tmp}"; bad workdir-setup-2 "(both workdir rows)"
fi

echo "=== configured kernels, setup failures, recorded status ==="
row kept-unresolvable-command-declined 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SB" "$SC" "$D/unavailable-with-empty-arg.json" --threads 4 --keep-config-kernels
row default-runs-challenge-kernels 2 'j["verdict"]=="DECLINED" and j["kernel_status"]["kept-0"]["status"]=="not decided" and j["kernel_status"]["kept-0"]["class"]=="nanoda"' \
  -- "$CN" "$D/t032-solution.export" "$D/t032-challenge.export" "$D/t032-comparator.json" --threads 4
row kept-nanoda-format-error-not-rejected 2 'j["verdict"]=="DECLINED" and "expected u32" in j["reason"]' \
  -- "$CN" "$D/t032-solution.export" "$D/t032-challenge.export" "$D/t032-comparator.json" --threads 4 --keep-config-kernels
row kept-label-collision-both-run 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/kernel-label-collision.json" --threads 4
# the package's official stage still refuses these (its cross-version gate reads the original file):
# no verdict here either, but never an "official comparator configuration error" claim from the notary's own decoder
row ignored-integer-no-official-error-claim 2 'j["verdict"]=="DECLINED" and j["reason"].startswith("xversion gate") and "official comparator configuration error" not in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/ignored-integer.json" --threads 4
row ignored-surrogate-normalized-not-refused 2 'j["verdict"]=="DECLINED" and j["reason"].startswith("xversion gate") and "config refused" not in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/unicode-comment.json" --threads 4
row cr-kernel-timing-reported 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-kept-cr-name.json" --threads 4
"$CN" "${G[@]}" > /dev/full 2>/dev/null; frc=$?
if [ "$frc" = 2 ]; then ok stdout-write-failure-exit2 "rc=2"; else bad stdout-write-failure-exit2 "rc=$frc (the report never reached the caller)"; fi
# negative control: a selected kernel's recorded failure on the well-typed bad fixture fails the self-test
S=$W/s-mockconron2; mk_stage "$S" gruszka
printf '#!/bin/sh\nexec "%s" "$@"\n' "$STAGE_DIR/bin/gruszka.real" > "$STAGE_DIR/bin/gruszka"
cat > "$STAGE_DIR/bin/mock-con-ron" <<EOF
#!/bin/sh
case "\$*" in *"$(basename "$SG")") echo "con-ron: accepted 584 declarations (--verified)"; exit 0;; esac
exit 1
EOF
sed -i "s|^CONRON_BIN=\"\$TC36/bin/con-ron\"|CONRON_BIN=\"$STAGE_DIR/bin/mock-con-ron\"|" "$STAGE_DIR/check-notary.sh"
write_pins
row negative-control-selected-kernel-status 2 'j["verdict"]=="DECLINED" and "selftest-con-ron-" in j["reason"] and "status '"'"'1'"'"'" in j["reason"]' -- "$STAGE_DIR/check-notary.sh" --preflight --threads 4 --kernels con-ron

echo "=== configured-kernel sandbox, comparator pin, negative control ==="
# (1) a challenge-configured kernel runs in its own sandbox: it cannot write into the judge's work dir (other legs' status,
# log and R7 digest files); the probe kernel exits 1 if its write succeeds
row config-kernel-cannot-write-work-dir 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-kept-write-probe.json" --threads 4
# (3) comparator pin rule: a pinned challenge needs a pinned comparator config
CSHA=$(sha256sum "$SC" | cut -d' ' -f1); FSHA=$(sha256sum "$SCFG" | cut -d' ' -f1)
row pinned-challenge-without-config-pin-refused 2 'j["verdict"]=="DECLINED" and "requires --comparator-sha256" in j["reason"]' \
  -- "$CN" "${G[@]}" --challenge-sha256 "$CSHA"
row wrong-config-pin-refused 2 'j["verdict"]=="DECLINED" and "!= --comparator-sha256" in j["reason"]' \
  -- "$CN" "${G[@]}" --challenge-sha256 "$CSHA" --comparator-sha256 "$CSHA"
row both-pins-honest-accepted 0 'j["verdict"]=="ACCEPTED" and j["pinned_inputs"]["comparator_pinned"] is True and j["pinned_inputs"]["challenge_pinned"] is True' \
  -- "$CN" "${G[@]}" --challenge-sha256 "$CSHA" --comparator-sha256 "$FSHA"
row both-pins-cheat-rejected 1 'j["verdict"]=="REJECTED" and j["pinned_inputs"]["comparator_sha256"]=="'"$FSHA"'"' \
  -- "$CN" "$SB" "$SC" "$SCFG" --threads 4 --challenge-sha256 "$CSHA" --comparator-sha256 "$FSHA"
# (2) nanoda's exit 101 on the negative control must be its stop on the axiom fvCheat (mock: 101 for another reason)
S=$W/s-mocknanoda; mk_stage "$S" gruszka
printf '#!/bin/sh\nexec "%s" "$@"\n' "$STAGE_DIR/bin/gruszka.real" > "$STAGE_DIR/bin/gruszka"
cat > "$STAGE_DIR/bin/mock-nanoda" <<EOF
#!/bin/sh
if grep -q '$(basename "$SG")' "\$1"; then exit 0; fi
echo "thread 'thread_2' (5) panicked at src/tc.rs:1:1:"; echo "simulated failure unrelated to the axiom"; exit 101
EOF
sed -i "s|^NANODA_BIN=\"\$TC36/bin/nanoda_bin\"|NANODA_BIN=\"$STAGE_DIR/bin/mock-nanoda\"|" "$STAGE_DIR/check-notary.sh"
write_pins
row negative-control-nanoda-101-needs-fvcheat 2 'j["verdict"]=="DECLINED" and "selftest-nanoda-" in j["reason"] and "101" in j["reason"]' \
  -- "$STAGE_DIR/check-notary.sh" --preflight --threads 4 --kernels nanoda

# a configured kernel's failure with a long label is classified on the complete diagnostic (DECLINED)
row long-label-kernel-failure-declined 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-kept-long-label-exit1.json" --threads 4
# Lake's options for a nanoda-style configured kernel (num_threads 4 whatever --threads is)
row config-kernel-gets-lake-options 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' \
  -- "$CN" "$SG" "$SC" "$D/cfg-kept-noda-threads.json" --threads 3
# run by the `which` path (a BusyBox applet keeps its name) and executables anywhere Lake can bind them
if KX=$(mktemp -d /tmp/f6-kexe.XXXXXX) && ln -s /bin/busybox "$KX/wc" && printf '#!/bin/sh\nexit 0\n' > "$KX/check.sh" && chmod 755 "$KX/check.sh"; then
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["external_kernels"]={"applet": [sys.argv[2]+"/wc", "-c"]}; json.dump(c,open(sys.argv[3],"w")); c["external_kernels"]={"tmp-exe": [sys.argv[2]+"/check.sh"]}; json.dump(c,open(sys.argv[4],"w"))' "$SCFG" "$KX" "$W/cfg-applet.json" "$W/cfg-tmpexe.json"
  row applet-name-preserved 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' -- "$CN" "$SG" "$SC" "$W/cfg-applet.json" --threads 4
  row executable-under-tmp-bound 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"]' -- "$CN" "$SG" "$SC" "$W/cfg-tmpexe.json" --threads 4
  rm -rf "$KX"
else bad kexe-setup "cannot create the test executables under /tmp"; fi
# a closed stdout pipe -> exit 2 and a DECLINED --json report (not a SIGPIPE death, 141)
"$CN" "${G[@]}" --json "$W/closed-pipe.json" 2>/dev/null | true; prc=${PIPESTATUS[0]}
if [ "$prc" = 2 ] && grep -q '"verdict":"DECLINED"' "$W/closed-pipe.json" 2>/dev/null; then ok closed-stdout-pipe-exit2 "rc=2"
else bad closed-stdout-pipe-exit2 "rc=$prc :: $(head -c 200 "$W/closed-pipe.json" 2>/dev/null)"; fi

echo "=== v0.1 scope, preflight options, closed pipes ==="
# v0.1 scope: among challenge-configured kernels only the bundled nanoda registration runs (the rows above that use other
# configured kernels now expect the scope decline); enable_nanoda: true is that registration too
row enable-nanoda-registration-runs 0 'j["verdict"]=="ACCEPTED" and j["kernel_status"]["kept-0"]["status"]=="accepted" and j["kernel_status"]["kept-0"]["name"]=="config kernel nanoda"' \
  -- "$CN" "$SG" "$SC" "$D/cfg-enable-nanoda.json" --threads 4
# a challenge judged by Lean >= 4.37 runs that release's kernels in the official stage: configured kernels -> no verdict
row configured-kernel-on-437-challenge-declined 2 'j["verdict"]=="DECLINED" and "v0.1 scope: the challenge is Lean 4.37" in j["reason"]' \
  -- "$CN" "$SG" "$D/challenge-437meta.export" "$SCFG" --threads 4
# nanoda's missing-declaration panic on a reordered export is a limitation (official lean-only accepts it)
row nanoda-ordering-limitation-not-rejected 2 'j["verdict"]=="DECLINED" and j["kernel_status"]["kept-0"]["status"]=="not decided" and "could not resolve a declaration" in j["kernel_status"]["kept-0"]["reason"]' \
  -- "$CN" "$D/order-thm-moved-to-end.export" "$D/rhminiF-challenge.export" "$D/rhminiF-comparator.nanoda.json" --threads 4
# --preflight refuses pin options (it does not use them)
row preflight-with-pins-refused 2 'j["verdict"]=="DECLINED" and "--preflight" in j["reason"]' -- "$CN" --preflight --threads 4 --challenge-sha256 "$CSHA" --comparator-sha256 "$FSHA"
# a closed stderr pipe never kills the judge (the missing-pin refusal still exits 2)
"$CN" "${G[@]}" --challenge-sha256 "$CSHA" --json "$W/stderr-pipe.json" 2>&1 >/dev/null | true; erc=${PIPESTATUS[0]}
if [ "$erc" = 2 ] && grep -q 'requires --comparator-sha256' "$W/stderr-pipe.json" 2>/dev/null; then ok closed-stderr-pipe-exit2 "rc=2"
else bad closed-stderr-pipe-exit2 "rc=$erc :: $(head -c 200 "$W/stderr-pipe.json" 2>/dev/null)"; fi

# diagnostics still reach stderr (only SIGPIPE is suppressed): the usage text without
# arguments, and the verdict line of a run without --log
"$CN" > /dev/null 2> "$W/usage.err"; "$CN" "${G[@]}" > /dev/null 2> "$W/verdict.err"
if grep -q '^usage: check-notary.sh ' "$W/usage.err" && grep -q '^\[checkNotary\] verdict ACCEPTED (exit 0)' "$W/verdict.err"; then ok diagnostics-reach-stderr "usage + verdict line on stderr"
else bad diagnostics-reach-stderr "stderr: $(wc -c < "$W/usage.err") / $(wc -c < "$W/verdict.err") bytes"; fi

echo "=== scope check, rejection classification ==="
# --scope-check = the v0.1 scope decision alone (the public preset applies it before any build); SCOPE_OK / DECLINED
row scope-check-in-scope 0 'j["verdict"]=="SCOPE_OK" and j["exit"]==0 and "within the v0.1 notary scope" in j["reason"]' \
  -- "$CN" --scope-check "$SC" "$SCFG" --threads 4 --challenge-sha256 "$CSHA" --comparator-sha256 "$FSHA"
python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["external_kernels"]={"nanoda": ["nanoda_bin"], "site checker": ["/usr/bin/true"]}; json.dump(c,open(sys.argv[2],"w"))' "$SCFG" "$W/cfg-extra-kernel.json"
row scope-check-extra-kernel-declined 2 'j["verdict"]=="DECLINED" and "v0.1 scope" in j["reason"] and "--preset reference" in j["reason"]' \
  -- "$CN" --scope-check "$SC" "$W/cfg-extra-kernel.json" --threads 4
row scope-check-437-challenge-declined 2 'j["verdict"]=="DECLINED" and "v0.1 scope: the challenge is Lean 4.37" in j["reason"] and "--preset reference" in j["reason"]' \
  -- "$CN" --scope-check "$D/challenge-437meta.export" "$SCFG" --threads 4
row scope-check-pin-rule 2 'j["verdict"]=="DECLINED" and "requires --comparator-sha256" in j["reason"]' \
  -- "$CN" --scope-check "$SC" "$SCFG" --threads 4 --challenge-sha256 "$CSHA"
# the scope decision comes before the cross-version verdict (4.37 challenge with an unsorried definition + nanoda)
row scope-before-xversion-failure 2 'j["verdict"]=="DECLINED" and "v0.1 scope: the challenge is Lean 4.37.0-rc1" in j["reason"] and "--preset reference" in j["reason"]' \
  -- "$CN" "$D/x437-unsorried-challenge.export" "$D/x437-unsorried-challenge.export" "$D/x437-unsorried-enable-nanoda.json" --threads 4
# the Lean leg's exit 1 is a rejection only with its complete, definite rejection line (unit: --lean-classify)
: > "$W/lean-empty.log"; printf 'Lean default kernel rejects the solution: (kernel) type mismatch' > "$W/lean-cut.log"
printf "Lean default kernel rejects the solution: while replaying declaration 'f':\n(kernel) declaration type mismatch, 'f' has type\n" > "$W/lean-def.log"
lc() { "$CN" --lean-classify "$1" 2>/dev/null | head -1; }
if [ "$(lc "$D/log-lean-thread-resource.log")" = "not decided" ] && [ "$(lc "$W/lean-empty.log")" = "not decided" ] && [ "$(lc "$W/nonexistent.log")" = "not decided" ] \
   && [ "$(lc "$W/lean-cut.log")" = "not decided" ] && [ "$(lc "$W/lean-def.log")" = rejected ]; then ok lean-exit1-needs-definite-rejection "thread failure / empty / absent / cut -> not decided; kernel exception -> rejected"
else bad lean-exit1-needs-definite-rejection "$(lc "$D/log-lean-thread-resource.log") / $(lc "$W/lean-empty.log") / $(lc "$W/nonexistent.log") / $(lc "$W/lean-cut.log") / $(lc "$W/lean-def.log")"; fi
# an incomplete / uninformative nanoda panic is not decided; the def_eq assertion stays rejected
nc() { "$CN" --xk-classify nanoda "$1" 101 2>/dev/null | head -1; }
if [ "$(nc "$D/log-nanoda-short.log")" = "not decided" ] && [ "$(nc "$D/log-nanoda-join.log")" = "not decided" ] && [ "$(nc "$D/log-nanoda-assert.log")" = rejected ]; then
  ok nanoda-incomplete-panic-not-decided "short / join -> not decided; def_eq assertion -> rejected"
else bad nanoda-incomplete-panic-not-decided "$(nc "$D/log-nanoda-short.log") / $(nc "$D/log-nanoda-join.log") / $(nc "$D/log-nanoda-assert.log")"; fi
# the export reader's literal diagnostics are definite format rejections (official stage and Lake reject too)
sed '0,/"natVal":"2"/s//"natVal":"two"/' "$SG" > "$W/natval-two.export"
row expr-lit-natval-format-rejected 1 'j["verdict"]=="REJECTED" and "Expr.lit natVal invalid" in j["reason"]' -- "$CN" "$W/natval-two.export" "$SC" "$SCFG" --threads 4
# a log that cannot be opened, with stderr a pipe without reader -> exit 2 (not 141)
"$CN" "${G[@]}" --json "$W/logopen.json" --log "$W/absent-dir/x.log" 2>&1 >/dev/null | true; lrc=${PIPESTATUS[0]}
if [ "$lrc" = 2 ] && grep -q 'cannot write log' "$W/logopen.json" 2>/dev/null; then ok log-open-failure-closed-stderr-exit2 "rc=2"
else bad log-open-failure-closed-stderr-exit2 "rc=$lrc :: $(head -c 200 "$W/logopen.json" 2>/dev/null)"; fi
# the classifier's usage reaches stderr
"$CN" --xk-classify > /dev/null 2> "$W/xk-usage.err"
if grep -q '^usage: check-notary.sh --xk-classify ' "$W/xk-usage.err"; then ok classifier-usage-on-stderr "usage on stderr"
else bad classifier-usage-on-stderr "stderr: $(wc -c < "$W/xk-usage.err") bytes"; fi

echo "=== gruszka worker-table retry ==="
# the candidate's gruszka run declines for worker-table room with more than 1 worker (after writing a WRONG digest): the
# wrapper retries once with 1 worker (the real gruszka-r7) and the R7 gate compares the RETRY's digest -> ACCEPTED
S=$W/s-room1; mk_stage "$S" gruszka
cat > "$STAGE_DIR/bin/gruszka" <<EOF
#!/bin/sh
for a do w=\$a; done
case "\$1" in *solution.ndjson) if [ "\$w" -gt 1 ]; then echo garbage > "\$GRUSZKA_DIGEST_OUT"; echo "declined: Big.decl: a worker table is full"; exit 2; fi;; esac
exec "$STAGE_DIR/bin/gruszka.real" "\$@"
EOF
write_pins
row room-decline-retried-with-1-worker-accepted 0 'j["verdict"]=="ACCEPTED" and j["r7_digest"]["matched_legs"]==["ccmp","lean","gruszka"] and (j["legs"]["k2"].get("retry") or {}).get("first_rc")==2' \
  -- "$STAGE_DIR/check-notary.sh" "${G[@]}"
# no first-attempt digest survives: the first (declined) attempt writes the CORRECT digest, the 1-worker retry accepts
# without writing one -> the R7 gate finds no gruszka digest -> DECLINED (a surviving first-attempt digest would pass)
S=$W/s-room2; mk_stage "$S" gruszka
cat > "$STAGE_DIR/bin/gruszka" <<EOF
#!/bin/sh
for a do w=\$a; done
case "\$1" in *solution.ndjson)
  if [ "\$w" -gt 1 ]; then "$STAGE_DIR/bin/gruszka.real" "\$@" > /dev/null 2>&1; echo "declined: Big.decl: a worker table is full"; exit 2; fi
  unset GRUSZKA_DIGEST_OUT;; esac
exec "$STAGE_DIR/bin/gruszka.real" "\$@"
EOF
write_pins
row first-attempt-digest-never-compared 2 'j["verdict"]=="DECLINED" and "gruszka digest" in j["reason"]' \
  -- "$STAGE_DIR/check-notary.sh" "${G[@]}"

# runtime failures only from the runtime's own lines - prover-chosen names never demote a rejection
# (a real rh-mid mutant log with the longest-job name renamed to Foo.interrupted_sum; names / string literals
# with 'killed', 'Segmentation fault', 'INTERNAL PANIC' in the kernel message) -> rejected; a real runtime line or a
# resource-limit kernel exception -> not decided; nanoda likewise
printf "Lean default kernel rejects the solution: while replaying declaration 'Foo.killedLemma':\n(kernel) declaration type mismatch, 'Foo.killedLemma' has type\n  \"Segmentation fault\" = \"INTERNAL PANIC\"\nbut it is expected to have type\n  True\n" > "$W/n2-names.log"
printf "INTERNAL PANIC: out of memory\nLean default kernel rejects the solution: (kernel) type mismatch\n" > "$W/n2-panic.log"
printf "Lean default kernel rejects the solution: (kernel) deep recursion detected\n" > "$W/n2-deep.log"
printf "thread 'thread_2' (5) panicked at src/tc.rs:955:71:\nassertion failed: self.def_eq(u, v)\nnote: run with RUST_BACKTRACE=1 (Foo.Killed_out_of_memory)\n" > "$W/n2-nanoda-name.log"
printf "memory allocation of 99 bytes failed\nthread 'thread_2' (5) panicked at src/tc.rs:955:71:\nassertion failed: self.def_eq(u, v)\n" > "$W/n2-nanoda-alloc.log"
if [ "$(lc "$D/log-rhmid-M2-renamed-longest.log")" = rejected ] && [ "$(lc "$W/n2-names.log")" = rejected ] && [ "$(lc "$W/n2-panic.log")" = "not decided" ] \
   && [ "$(lc "$W/n2-deep.log")" = "not decided" ] && [ "$(nc "$W/n2-nanoda-name.log")" = rejected ] && [ "$(nc "$W/n2-nanoda-alloc.log")" = "not decided" ]; then
  ok prover-names-never-demote-a-rejection "renamed M2 / quoted names -> rejected; runtime line / resource exception / allocator line -> not decided"
else bad prover-names-never-demote-a-rejection "$(lc "$D/log-rhmid-M2-renamed-longest.log") / $(lc "$W/n2-names.log") / $(lc "$W/n2-panic.log") / $(lc "$W/n2-deep.log") / $(nc "$W/n2-nanoda-name.log") / $(nc "$W/n2-nanoda-alloc.log")"; fi

echo "=== classifier regression and further classifier rows ==="
# REGRESSION: the kernel-only type error with its definition renamed to wasInterrupted - an earlier notary,
# Lake and leanchecker reject it; a later notary declined it (resource word in the name) -> REJECTED again
row renamed-type-error-wasInterrupted-rejected 1 'j["verdict"]=="REJECTED" and "Lean default exited with 1" in j["reason"] and "wasInterrupted" in j["reason"]' \
  -- "$CN" "$D/x-wasInterrupted-solution.export" "$D/rhminiF-challenge.export" "$D/rhminiF-comparator.leanonly.json" --threads 4
# a cut comparator diagnostic is no rejection (staged ccmp: the candidate's illegal-axiom line is cut after ': ')
S=$W/s-cutccmp; mk_stage "$S" ccmp
cat > "$STAGE_DIR/bin/ccmp" <<EOF
#!/bin/bash
case " \$* " in *"/solution.export "*) out=\$("$STAGE_DIR/bin/ccmp.real" "\$@" 2>&1); rc=\$?; printf '%s' "\$out" | sed 's/^\(error: Illegal axiom detected: \).*/\1/'; exit \$rc;; esac
exec "$STAGE_DIR/bin/ccmp.real" "\$@"
EOF
write_pins
row cut-comparator-diagnostic-declined 2 'j["verdict"]=="DECLINED" and "incomplete" in j["reason"]' -- "$STAGE_DIR/check-notary.sh" "$SB" "$SC" "$SCFG" --threads 4
# (unit) gruszka exit 1 needs its rejection line; Lean quotient post-check only its own messages, a damaged
# (non-UTF-8) log is no evidence; nanoda assertions only as the exact source text
gc() { "$CN" --xk-classify gruszka "$1" 1 2>/dev/null | head -1; }
printf 'rejected: Foo: type mismatch\n' > "$W/gz-real.log"
if [ "$(gc "$D/log-empty.log")" = "not decided" ] && [ "$(gc "$D/log-lean-thread-resource.log")" = "not decided" ] && [ "$(gc "$W/gz-real.log")" = rejected ] \
   && [ "$(lc "$D/log-quot-io.log")" = "not decided" ] && [ "$(lc "$D/log-quot-valid.log")" = rejected ] && [ "$(lc "$D/log-lean-damaged-utf8.log")" = "not decided" ] \
   && [ "$(nc "$D/log-nanoda-incomplete-assertion.log")" = "not decided" ] && [ "$(nc "$D/log-nanoda-complete-assertion.log")" = rejected ]; then
  ok classifier-evidence-must-be-complete "gruszka empty/thread, quotient I/O, damaged UTF-8, partial nanoda assertion -> not decided; complete forms -> rejected"
else bad classifier-evidence-must-be-complete "$(gc "$D/log-empty.log") $(gc "$D/log-lean-thread-resource.log") $(gc "$W/gz-real.log") / $(lc "$D/log-quot-io.log") $(lc "$D/log-quot-valid.log") $(lc "$D/log-lean-damaged-utf8.log") / $(nc "$D/log-nanoda-incomplete-assertion.log") $(nc "$D/log-nanoda-complete-assertion.log")"; fi
# a log larger than 64 MiB is never classified from its prefix (a resource line past the limit)
{ printf 'Lean default kernel rejects the solution: (kernel) type mismatch\n'; head -c 67108864 /dev/zero | tr '\0' 'x'; printf '\nfatal runtime error: failed to create thread\n'; } > "$W/big-lean.log"
{ printf "thread 'thread_2' (5) panicked at src/tc.rs:955:71:\nassertion failed: self.def_eq(u, v)\n"; head -c 67108864 /dev/zero | tr '\0' 'x'; printf '\nfatal runtime error: failed to create thread\n'; } > "$W/big-nanoda.log"
if [ "$(lc "$W/big-lean.log")" = "not decided" ] && [ "$(nc "$W/big-nanoda.log")" = "not decided" ]; then ok oversize-logs-not-classified "65 MiB Lean / nanoda logs -> not decided"
else bad oversize-logs-not-classified "$(lc "$W/big-lean.log") / $(nc "$W/big-nanoda.log")"; fi
rm -f "$W/big-lean.log" "$W/big-nanoda.log"
# --scope-check needs an identified release (a challenge the cross-version gate cannot read -> DECLINED)
printf '{\n' > "$W/brace.export"
python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("external_kernels",None); c.pop("enable_nanoda",None); json.dump(c,open(sys.argv[2],"w"))' "$SCFG" "$W/cfg-nokernel.json"
row scope-check-unreadable-release-declined 2 'j["verdict"]=="DECLINED"' -- "$CN" --scope-check "$W/brace.export" "$W/cfg-nokernel.json" --threads 4
# the diagnostic line states the EFFECTIVE verdict (report undeliverable -> DECLINED, not ACCEPTED)
"$CN" "${G[@]}" --json "$W/absent-dir/r.json" > /dev/null 2> "$W/eff.err"; erc=$?
if [ "$erc" = 2 ] && grep -q '^\[checkNotary\] verdict DECLINED (exit 2)' "$W/eff.err" && ! grep -q 'verdict ACCEPTED' "$W/eff.err"; then ok effective-verdict-logged "rc=2, stderr says DECLINED"
else bad effective-verdict-logged "rc=$erc :: $(tail -1 "$W/eff.err" | cut -c1-200)"; fi
# the environment guard's refusal with stdout a pipe without reader -> exit 2 (not 141)
env -i EXTRA=1 PATH=/usr/bin:/bin LANG=C.UTF-8 /bin/bash "$CN" --clean-env-reexec x 2>/dev/null | true; grc=${PIPESTATUS[0]}
if [ "$grc" = 2 ]; then ok env-guard-closed-stdout-exit2 "rc=2"; else bad env-guard-closed-stdout-exit2 "rc=$grc"; fi

echo "=== second-kernel failure reported by ccmp while the Lean leg rejected ==="
# End to end: staged pleanchecker writes a definite kernel rejection for the CANDIDATE and exits 1; staged ccmp rewrites
# its error line for the candidate to 'error: gruszka (second kernel) exited with 1' (exit status kept). The decision then
# takes the external-kernel branch with the Lean leg at exit 1 + a definite rejection -> REJECTED (a code mutant
# 'finish 0 ACCEPTED' at that line survived every suite before this row). Self-test runs pass through to the real binaries.
S=$W/s-k2fail-leanrej; mk_stage "$S" ccmp plc
cat > "$STAGE_DIR/bin/plc" <<EOF
#!/bin/bash
case " \$* " in *"/solution.export "*) printf "Lean default kernel rejects the solution: (kernel) declaration type mismatch, 'fvSelfTest' has type\n"; exit 1;; esac
exec "$STAGE_DIR/bin/plc.real" "\$@"
EOF
cat > "$STAGE_DIR/bin/ccmp" <<EOF
#!/bin/bash
case " \$* " in *"/solution.export "*) out=\$("$STAGE_DIR/bin/ccmp.real" "\$@" 2>&1); rc=\$?; printf '%s\n' "\$out" | sed 's/^error: Lean default exited with 1\$/error: gruszka (second kernel) exited with 1/'; exit \$rc;; esac
exec "$STAGE_DIR/bin/ccmp.real" "\$@"
EOF
write_pins
row k2-failure-with-lean-rejection-rejected 1 'j["verdict"]=="REJECTED" and j["exit"]==1 and "gruszka (second kernel) exited with 1" in j["reason"] and "official-kernel leg rejected" in j["reason"]' \
  -- "$STAGE_DIR/check-notary.sh" "${G[@]}"

echo "RESULT pass=$PASS fail=$FAIL"
[ "$FAIL" = 0 ]
