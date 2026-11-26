#!/bin/bash
# fastverify/tests/notary-matrix/run.sh — End-to-end & adversarial test suite for check/notary (the notary judge + --preset notary)
set -euo pipefail

HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../.." && pwd)
NOTARY=$FV/check/notary
CN=$NOTARY/check-notary.sh

SG=$(awk '$1=="PIN" && $2=="selftest_good" {print $4}' "$NOTARY/pins.env")
SB=$(awk '$1=="PIN" && $2=="selftest_bad" {print $4}' "$NOTARY/pins.env")
SC=$(awk '$1=="PIN" && $2=="selftest_challenge" {print $4}' "$NOTARY/pins.env")
SCFG=$(awk '$1=="PIN" && $2=="selftest_comparator" {print $4}' "$NOTARY/pins.env")

W=$(mktemp -d "${NOTARY_TEST_DIR:-/dev/shm}/notary-matrix-test.XXXXXX")
trap 'chmod -R u+w "$W" 2>/dev/null || true; rm -rf "$W"' EXIT

PASS=0; FAIL=0
ok()   { echo "PASS $1: $2"; PASS=$((PASS+1)); }
fail() { echo "FAIL $1: $2"; FAIL=$((FAIL+1)); }

run_j() {
  local name=$1 want_rc=$2 pred=$3; shift 3
  set +e
  local out; out=$("$@" 2>"$W/err.log")
  local rc=$?
  set -e
  local last; last=$(printf '%s\n' "$out" | tail -n 1)
  local check_ok=0
  if [ "$rc" = "$want_rc" ]; then
    if python3 -I -c "import json,sys; j=json.loads(sys.argv[1]); sys.exit(0 if ($pred) else 1)" "$last" 2>/dev/null; then
      check_ok=1
    fi
  fi
  if [ "$check_ok" = 1 ]; then
    ok "$name" "rc=$rc :: $(printf '%s' "$last" | cut -c1-180)"
  else
    fail "$name" "want rc=$want_rc pred=[$pred], got rc=$rc :: $(printf '%s' "$last" | cut -c1-260)"
  fi
}

echo "=== 1. Preflight & Multi-Kernel Notary Baselines ==="
run_j "notary-preflight" 0 'j["verdict"]=="PREFLIGHT_OK"' \
  "$CN" --preflight --threads 4

run_j "notary-accept-gruszka-r7" 0 \
  'j["verdict"]=="ACCEPTED" and j["r7_digest"]["verified"]==True and j["r7_digest"]["matched_legs"]==["ccmp","lean","gruszka"] and len(j["r7_digest"]["env_sha256_v1"])==64 and j["r7_digest"]["const_count"]==584' \
  "$CN" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka

run_j "notary-accept-4kernels-all" 0 \
  'j["verdict"]=="ACCEPTED" and j["r7_digest"]["verified"]==True and j["legs"]["lean"]["rc"]==0 and j["legs"]["k2"]["rc"]==0 and j["legs"]["con-ron"]["rc"]==0 and j["legs"]["con-leche"]["rc"]==0' \
  "$CN" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka,con-ron,con-leche

run_j "notary-accept-nanoda" 0 \
  'j["verdict"]=="ACCEPTED" and j["r7_digest"]["verified"]==True and j["legs"]["nanoda"]["rc"]==0' \
  "$CN" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka,nanoda

run_j "notary-reject-bad-export" 1 \
  'j["verdict"]=="REJECTED"' \
  "$CN" "$SB" "$SC" "$SCFG" --threads 4 --kernels gruszka

run_j "notary-refuse-empty-kernels" 2 \
  'j["verdict"]=="DECLINED" and "at least one" in j["reason"]' \
  "$CN" "$SG" "$SC" "$SCFG" --threads 4 --kernels ""

echo "=== 2. Adversarial Split-Brain & Parser-Differential Tests ==="
# Create a staging copy of check-notary.sh + pins.env so we can inject simulated split-brain legs
# without modifying the real check/notary/!
mk_stage() {
  local base=$1
  local sdir="$base/check/notary"
  mkdir -p "$sdir/bin"
  ln -s "$FV/config" "$base/config"
  ln -s "$FV/lib" "$base/lib"
  ln -s "$FV/toolchains" "$base/toolchains"
  ln -s "$FV/check/sound" "$base/check/sound"
  ln -s "$FV/check/xversion" "$base/check/xversion"
  cp "$CN" "$sdir/check-notary.sh"
  # the pinned binaries (check/notary/pins.env), copied so that the staged legs can be swapped
  local pin; pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$NOTARY/pins.env"; }
  cp "$(pin ccmp_notary)" "$sdir/bin/ccmp-notary"
  cp "$(pin pleanchecker_notary)" "$sdir/bin/pleanchecker-notary"
  cp "$(pin gruszka_r7)" "$sdir/bin/gruszka-r7"
  chmod 755 "$sdir/check-notary.sh" "$sdir/bin/"*
}
write_stage_pins() {
  local sdir="$1/check/notary"
  {
    echo "NOTARY_VERSION=notary-test-stage"
    echo "TC36=@components"
    echo "PIN ccmp_notary $(sha256sum "$sdir/bin/ccmp-notary" | cut -d' ' -f1) $sdir/bin/ccmp-notary"
    echo "PIN pleanchecker_notary $(sha256sum "$sdir/bin/pleanchecker-notary" | cut -d' ' -f1) $sdir/bin/pleanchecker-notary"
    echo "PIN gruszka_r7 $(sha256sum "$sdir/bin/gruszka-r7" | cut -d' ' -f1) $sdir/bin/gruszka-r7"
    grep -E '^PIN selftest_' "$NOTARY/pins.env"
  } > "$sdir/pins.env"
}

# Attack 1: Split-brain parser differential between ccmp and pleanchecker on env_sha256_v1!
S1=$W/stage1; mk_stage "$S1"; S1N="$S1/check/notary"
mv "$S1N/bin/pleanchecker-notary" "$S1N/bin/pleanchecker-notary.real"
cat > "$S1N/bin/pleanchecker-notary" <<EOF
#!/bin/sh
"$S1N/bin/pleanchecker-notary.real" "\$@"
rc=\$?
if [ "\$rc" = 0 ] && [ -n "\${PCHK_DIGEST_OUT:-}" ] && echo "\$PCHK_DIGEST_OUT" | grep -q 'digest-lean\.txt$'; then
  sed -i 's/^env_sha256_v1=./env_sha256_v1=0/' "\$PCHK_DIGEST_OUT"
fi
exit \$rc
EOF
chmod 755 "$S1N/bin/pleanchecker-notary"
write_stage_pins "$S1"
run_j "r7-attack-splitbrain-ccmp-vs-lean" 2 \
  'j["verdict"]=="DECLINED" and "R7_ENV_DIGEST_MISMATCH ccmp!=lean" in j["reason"]' \
  "$S1N/check-notary.sh" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka

# Attack 2: letE.nondep / mdata strict differential (v1 identical across all 3 legs, strict_v1 differs!)
S2=$W/stage2; mk_stage "$S2"; S2N="$S2/check/notary"
mv "$S2N/bin/pleanchecker-notary" "$S2N/bin/pleanchecker-notary.real"
cat > "$S2N/bin/pleanchecker-notary" <<EOF
#!/bin/sh
"$S2N/bin/pleanchecker-notary.real" "\$@"
rc=\$?
if [ "\$rc" = 0 ] && [ -n "\${PCHK_DIGEST_OUT:-}" ] && echo "\$PCHK_DIGEST_OUT" | grep -q 'digest-lean\.txt$'; then
  sed -i 's/^env_strict_sha256_v1=./env_strict_sha256_v1=0/' "\$PCHK_DIGEST_OUT"
fi
exit \$rc
EOF
chmod 755 "$S2N/bin/pleanchecker-notary"
write_stage_pins "$S2"
run_j "r7-attack-strict-nondep-diff" 2 \
  'j["verdict"]=="DECLINED" and "R7_STRICT_DIGEST_MISMATCH" in j["reason"]' \
  "$S2N/check-notary.sh" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka

# Attack 3: gruszka-r7 / susz split-brain differential (gruszka accepts rc=0 but saw different AST!)
S3=$W/stage3; mk_stage "$S3"; S3N="$S3/check/notary"
mv "$S3N/bin/gruszka-r7" "$S3N/bin/gruszka-r7.real"
cat > "$S3N/bin/gruszka-r7" <<EOF
#!/bin/sh
"$S3N/bin/gruszka-r7.real" "\$@"
rc=\$?
if [ "\$rc" = 0 ] && [ -n "\${GRUSZKA_DIGEST_OUT:-}" ] && echo "\$GRUSZKA_DIGEST_OUT" | grep -q 'digest-k2\.txt$'; then
  sed -i 's/^env_sha256_v1=./env_sha256_v1=f/' "\$GRUSZKA_DIGEST_OUT"
fi
exit \$rc
EOF
chmod 755 "$S3N/bin/gruszka-r7"
write_stage_pins "$S3"
run_j "r7-attack-splitbrain-gruszka" 2 \
  'j["verdict"]=="DECLINED" and "R7_ENV_DIGEST_MISMATCH ccmp!=gruszka" in j["reason"]' \
  "$S3N/check-notary.sh" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka

# Attack 4: missing digest file (gruszka accepts rc=0 without writing digest -> MUST DECLINE!)
S4=$W/stage4; mk_stage "$S4"; S4N="$S4/check/notary"
mv "$S4N/bin/gruszka-r7" "$S4N/bin/gruszka-r7.real"
cat > "$S4N/bin/gruszka-r7" <<EOF
#!/bin/sh
"$S4N/bin/gruszka-r7.real" "\$@"
rc=\$?
if [ "\$rc" = 0 ] && [ -n "\${GRUSZKA_DIGEST_OUT:-}" ] && echo "\$GRUSZKA_DIGEST_OUT" | grep -q 'digest-k2\.txt$'; then
  rm -f "\$GRUSZKA_DIGEST_OUT"
fi
exit \$rc
EOF
chmod 755 "$S4N/bin/gruszka-r7"
write_stage_pins "$S4"
run_j "r7-attack-missing-digest" 2 \
  'j["verdict"]=="DECLINED" and "missing or invalid gruszka digest" in j["reason"]' \
  "$S4N/check-notary.sh" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka

echo "=== 3. con-leche OOM Exit-1 Safety Trap Test ==="
S5=$W/stage5; mk_stage "$S5"; S5N="$S5/check/notary"
write_stage_pins "$S5"
cat > "$S5N/bin/mock-conleche-oom" <<'EOF'
#!/bin/sh
echo "memory allocation of 1073741824 bytes failed" >&2
exit 1
EOF
chmod 755 "$S5N/bin/mock-conleche-oom"
sed -i "s|CONLECHE_BIN=\"\$TC36/bin/con-leche\"|CONLECHE_BIN=\"$S5N/bin/mock-conleche-oom\"|" "$S5N/check-notary.sh"
# classified by notary_xk_classify: a runtime/resource line not written by con-leche -> 'not decided' -> DECLINED
run_j "con-leche-oom-exit1-declines-never-rejects" 2 \
  'j["verdict"]=="DECLINED" and j["kernel_status"]["con-leche"]["status"]=="not decided" and "resource" in j["kernel_status"]["con-leche"]["reason"]' \
  "$S5N/check-notary.sh" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka,con-leche

# con-leche's own rejection line (official kernel + gruszka accepted) is a VETO: DECLINED, never REJECTED
# (con-leche treats theorem bodies as opaque and rejects some valid proofs); a line in another format is 'not decided'
cat > "$S5N/bin/mock-conleche-reject" <<'EOF'
#!/bin/sh
echo "con-leche: invalid: type mismatch [at theorem Foo, fold position 3] (--verified) t=0.1s"
exit 1
EOF
chmod 755 "$S5N/bin/mock-conleche-reject"
sed -i "s|mock-conleche-oom|mock-conleche-reject|" "$S5N/check-notary.sh"
run_j "con-leche-real-reject-vetoes-as-declined" 2 \
  'j["verdict"]=="DECLINED" and j["kernel_status"]["con-leche"]["status"]=="rejected" and "theorem bodies as opaque" in j["reason"]' \
  "$S5N/check-notary.sh" "$SG" "$SC" "$SCFG" --threads 4 --kernels gruszka,con-leche

echo "RESULT pass=$PASS fail=$FAIL"
[ "$FAIL" = 0 ]
