#!/bin/bash
# fastverify/tests/lowmem-check/test.sh — Regression & adversarial suite for the low-memory sound check & exporter.
set -uo pipefail

HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../.." && pwd)
CS_LM="$FV/check/lowmem/check-sound-lowmem.sh"
PINS="$FV/check/lowmem/pins.env"
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set; rows whose inputs are not part of the repository SKIP
ELAN_HOME=${ELAN_HOME:-$HOME/.elan}
CGRUN=${FV_CGRUN:-}; [ -n "$CGRUN" ] || [ ! -x /usr/local/bin/cgrun ] || CGRUN=/usr/local/bin/cgrun; [ -n "$CGRUN" ] || CGRUN=$(command -v cgrun 2>/dev/null || true)   # FV_CGRUN, else /usr/local/bin/cgrun, else cgrun on PATH

W=$(mktemp -d "${TMPDIR:-/tmp}/lowmem-check-test.XXXXXX")
trap 'rm -rf "$W"' EXIT

PASS=0; FAIL=0
ok()   { echo "PASS $1"; PASS=$((PASS + 1)); }
fail() { echo "FAIL $1: $2"; FAIL=$((FAIL + 1)); }

declare -A PIN_P
while read -r tag name sum path; do [ "$tag" = PIN ] && PIN_P[$name]=$path; done < "$PINS"

# 1. Portability: ccmp-lowmem and lean4export-lowmem must need <= GLIBC_2.17 and zero GLIBCXX
check_port() {
  local label=$1 bin=$2
  if [ ! -f "$bin" ]; then fail "$label" "missing $bin"; return; fi
  local bad
  bad=$(objdump -T "$bin" | grep -oE 'GLIBC_[0-9.]+|GLIBCXX_[0-9.]+|CXXABI_[0-9.]+' | sort -uV | \
        awk -F_ '$1!="GLIBC" {print; next} {split($2,a,"."); if (a[1]>2 || (a[1]==2 && a[2]>17)) print}')
  if [ -z "$bad" ]; then ok "$label"; else fail "$label" "non-portable symbols: $bad"; fi
}
check_port "portability-ccmp-lowmem-glibc217" "${PIN_P[ccmp_lowmem]}"
check_port "portability-pleanchecker-glibc217" "${PIN_P[pleanchecker]}"
check_port "portability-gruszka-glibc217" "${PIN_P[gruszka]}"
check_port "portability-pleanchecker-incr-glibc217" "${PIN_P[pleanchecker_incr]}"
if [ -f /scratch/fastverify-next/exporter-lowmem/v1/lean4export-lowmem ]; then
  check_port "portability-lean4export-lowmem-glibc217" "/scratch/fastverify-next/exporter-lowmem/v1/lean4export-lowmem"
fi

# 2. Preflight
out=$("$CS_LM" --preflight --threads 4 2>/dev/null); rc=$?
if [ "$rc" = 0 ] && printf '%s' "$out" | grep -q '"verdict":"PREFLIGHT_OK"'; then
  ok "preflight"
else
  fail "preflight" "rc=$rc out=$out"
fi

# 3. Good export -> ACCEPTED, all 3 legs rc=0, private copy
"$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
  --threads 2 --json "$W/good.json" > "$W/good.out" 2>&1
rc=$?
if [ "$rc" = 0 ] && python3 -I -c '
import json, sys
j = json.load(open(sys.argv[1]))
assert j["verdict"] == "ACCEPTED" and j["exit"] == 0
assert j["legs"]["compare"]["rc"] == 0 and j["legs"]["lean"]["rc"] == 0 and j["legs"]["k2"]["rc"] == 0
assert j["inputs"]["export"]["private"] == "copy"
' "$W/good.json" 2>/dev/null; then
  ok "good-accepted-sequential-legs"
else
  fail "good-accepted-sequential-legs" "rc=$rc $(cat "$W/good.json" 2>/dev/null)"
fi

# 4. Illegal axiom -> REJECTED at Leg 1 (short-circuit: kernels never started!)
"$CS_LM" "${PIN_P[selftest_bad]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
  --threads 2 --json "$W/bad.json" > "$W/bad.out" 2>&1
rc=$?
if [ "$rc" = 1 ] && python3 -I -c '
import json, sys
j = json.load(open(sys.argv[1]))
assert j["verdict"] == "REJECTED" and "Illegal axiom" in j["reason"]
assert j["legs"]["compare"]["rc"] == 1 and j["legs"]["lean"]["rc"] is None and j["legs"]["k2"]["rc"] is None
' "$W/bad.json" 2>/dev/null; then
  ok "bad-axiom-shortcircuit-leg1"
else
  fail "bad-axiom-shortcircuit-leg1" "rc=$rc $(cat "$W/bad.json" 2>/dev/null)"
fi

# 5. cmpx statement drift & transitive definition drift
CMPX="${FV_BENCH_INPUTS:-/scratch/bench-inputs}/cmpx"
CH="/scratch/bench-inputs/rh-miniF/challenge"
if [ -d "$CMPX" ] && [ -d "$CH" ]; then
  for c in reject-stmt-true.ndjson reject-def-body-changed.ndjson accept-base.ndjson; do
    [ -f "$CMPX/$c" ] || continue
    want=1; [[ "$c" == accept-* ]] && want=0
    "$CS_LM" "$CMPX/$c" "$CH/challenge.export" "$CH/comparator.leanonly.json" --threads 2 --json "$W/$c.json" > /dev/null 2>&1
    rc=$?
    if [ "$rc" = "$want" ]; then ok "cmpx-$c"; else fail "cmpx-$c" "expected $want got $rc"; fi
  done
else
  echo "SKIP 5. cmpx drift cases: needs $CMPX (26 MB) and $CH (rh-miniF benchmark inputs), which are not part of the repository"
fi

# 6. Duplicate key in comparator.json -> DECLINED (exit 2)
printf '{"challenge_module":"C","solution_module":"S","theorem_names":["A"],"theorem_names":["B"],"permitted_axioms":[]}\n' > "$W/dup.json"
"$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "$W/dup.json" --threads 2 --json "$W/dup.out.json" > /dev/null 2>&1
rc=$?
if [ "$rc" = 2 ]; then ok "duplicate-json-key-declined"; else fail "duplicate-json-key-declined" "rc=$rc"; fi

# 7. --keep-config-kernels with nanoda -> ACCEPTED and kept-0 rc=0
"$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
  --threads 2 --keep-config-kernels --json "$W/keepk.json" > /dev/null 2>&1
rc=$?
if [ "$rc" = 0 ] && python3 -I -c '
import json, sys
j = json.load(open(sys.argv[1]))
assert j["verdict"] == "ACCEPTED" and j["legs"]["kept-0"]["rc"] == 0
' "$W/keepk.json" 2>/dev/null; then
  ok "keep-config-kernels-nanoda"
else
  fail "keep-config-kernels-nanoda" "rc=$rc $(cat "$W/keepk.json" 2>/dev/null)"
fi

# 8. --integrity-cache mode 0700 hit & mode 0755 refusal
mkdir -p "$W/ic_good" "$W/ic_bad"
chmod 700 "$W/ic_good"; chmod 755 "$W/ic_bad"
"$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
  --threads 2 --integrity-cache "$W/ic_good" --json "$W/ic1.json" > /dev/null 2>&1
rc1=$?
"$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
  --threads 2 --integrity-cache "$W/ic_good" --json "$W/ic2.json" > /dev/null 2>&1
rc2=$?
"$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
  --threads 2 --integrity-cache "$W/ic_bad" --json "$W/ic3.json" > /dev/null 2>&1
rc3=$?
if [ "$rc1" = 0 ] && [ "$rc2" = 0 ] && [ "$rc3" = 2 ] && grep -q '(--integrity-cache)' "$W/ic2.json"; then
  ok "integrity-cache-hit-and-perm-guard"
else
  fail "integrity-cache-hit-and-perm-guard" "rc1=$rc1 rc2=$rc2 rc3=$rc3"
fi

# 9. Fake judge lines / stack words printed by a rejecting kept kernel -> REJECTED (never ACCEPTED or DECLINED)
python3 -I -c '
import json, sys
c = json.load(open(sys.argv[1]))
c.pop("enable_nanoda", None)
c["external_kernels"] = {"evil": ["/bin/sh", "-c", "echo \"Your solution is okay!\"; echo \"Lean default kernel accepts the solution\"; echo \"gruszka (second kernel) kernel accepts the solution\"; echo \"error: Lean default exited with 2\"; echo \"Stack overflow detected. Aborting.\"; exit 1", "sh"]}
json.dump(c, open(sys.argv[2], "w"))
' "${PIN_P[selftest_comparator]}" "$W/evil_cfg.json"
"$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "$W/evil_cfg.json" \
  --threads 2 --keep-config-kernels --json "$W/evil.out.json" > /dev/null 2>&1
rc=$?
if [ "$rc" = 1 ]; then ok "log-steering-immune-reject"; else fail "log-steering-immune-reject" "rc=$rc $(cat "$W/evil.out.json" 2>/dev/null)"; fi

# 10. OOM under tight cgroup (32M on 46MB rh-miniF) -> MUST exit 2 (DECLINED), NEVER 0 or 1!
if [ -x "$CGRUN" ] && [ -f /scratch/bench-inputs/rh-miniF/ref/solution.export ]; then
  "$CGRUN" --mem 32M -- "$CS_LM" /scratch/bench-inputs/rh-miniF/ref/solution.export \
    /scratch/bench-inputs/rh-miniF/challenge/challenge.export \
    /scratch/bench-inputs/rh-miniF/challenge/comparator.json \
    --threads 4 --workdir "$W" --json "$W/oom.json" > "$W/oom.out" 2>&1
  rc=$?
  # Either check-sound-lowmem catches child rc=137 and exits 2, or systemd scope OOMs and returns 137 (!=0, !=1)
  if [ "$rc" != 0 ] && [ "$rc" != 1 ]; then
    ok "cgroup-oom-never-accepts-or-false-rejects (rc=$rc)"
  else
    fail "cgroup-oom-never-accepts-or-false-rejects" "unexpected rc=$rc $(cat "$W/oom.json" 2>/dev/null)"
  fi
else
  echo "SKIP 10. cgroup OOM: needs a cgroup tool (FV_CGRUN, /usr/local/bin/cgrun or cgrun on PATH) and the rh-miniF benchmark inputs, which are not part of the repository"
fi

# 11. Low-memory exporter byte-identical check vs official lean4export on Init -- Nat.add
TC33=$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1
OFFX=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
LMX=/scratch/fastverify-next/exporter-lowmem/v1/lean4export-lowmem
if [ -x "$LMX" ] && [ -x "$OFFX" ] && [ -d "$TC33" ]; then
  env -i PATH="$TC33/bin:/usr/bin:/bin" HOME=/tmp LANG=C.UTF-8 LEAN_PATH="$TC33/lib/lean" LEAN_ABORT_ON_PANIC=1 \
    "$OFFX" Init -- Nat.add > "$W/e0.export" 2>/dev/null
  env -i PATH="$TC33/bin:/usr/bin:/bin" HOME=/tmp LANG=C.UTF-8 LEAN_PATH="$TC33/lib/lean" LEAN_ABORT_ON_PANIC=1 \
    LEAN4EXPORT_LOWMEM=1 LEAN4EXPORT_THREADS=4 "$LMX" Init -- Nat.add > "$W/elm.export" 2>/dev/null
  if cmp -s "$W/e0.export" "$W/elm.export"; then
    ok "exporter-lowmem-byte-identical-to-E0"
  else
    fail "exporter-lowmem-byte-identical-to-E0" "output differs from official E0"
  fi
fi

# 12. fv_lowmem.py CLI (--from-export good, bad, and sha256 tamper guard)
FVL="$FV/tools/lowmem/fv_lowmem.py"
if [ -f "$FVL" ]; then
  mkdir -p "$W/fvl_chal"
  cp "${PIN_P[selftest_challenge]}" "$W/fvl_chal/challenge.export"
  cp "${PIN_P[selftest_comparator]}" "$W/fvl_chal/comparator.json"
  CSHA=$(sha256sum "$W/fvl_chal/challenge.export" | cut -d' ' -f1)
  CFGSHA=$(sha256sum "$W/fvl_chal/comparator.json" | cut -d' ' -f1)   # (the comparator pin too)
  python3 -I "$FVL" - "$W/fvl_chal" "$W/fvl_out_good" --from-export "${PIN_P[selftest_good]}" \
    --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --threads 2 --integrity-cache "$W/ic_good" > /dev/null 2>&1
  rc_g=$?
  python3 -I "$FVL" - "$W/fvl_chal" "$W/fvl_out_bad" --from-export "${PIN_P[selftest_bad]}" \
    --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --threads 2 --integrity-cache "$W/ic_good" > /dev/null 2>&1
  rc_b=$?
  python3 -I "$FVL" - "$W/fvl_chal" "$W/fvl_out_tamper" --from-export "${PIN_P[selftest_good]}" \
    --challenge-sha256 "0000000000000000000000000000000000000000000000000000000000000000" --comparator-sha256 "$CFGSHA" --threads 2 > /dev/null 2>&1
  rc_t=$?
  if [ "$rc_g" = 0 ] && [ "$rc_b" = 1 ] && [ "$rc_t" = 2 ]; then
    ok "fv-lowmem-cli-export-good-bad-and-sha256-guard"
  else
    fail "fv-lowmem-cli-export-good-bad-and-sha256-guard" "rc_g=$rc_g rc_b=$rc_b rc_t=$rc_t"
  fi
fi

# 13. fv_lowmem.py sources-in mode (source-only challenge -> official B0+E0, solution -> B1 + export-lowmem + check-sound-lowmem)
if [ -f "$FVL" ] && [ -d "$TC33" ]; then
  mkdir -p "$W/src_chal" "$W/src_good" "$W/src_sorry"
  for d in "$W/src_chal" "$W/src_good" "$W/src_sorry"; do
    printf 'leanprover/lean4:v4.33.1\n' > "$d/lean-toolchain"
    cat > "$d/lakefile.toml" <<'TOML'
name = "Mini"
defaultTargets = ["Mini"]
[[lean_lib]]
name = "Mini"
TOML
  done
  printf 'theorem mini_add_zero (n : Nat) : n + 0 = n := sorry\n' > "$W/src_chal/Mini.lean"
  cat > "$W/src_chal/comparator.json" <<'JSON'
{
  "challenge_module": "Mini",
  "solution_module": "Mini",
  "theorem_names": ["mini_add_zero"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
JSON
  printf 'theorem mini_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n\n' > "$W/src_good/Mini.lean"
  printf 'theorem mini_add_zero (n : Nat) : n + 0 = n := sorry\n' > "$W/src_sorry/Mini.lean"
  python3 -I "$FVL" "$W/src_good" "$W/src_chal" "$W/src_out_good" --threads 2 --mem-budget-mb 2048 --integrity-cache "$W/ic_good" > /dev/null 2>&1
  rc_sg=$?
  python3 -I "$FVL" "$W/src_sorry" "$W/src_chal" "$W/src_out_sorry" --threads 2 --mem-budget-mb 2048 --integrity-cache "$W/ic_good" > /dev/null 2>&1
  rc_sb=$?
  if [ "$rc_sg" = 0 ] && [ "$rc_sb" = 1 ]; then
    ok "fv-lowmem-cli-sources-in-honest-and-sorry"
  else
    fail "fv-lowmem-cli-sources-in-honest-and-sorry" "rc_sg=$rc_sg rc_sb=$rc_sb $(cat "$W/src_out_good/result.json" 2>/dev/null)"
  fi
fi

# 14. Lean 4.37.0-rc1 export-lowmem.sh --preflight and --verify byte-identity vs bundled $TC/bin/leanexport
TC37=$ELAN_HOME/toolchains/leanprover--lean4---v4.37.0-rc1
LMX437=/scratch/fastverify-next/exporter-lowmem/v1/lean4export-lowmem-v4.37.0-rc1
if [ -d "$TC37" ] && [ -x "$LMX437" ]; then
  mkdir -p "$W/p437"
  printf 'Nat.add\nList.map\n' > "$W/p437/tg.txt"
  "$FV/export/export-lowmem.sh" --preflight "$TC37" > /dev/null 2>&1
  rc_pf=$?
  "$FV/export/export-lowmem.sh" --lean-path "$TC37/lib/lean" --module Init --targets-nl "$W/p437/tg.txt" \
    --toolchain "$TC37" --project "$W/p437" --out "$W/p437/out.export" --threads 4 --verify --json "$W/p437/out.json" > /dev/null 2>&1
  rc_ex=$?
  if [ "$rc_pf" = 0 ] && [ "$rc_ex" = 0 ] && grep -q '"verify": "identical"' "$W/p437/out.json"; then
    ok "exporter-lowmem-437-byte-identical-to-official-leanexport"
  else
    fail "exporter-lowmem-437-byte-identical-to-official-leanexport" "rc_pf=$rc_pf rc_ex=$rc_ex $(cat "$W/p437/out.json" 2>/dev/null)"
  fi
fi

# 15. CS-lowmem v1.2 --pins check/lowmem/pins-437.env + --hide (preflight, selftest, symlink icache guard, 4.37 fixtures & the fv_lowmem --pins boundary)
PINS437="$FV/check/lowmem/pins-437.env"
HIDE437="$FV/check/sound/hide/lean-4.37.0-rc1-no-expose.txt"
CCMP437="/scratch/fastverify-next/lowmem/a1fbc56d/ccmp-lowmem"
PLC437="/scratch/fastverify-next/sound/acf82e83/pleanchecker"
if [ -f "$PINS437" ] && [ -x "$CCMP437" ] && [ -x "$PLC437" ] && [ -d "$TC37" ]; then
  "$CS_LM" --preflight --pins "$PINS437" > "$W/pf437.out" 2>&1; rc_pf437=$?
  "$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
    --threads 2 --pins "$PINS437" --json "$W/g437.json" > /dev/null 2>&1; rc_g437=$?
  "$CS_LM" "${PIN_P[selftest_bad]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
    --threads 2 --pins "$PINS437" --json "$W/b437.json" > /dev/null 2>&1; rc_b437=$?
  P37_SHA=$(sha256sum "$PINS437" | cut -d' ' -f1)
  if [ "$rc_pf437" = 0 ] && [ "$rc_g437" = 0 ] && [ "$rc_b437" = 1 ] && python3 -I -c '
import json, sys
j = json.load(open(sys.argv[1]))
assert j["toolchain"] == "leanprover/lean4:v4.37.0-rc1" and j["pins_sha256"] == sys.argv[2]
' "$W/g437.json" "$P37_SHA" 2>/dev/null; then
    ok "cs-lowmem-437-preflight-and-selftest"
  else
    fail "cs-lowmem-437-preflight-and-selftest" "pf=$rc_pf437 g=$rc_g437 b=$rc_b437"
  fi

  if [ -f "$HIDE437" ]; then
    H37_SHA=$(sha256sum "$HIDE437" | cut -d' ' -f1)
    "$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
      --threads 2 --pins "$PINS437" --hide "$HIDE437" --json "$W/ghide.json" > /dev/null 2>&1; rc_gh=$?
    "$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
      --threads 2 --pins "$PINS437" --hide none --json "$W/gnone.json" > /dev/null 2>&1; rc_gn=$?
    "$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
      --threads 2 --pins "$PINS437" --hide "$W" --json "$W/gbadhide.json" > /dev/null 2>&1; rc_gbh=$?
    if [ "$rc_gh" = 0 ] && [ "$rc_gn" = 0 ] && [ "$rc_gbh" = 2 ] && python3 -I -c '
import json, sys
jh = json.load(open(sys.argv[1]))
jn = json.load(open(sys.argv[2]))
assert jh["hide_sha256"] == sys.argv[3] and not jn.get("hide") and not jn.get("hide_sha256")
' "$W/ghide.json" "$W/gnone.json" "$H37_SHA" 2>/dev/null; then
      ok "cs-lowmem-v12-hide-and-invalid-hide-guard"
    else
      fail "cs-lowmem-v12-hide-and-invalid-hide-guard" "gh=$rc_gh gn=$rc_gn gbh=$rc_gbh"
    fi
  fi

  mkdir -p "$W/ic_sym" && chmod 700 "$W/ic_sym"
  # --pins must resolve to a pins*.env of check/lowmem/ itself; a symlink that resolves INTO the package is
  # still accepted (and still writes no integrity record), a copy of the package's file outside the package is refused.
  cp "$PINS437" "$W/copy-pins-437.env"
  ln -s "$PINS437" "$W/sym-pins-437.env"
  "$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
    --threads 2 --pins "$W/sym-pins-437.env" --integrity-cache "$W/ic_sym" --json "$W/sym437.json" > /dev/null 2>&1
  rc_sym=$?
  n_rec=$(ls "$W/ic_sym" | wc -l)
  if [ "$rc_sym" = 0 ] && [ "$n_rec" = 0 ]; then
    ok "cs-lowmem-symlink-pins-icache-guard"
  else
    fail "cs-lowmem-symlink-pins-icache-guard" "rc_sym=$rc_sym n_rec=$n_rec"
  fi
  "$CS_LM" "${PIN_P[selftest_good]}" "${PIN_P[selftest_challenge]}" "${PIN_P[selftest_comparator]}" \
    --threads 2 --pins "$W/copy-pins-437.env" --json "$W/copy437.json" > /dev/null 2>&1
  rc_copy=$?
  if [ "$rc_copy" = 2 ] && grep -q 'must name a pins' "$W/copy437.json"; then
    ok "cs-lowmem-pins-outside-package-refused"
  else
    fail "cs-lowmem-pins-outside-package-refused" "rc_copy=$rc_copy"
  fi

  FX437="/scratch/fastverify-next/fixtures/lean-4.37"
  if [ -f "$FX437/challenge.export" ]; then
    "$CS_LM" "$FX437/good.export" "$FX437/challenge.export" "$FX437/comparator.json" \
      --threads 2 --pins "$PINS437" --json "$W/fx437.json" > /dev/null 2>&1
    rc_fx=$?
    if [ "$rc_fx" = 1 ] && grep -q "Challenge definition is not sorried" "$W/fx437.json"; then
      ok "cs-lowmem-437-nonsorried-challenge-def-rejected"
    else
      fail "cs-lowmem-437-nonsorried-challenge-def-rejected" "rc_fx=$rc_fx $(cat "$W/fx437.json" 2>/dev/null)"
    fi
  fi

  CFGSHA=$(sha256sum "$W/fvl_chal/comparator.json" | cut -d' ' -f1)
  cp "$PINS437" "$W/rogue-pins.env"
  python3 -I "$FVL" - "$W/fvl_chal" "$W/fvl_b4_ok" --from-export "${PIN_P[selftest_good]}" \
    --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --pins 437 --threads 2 > /dev/null 2>&1
  rc_b4ok=$?
  python3 -I "$FVL" - "$W/fvl_chal" "$W/fvl_b4_badcfg" --from-export "${PIN_P[selftest_good]}" \
    --challenge-sha256 "$CSHA" --comparator-sha256 "1111111111111111111111111111111111111111111111111111111111111111" --threads 2 > /dev/null 2>&1
  rc_b4cfg=$?
  python3 -I "$FVL" - "$W/fvl_chal" "$W/fvl_b4_badpins" --from-export "${PIN_P[selftest_good]}" \
    --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --pins "$W/rogue-pins.env" --threads 2 > /dev/null 2>&1
  rc_b4pins=$?
  if [ "$rc_b4ok" = 0 ] && [ "$rc_b4cfg" = 2 ] && [ "$rc_b4pins" = 2 ]; then
    ok "fv-lowmem-b4-comparator-sha256-and-pins-guard"
  else
    fail "fv-lowmem-b4-comparator-sha256-and-pins-guard" "ok=$rc_b4ok cfg=$rc_b4cfg pins=$rc_b4pins"
  fi
fi

echo "RESULT pass=$PASS fail=$FAIL"
[ "$FAIL" -eq 0 ]
