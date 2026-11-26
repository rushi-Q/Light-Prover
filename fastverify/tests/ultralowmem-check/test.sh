#!/bin/bash
# Regression & adversarial test suite for the low-memory kernels (`pleanchecker-lowmem` + `gruszka-lowmem`).
# Usage: bash fastverify/tests/ultralowmem-check/test.sh [PLC_BIN] [GRZ_BIN] [CHECK_LOWMEM_SH]
set -euo pipefail

HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKGROOT=$(cd "$HERE/../.." && pwd)
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set; rows whose inputs are not part of the repository SKIP
ELAN_HOME=${ELAN_HOME:-$HOME/.elan}
TC36=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
CGRUN=${FV_CGRUN:-}; [ -n "$CGRUN" ] || [ ! -x /usr/local/bin/cgrun ] || CGRUN=/usr/local/bin/cgrun; [ -n "$CGRUN" ] || CGRUN=$(command -v cgrun 2>/dev/null || true)   # FV_CGRUN, else /usr/local/bin/cgrun, else cgrun on PATH

ulmpin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$PKGROOT/check/lowmem/pins-ultralowmem.env"; }   # the pinned low-memory legs
PLC=${1:-$(ulmpin pleanchecker_lowmem)}
GRZ=${2:-$(ulmpin gruszka_lowmem)}
CSLM=${3:-$PKGROOT/check/lowmem/check-sound-ultralowmem.sh}

FIX="$HERE/fixtures"
(cd "$FIX" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL: fixtures do not match fixtures/SHA256SUMS"; exit 1; }
W=$(mktemp -d "${TMPDIR:-/tmp}/ultralowmem-check-test.XXXXXX")
trap 'rm -rf "$W"' EXIT

PASS=0
FAIL=0
check_rc() {
  local name="$1" want="$2" got="$3" detail="${4:-}"
  if [ "$got" = "$want" ]; then
    echo "PASS: $name (rc=$got)"
    PASS=$((PASS + 1))
  else
    echo "FAIL: $name (want rc=$want, got rc=$got) $detail"
    FAIL=$((FAIL + 1))
  fi
}

echo "=== Low-Memory Kernel Regression Suite ==="
echo "PLC=$PLC"
echo "GRZ=$GRZ"

# 1. Official Lean 4.36 kernel theorem-unfolding proof (TestAcc: Acc.rec on theorem accZero)
"$TC36/bin/leanchecker" --from-export "$FIX/acc_unfold.export" > "$W/off_ok.log" 2>&1 && rc=0 || rc=$?
check_rc "1a. official leanchecker accepts acc_unfold.export" 0 "$rc"
"$TC36/bin/leanchecker" --from-export "$FIX/acc_unfold_evicted.export" > "$W/off_ev.log" 2>&1 && rc=0 || rc=$?
check_rc "1b. official leanchecker rejects acc_unfold_evicted.export" 1 "$rc"

# 2. pleanchecker-lowmem eviction modes on TestAcc
"$PLC" --low-mem --evict=strict -v -j2 "$FIX/acc_unfold.export" > "$W/plc_strict.log" 2>&1 && rc=0 || rc=$?
check_rc "2a. pleanchecker-lowmem --evict=strict rejects acc_unfold (proves theorem unfolding needed)" 1 "$rc"

"$PLC" --low-mem --evict=smart -v -j2 "$FIX/acc_unfold.export" > "$W/plc_smart_ok.log" 2>&1 && rc=0 || rc=$?
check_rc "2b. pleanchecker-lowmem --evict=smart accepts acc_unfold via targeted retry" 0 "$rc"
if grep -q "ACCEPTED via targeted retry iter 1" "$W/plc_smart_ok.log"; then
  echo "PASS: 2c. --evict=smart recovered acc_unfold in targeted retry iter 1"; PASS=$((PASS + 1))
else
  echo "FAIL: 2c. missing targeted retry iter 1 log"; FAIL=$((FAIL + 1))
fi

"$PLC" --low-mem --evict=off -v -j2 "$FIX/acc_unfold.export" > "$W/plc_off_ok.log" 2>&1 && rc=0 || rc=$?
check_rc "2d. pleanchecker-lowmem --evict=off accepts acc_unfold" 0 "$rc"

"$PLC" --low-mem --evict=smart -v -j2 "$FIX/acc_unfold_evicted.export" > "$W/plc_smart_ev.log" 2>&1 && rc=0 || rc=$?
check_rc "2e. pleanchecker-lowmem --evict=smart rejects acc_unfold_evicted" 1 "$rc"
if grep -q "fixed point reached at iter 1 (kept=0)" "$W/plc_smart_ev.log"; then
  echo "PASS: 2f. realAxioms filter reached fixed point at iter 1 (kept=0, 0 wasted retries)"; PASS=$((PASS + 1))
else
  echo "FAIL: 2f. expected iter 1 (kept=0) fixed point"; FAIL=$((FAIL + 1))
fi

# 3. Real-world suitex theorem-unfolding case (if suitex mirror is present)
K04_IOTA=$FIX/thm-unfold-iota-good.ndjson   # shipped with the test (crafted theorem-unfolding case)
if [ -f "$K04_IOTA" ]; then
  "$PLC" --low-mem --evict=strict -j2 "$K04_IOTA" > "$W/k04_strict.log" 2>&1 && rc=0 || rc=$?
  check_rc "3a. K-K04-thm-unfold-iota-good strict rejects" 1 "$rc"
  "$PLC" --low-mem --evict=smart -j2 "$K04_IOTA" > "$W/k04_smart.log" 2>&1 && rc=0 || rc=$?
  check_rc "3b. K-K04-thm-unfold-iota-good smart accepts" 0 "$rc"
else
  echo "SKIP 3. theorem-unfolding case: input $K04_IOTA missing"
fi

# 4. Adversarial exports: duplicate decl, non-dense fallback, invalid type, selftest good/bad
cp "$FIX/acc_unfold.export" "$W/dup.export"
tail -n 1 "$FIX/acc_unfold.export" >> "$W/dup.export"
"$PLC" --low-mem --evict=smart -j2 "$W/dup.export" > "$W/dup.log" 2>&1 && rc=0 || rc=$?
check_rc "4a. duplicate declaration rejected" 1 "$rc"

# Non-dense expr index forces fallback to official LeanExport.parseStream + Lean.Replay
python3 - "$FIX/acc_unfold.export" "$W/sparse.export" <<'PY'
import sys
lines = open(sys.argv[1]).readlines()
# Replace expr index 0 -> 999999 in all records cleanly? Easier: insert a blank/comment or bump highest unused expr index!
out = [lines[0]]
for l in lines[1:]:
    out.append(l)
out.append('{"ie":999999,"bvar":0}\n')
open(sys.argv[2], "w").writelines(out)
PY
"$PLC" --low-mem --evict=smart -v -j2 "$W/sparse.export" > "$W/sparse.log" 2>&1 && rc=0 || rc=$?
check_rc "4b. non-dense expr index falls back cleanly to official parser and accepts" 0 "$rc"
if grep -q "falling back to official LeanExport.parseStream" "$W/sparse.log"; then
  echo "PASS: 4c. official fallback triggered on non-dense index"; PASS=$((PASS + 1))
else
  echo "FAIL: 4c. expected fallback log"; FAIL=$((FAIL + 1))
fi

ST_GOOD=/scratch/fastverify-next/selftest/good.export
ST_BAD=/scratch/fastverify-next/selftest/bad.export
ST_CH=/scratch/fastverify-next/selftest/challenge.export
ST_CFG=/scratch/fastverify-next/selftest/comparator.json
if [ -f "$ST_GOOD" ] && [ -f "$ST_BAD" ]; then
  "$PLC" --low-mem --evict=smart -j2 "$ST_GOOD" > "$W/stg.log" 2>&1 && rc=0 || rc=$?
  check_rc "4d. selftest good accepted by pleanchecker-lowmem" 0 "$rc"
  # selftest/bad.export is kernel-valid (uses sorryAx), so kernel accepts (0) and full check-sound-lowmem rejects (1)
  "$PLC" --low-mem --evict=smart -j2 "$ST_BAD" > "$W/stb_k.log" 2>&1 && rc=0 || rc=$?
  check_rc "4e. selftest bad (sorryAx) kernel-valid matches official leanchecker" 0 "$rc"
  if [ -x "$CSLM" ] && [ -f "$ST_CH" ] && [ -f "$ST_CFG" ]; then
    "$CSLM" "$ST_BAD" "$ST_CH" "$ST_CFG" --threads 2 --workdir "$W" > "$W/stb_cs.log" 2>&1 && rc=0 || rc=$?
    check_rc "4f. selftest bad rejected by combined check-sound-ultralowmem.sh" 1 "$rc"
  fi
fi

# 5. gruszka-lowmem checks + zero temp-file leak check
mkdir -p "$W/packdir"
"$GRZ" --low-mem --pack-dir="$W/packdir" "$FIX/acc_unfold.export" 2 > "$W/gr_ok.log" 2>&1 && rc=0 || rc=$?
check_rc "5a. gruszka-lowmem accepts acc_unfold.export" 0 "$rc"
"$GRZ" --low-mem --pack-dir="$W/packdir" "$FIX/acc_unfold_evicted.export" 2 > "$W/gr_ev.log" 2>&1 && rc=0 || rc=$?
check_rc "5b. gruszka-lowmem rejects acc_unfold_evicted.export" 1 "$rc"
"$GRZ" --low-mem --pack-dir="$W/packdir" "$W/dup.export" 2 > "$W/gr_dup.log" 2>&1 && rc=0 || rc=$?
check_rc "5c. gruszka-lowmem declines (rc=2) duplicate decl" 2 "$rc"
leftovers=$(ls -A "$W/packdir" | wc -l)
if [ "$leftovers" = 0 ]; then
  echo "PASS: 5d. zero temp .susz files leaked in pack-dir"; PASS=$((PASS + 1))
else
  echo "FAIL: 5d. $leftovers leftover file(s) in pack-dir"; FAIL=$((FAIL + 1))
fi

# 6. Portability & instruction audit
max_glibc=$(objdump -T "$PLC" 2>/dev/null | grep -oE 'GLIBC_[0-9.]+' | sort -Vu | tail -n 1 || echo "NONE")
libstdcxx=$(ldd "$PLC" 2>/dev/null | grep -c 'libstdc++' || true)
if [ "$libstdcxx" = 0 ] && [ "$(printf '%s\nGLIBC_2.17\n' "$max_glibc" | sort -Vu | tail -n 1)" = "GLIBC_2.17" ]; then
  echo "PASS: 6a. pleanchecker-lowmem portable (max=$max_glibc, dynamic libstdc++=$libstdcxx)"; PASS=$((PASS + 1))
else
  echo "FAIL: 6a. pleanchecker-lowmem portability check failed (max=$max_glibc, libstdc++=$libstdcxx)"; FAIL=$((FAIL + 1))
fi
sse4a=$(objdump -d "$GRZ" 2>/dev/null | grep -cE '\b(insertq|extrq)\b' || true)
if [ "$sse4a" = 0 ]; then
  echo "PASS: 6b. gruszka-lowmem has 0 AMD-only SSE4a (insertq/extrq) instructions"; PASS=$((PASS + 1))
else
  echo "FAIL: 6b. gruszka-lowmem has $sse4a SSE4a instructions"; FAIL=$((FAIL + 1))
fi

# 7. OOM fail-closed test under cgrun (if available)
if [ -x "$CGRUN" ] && [ -x "$CSLM" ] && [ -f "$ST_GOOD" ]; then
  ST_CH=/scratch/fastverify-next/selftest/challenge.export
  ST_CFG=/scratch/fastverify-next/selftest/comparator.json
  "$CGRUN" --mem 24M --name ultralowmem-test-oom -- "$CSLM" "$ST_GOOD" "$ST_CH" "$ST_CFG" --threads 1 --workdir "$W" > "$W/oom.log" 2>&1 && rc=0 || rc=$?
  if [ "$rc" != 0 ] && [ "$rc" != 1 ]; then
    echo "PASS: 7a. OOM under cgrun --mem 24M failed closed (rc=$rc, never ACCEPTED=0 or REJECTED=1)"; PASS=$((PASS + 1))
  else
    echo "FAIL: 7a. OOM under cgrun --mem 24M gave rc=$rc (must never be 0 or 1!)"; FAIL=$((FAIL + 1))
  fi
else
  echo "SKIP 7a. OOM under cgrun: needs a cgroup tool (FV_CGRUN, /usr/local/bin/cgrun or cgrun on PATH; sudo systemd-run), which is not part of the repository"
fi

# 8. Cyclic-def WHNF DoS regression (C-c03-lv-cyclic-defs-unfold) + Lean #16489/#15100/#15101 adversarial exploits
C03=${FV_BENCH_INPUTS:-/scratch/bench-inputs}/suitex/bad/C-c03-lv-cyclic-defs-unfold.ndjson
if [ -f "$C03" ]; then
  timeout 5 "$PLC" --low-mem --evict=smart -j4 "$C03" > "$W/c03.log" 2>&1 && rc=0 || rc=$?
  check_rc "8a. cyclic-def DoS C-c03-lv-cyclic-defs-unfold rejected in <5s (no WHNF hang)" 1 "$rc"
else
  echo "SKIP 8a. cyclic-def DoS: input $C03 (3.8 MB) is not part of the repository"
fi
if [ -f "$ST_GOOD" ] && [ -f "$ST_CH" ] && [ -f "$ST_CFG" ] && [ -x "$CSLM" ]; then
  python3 -I - "$ST_GOOD" "$W" <<'PY'
import json, os, sys
good = open(sys.argv[1], encoding="utf-8").read().splitlines()
outd = sys.argv[2]
mi = max((json.loads(l).get("in", 0) for l in good[1:]), default=0)
me = max((json.loads(l).get("ie", 0) for l in good[1:]), default=0)
def mk16489(u):
    n1, n2, n3, n4 = mi+1, mi+2, mi+3, mi+4
    e0, e1, e2, e3, e4, e5, e6 = [me+k for k in range(1, 8)]
    return good + [
        json.dumps({"in": n1, "str": {"pre": 0, "str": "Bad16489"}}),
        json.dumps({"in": n2, "str": {"pre": n1, "str": "mk"}}),
        json.dumps({"in": n3, "str": {"pre": 0, "str": "a"}}),
        json.dumps({"in": n4, "str": {"pre": 0, "str": "x"}}),
        json.dumps({"ie": e0, "sort": 0}),
        json.dumps({"const": {"name": n1, "us": []}, "ie": e1}),
        json.dumps({"bvar": 1, "ie": e2}),
        json.dumps({"forallE": {"binderInfo": "default", "body": e0, "name": n3, "type": e0}, "ie": e3}),
        json.dumps({"app": {"arg": e2, "fn": e1}, "ie": e4}),
        json.dumps({"forallE": {"binderInfo": "default", "body": e4, "name": n4, "type": e2}, "ie": e5}),
        json.dumps({"forallE": {"binderInfo": "default", "body": e5, "name": n3, "type": e0}, "ie": e6}),
        json.dumps({"inductive": {
            "types": [{"name": n1, "levelParams": [], "type": e3, "numParams": 1, "numIndices": 0,
                       "all": [n1], "ctors": [n2], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
            "ctors": [{"name": n2, "levelParams": [], "type": e6, "induct": n1, "cidx": 0,
                       "numParams": 1, "numFields": 1, "isUnsafe": u}],
            "recs": [],
        }}),
    ]
open(os.path.join(outd, "cve_16489_unsafe.export"), "w").write("\n".join(mk16489(True)) + "\n")
open(os.path.join(outd, "cve_15101_quot.export"), "w").write("\n".join(good + [
    json.dumps({"in": mi+1, "str": {"pre": 0, "str": "FakeQuot"}}),
    json.dumps({"ie": me+1, "sort": 0}),
    json.dumps({"quot": {"name": mi+1, "levelParams": [], "type": me+1, "kind": "type"}}),
]) + "\n")
PY
  "$PLC" --low-mem --evict=smart -j2 "$W/cve_16489_unsafe.export" > "$W/c16489p.log" 2>&1 && rc=0 || rc=$?
  check_rc "8b. Lean #16489 (loose bvar + isUnsafe=true ctor bypass) directly rejected by pleanchecker-lowmem" 1 "$rc"
  "$CSLM" "$W/cve_16489_unsafe.export" "$ST_CH" "$ST_CFG" --threads 2 --workdir "$W" > "$W/c16489c.log" 2>&1 && rc=0 || rc=$?
  check_rc "8c. Lean #16489 (unsafe ctor) rejected by check-sound-ultralowmem.sh" 1 "$rc"
  "$CSLM" "$W/cve_15101_quot.export" "$ST_CH" "$ST_CFG" --threads 2 --workdir "$W" > "$W/c15101c.log" 2>&1 && rc=0 || rc=$?
  check_rc "8d. Lean #15101 (FakeQuot) rejected by check-sound-ultralowmem.sh" 1 "$rc"
fi

echo "=== SUMMARY: PASS=$PASS FAIL=$FAIL ==="
[ "$FAIL" = 0 ]
