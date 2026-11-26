#!/bin/bash
# fastverify/tests/warm-delta/test.sh [WORKDIR]
# Component test for the persistent warm delta verification (fastverify/check/warm/ + tools/delta-export/).
# Verifies:
#   1. All 43 adversarial soundness attacks (stale-dep 1/2-hop, inductive attacks, implicit/Quot fallback,
#      JSON/newline injection, 40-iter TOCTOU race, startup config pinning, startup Check A,
#      tiny-timeout clamp, leg-crash auto-respawn, conditional mode exit 3, gruszka Ref::Main edge, RSS soak).
#   2. Conditional lifecycle: stage 0 -> lemma closures and cheats (--conditional-mode, never exit 0) -> graduation (10/10).
#   3. Live Lean 4.37.0-rc1 E2E + adversarial suite (10/10: Tier-1/Tier-2 --exclude, mid-DAG clean importer,
#      dual-kernel drift, sorry, 4.37 unsorried def hole, #15101 FakeQuot, B4 --pins, conditional mode,
#      and C11 --hide E2E + adversarial size/FIFO/symlink refusal;
#      auto-SKIPs if v4.37.0-rc1 toolchain or /scratch/fastverify-next/warm/v1-437 binaries are absent).
set -euo pipefail
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKG=${FASTVERIFY:-$(cd "$H/../.." && pwd)}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/warm-delta.XXXXXX")}
BINS=${WARM_BINS:-/scratch/fastverify-next/warm/v1}
rm -rf "$W"; mkdir -p "$W/adv" "$W/cond" "$W/out" "$W/e2e437"

echo "=== [1/3] adversarial-43 (fvcheckd soundness, config-pinning, Check A, TOCTOU, gruszka Ref::Main, soak) ==="
python3 -I "$H/run_adversarial.py" \
  --fvcheckd "$PKG/check/warm/fvcheckd.py" \
  --bins-dir "$BINS" --pkgroot "$PKG" --work "$W/adv" --soak-n 100

echo "=== [2/3] conditional delta lifecycle (10/10, startup Check A) ==="
python3 -I "$H/bench_conditional_lifecycle.py" \
  --fvcheckd "$PKG/check/warm/fvcheckd.py" \
  --work "$W/cond" --out "$W/out" --bins-dir "$BINS" --pkgroot "$PKG"

echo "=== [3/3] Live Lean 4.37.0-rc1 warm delta E2E + adversarial (10/10, pins-437.env + --hide + auto-dispatch) ==="
python3 -I "$H/test_warm437.py" --work "$W/e2e437" --pkgroot "$PKG"

echo "PASS warm-delta"
