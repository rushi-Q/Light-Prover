#!/bin/bash
# prechk.sh — official-tool hazard pre-check. Wrapper around the pinned static binary $PRECHK_BIN (pins.env).
#
#   prechk.sh [--mode strict|checkA|checkB] [--config COMPARATOR_JSON] [--nanoda yes|no|auto] [--ignore C1,C2]
#             [--threads N] [--json F] EXPORT
#   prechk.sh --closure TARGETS_FILE [--threads N] [--json F] EXPORT   (export guard: exit 0 iff every target and every
#             constant referenced by the export is declared in it and the file is canonical; else 3/4 -> discard the export)
#   prechk.sh --preflight
#
# Exit: 0 = clean (no official-tool hazard counted for this mode), 3 = hazard -> the fast check must DECLINE,
#       4 = malformed / non-canonical export -> DECLINE, 2 = cannot run (missing/modified binary, bad args) -> DECLINE.
# Modes:
#   strict / checkB (default strict): every hazard class counts, including the replay-ORDER classes (order_quot,
#          order_strlit, order_natlit). Use for any checker that does NOT replay constants in Lean.Replay's order
#          with the official kernel (e.g. check B = kcompare + gruszka/nano-lean).
#   checkA: the order classes are reported but not counted, because check A's Lean leg (pchk Par.lean, reviewed
#          equivalent to Lean.Replay's walk, linked against the official 4.36 kernel) reproduces the official order and
#          therefore the official verdict on those exports by construction. All limit classes still count.
# --config: the project's comparator.json; nanoda_* classes count only if it runs a nanoda kernel (external_kernels
#          name containing "noda", or enable_nanoda) -- exactly the official comparator's isNanodaKernel heuristic.
#          Without --config (or --nanoda auto without a config) nanoda classes count (conservative).
set -u
H=$(cd "$(dirname "$0")" && pwd)
# the binary lives outside the package (node-local, see pins.env); its sha256 is pinned in SHA256SUMS
PRECHK_BIN=
[ -f "$H/pins.env" ] && . "$H/pins.env"
BIN=${PRECHK_BIN:-/scratch/fastverify-next/prechk/prechk}
EXPECT_VERSION="prechk 1.6"
MODE=strict; CFG=; NANODA=auto; THREADS=; JSON=; PREFLIGHT=0; EXPORT=; EXTRA_IGNORE=; CLOSURE=
die() { echo "prechk.sh: $*" >&2; exit 2; }
while [ $# -gt 0 ]; do
  case "$1" in
    --mode) MODE=${2:-}; shift 2;;
    --config) CFG=${2:-}; shift 2;;
    --nanoda) NANODA=${2:-}; shift 2;;
    --threads) THREADS=${2:-}; shift 2;;
    --json) JSON=${2:-}; shift 2;;
    --preflight) PREFLIGHT=1; shift;;
    --ignore) EXTRA_IGNORE=${2:-}; shift 2;;          # passthrough (classes reported but not counted)
    --no-nanoda) NANODA=no; shift;;
    --closure) CLOSURE=${2:-}; shift 2;;            # export-completeness guard mode (see README)
    -h|--help) sed -n 2,19p "$0"; exit 2;;
    -*) die "unknown option $1";;
    *) [ -z "$EXPORT" ] || die "more than one export given"; EXPORT=$1; shift;;
  esac
done
case "$MODE" in strict|checkA|checkB) ;; *) die "--mode must be strict, checkA or checkB";; esac
case "$NANODA" in yes|no|auto) ;; *) die "--nanoda must be yes, no or auto";; esac

# ---- pinned binary: sha256 must match SHA256SUMS, and it must start and report the expected version
[ -x "$BIN" ] || die "binary $BIN missing (deploy it: check/prechk/build.sh --install on this host, or tools/deploy.sh)"
want=$(awk '$2=="prechk"{print $1}' "$H/SHA256SUMS" 2>/dev/null)
have=$(sha256sum "$BIN" 2>/dev/null | cut -d' ' -f1)
[ -n "$want" ] && [ "$want" = "$have" ] || die "binary sha256 $have does not match the pinned $want"
ver=$(env -i "$BIN" --version 2>&1) || die "binary cannot start: $ver"
[ "$ver" = "$EXPECT_VERSION" ] || die "unexpected version '$ver'"
if [ "$PREFLIGHT" = 1 ]; then echo "prechk.sh preflight OK: $ver sha256 $have"; exit 0; fi

[ -n "$EXPORT" ] || die "no export given"
[ -f "$EXPORT" ] || die "export must be a regular file (not a pipe/device/directory): $EXPORT"   # the binary re-checks the opened fd (fstat S_ISREG)

ARGS=()
[ -n "$THREADS" ] && ARGS+=(--threads "$THREADS")
[ -n "$JSON" ] && ARGS+=(--json "$JSON")
IGN=$EXTRA_IGNORE
[ "$MODE" = checkA ] && IGN=${IGN:+$IGN,}order_quot,order_strlit,order_natlit
[ -n "$IGN" ] && ARGS+=(--ignore "$IGN")
if [ "$NANODA" = auto ] && [ -n "$CFG" ]; then
  [ -f "$CFG" ] || die "config $CFG not found"
  NANODA=$(/usr/bin/python3 -I - "$CFG" <<'PY'
import json, sys
try:
    c = json.load(open(sys.argv[1]))
except Exception as e:
    print("error"); sys.exit(0)
ek = c.get("external_kernels") or {}
uses = bool(c.get("enable_nanoda")) or any("noda" in k for k in ek)
print("yes" if uses else "no")
PY
)
  [ "$NANODA" = yes ] || [ "$NANODA" = no ] || die "cannot parse comparator config $CFG"
fi
[ "$NANODA" = no ] && ARGS+=(--no-nanoda)
if [ -n "$CLOSURE" ]; then [ -f "$CLOSURE" ] || die "targets file $CLOSURE not found"; ARGS+=(--closure "$CLOSURE"); fi

env -i "$BIN" "${ARGS[@]}" "$EXPORT"
rc=$?
case $rc in 0|3|4) exit $rc;; *) exit 2;; esac
