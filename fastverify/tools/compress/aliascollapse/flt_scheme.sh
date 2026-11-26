#!/bin/bash
# flt_scheme.sh SRC OUT [--deny FILE] [--hide RESULTS_DIR|all] [--no-unify] [--no-normalize]
# The compression scheme on the AI-FLT layout, as one reproducible pipeline (text only; nothing is
# elaborated here - every output tree must be built and judged by the trusted check against the official challenge):
#   1. attrhide.py --mode hide (only with --hide: the .lake/p2m_hide results of a check build of the SAME source tree;
#      files whose explicit erasure lists equal the generating rule get one `p2m_hide` line per kind)
#   2. collapse.py --pairs flt --unify --deny FILE (alias-layer collapse; statement unification where the card is a pure
#      alias with the identical statement text; pairs in FILE stay separate)
#   3. normalize.py (imports C1/C2, redundant options; G1) + apply_tree.py, with the dfsverify graphs written
#      next to OUT (OUT.norm-g*) for the exact import-order check.
# Env: NORMALIZE_DIR (default tools/compress/normalize), WS_PACKAGES, TC_SRC.
set -eu
H=$(cd "$(dirname "$0")/.." && pwd)
SRC=$(realpath "$1"); OUT=$2; shift 2
DENY=/dev/null; DENY_UNIFY=/dev/null; HIDE=""; UNIFY=--unify; NORM=1
while [ $# -gt 0 ]; do case $1 in
  --deny) DENY=$2; shift 2;; --deny-unify) DENY_UNIFY=$2; shift 2;; --hide) HIDE=$2; shift 2;; --no-unify) UNIFY=""; shift;; --no-normalize) NORM=0; shift;;
  *) echo "unknown option $1"; exit 2;; esac; done
[ -e "$OUT" ] && { echo "refusing: $OUT exists"; exit 2; }
ND=${NORMALIZE_DIR:-$H/normalize}
WS=${WS_PACKAGES:-$(cd "$H/../../.." && pwd)/verify/challenge/.lake/packages}
TCS=${TC_SRC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean}
T=$(mktemp -d "${OUT%/}.tmp.XXXX")
cur=$SRC
if [ -n "$HIDE" ]; then
  if [ "$HIDE" = all ]; then python3 -I "$H/attrhide/attrhide.py" "$cur" "$T/s1" --mode hide-all --stats "$OUT.attrhide.json"
  elif [ "${HIDE_MODE:-hide}" = hide-auto ]; then python3 -I "$H/attrhide/attrhide.py" "$cur" "$T/s1" --mode hide-auto --matched "$HIDE" --stats "$OUT.attrhide.json"
  else python3 -I "$H/attrhide/attrhide.py" "$cur" "$T/s1" --mode hide --matched "$HIDE" --stats "$OUT.attrhide.json"; fi; cur=$T/s1
fi
python3 -I "$H/aliascollapse/collapse.py" "$cur" "$T/s2" --pairs flt --deny "$DENY" --deny-unify "$DENY_UNIFY" $UNIFY --stats "$OUT.collapse.json" --pairs-out "$OUT.pairs.tsv"; cur=$T/s2
if [ "$NORM" = 1 ]; then
  python3 -I "$ND/normalize.py" "$cur" --edits "$OUT.norm.tsv" --classes imp,opt,optres --srcdir . --packages "$WS" \
    --toolchain-src "$TCS" --json "$OUT.norm.json" --graph-out "$OUT.norm-g"
  python3 -I "$ND/apply_tree.py" "$cur" "$T/s3" "$OUT.norm.tsv" --srcdir . > "$OUT.apply.json"; cur=$T/s3
fi
mv "$cur" "$OUT"; rm -rf "$T"
echo "$OUT: $(find "$OUT" -name '*.lean' | wc -l) files, $(find "$OUT" -name '*.lean' -print0 | xargs -0 cat | wc -l) lines, $(find "$OUT" -name '*.lean' -print0 | xargs -0 cat | wc -c) bytes"
