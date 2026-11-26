#!/bin/bash
# export-delta.sh — untrusted sandboxed Delta Native Exporter wrapper.
#
#   export-delta.sh PROJECT_DIR MODULES_LIST_OR_NAME OUT_DELTA.ndjson [--packages WS] [--toolchain TC433]
#                   [--bin LEAN4EXPORT_DELTA] [--threads N] [--targets T1,T2,...] [--exclude BASE_CONSTS.txt]
#
# Tier 1 (default): reads ONLY the specified .olean module(s) (LEAN4EXPORT_DELTA_ONLY=1, ~10-50 ms, KB).
# Tier 2 (--exclude BASE_CONSTS.txt): loads imported .oleans and stops traversing at any constant listed
#   in BASE_CONSTS.txt (LEAN4EXPORT_SNAP=1 LEAN4EXPORT_EXCLUDE=...), capturing newly-used Mathlib/base
#   lemmas that were not yet present in the base export without re-serializing the base.
#
# Completely UNTRUSTED (S3): runs inside bwrap --unshare-all without network; a missing or
# wrong constant in the delta can ONLY cause REJECTED or FALLBACK_REQUIRED in fvcheckd, never ACCEPTED.
set -euo pipefail
[ $# -ge 3 ] || { echo "usage: export-delta.sh PROJECT_DIR MOD_OR_@FILE OUT_DELTA [--packages WS] [--toolchain TC] [--bin BIN] [--threads N] [--targets T1,T2] [--exclude FILE]" >&2; exit 2; }
PROJ=$(readlink -f -- "$1"); MOD=$2; OUT=$3; shift 3
WS=; TC=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1
BIN=; THREADS=1; TARGETS=; EXCLUDE=
while [ $# -gt 0 ]; do
  case "$1" in
    --packages) WS=$(readlink -f -- "$2"); shift 2;;
    --toolchain) TC=$(readlink -f -- "$2"); shift 2;;
    --bin) BIN=$(readlink -f -- "$2"); shift 2;;
    --threads) THREADS=$2; shift 2;;
    --targets) TARGETS=$2; shift 2;;
    --exclude) EXCLUDE=$(readlink -f -- "$2"); shift 2;;
    *) echo "export-delta.sh: unknown arg '$1'" >&2; exit 2;;
  esac
done
if [ -z "$BIN" ]; then
  TCVER=$("$TC/bin/lean" --version 2>/dev/null || true)
  if [[ "$TCVER" == *"version 4.37.0-rc1"* ]]; then
    BIN=/scratch/fastverify-next/warm/v1-437/lean4export-delta-437
  else
    BIN=/scratch/fastverify-next/warm/714773ea/lean4export-delta
  fi
fi
[ -x "$BIN" ] || { echo "export-delta.sh: missing binary $BIN" >&2; exit 2; }
LP="$PROJ/.lake/build/lib/lean"
if [ -n "$WS" ] && [ -d "$WS/.lake/packages" ]; then
  for d in "$WS/.lake/packages"/*/.lake/build/lib/lean; do
    [ -d "$d" ] && LP="$LP:$d"
  done
fi
OUT_ABS=$(readlink -m -- "$OUT")
OUT_DIR=$(dirname "$OUT_ABS")
mkdir -p "$OUT_DIR"
TMP=$(mktemp "$OUT_DIR/.delta.XXXXXX")
TMP_T1=
TMP_EX=
trap 'rm -f "$TMP" "$TMP_T1" "$TMP_EX"' EXIT

BWRAP_MOD_BIND=()
if [[ "$MOD" == @* ]]; then
  MFILE=$(readlink -f -- "${MOD#@}")
  BWRAP_MOD_BIND=(--ro-bind "$MFILE" "$MFILE")
  MOD="@$MFILE"
fi
BWRAP_WS_BIND=()
if [ -n "$WS" ]; then BWRAP_WS_BIND=(--ro-bind "$WS" "$WS"); fi

ARGS=("$MOD")
if [ -n "$TARGETS" ]; then
  ARGS+=(--)
  IFS=',' read -r -a TARR <<< "$TARGETS"
  for t in "${TARR[@]}"; do [ -n "$t" ] && ARGS+=("$t"); done
fi

BWRAP_EX_BIND=()
MODE_ENV=(--setenv LEAN4EXPORT_DELTA_ONLY 1)
if [ -n "$EXCLUDE" ]; then
  # Tier 2: NEVER exclude constants declared in the dirty module(s) themselves!
  # First run a fast (~20 ms) Tier-1 export of the dirty module(s) to get their declared constant names,
  # subtract those names from $EXCLUDE, and then run SNAP with the filtered exclude list.
  TMP_T1=$(mktemp "$OUT_DIR/.delta_t1.XXXXXX")
  TMP_EX=$(mktemp "$OUT_DIR/.delta_ex.XXXXXX")
  env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
    --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc \
    --ro-bind "$TC" "$TC" --ro-bind "$PROJ" "$PROJ" --ro-bind "$BIN" "$BIN" \
    "${BWRAP_WS_BIND[@]}" "${BWRAP_MOD_BIND[@]}" \
    --setenv HOME /tmp --setenv TMPDIR /tmp --setenv LANG C.UTF-8 \
    --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_PATH "$LP" \
    --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN4EXPORT_DELTA_ONLY 1 \
    --setenv LEAN4EXPORT_THREADS 1 \
    -- "$BIN" "$MOD" > "$TMP_T1"
  python3 -I - "$TMP_T1" "$EXCLUDE" "$TMP_EX" <<'PY'
import json, sys
t1_path, ex_path, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
names = {0: ""}
dirty = set()
with open(t1_path, "r", encoding="utf-8") as f:
    for ln in f:
        ln = ln.strip()
        if not ln: continue
        obj = json.loads(ln)
        if "in" in obj:
            if "str" in obj:
                p = names[obj["str"]["pre"]]
                names[obj["in"]] = (p + "." + obj["str"]["str"]) if p else obj["str"]["str"]
            elif "num" in obj:
                p = names[obj["num"]["pre"]]
                names[obj["in"]] = (p + "." + str(obj["num"]["i"])) if p else str(obj["num"]["i"])
        elif "inductive" in obj:
            ind = obj["inductive"]
            for grp in ("types", "ctors", "recs"):
                for it in ind.get(grp, ()):
                    dirty.add(names[it["name"]])
        else:
            for k in ("axiom", "def", "thm", "opaque", "quot"):
                if k in obj:
                    dirty.add(names[obj[k]["name"]])
with open(ex_path, "r", encoding="utf-8") as fin, open(out_path, "w", encoding="utf-8") as fout:
    for ln in fin:
        s = ln.rstrip("\r\n")
        if s and s not in dirty:
            fout.write(s + "\n")
PY
  BWRAP_EX_BIND=(--ro-bind "$TMP_EX" "$TMP_EX")
  MODE_ENV=(--setenv LEAN4EXPORT_SNAP 1 --setenv LEAN4EXPORT_EXCLUDE "$TMP_EX")
  # SNAP mode requires whole-environment form (no target list)
  ARGS=("$MOD")
fi

env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc \
  --ro-bind "$TC" "$TC" --ro-bind "$PROJ" "$PROJ" --ro-bind "$BIN" "$BIN" \
  "${BWRAP_WS_BIND[@]}" "${BWRAP_MOD_BIND[@]}" "${BWRAP_EX_BIND[@]}" \
  --setenv HOME /tmp --setenv TMPDIR /tmp --setenv LANG C.UTF-8 \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_PATH "$LP" \
  --setenv LEAN_ABORT_ON_PANIC 1 "${MODE_ENV[@]}" \
  --setenv LEAN4EXPORT_THREADS "$THREADS" \
  -- "$BIN" "${ARGS[@]}" > "$TMP"
mv -f "$TMP" "$OUT_ABS"
rm -f "$TMP_T1" "$TMP_EX"
trap - EXIT
