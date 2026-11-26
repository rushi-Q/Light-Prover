#!/bin/bash
# fastverify/export/export-lowmem.sh — LOW-MEMORY EXPORT stage (additive drop-in for export.sh).
#
# Identical CLI, exit codes, closure_check guard, and byte-for-byte NDJSON output as export.sh, using
# lean4export-lowmem with LEAN4EXPORT_LOWMEM=1 (untested/untrusted under S3; validated by closure_check + CS check):
#   * .ir.sig / .ir validated identically to export.sh and unmapped immediately (saves ~40 GB + 440k mmaps on RH);
#   * 4 KB demand paging on MAP_NORESERVE tables (no MADV_HUGEPAGE 512x THP amplification, no prefault_huge);
#   * clean file-backed .olean pages released via MADV_DONTNEED after metadata/phase-A scans (reclaimable under cgroup);
#   * sequential St dump (no ~80 GB PD event/owner arenas) + O_DIRECT/stream output (no 61.6 GB MAP_SHARED output mmap).
set -u
main() {
EMITTED=0; PART=; JSON=; OUT=
on_exit() {
  local rc=$?
  [ -n "${PART:-}" ] && rm -f "$PART" "$PART.official" "$PART.err" "$PART.pf"
  if [ "${EMITTED:-0}" != 1 ]; then
    local line="{\"stage\": \"export\", \"exit\": 2, \"exporter\": \"none\", \"detail\": \"internal error (exit $rc)\"}"
    echo "$line"; [ -n "${JSON:-}" ] && echo "$line" > "$JSON"
    [ -n "${OUT:-}" ] && rm -f "$OUT"
    exit 2
  fi
}
trap on_exit EXIT
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PY=/usr/bin/python3
BWRAP=/usr/bin/bwrap
COMP=$HERE/components-lowmem.json

jget() { "$PY" -I -c 'import json,sys; c=json.load(open(sys.argv[1]))
for k in sys.argv[2].split("/"): c=c[k]
print(c)' "$COMP" "$1"; }

NATIVE=$(jget native/path) || { echo "export-lowmem: cannot read $COMP" >&2; exit 2; }
NATIVE_SHA=$(jget native/sha256)
NATIVE_LEAN=$(jget native/lean_version)
OFFX=$(jget official/path); OFFX=${OFFX/\$LIGHT_LEAN/$(dirname "$PKG")}; OFFSHA=$(jget official/sha256)
select_native() {  # TC -> select matching natives_other entry (e.g. Lean 4.37.0-rc1) if present
  local v sel; v=$(env -i PATH=/usr/bin:/bin "$1/bin/lean" --version 2>/dev/null) || return 0
  sel=$("$PY" -I -c 'import json,sys
c=json.load(open(sys.argv[1]))
for e in c.get("natives_other", []):
    if e["lean_version"] == sys.argv[2]:
        op = e["official"]["path"]
        if op.startswith("$TC/"): op = sys.argv[3] + op[3:]
        print("\t".join([e["path"], e["sha256"], e["lean_version"], op, e["official"]["sha256"]])); break' "$COMP" "$v" "$1") || return 0
  [ -n "$sel" ] && IFS=$'\t' read -r NATIVE NATIVE_SHA NATIVE_LEAN OFFX OFFSHA <<< "$sel"
  return 0
}
CLOSURE=$(jget closure_check/path)
CLOSURE_SHA=$(jget closure_check/sha256)

lean_version_of() { env -i PATH=/usr/bin:/bin "$1/bin/lean" --version 2>/dev/null; }

preflight() {
  local tc=$1 have v
  select_native "$tc"
  [ -x "$BWRAP" ] || { echo "export-lowmem: preflight: $BWRAP missing" >&2; return 1; }
  [ -x "$NATIVE" ] || { echo "export-lowmem: preflight: $NATIVE missing" >&2; return 1; }
  have=$(sha256sum "$NATIVE" | cut -d' ' -f1)
  [ "$have" = "$NATIVE_SHA" ] || { echo "export-lowmem: preflight: $NATIVE sha256 $have != pinned $NATIVE_SHA" >&2; return 1; }
  [ -x "$CLOSURE" ] || { echo "export-lowmem: preflight: closure guard $CLOSURE missing" >&2; return 1; }
  have=$(sha256sum "$CLOSURE" | cut -d' ' -f1)
  [ "$have" = "$CLOSURE_SHA" ] || { echo "export-lowmem: preflight: $CLOSURE sha256 $have != pinned $CLOSURE_SHA" >&2; return 1; }
  v=$(lean_version_of "$tc")
  [ "$v" = "$NATIVE_LEAN" ] || { echo "export-lowmem: preflight: toolchain is '$v'; supports only '$NATIVE_LEAN'" >&2; return 1; }
  local out; out=$(mktemp /tmp/fv-export-lm-pf.XXXXXX) || return 1
  "$BWRAP" --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --dev /dev --proc /proc --clearenv \
      --ro-bind "$tc" "$tc" --setenv PATH "$tc/bin:/usr/bin:/bin" --setenv HOME /tmp --setenv LANG C.UTF-8 \
      --setenv LEAN_PATH "$tc/lib/lean" --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN4EXPORT_VERBOSE 0 \
      --setenv LEAN4EXPORT_LOWMEM 1 \
      --unshare-all --die-with-parent --new-session --chdir / -- "$NATIVE" Init -- Nat.add > "$out" 2>/dev/null
  local rc=$?
  local n; n=$(grep -c '"def"' "$out" 2>/dev/null)
  rm -f "$out"
  [ $rc -eq 0 ] && [ "${n:-0}" -ge 1 ] || { echo "export-lowmem: preflight: native exporter failed (exit $rc)" >&2; return 1; }
  return 0
}
if [ "${1:-}" = --preflight ]; then EMITTED=1; [ $# -ge 2 ] || { echo "export-lowmem: --preflight TOOLCHAIN_PREFIX" >&2; exit 2; }; preflight "$2"; exit $?; fi

LP=; MOD=; TF=; TFNL=0; TC=; PROJ=; BINDS=; OUT=; THREADS=0; JSON=; FALLBACK=0; VERIFY=0; export FV_EXPORT_SHA=0
while [ $# -gt 0 ]; do
  case "$1" in
    --lean-path) LP=$2; shift 2 ;;
    --module) MOD=$2; shift 2 ;;
    --targets-file) TF=$2; shift 2 ;;
    --targets-nl) TF=$2; TFNL=1; shift 2 ;;
    --toolchain) TC=$2; shift 2 ;;
    --project) PROJ=$2; shift 2 ;;
    --binds) BINDS=$2; shift 2 ;;
    --out) OUT=$2; shift 2 ;;
    --threads) THREADS=$2; shift 2 ;;
    --json) JSON=$2; shift 2 ;;
    --official-fallback) FALLBACK=1; shift ;;
    --verify) VERIFY=1; shift ;;
    --sha256) FV_EXPORT_SHA=1; shift ;;
    *) echo "export-lowmem: unknown argument $1" >&2; exit 2 ;;
  esac
done
T0=$(date +%s.%N)
NAT_RC=null; NAT_SEC=0; NAT_WHY=""; NAT_EARLY=0; OFF_RC=null; OFF_SEC=0; MODE=none; VER=null; CC_SEC=null
emit() {
  local line
  line=$("$PY" -I - "$1" "$OUT" "$MODE" "$NAT_RC" "$NAT_SEC" "$NAT_WHY" "$OFF_RC" "$OFF_SEC" "$VER" "$T0" "$NATIVE" "$NATIVE_SHA" "$CC_SEC" "$NAT_EARLY" <<'EOF'
import hashlib, json, os, sys, time
rc, out, mode, nrc, nsec, nwhy, orc, osec, ver, t0, nat, natsha, ccsec, nearly = sys.argv[1:15]
def num(x):
    return None if x == "null" else (float(x) if "." in x else int(x))
r = {"stage": "export", "exit": int(rc), "exporter": mode, "lowmem": True, "out": out,
     "native": {"path": nat, "sha256": natsha, "exit": num(nrc), "seconds": num(nsec), "decline_reason": nwhy or None,
                "closure_guard_seconds": num(ccsec), "early_return": nearly == "1"},
     "official": {"exit": num(orc), "seconds": num(osec)},
     "verify": None if ver == "null" else ver, "seconds": round(time.time() - float(t0), 3)}
if int(rc) == 0 and os.path.isfile(out) and os.environ.get("FV_EXPORT_SHA") == "1":
    h = hashlib.sha256()
    with open(out, "rb") as f:
        for b in iter(lambda: f.read(1 << 24), b""):
            h.update(b)
    r["sha256"] = h.hexdigest(); r["size"] = os.path.getsize(out)
print(json.dumps(r))
EOF
)
  echo "$line"; [ -n "$JSON" ] && echo "$line" > "$JSON"
  EMITTED=1
  exit "$1"
}
for v in LP MOD TF TC PROJ OUT; do [ -n "${!v}" ] || { echo "export-lowmem: --${v,,} missing" >&2; NAT_WHY="usage"; emit 2; }; done
[ -f "$TF" ] && [ -r "$TF" ] || { NAT_WHY="targets file unreadable"; emit 2; }
[ -d "$PROJ" ] && [ -d "$TC" ] || { NAT_WHY="project or toolchain dir missing"; emit 2; }
PROJ=$(readlink -f "$PROJ"); TC=$(readlink -f "$TC")
select_native "$TC"
case "$THREADS" in ''|*[!0-9]*) NAT_WHY="bad --threads"; emit 2 ;; esac
read -r -a MODS <<< "$MOD"
TARGETS=()
if [ $TFNL = 1 ]; then
  while IFS= read -r t || [ -n "$t" ]; do [ -n "$t" ] && TARGETS+=("$t"); done < "$TF"
else
  read -r -d '' -a TARGETS < "$TF"
  for t in "${TARGETS[@]}"; do
    o=$(printf '%s' "$t" | LC_ALL=C grep -o '«' | wc -l); c=$(printf '%s' "$t" | LC_ALL=C grep -o '»' | wc -l)
    [ "$o" = "$c" ] || { NAT_WHY="target name split at whitespace ('$t'); use --targets-nl"; emit 2; }
  done
fi
[ ${#TARGETS[@]} -gt 0 ] || { NAT_WHY="empty targets file"; emit 2; }
OUTDIR=$(dirname "$OUT"); mkdir -p "$OUTDIR" || emit 2
rm -f "$OUT"
PART=$(mktemp "$OUTDIR/.export-lm.partial.XXXXXX") || { NAT_WHY="cannot create private output file"; emit 2; }
LOGBASE=${JSON:-$OUT}; OFF_BAD=0

SBX=("$BWRAP" --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --dir /tmp/home --tmpfs /run
     --tmpfs /var)
# as export/export.sh - the exporters read UNTRUSTED .olean files: every other top-level directory
# except the system ones is hidden (then read-only); the exporter binaries, toolchain, project and packages are bound back
SBXRO=()
for d in /*; do
  [ -d "$d" ] && [ ! -L "$d" ] || continue
  case "${d#/}" in bin|sbin|lib|lib32|lib64|libx32|usr|etc|dev|proc|sys|nix|gnu|home|root|tmp|run|var) ;; *) SBX+=(--tmpfs "$d"); SBXRO+=(--remount-ro "$d") ;; esac
done
SBX+=(--dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --ro-bind "$PROJ" "$PROJ")
if [ -n "$BINDS" ]; then
  while IFS=$'\t' read -r src dst; do
    [ -n "$src" ] || continue
    # only plain absolute paths (no control character, no empty/'.'/'..' component) - else no export (fail closed)
    case "$src${dst:-}" in *[[:cntrl:]]*) NAT_WHY="bad binds line"; emit 2 ;; esac
    for x in "$src" "${dst:-$src}"; do
      case "$x" in /*) ;; *) NAT_WHY="bad binds line"; emit 2 ;; esac
      case "$x/" in */../*|*/./*|*//*) NAT_WHY="bad binds line"; emit 2 ;; esac
    done
    SBX+=(--ro-bind "$src" "${dst:-$src}")
  done < "$BINDS"
fi
SBX+=(--setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP"
      --setenv LEAN_ABORT_ON_PANIC 1)

run_official() {
  local t; t=$(date +%s.%N)
  local osha=$OFFSHA
  [ "$(lean_version_of "$TC")" = "$NATIVE_LEAN" ] || { echo "export-lowmem: no official exporter pinned for this toolchain's release" >&2; OFF_RC=null; OFF_BAD=1; return 2; }
  [ "$(sha256sum "$OFFX" | cut -d' ' -f1)" = "$osha" ] || { echo "export-lowmem: official sha256 mismatch" >&2; OFF_RC=null; OFF_BAD=1; return 2; }
  "${SBX[@]}" --ro-bind "$OFFX" "$OFFX" ${SBXRO[@]+"${SBXRO[@]}"} --unshare-all --die-with-parent --new-session --chdir "$PROJ" -- \
      "$OFFX" "${MODS[@]}" -- "${TARGETS[@]}" > "$1" 2>> "$LOGBASE.official.log"
  OFF_RC=$?
  OFF_SEC=$(echo "$(date +%s.%N) - $t" | bc)
  return $OFF_RC
}

if ! preflight "$TC" 2> "$PART.pf"; then
  NAT_WHY="preflight: $(tail -1 "$PART.pf")"; rm -f "$PART.pf"
else
  rm -f "$PART.pf"
  NM=0
  IFS=: read -r -a LPD <<< "$LP"
  for d in "${LPD[@]}"; do
    [ -d "$d" ] && [ "$d" != "$TC/lib/lean" ] && NM=$((NM + $(find "$d" -name '*.olean' 2>/dev/null | wc -l)))
  done
  EXTRA=(--setenv LEAN4EXPORT_VERBOSE 1 --setenv LEAN4EXPORT_LOWMEM 1)
  [ "$THREADS" -gt 0 ] && EXTRA+=(--setenv LEAN4EXPORT_THREADS "$THREADS")
  [ "$NM" -gt 100000 ] && EXTRA+=(--setenv LEAN4EXPORT_EXPR_ESTIMATE_LOG2 30)
  t=$(date +%s.%N)
  "${SBX[@]}" "${EXTRA[@]}" --ro-bind "$NATIVE" "$NATIVE" ${SBXRO[@]+"${SBXRO[@]}"} --unshare-all --die-with-parent --new-session --chdir "$PROJ" -- \
      "$NATIVE" "${MODS[@]}" -- "${TARGETS[@]}" > "$PART" 2> "$PART.err" &
  NPID=$!
  while :; do
    if ! kill -0 "$NPID" 2>/dev/null; then wait "$NPID"; NAT_RC=$?; break; fi
    if grep -q 's thread\] done: names ' "$PART.err" 2>/dev/null; then
      kill -KILL "$NPID" 2>/dev/null; NAT_RC=0; NAT_EARLY=1; break
    fi
    sleep 0.05
  done
  NAT_SEC=$(echo "$(date +%s.%N) - $t" | bc)
  cp "$PART.err" "$LOGBASE.native.log" 2>/dev/null
  if [ $NAT_RC -eq 0 ] && [ -s "$PART" ]; then
    printf '%s\n' "${TARGETS[@]}" > "$PART.tg"
    t=$(date +%s.%N)
    if env -i PATH=/usr/bin:/bin "$CLOSURE" "$PART" "$PART.tg" "$([ "$THREADS" -gt 0 ] && echo "$THREADS" || nproc)" > "$PART.cc" 2>&1; then
      MODE=native-lowmem
    else
      NAT_RC=4
      NAT_WHY="closure guard: $(head -c 300 "$PART.cc")"
    fi
    CC_SEC=$(echo "$(date +%s.%N) - $t" | bc)
    cat "$PART.cc" >> "$PART.err"; cp "$PART.err" "$LOGBASE.native.log" 2>/dev/null
    rm -f "$PART.tg" "$PART.cc"
  fi
  if [ "$MODE" != native-lowmem ]; then
    [ -n "$NAT_WHY" ] || NAT_WHY=$(grep -E '^lean4export \(native\): ' "$PART.err" | head -1 | sed 's/^lean4export (native): //' | cut -c1-300)
    [ -n "$NAT_WHY" ] || NAT_WHY="native exit $NAT_RC"
  fi
  rm -f "$PART.err"
fi

if [ "$MODE" = native-lowmem ]; then
  if [ $VERIFY -eq 1 ]; then
    run_official "$PART.official"
    if [ "$OFF_RC" = 0 ] && cmp -s "$PART" "$PART.official"; then VER=identical
    else VER="DIFFERENT (official exit $OFF_RC)"; rm -f "$PART"; MODE=none; emit 3; fi
    rm -f "$PART.official"
  fi
  chmod 0644 "$PART"; mv -f "$PART" "$OUT" || emit 2
  emit 0
fi
if [ $FALLBACK -eq 0 ]; then rm -f "$PART"; emit 2; fi
: > "$PART"
run_official "$PART"
MODE=official
if [ "$OFF_RC" = 0 ]; then chmod 0644 "$PART"; mv -f "$PART" "$OUT" || emit 2; emit 0; fi
rm -f "$PART"
[ $OFF_BAD -eq 1 ] && emit 2
emit 1
}
main "$@"; exit $?
