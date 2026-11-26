#!/bin/bash
# fastverify/export/export.sh — EXPORT stage
#
#   export.sh --preflight TOOLCHAIN_PREFIX
#   export.sh --lean-path LP --module MOD (--targets-file TF | --targets-nl TF) --toolchain TC --project PROJ [--binds BINDS_TSV]
#             --out OUT [--threads N] [--json FILE] [--official-fallback] [--verify] [--sha256] [--ro DIR]...
#
# Produces OUT = the lean4export NDJSON of the import closure of MOD (one or more root modules, space-separated) restricted to the targets in TF, BYTE-IDENTICAL to what
# the official lean4export (v4.33.0 tag, built with the project's official toolchain) writes for the same .olean files
# (other releases with an entry in components.json "natives_other": that release's official exporter, e.g. the bundled
# bin/leanexport of 4.37.0-rc1).
#
# How: the NATIVE exporter (lean4export f581123 native C++ core + the fixes of tests 008-010 + fail-closed patches, built with
# the official v4.33.1 Lake; pinned by sha256 in export/components.json) runs first, inside bwrap (read-only filesystem,
# no network, clean environment). It is native-only: exit 0 = complete export, anything else = it DECLINED (it gives up
# on every input it cannot reproduce exactly: other Lean githash, duplicate constants it cannot decide, panic paths of
# the official exporter, non-UTF-8 strings, huge indices, missing constants, options, ...). Its output is written to a
# fresh private file and only renamed to OUT on exit 0.
#
# On a decline this stage exits 2 (no OUT) and the caller runs the OFFICIAL lean4export (bin/fastverify does that), or,
# with --official-fallback, this script runs the official lean4export itself (same sandbox, LEAN_ABORT_ON_PANIC=1 as
# bin/fastverify's official export) and returns its result.
# --verify additionally runs the official exporter and byte-compares (diagnostic; costs the official export time).
#
# Exit: 0 = OUT written (by the native exporter, or by the official one with --official-fallback)
#       1 = the official exporter failed (only with --official-fallback) = the official flow's export fails too
#       2 = declined / cannot run (no OUT); 3 = --verify found a difference (OUT removed; report as exporter bug)
# One JSON object is printed on stdout (last line) and written to --json FILE.
set -u
# The whole script is one function, parsed completely before it runs: editing or replacing this file (also on NFS)
# cannot corrupt a run in progress.
main() {
# fail closed: any exit that does not go through emit() (internal error, unbound variable under set -u, signal) is
# reported as exit 2 (declined / cannot decide) - never as 1 (= "the official exporter failed" = REJECT)
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
PKG=$(cd "$HERE/.." && pwd)
PY=/usr/bin/python3
BWRAP=/usr/bin/bwrap
COMP=$HERE/components.json

jget() { "$PY" -I -c 'import json,sys; c=json.load(open(sys.argv[1]))
for k in sys.argv[2].split("/"): c=c[k]
print(c)' "$COMP" "$1"; }

NATIVE=$(jget native/path) || { echo "export: cannot read $COMP" >&2; exit 2; }
NATIVE_SHA=$(jget native/sha256)
NATIVE_LEAN=$(jget native/lean_version)          # the only Lean the native exporter reads (githash compiled in)
OFFX=$(jget official/path); OFFX=${OFFX/\$LIGHT_LEAN/$(dirname "$PKG")}; OFFSHA=$(jget official/sha256)   # the official exporter of that same release
# Other releases: components.json "natives_other" lists further native exporters, each the
# native source built with (and reading only the .olean files of) ONE other official release, together with that
# release's official exporter ("official": {"path": ..., "sha256": ...}; a path starting with "$TC/" is relative to the
# project's toolchain prefix, e.g. "$TC/bin/leanexport" = the exporter bundled with releases >= 4.35).  The entry whose
# lean_version equals the toolchain's `lean --version` is selected; with no match the default entry stays selected, so the
# preflight declines as before (other Lean -> the caller runs the official exporter) and --official-fallback declines
# instead of running the exporter of another release (see run_official).
select_native() {  # TC
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
CLOSURE=$(jget closure_check/path)                 # independent closure guard behind every native export
CLOSURE_SHA=$(jget closure_check/sha256)

lean_version_of() { env -i PATH=/usr/bin:/bin "$1/bin/lean" --version 2>/dev/null; }

preflight() {  # TC -> 0 iff the native exporter can be used for this toolchain on this host
  local tc=$1 have v
  select_native "$tc"
  [ -x "$BWRAP" ] || { echo "export: preflight: $BWRAP missing" >&2; return 1; }
  [ -x "$NATIVE" ] || { echo "export: preflight: native exporter $NATIVE missing" >&2; return 1; }
  have=$(sha256sum "$NATIVE" | cut -d' ' -f1)
  [ "$have" = "$NATIVE_SHA" ] || { echo "export: preflight: $NATIVE sha256 $have != pinned $NATIVE_SHA" >&2; return 1; }
  [ -x "$CLOSURE" ] || { echo "export: preflight: closure guard $CLOSURE missing" >&2; return 1; }
  have=$(sha256sum "$CLOSURE" | cut -d' ' -f1)
  [ "$have" = "$CLOSURE_SHA" ] || { echo "export: preflight: $CLOSURE sha256 $have != pinned $CLOSURE_SHA" >&2; return 1; }
  v=$(lean_version_of "$tc")
  [ "$v" = "$NATIVE_LEAN" ] || { echo "export: preflight: toolchain is '$v'; the native exporter supports only '$NATIVE_LEAN'" >&2; return 1; }
  # must start and export a tiny closure (Init, Nat.add) on this host, in the sandbox it runs in
  local out; out=$(mktemp /tmp/fv-export-pf.XXXXXX) || return 1
  "$BWRAP" --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --dev /dev --proc /proc --clearenv \
      --ro-bind "$tc" "$tc" --setenv PATH "$tc/bin:/usr/bin:/bin" --setenv HOME /tmp --setenv LANG C.UTF-8 \
      --setenv LEAN_PATH "$tc/lib/lean" --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN4EXPORT_VERBOSE 0 \
      --unshare-all --die-with-parent --new-session --chdir / -- "$NATIVE" Init -- Nat.add > "$out" 2>/dev/null
  local rc=$?
  local n; n=$(grep -c '"def"' "$out" 2>/dev/null)
  rm -f "$out"
  [ $rc -eq 0 ] && [ "${n:-0}" -ge 1 ] || { echo "export: preflight: native exporter does not run on this host (exit $rc)" >&2; return 1; }
  return 0
}
if [ "${1:-}" = --preflight ]; then EMITTED=1; [ $# -ge 2 ] || { echo "export: --preflight TOOLCHAIN_PREFIX" >&2; exit 2; }; preflight "$2"; exit $?; fi

LP=; MOD=; TF=; TFNL=0; TC=; PROJ=; BINDS=; OUT=; THREADS=0; JSON=; FALLBACK=0; VERIFY=0; export FV_EXPORT_SHA=0; RO=()
while [ $# -gt 0 ]; do
  case "$1" in
    --lean-path) LP=$2; shift 2 ;;
    --module) MOD=$2; shift 2 ;;
    --targets-file) TF=$2; shift 2 ;;
    --targets-nl) TF=$2; TFNL=1; shift 2 ;;   # one target name per line, taken verbatim (names may contain spaces)
    --toolchain) TC=$2; shift 2 ;;
    --project) PROJ=$2; shift 2 ;;
    --binds) BINDS=$2; shift 2 ;;
    --out) OUT=$2; shift 2 ;;
    --threads) THREADS=$2; shift 2 ;;
    --json) JSON=$2; shift 2 ;;
    --official-fallback) FALLBACK=1; shift ;;
    --verify) VERIFY=1; shift ;;
    --sha256) FV_EXPORT_SHA=1; shift ;;   # also put sha256/size of OUT into the JSON (bin/fastverify hashes it itself)
    --ro) RO+=("$2"); shift 2 ;;   # a caller's own read-only tree the project links into
                                   # (fvwork --copy-mode farm: the fixed base project); validated below, bound read-only
    *) echo "export: unknown argument $1" >&2; exit 2 ;;
  esac
done
T0=$(date +%s.%N)
NAT_RC=null; NAT_SEC=0; NAT_WHY=""; NAT_EARLY=0; OFF_RC=null; OFF_SEC=0; MODE=none; VER=null; CC_SEC=null
emit() {  # exit-code
  local line
  line=$("$PY" -I - "$1" "$OUT" "$MODE" "$NAT_RC" "$NAT_SEC" "$NAT_WHY" "$OFF_RC" "$OFF_SEC" "$VER" "$T0" "$NATIVE" "$NATIVE_SHA" "$CC_SEC" "$NAT_EARLY" <<'EOF'
import hashlib, json, os, sys, time
rc, out, mode, nrc, nsec, nwhy, orc, osec, ver, t0, nat, natsha, ccsec, nearly = sys.argv[1:15]
def num(x):
    return None if x == "null" else (float(x) if "." in x else int(x))
r = {"stage": "export", "exit": int(rc), "exporter": mode, "out": out,
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
for v in LP MOD TF TC PROJ OUT; do [ -n "${!v}" ] || { echo "export: --${v,,} missing" >&2; NAT_WHY="usage"; emit 2; }; done
[ -f "$TF" ] && [ -r "$TF" ] || { NAT_WHY="targets file unreadable"; emit 2; }
[ -d "$PROJ" ] && [ -d "$TC" ] || { NAT_WHY="project or toolchain dir missing"; emit 2; }
PROJ=$(readlink -f "$PROJ"); TC=$(readlink -f "$TC")
select_native "$TC"
case "$THREADS" in ''|*[!0-9]*) NAT_WHY="bad --threads"; emit 2 ;; esac
read -r -a MODS <<< "$MOD"   # one or more root modules (whitespace-separated), as lean4export takes them
TARGETS=()
if [ $TFNL = 1 ]; then
  while IFS= read -r t || [ -n "$t" ]; do [ -n "$t" ] && TARGETS+=("$t"); done < "$TF"
else
  read -r -d '' -a TARGETS < "$TF"   # all whitespace-separated names (any number of lines)
  # a name containing whitespace («a b») cannot be passed this way: it would be split into several targets -> decline
  for t in "${TARGETS[@]}"; do
    o=$(printf '%s' "$t" | LC_ALL=C grep -o '«' | wc -l); c=$(printf '%s' "$t" | LC_ALL=C grep -o '»' | wc -l)
    [ "$o" = "$c" ] || { NAT_WHY="target name split at whitespace ('$t'); use --targets-nl"; emit 2; }
  done
fi
[ ${#TARGETS[@]} -gt 0 ] || { NAT_WHY="empty targets file"; emit 2; }
OUTDIR=$(dirname "$OUT"); mkdir -p "$OUTDIR" || emit 2
rm -f "$OUT"
PART=$(mktemp "$OUTDIR/.export.partial.XXXXXX") || { NAT_WHY="cannot create a private output file"; emit 2; }
LOGBASE=${JSON:-$OUT}; OFF_BAD=0

SBX=("$BWRAP" --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --dir /tmp/home --tmpfs /run
     --tmpfs /var)
# the exporters read UNTRUSTED .olean files (a crafted .olean can corrupt the reader): every other
# top-level directory except the system ones is hidden too (/scratch, /data, ...: service state dirs, sockets, FIFOs,
# other runs' files); the exporter binaries, the toolchain, the project and the dependency packages are bound back
SBXRO=()   # the masks are remounted read-only after the last bind (only visibility changes, writes fail as before)
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
# --ro DIR (r2, review M3): only a plain absolute directory (no control character, no empty/'.'/'..' component, no symlink
# component: realpath = DIR), below a top-level directory (never '/' or a top-level dir itself), owned by this user (the
# service's own tree); anything else -> no export (fail closed). Bound read-only at its own path, before the masks are
# remounted read-only.
for x in ${RO[@]+"${RO[@]}"}; do
  case "$x" in *[[:cntrl:]]*) NAT_WHY="bad --ro"; emit 2 ;; esac
  case "$x" in /?*/?*) ;; *) NAT_WHY="--ro $x: not below a top-level directory"; emit 2 ;; esac
  case "$x/" in */../*|*/./*|*//*) NAT_WHY="--ro $x: not a plain path"; emit 2 ;; esac
  [ -d "$x" ] && [ "$(realpath -e -- "$x")" = "$x" ] && [ "$(stat -c %u -- "$x")" = "$(id -u)" ] \
    || { NAT_WHY="--ro $x: not a plain directory of this user"; emit 2; }
  SBX+=(--ro-bind "$x" "$x")
done
SBX+=(--setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP"
      --setenv LEAN_ABORT_ON_PANIC 1)

run_official() {  # $1 = output file
  local t; t=$(date +%s.%N)
  local osha=$OFFSHA   # the official exporter of the selected entry's release (select_native)
  # D22: only the exporter of the toolchain's own release may stand in for the official flow
  [ "$(lean_version_of "$TC")" = "$NATIVE_LEAN" ] || { echo "export: no official exporter pinned for this toolchain's release" >&2; OFF_RC=null; OFF_BAD=1; return 2; }
  [ "$(sha256sum "$OFFX" | cut -d' ' -f1)" = "$osha" ] || { echo "export: official exporter sha256 mismatch" >&2; OFF_RC=null; OFF_BAD=1; return 2; }
  "${SBX[@]}" --ro-bind "$OFFX" "$OFFX" ${SBXRO[@]+"${SBXRO[@]}"} --unshare-all --die-with-parent --new-session --chdir "$PROJ" -- \
      "$OFFX" "${MODS[@]}" -- "${TARGETS[@]}" > "$1" 2>> "$LOGBASE.official.log"
  OFF_RC=$?
  OFF_SEC=$(echo "$(date +%s.%N) - $t" | bc)
  return $OFF_RC
}

# ---- native attempt
if ! preflight "$TC" 2> "$PART.pf"; then
  NAT_WHY="preflight: $(tail -1 "$PART.pf")"; rm -f "$PART.pf"
else
  rm -f "$PART.pf"
  # sizing hint only (output-independent): projects with > 100k modules start the expr table at 2^31 keys
  NM=0
  IFS=: read -r -a LPD <<< "$LP"
  for d in "${LPD[@]}"; do
    [ -d "$d" ] && [ "$d" != "$TC/lib/lean" ] && NM=$((NM + $(find "$d" -name '*.olean' 2>/dev/null | wc -l)))
  done
  EXTRA=(--setenv LEAN4EXPORT_VERBOSE 1)
  [ "$THREADS" -gt 0 ] && EXTRA+=(--setenv LEAN4EXPORT_THREADS "$THREADS")
  [ "$NM" -gt 100000 ] && EXTRA+=(--setenv LEAN4EXPORT_EXPR_ESTIMATE_LOG2 31)
  t=$(date +%s.%N)
  "${SBX[@]}" "${EXTRA[@]}" --ro-bind "$NATIVE" "$NATIVE" ${SBXRO[@]+"${SBXRO[@]}"} --unshare-all --die-with-parent --new-session --chdir "$PROJ" -- \
      "$NATIVE" "${MODS[@]}" -- "${TARGETS[@]}" > "$PART" 2> "$PART.err" &
  NPID=$!
  # S07 (early return): the native child logs 'done: names ...' right after OSink::finish() = every output chunk is in
  # the file and the file is trimmed to its exact length; what follows is only its page teardown and exit (~10 s on RH
  # for ~260 GB of mappings). Do not wait for that: kill the sandbox (the export bytes are in the page cache and stay
  # there) and go on; the independent closure guard below still validates the file. Any exit before that line is
  # handled exactly as before (exit code of the native exporter).
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
    # independent closure guard (catches silent truncation / missing content, as observed with >256 exporter threads): sequential ids,
    # every reference defined, every referenced constant and every target declared; anything else -> decline
    printf '%s\n' "${TARGETS[@]}" > "$PART.tg"
    t=$(date +%s.%N)
    if env -i PATH=/usr/bin:/bin "$CLOSURE" "$PART" "$PART.tg" "$([ "$THREADS" -gt 0 ] && echo "$THREADS" || nproc)" > "$PART.cc" 2>&1; then
      MODE=native
    else
      NAT_RC=4
      NAT_WHY="closure guard: $(head -c 300 "$PART.cc")"
    fi
    CC_SEC=$(echo "$(date +%s.%N) - $t" | bc)
    cat "$PART.cc" >> "$PART.err"; cp "$PART.err" "$LOGBASE.native.log" 2>/dev/null
    rm -f "$PART.tg" "$PART.cc"
  fi
  if [ "$MODE" = native ]; then
    :
  else
    [ -n "$NAT_WHY" ] || NAT_WHY=$(grep -E '^lean4export \(native\): ' "$PART.err" | head -1 | sed 's/^lean4export (native): //' | cut -c1-300)
    [ -n "$NAT_WHY" ] || NAT_WHY=$(grep -vE ' wall(,|\])' "$PART.err" | grep -v 'native-only' | head -1 | cut -c1-300)
    [ -n "$NAT_WHY" ] || NAT_WHY="native exit $NAT_RC"
  fi
  rm -f "$PART.err"
fi

if [ "$MODE" = native ]; then
  if [ $VERIFY -eq 1 ]; then
    run_official "$PART.official"
    if [ "$OFF_RC" = 0 ] && cmp -s "$PART" "$PART.official"; then VER=identical
    else VER="DIFFERENT (official exit $OFF_RC)"; rm -f "$PART"; MODE=none; emit 3; fi
    rm -f "$PART.official"
  fi
  chmod 0644 "$PART"; mv -f "$PART" "$OUT" || emit 2
  emit 0
fi
# ---- declined
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
