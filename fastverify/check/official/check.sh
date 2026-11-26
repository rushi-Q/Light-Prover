#!/bin/bash
# check/official/check.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--timeout SEC] [--workdir DIR]
# check/official/check.sh --preflight
#
# The OFFICIAL verdict: the UNMODIFIED `lake comparator` OF THE CHALLENGE'S RELEASE, run from
# the two exports. The release is the one named in the challenge export's meta line (read with check/xversion/xvcheck.py's
# strict meta parser):
#   * Lean 4.36.0                -> the 4.36.0 release's lake comparator (config/components.json "comparator", pinned by
#                                   sha256 file by file), as before;
#   * a release >= 4.37 (4.37.0-rc1, ...) -> THAT release's own lake comparator: the toolchain registered for it in
#                                   config/components.json lean_toolchains (same githash), its listed sha256s, its whole
#                                   tree verified by lib/toolchain.py against toolchains/<id>.json, `lean --version`
#                                   exact; a release >= 4.37 without such a toolchain -> ERROR (no verdict), never 4.36;
#   * an earlier release (4.26 .. 4.36.0-rcN, which ship no comparator of their own) -> the 4.36.0 comparator ONLY after
#                                   the cross-version gate (check/xversion/xvcheck.py + releases.json) admits the release
#                                   and its extra rules hold (gate REJECTED -> REJECTED, anything else -> ERROR);
#   * no / malformed meta line, unknown release -> ERROR (exit 2).
# --preflight checks the 4.36.0 comparator (the default); another release's comparator is preflighted when it is selected.
# The comparator runs as:
#   lake comparator --config COMPARATOR_JSON --challenge-from-export CHALLENGE_EXPORT --solution-from-export EXPORT
# in a fresh empty working directory under `env -i` (PATH = the judging release's toolchain bin + /usr/bin:/bin, HOME and TMPDIR =
# private dirs). With both --*-from-export flags the comparator does not load any workspace; it compares the statements
# (compareAt + checkAxioms) and runs the configured external kernels and the Lean kernel (leanchecker), each inside its own
# bwrap sandbox, exactly as upstream. --threads is accepted for interface compatibility and ignored (the official tool has
# no thread option; nanoda gets num_threads=4 from Lake's generated config).
# Exit: 0 = ACCEPTED, 1 = REJECTED, 2 = could not run (preflight failure, unreadable inputs, timeout, signal).
set -u
D=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)
PY=/usr/bin/python3
cfg() { "$PY" -I -c 'import json,sys; c=json.load(open(sys.argv[1])); k=sys.argv[2].split("/",1); v=c[k[0]]
if len(k)>1: v=v[k[1]]
print(json.dumps(v) if isinstance(v,(dict,list)) else v)' "$D/config/components.json" "$1"; }
T36=$(cfg comparator/prefix) || { echo "official: cannot read config" >&2; exit 2; }
WANT_VER=$(cfg comparator/lean_version)

preflight() {
  local bad=0
  while read -r rel sum; do
    local have; have=$(sha256sum "$T36/$rel" 2>/dev/null | cut -d' ' -f1)
    if [ "$have" != "$sum" ]; then echo "official: preflight: $T36/$rel sha256 mismatch (have '${have:-missing}')" >&2; bad=1; fi
  done < <("$PY" -I -c 'import json,sys; [print(k,v) for k,v in json.load(open(sys.argv[1]))["comparator"]["sha256"].items()]' "$D/config/components.json")
  local v; v=$(env -i PATH=/usr/bin:/bin "$T36/bin/lean" --version 2>&1)
  [ "$v" = "$WANT_VER" ] || { echo "official: preflight: lean --version = '$v', expected '$WANT_VER'" >&2; bad=1; }
  env -i PATH=/usr/bin:/bin "$T36/bin/lake" --version > /dev/null 2>&1 || { echo "official: preflight: lake does not start" >&2; bad=1; }
  command -v bwrap > /dev/null || { echo "official: preflight: bwrap not on PATH (the comparator sandboxes its kernels)" >&2; bad=1; }
  command -v git > /dev/null || { echo "official: preflight: git not on PATH (lake comparator requires it)" >&2; bad=1; }
  return $bad
}
if [ "${1:-}" = --preflight ] && [ "${2:-}" != --release ]; then preflight; exit $?; fi

# the comparator of another registered release (>= 4.37): listed sha256s + whole-tree manifest + exact version
preflight_release() {  # preflight_release PREFIX ID WANT_VERSION
  local P=$1 ID=$2 WV=$3 bad=0
  while read -r rel sum; do
    local have; have=$(sha256sum "$P/$rel" 2>/dev/null | cut -d' ' -f1)
    if [ "$have" != "$sum" ]; then echo "official: preflight $ID: $P/$rel sha256 mismatch (have '${have:-missing}')" >&2; bad=1; fi
  done < <("$PY" -I -c 'import json,sys; [print(k,v) for k,v in json.load(open(sys.argv[1]))["lean_toolchains"][sys.argv[2]]["sha256"].items()]' "$D/config/components.json" "$ID")
  "$PY" -I "$D/lib/toolchain.py" verify "$P" "$ID" > /dev/null 2>&1 || { echo "official: preflight $ID: toolchain tree does not verify (lib/toolchain.py verify)" >&2; bad=1; }
  local v; v=$(env -i PATH=/usr/bin:/bin "$P/bin/lean" --version 2>&1)
  [ "$v" = "$WV" ] || { echo "official: preflight $ID: lean --version = '$v', expected '$WV'" >&2; bad=1; }
  env -i PATH=/usr/bin:/bin "$P/bin/lake" --version > /dev/null 2>&1 || { echo "official: preflight $ID: lake does not start" >&2; bad=1; }
  command -v bwrap > /dev/null || { echo "official: preflight: bwrap not on PATH" >&2; bad=1; }
  command -v git > /dev/null || { echo "official: preflight: git not on PATH" >&2; bad=1; }
  return $bad
}

# `--preflight --release VER`: preflight the comparator C0 will run for a challenge of release VER
# (>= 4.37 with its own registered toolchain: that release's comparator, no 4.36.0 installation needed; else the default)
if [ "${1:-}" = --preflight ] && [ "${2:-}" = --release ]; then
  RV=${3:-}
  # a release spelling as in releases.json (X.Y.Z or X.Y.Z-rcN), nothing else
  [[ "$RV" =~ ^[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]] || { echo "official: --preflight --release: bad release '$RV'" >&2; exit 2; }
  RID="leanprover/lean4:v$RV"
  RP=$("$PY" -I -c 'import json,sys; t=(json.load(open(sys.argv[1])).get("lean_toolchains") or {}).get(sys.argv[2]) or {}; print(t.get("prefix",""))' "$D/config/components.json" "$RID" 2>/dev/null)
  RWV=$("$PY" -I -c 'import json,sys; t=(json.load(open(sys.argv[1])).get("lean_toolchains") or {}).get(sys.argv[2]) or {}; print(t.get("lean_version",""))' "$D/config/components.json" "$RID" 2>/dev/null)
  if [ -n "$RP" ] && [ -n "$RWV" ] && [ "$("$PY" -I -c 'import sys; v=tuple(int(x) for x in sys.argv[1].split("-")[0].split(".")); print(1 if v >= (4,37,0) else 0)' "$RV")" = 1 ]; then
    preflight_release "$RP" "$RID" "$RWV"; exit $?
  fi
  if [ "$("$PY" -I -c 'import sys; v=tuple(int(x) for x in sys.argv[1].split("-")[0].split(".")); print(1 if v >= (4,37,0) else 0)' "$RV" 2>/dev/null)" = 1 ]; then
    # as the run itself: a 4.37+ release without its registered toolchain is refused, never the 4.36 one
    echo "official: preflight: no registered toolchain for Lean $RV (config/components.json lean_toolchains)" >&2; exit 2
  fi
  preflight; exit $?
fi
[ $# -ge 3 ] || { sed -n 2,3p "$0" >&2; exit 2; }
EXPORT=$1; CEXPORT=$2; CFG=$3; shift 3
JSON=; TIMEOUT=0; WD=
while [ $# -gt 0 ]; do
  case "$1" in
    --threads|--json|--timeout|--workdir)   # a value option without its value: usage error (no loop)
      [ $# -ge 2 ] || { echo "official: $1 needs a value" >&2; exit 2; } ;;
  esac
  case "$1" in
    --threads) shift 2 ;;
    --json) JSON=$2; shift 2 ;;
    --timeout) TIMEOUT=$2; shift 2 ;;
    --workdir) WD=$2; shift 2 ;;
    *) echo "official: unknown argument $1" >&2; exit 2 ;;
  esac
done
TOOL="lake comparator (Lean 4.36.0, unmodified)"; REL=; RELID=
emit() { # verdict exit detail seconds
  local line
  line=$("$PY" -I -c 'import json,sys; print(json.dumps({"checker":"official","tool":sys.argv[5],"challenge_release":sys.argv[6] or None,"comparator_toolchain":sys.argv[7] or None,"verdict":sys.argv[1],"exit":int(sys.argv[2]),"detail":sys.argv[3],"seconds":float(sys.argv[4])}))' "$1" "$2" "$3" "$4" "$TOOL" "$REL" "$RELID")
  # the requested --json file is part of the result: if it cannot be written the run is an ERROR
  # (exit 2, an ERROR line on stdout), never the verdict's exit status with the artifact silently missing
  if [ -n "$JSON" ] && ! { echo "$line" > "$JSON"; } 2>/dev/null; then
    echo "official: cannot write the --json file $JSON" >&2
    line=$("$PY" -I -c 'import json,sys; print(json.dumps({"checker":"official","tool":sys.argv[3],"challenge_release":sys.argv[4] or None,"comparator_toolchain":sys.argv[5] or None,"verdict":"ERROR","exit":2,"detail":"cannot write the requested --json file %s (the comparator said %s): no verdict" % (sys.argv[1], sys.argv[2]),"seconds":0.0}))' "$JSON" "$1" "$TOOL" "$REL" "$RELID")
    echo "$line"
    [ "${CLEAN:-0}" = 1 ] && [ -n "${WD:-}" ] && rm -rf "$WD"
    exit 2
  fi
  echo "$line"
}
T0=$(date +%s.%N)
for f in "$EXPORT" "$CEXPORT" "$CFG"; do
  [ -f "$f" ] && [ -r "$f" ] || { emit ERROR 2 "input is not a readable regular file: $f" 0; exit 2; }
done
EXPORT=$(readlink -f "$EXPORT"); CEXPORT=$(readlink -f "$CEXPORT"); CFG=$(readlink -f "$CFG")
# ---- which release's comparator judges: the release that exported the challenge ----
SEL=$("$PY" -I - "$D" "$CEXPORT" <<'PY' 2>&1
import json, re, sys
d, chx = sys.argv[1], sys.argv[2]
sys.path.insert(0, d + "/check/xversion")
try:
    import xvcheck
except Exception as e:  # noqa: BLE001
    print("ERR cannot load the strict meta parser (check/xversion/xvcheck.py): %s" % e); sys.exit()
try:
    with open(chx, "rb") as f:
        first = f.readline(1 << 20)
    ver, gh, _fmt = xvcheck.parse_meta_line(first.rstrip(b"\n"))
except Exception as e:  # noqa: BLE001
    print("ERR challenge export has no valid meta line naming its release: %s" % str(e)[:200]); sys.exit()
if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?", ver or "") or not re.fullmatch(r"[0-9a-f]{40}", gh or ""):
    print("ERR challenge export meta names an unrecognised release %r / githash %r" % (ver, gh)); sys.exit()
c = json.load(open(d + "/config/components.json"))
def commit(lv):
    m = re.search(r"commit ([0-9a-f]{40})", lv or "")
    return m.group(1) if m else None
comp = c.get("comparator") or {}
base = tuple(int(x) for x in ver.split("-")[0].split("."))
if ver == "4.36.0":
    if commit(comp.get("lean_version")) != gh:
        print("ERR challenge export names Lean 4.36.0 with githash %s, not the pinned 4.36.0 release" % gh); sys.exit()
    print("OWN36 %s %s" % (ver, comp.get("id"))); sys.exit()
if base >= (4, 37, 0):
    tid = "leanprover/lean4:v" + ver
    t = (c.get("lean_toolchains") or {}).get(tid)
    if not t or not t.get("prefix") or not t.get("lean_version") or not t.get("sha256"):
        print("ERR no official comparator registered for Lean %s (config/components.json lean_toolchains %s): this release "
              "cannot be judged officially here" % (ver, tid)); sys.exit()
    if commit(t["lean_version"]) != gh:
        print("ERR challenge export names Lean %s with githash %s, not the registered release (%s)" % (ver, gh, commit(t["lean_version"]))); sys.exit()
    print("OWN %s %s %s" % (ver, tid, t["prefix"])); sys.exit()
print("GATE %s %s" % (ver, gh))
PY
)
case "$SEL" in
  OWN36\ *) REL=$(echo "$SEL" | cut -d' ' -f2); RELID=$(echo "$SEL" | cut -d' ' -f3)
     preflight || { emit ERROR 2 "preflight failed (see stderr)" 0; exit 2; } ;;
  OWN\ *) REL=$(echo "$SEL" | cut -d' ' -f2); RELID=$(echo "$SEL" | cut -d' ' -f3); TP=$(echo "$SEL" | cut -d' ' -f4-)
     WV=$("$PY" -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"][sys.argv[2]]["lean_version"])' "$D/config/components.json" "$RELID")
     TOOL="lake comparator (Lean $REL, unmodified: the challenge release's own)"
     preflight_release "$TP" "$RELID" "$WV" || { emit ERROR 2 "preflight of the Lean $REL comparator failed (see stderr): no verdict" 0; exit 2; }
     T36=$TP ;;
  GATE\ *) REL=$(echo "$SEL" | cut -d' ' -f2); RELID=$(cfg comparator/id)
     preflight || { emit ERROR 2 "preflight failed (see stderr)" 0; exit 2; }
     XJ=$(mktemp "${TMPDIR:-/tmp}/fv-official-xv.XXXXXX.json") || { emit ERROR 2 "cannot create a temp file" 0; exit 2; }
     "$PY" -I "$D/check/xversion/xvcheck.py" "$CEXPORT" "$CFG" --releases "$D/check/xversion/releases.json" --json "$XJ" > /dev/null 2>&1
     XRC=$?
     XV=$("$PY" -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j.get("verdict",""), "|", str(j.get("reason",""))[:300])' "$XJ" 2>/dev/null)
     rm -f "$XJ"
     if [ "$XRC" = 1 ] && [ "${XV%% |*}" = REJECTED ]; then
       TOOL="cross-version gate (check/xversion) for Lean $REL"; emit REJECTED 1 "rule of the challenge's release: ${XV#*| }" 0; exit 1
     fi
     [ "$XRC" = 0 ] && [ "${XV%% |*}" = OK ] || { emit ERROR 2 "Lean $REL has no comparator of its own and the cross-version gate does not admit it (rc=$XRC: ${XV#*| }): no verdict" 0; exit 2; }
     TOOL="lake comparator (Lean 4.36.0, unmodified; challenge exported by Lean $REL, admitted by check/xversion)" ;;
  *) emit ERROR 2 "${SEL#ERR }" 0; exit 2 ;;
esac
if [ -z "$WD" ]; then
  WD=$(mktemp -d "${TMPDIR:-/tmp}/fv-official.XXXXXX") || { emit ERROR 2 "cannot create a private work directory: no verdict" 0; exit 2; }
  CLEAN=1
else
  mkdir -p -- "$WD" 2>/dev/null; CLEAN=0
fi
WD=$(readlink -f -- "$WD")
# a work-directory setup failure (e.g. --workdir naming a regular file) is a host error: ERROR, exit 2,
# never the comparator's judgement (before: mkdir / the log redirection failed, the subshell exited 1 -> REJECTED)
# a private copy of the config: the comparator re-reads it by path
if ! { [ -n "$WD" ] && [ -d "$WD" ] && mkdir -p -- "$WD/cwd" "$WD/home" "$WD/tmp" && cp -- "$CFG" "$WD/comparator.json" \
       && : > "$WD/comparator.log"; } 2>/dev/null; then
  emit ERROR 2 "cannot set up the work directory ${WD:-?} (--workdir must name a writable directory): no verdict" 0; exit 2
fi
TO=(); [ "$TIMEOUT" != 0 ] && TO=(timeout --signal=KILL "$TIMEOUT")
# the upstream comparator's own kernel sandbox binds --tmpfs /run/user (Lake/CLI/Check.lean): on a host
# without /run/user it fails ("bwrap: Can't mkdir /run/user"). Then the unmodified comparator runs inside an outer view that
# only adds an empty /run with /run/user (everything else identical); a sandbox / startup failure is ERROR (below)
OUTER=(); [ -d /run/user ] || OUTER=(/usr/bin/bwrap --dev-bind / / --tmpfs /run --dir /run/user --)
( cd "$WD/cwd" && exec "${OUTER[@]}" "${TO[@]}" env -i PATH="$T36/bin:/usr/bin:/bin" HOME="$WD/home" TMPDIR="$WD/tmp" LANG=C.UTF-8 \
    "$T36/bin/lake" comparator --config "$WD/comparator.json" \
      --challenge-from-export "$CEXPORT" --solution-from-export "$EXPORT" ) > "$WD/comparator.log" 2>&1
rc=$?
T1=$(date +%s.%N); SEC=$(echo "$T1 - $T0" | bc)
# exit 1 with no output at all is not a judgement (a rejection always prints Lake's error lines)
if [ $rc = 1 ] && [ ! -s "$WD/comparator.log" ]; then
  emit ERROR 2 "lake comparator exit 1 without any output: not a judgement, no verdict" "$SEC"; [ $CLEAN = 1 ] && rm -rf "$WD"; exit 2
fi
sed 's/^/official: /' "$WD/comparator.log" | tail -n 30 >&2
LAST=$(grep -v '^\s*$' "$WD/comparator.log" | tail -n 3 | tr '\n' ' ' | cut -c1-400)
# rc 1 is the comparator's judgement only if it is not a tool/host failure: a kernel that could not be started
# ("Error while interacting with ... kernel"), an uncaught exception, or a host resource error -> ERROR, not REJECTED
# "<kernel> exited with 143" (a kernel killed by a signal / timeout: exit 128..255) is a tool failure too
# a sandbox that did not start ("bwrap: ..." at the start of a line: Can't mkdir, namespace errors) is a tool failure
if [ $rc = 1 ] && grep -qE "^(error: )?bwrap: |exited with (code )?(12[4-9]|1[3-9][0-9]|2[0-5][0-9])\b|Error while interacting with|uncaught exception|could not execute external process|No space left on device|Cannot allocate memory|Resource temporarily unavailable|failed to create thread|Too many open files|mmap.*failed|out of memory|Stale file handle|failed to read file '" "$WD/comparator.log"; then
  emit ERROR 2 "comparator tool/host failure (not a judgement): $LAST" "$SEC"; [ $CLEAN = 1 ] && rm -rf "$WD"; exit 2
fi
case $rc in
  0) emit ACCEPTED 0 "$LAST" "$SEC" ;;
  1) emit REJECTED 1 "$LAST" "$SEC" ;;
  *) emit ERROR 2 "lake comparator exit $rc: $LAST" "$SEC"; rc=2 ;;
esac
[ $CLEAN = 1 ] && rm -rf "$WD"
exit $rc
