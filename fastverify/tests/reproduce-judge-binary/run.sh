#!/bin/bash
# tests/reproduce-judge-binary/run.sh [WORKDIR]  (kind: reproducibility of pinned binaries; ~15 s, no Mathlib)
# The judge binary of the sound check must rebuild BYTE-FOR-BYTE from the published sources with the official 4.36 toolchain:
#   ccmp-rebuild     tools/reproduce/rebuild-pchk.sh on check/sound/src in a fresh dir -> bin/ccmp sha256 == PIN ccmp of
#                    check/sound/pins.env (4e82fe00...), and bin/pleanchecker (release kernel libraries) == the provenance's
#                    release-lib hash aefcf5cb... (the pinned pleanchecker is the same objects relinked against the PGO
#                    kernel libraries, reproduced by tools/reproduce/rebuild-pgolibs.sh + relink-pgo.sh: too heavy here)
#   objects-stable   the 4 pleanchecker objects of the rebuild equal the recorded hashes (FastParse eaa8b9de, Main d0ea705c,
#                    Par 85a0b6a6, PersistentRead f7d8b502)
#   check437-rebuild (when check/sound/pins-437.env and its registered official 4.37 toolchain exist; else SKIP) the 4.37
#                    trusted check rebuilds from check/sound/src-437 to EXACTLY the pinned ccmp AND pleanchecker of
#                    pins-437.env (both are plain Lake builds against the release's libraries, so both must match)
# Prints 'PASS|FAIL case detail' rows and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/reproduce-judge-binary.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"; fails=0
row() { echo "$1 $2: $3"; [ "$1" = PASS ] || fails=$((fails+1)); }
TC36=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
PIN=$(awk '$1=="PIN" && $2=="ccmp" {print $3}' "$FV/check/sound/pins.env")
"$FV/tools/reproduce/rebuild-pchk.sh" "$FV/check/sound/src" "$W/pchk" "$TC36" > "$W/rebuild.log" 2>&1 || { row FAIL ccmp-rebuild "rebuild failed: $(tail -2 "$W/rebuild.log" | tr '\n' ' ')"; echo "RESULT FAIL"; exit 1; }
C=$(grep -E ' bin/ccmp$' "$W/pchk/SHA256SUMS.all" | cut -d' ' -f1); P=$(grep -E ' bin/pleanchecker$' "$W/pchk/SHA256SUMS.all" | cut -d' ' -f1)
[ "$C" = "$PIN" ] && row PASS ccmp-rebuild "ccmp ${C:0:16} == pin" || row FAIL ccmp-rebuild "ccmp $C != pin $PIN"
[ "$P" = aefcf5cb1a5e43e8dcbb005256da0973984597c8895b34cc5d506560982101e6 ] && row PASS pleanchecker-release-libs "aefcf5cb... as recorded" || row FAIL pleanchecker-release-libs "$P"
ok=1; for pair in FastParse:eaa8b9defa9bfd24 Main:d0ea705cf18056de Par:85a0b6a629bb35fc PersistentRead:f7d8b502859f9717; do f=${pair%%:*}; h=${pair##*:}; g=$(grep -E "/$f\.c\.o\.export$" "$W/pchk/SHA256SUMS.all" | cut -c1-16); [ "$g" = "$h" ] || { ok=0; echo "  $f: $g != $h"; }; done
[ $ok = 1 ] && row PASS objects-stable "4 pleanchecker objects as recorded" || row FAIL objects-stable "object hash drift"
# ---- the 4.37.0-rc1 trusted check, if published here ----
P437=$FV/check/sound/pins-437.env
if [ -f "$P437" ] && [ -d "$FV/check/sound/src-437" ]; then
  TCV=$(sed -n 's/^TC_VERSION=//p' "$P437" | head -1); TC37=$(sed -n 's/^TC36=//p' "$P437" | head -1)
  if [ "$TC37" = @components ]; then
    TC37=$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); print(c["lean_toolchains"][sys.argv[2]]["prefix"])' "$FV/config/components.json" "$TCV" 2>/dev/null || true)
  fi
  if [ -n "$TC37" ] && [ -d "$TC37" ] && python3 -I "$FV/lib/toolchain.py" verify "$TC37" "$TCV" > /dev/null 2>&1; then
    PC=$(awk '$1=="PIN" && $2=="ccmp" {print $3}' "$P437"); PP=$(awk '$1=="PIN" && $2=="pleanchecker" {print $3}' "$P437")
    if "$FV/tools/reproduce/rebuild-pchk.sh" "$FV/check/sound/src-437" "$W/pchk437" "$TC37" > "$W/rebuild437.log" 2>&1; then
      C=$(grep -E ' bin/ccmp$' "$W/pchk437/SHA256SUMS.all" | cut -d' ' -f1); P=$(grep -E ' bin/pleanchecker$' "$W/pchk437/SHA256SUMS.all" | cut -d' ' -f1)
      if [ "$C" = "$PC" ] && [ "$P" = "$PP" ]; then row PASS check437-rebuild "ccmp ${C:0:16} and pleanchecker ${P:0:16} == pins-437.env ($TCV)"
      else row FAIL check437-rebuild "ccmp $C vs pin $PC; pleanchecker $P vs pin $PP"; fi
    else row FAIL check437-rebuild "rebuild failed: $(tail -2 "$W/rebuild437.log" | tr '\n' ' ')"; fi
  else echo "SKIP check437-rebuild: no verified official $TCV toolchain here ($TC37)"; fi
else echo "SKIP check437-rebuild: no check/sound/pins-437.env + src-437 in this package"; fi
[ $fails = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL ($fails)"
