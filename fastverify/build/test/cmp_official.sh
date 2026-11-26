#!/bin/bash
# build/test/cmp_official.sh PROJECT_SRC WORK PACKAGES_WS [TC]
# Builds PROJECT_SRC twice AT THE SAME PATH (WORK/proj): (1) build/official-build.sh = sandboxed official `lake build`,
# (2) build/build.sh = the fast build; then compares exit codes and EVERY build artifact byte for byte
# (.olean/.olean.server/.olean.private/.ilean/.ir/.ir.sig/.c and setup.json; Lake's own .trace/.hash/.log bookkeeping
# is excluded - the fast build does not write it). Prints "CMP: SAME|DIFFERENT|DECLINED ..."; exit 0 iff SAME (or the
# fast build DECLINED and official ran), 1 otherwise. FASTARGS="--preset B2" etc. are passed to build.sh.
set -u
D=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)
SRC=$(readlink -f "$1"); W=$2; WS=$3; TC=${4:-${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}}
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
cp -a "$SRC" "$W/proj"; rm -rf "$W/proj/.lake"
"$D/build/official-build.sh" "$W/proj" "$WS" "$TC" --log "$W/log-off" --timeout "${TIMEOUT:-1800}" > "$W/off.json" 2>&1; orc=$?
mv "$W/proj" "$W/official"
cp -a "$SRC" "$W/proj"; rm -rf "$W/proj/.lake"
"$D/build/build.sh" "$W/proj" "$WS" "$TC" --log "$W/log-fast" --threads "${THREADS:-8}" --timeout "${TIMEOUT:-1800}" ${FASTARGS:-} > "$W/fast.json" 2>&1; frc=$?
echo "official rc=$orc fast rc=$frc"
if [ $frc = 2 ]; then echo "CMP: DECLINED ($(tail -1 "$W/fast.json" | cut -c1-300))"; exit 0; fi
if [ $orc != $frc ]; then echo "CMP: DIFFERENT (exit codes)"; exit 1; fi
list() { (cd "$1" && find .lake/build -type f \( -name '*.olean' -o -name '*.olean.server' -o -name '*.olean.private' \
          -o -name '*.ilean' -o -name '*.ir' -o -name '*.ir.sig' -o -name '*.c' -o -name '*.setup.json' \) | sort); }
diff <(list "$W/official") <(list "$W/proj") > "$W/filelist.diff" || { echo "CMP: DIFFERENT (file sets, see $W/filelist.diff)"; exit 1; }
n=0; bad=0; eqv=0
# setup.json: the fast build writes importArts = {} for non-module importers of large projects (build/README.md
# "importArts": equivalent by construction + per-run checks); such a file counts as EQUIVALENT iff every other field is
# identical and the fast side's importArts is {} (all other artifacts must be byte-identical).
setup_equiv() { /usr/bin/python3 -I -c 'import json,sys
o=json.load(open(sys.argv[1])); f=json.load(open(sys.argv[2]))
ok = f.get("importArts") == {} and {k:v for k,v in o.items() if k!="importArts"} == {k:v for k,v in f.items() if k!="importArts"}
sys.exit(0 if ok else 1)' "$1" "$2"; }
while read -r f; do n=$((n+1))
  cmp -s "$W/official/$f" "$W/proj/$f" && continue
  case "$f" in *.setup.json) if setup_equiv "$W/official/$f" "$W/proj/$f"; then eqv=$((eqv+1)); continue; fi ;; esac
  bad=$((bad+1)); echo "differs: $f"
done < <(list "$W/proj")
if [ $bad = 0 ]; then
  if [ $eqv = 0 ]; then echo "CMP: SAME ($n artifacts byte-identical)"
  else echo "CMP: SAME ($((n-eqv)) artifacts byte-identical + $eqv setup.json identical except importArts = {} by design)"; fi
  exit 0
else echo "CMP: DIFFERENT ($bad of $n artifacts)"; exit 1; fi
