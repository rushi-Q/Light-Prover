#!/bin/bash
# refs_for.sh PROJ OUTDIR [CHUNKS] : olean_meta / olean_refs (ranges + hashes) over every project olean, sandboxed.
# Prefers OLEAN_META_DIR (.lake/build/bin/olean_meta, reading .olean + .olean.server + .olean.private
# for module-system projects), falling back to OLEAN_REFS_DIR (.lake/build/bin/olean_refs).
set -e
P=$1; O=$2; N=${3:-16}
if [ -n "${OLEAN_META_DIR:-}" ] && [ -x "$OLEAN_META_DIR/.lake/build/bin/olean_meta" ]; then
  T=$OLEAN_META_DIR
  BIN="$T/.lake/build/bin/olean_meta"
elif [ -n "${OLEAN_META_DIR:-}" ] && [ -x "$OLEAN_META_DIR/.lake/build/bin/olean_refs" ]; then
  T=$OLEAN_META_DIR
  BIN="$T/.lake/build/bin/olean_refs"
else
  T=${OLEAN_REFS_DIR:?set OLEAN_META_DIR to a built olean_meta reader (or OLEAN_REFS_DIR to a built olean_refs)}
  BIN="$T/.lake/build/bin/olean_refs"
fi
mkdir -p "$O/chunks" "$O/out"
L=$P/.lake/build/lib/lean
(cd "$L" && find . -name '*.olean' | sed 's#^\./##; s#\.olean$##' | while read r; do printf '%s\t%s\n' "$(echo "$r" | tr / .)" "$L/$r.olean"; done) > "$O/all.list"
rm -f "$O/chunks/c"* ; split -n "l/$N" -d -a 3 "$O/all.list" "$O/chunks/c"
pids=""
for f in "$O/chunks/c"*; do
  b=$(basename "$f")
  "$T/sandbox_ro.sh" "$O/out" "$P:$O/chunks" -- env OLEAN_REFS_RANGES=1 OLEAN_REFS_HASH=1 "$BIN" "$O/out/$b.tsv" "$f" 2> "$O/out/$b.err" &
  pids="$pids $!"
done
rc=0
for pid in $pids; do
  if ! wait "$pid"; then rc=1; fi
done
if [ "$rc" -ne 0 ]; then
  echo "ERROR: refs_for.sh chunk worker failed; stderr sample:" >&2
  head -n 20 "$O/out/"*.err >&2 || true
  exit 1
fi
wc -l "$O/all.list"
