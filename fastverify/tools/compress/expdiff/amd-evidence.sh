#!/bin/bash
# amd-evidence.sh NEW_EXPORT OUTDIR [ORIG_EXPORT] [TARGETS] -- export-level evidence for a compressed RH candidate on
# any node holding both exports: expdiff diff (--private-modulo --dead-lets, explain) against the honest export +
# expdiff stats of the candidate (closure, global DAG, exclusive nodes, statement closure) + evidence.md. Read-only on
# both exports. ORIG_EXPORT defaults to $RH_REF; TARGETS to log/export-targets.txt next to ORIG_EXPORT (the layout of
# a bin/fastverify OUT directory).
set -u
H=$(cd "$(dirname "$0")" && pwd)
NEW=$1; OUT=$2
ORIG=${3:-${RH_REF:?honest RH export (pass ORIG_EXPORT or set RH_REF)}}
TG=${4:-$(dirname "$ORIG")/log/export-targets.txt}
X=${EXPDIFF:-$H/expdiff}
T=${AMD_THREADS:-$(nproc)}
mkdir -p "$OUT"
python3 -I "$H/evidence.py" --expdiff "$X" --orig "$ORIG" --new "$NEW" --targets "$TG" --out "$OUT" --threads "$T" \
  --dead-lets > "$OUT/evidence.log" 2>&1 || echo "evidence.py failed (see $OUT/evidence.log)"
"$X" stats -j "$T" --targets "$TG" --top 20 "$NEW" > "$OUT/new.stats.out" 2>&1
grep -E "^(stats\.closure_decls|global_dag|exclusive_nodes|statement_closure\s|project_thm|identical_content)" "$OUT/new.stats.out"
cat "$OUT/evidence.md" 2>/dev/null
