#!/bin/bash
# e1_measure.sh OUTDIR TAG PROJ_TREE MODULE TARGETS_FILE THREADS  - the native exporter E1 (export/export.sh) alone on an
# existing build tree, inside a cgrun.sh scope measured by cgrun-inner.sh (peak memory of the export stage).
# env: TNL=1 = TARGETS_FILE has one name per line; BINDS=binds.tsv and LP_OVERRIDE=LEAN_PATH for trees whose dependency
# packages are bind-mounted from the trusted workspace (fastverify's own build trees: take both from the run's log/export.log).
set -u
OUT=$1; TAG=$2; P=$3; MOD=$4; TF=$5; T=$6
FV=${FV:-$LIGHT_LEAN/fastverify}; TC=${TC:-$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1}
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
LP=$P/.lake/build/lib/lean; for d in "$P"/.lake/packages/*/; do [ -d "$d/.lake/build/lib/lean" ] && LP="$LP:$d.lake/build/lib/lean"; done
mkdir -p "$OUT"; rm -f "$OUT/$TAG.export"
"$H/cgrun.sh" --name "e1-$TAG" --json "$OUT/$TAG.cg.json" --timeline "$OUT/$TAG.tl" --ps 2 -- \
  "$FV/export/export.sh" --lean-path "${LP_OVERRIDE:-$LP}" --module "$MOD" $([ -n "${TNL:-}" ] && echo --targets-nl || echo --targets-file) "$TF" --toolchain "$TC" --project "$P" ${BINDS:+--binds "$BINDS"} --out "$OUT/$TAG.export" --threads "$T" --json "$OUT/$TAG.export.json" > "$OUT/$TAG.out" 2>&1
echo "rc=$? size=$(stat -c %s "$OUT/$TAG.export" 2>/dev/null)"; python3 -c "import json; j=json.load(open('$OUT/$TAG.cg.json')); print('wall', round(j['wall_s'],1), 'peak GB', round(j['memory_peak']/2**30,1), 'anon', round((j['sampled_max']['anon'] or 0)/2**30,1), 'top', [(p['comm'], round(p['max_rss']/2**30,1)) for p in j['top_procs'][:3]])"
rm -f "$OUT/$TAG.export"
