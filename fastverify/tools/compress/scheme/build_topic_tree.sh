#!/bin/bash
# build_topic_tree.sh C1DIR WORKDIR -- Stage-3 LAYOUT.samedir_topic builder (extends build_tree.sh).
# Enforces 100% intra-directory topic purity (--same-dir, 0 cross-dir merges), <= MAX_COST (default 30.0s) merged-module
# build-cost cap, optional intra-directory sibling leaf coalescing (TOPIC_MODE=none|g1|g2, MAX_LINES=40|60|80),
# C++ dfsverify import-order identity at every normalization step, and post-coalescing second-pass --same-dir chainmerge.
set -euo pipefail

C=$1
R=$2
rm -rf "$R"
mkdir -p "$R"

FV=$(cd "$(dirname "$0")/../../.." && pwd)
N=${NORMDIR:-$FV/tools/compress/normalize}
APPLY=${APPLY:-$FV/tools/compress/dedup/apply_edits.py}
TOOLS=${TOOLS:-$(cd "$(dirname "$0")" && pwd)}
RH=${RH_BASE:-${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}}
WSP=${WSP:-${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}/.lake/packages}
TCS=${TCS:-$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/src/lean}
COSTS=${COSTS:-$FV/build/hints/rh-build-costs.json.gz}
MAX_COST=${MAX_COST:-30.0}
TOPIC_MODE=${TOPIC_MODE:-g1}     # none | g1 (--same-importers, 0 caller env drift) | g2 (side-effect-free + disjoint short names)
MAX_LINES=${MAX_LINES:-60}
MAX_GROUP_LINES=${MAX_GROUP_LINES:-300}

ts() { date +%s.%N; }
exec > >(tee "$C/pipeline.log") 2>&1
echo "== LAYOUT.samedir_topic pipeline $(date -u +%FT%TZ) $(hostname) TOPIC_MODE=$TOPIC_MODE MAX_LINES=$MAX_LINES MAX_COST=$MAX_COST"

args=()
prio=()
while IFS=$'\t' read -r owner f; do
  [ -n "$owner" ] || continue
  args+=("$C/$f")
  prio+=("$owner")
  echo "edit list $owner $f $(wc -l < "$C/$f") lines sha256 $(sha256sum < "$C/$f" | cut -c1-16)"
done < "$C/manifest.tsv"
P=$(IFS=,; echo "${prio[*]}")

mkdir -p "$R/rh"
(cd "$RH" && tar --exclude=.lake --exclude=.git -cf - .) | (cd "$R/rh" && tar xf -)

t0=$(ts)
python3 -I "$APPLY" "$R/rh" "$R/t0" "${args[@]}" --priority "$P" > "$R/apply.out" 2>&1
echo "apply_edits rc=$? $(echo "$(ts) - $t0" | bc) s"
tail -3 "$R/apply.out" | cut -c1-3000
[ -f "$R/t0/.apply-conflicts.tsv" ] && echo "conflicts: $(wc -l < "$R/t0/.apply-conflicts.tsv")" && awk -F'\t' '{print $5}' "$R/t0/.apply-conflicts.tsv" | sort | uniq -c | head

python3 -I "$FV/tools/compress/prune/fixlake.py" "$R/t0"
t0=$(ts)
python3 -I "$N/dropempty.py" "$R/t0" "$R/t0e"
echo "dropempty rc=$? $(echo "$(ts) - $t0" | bc) s"
cp "$R/t0/lake-manifest.json" "$R/t0e/" 2>/dev/null || true
python3 -I "$FV/tools/compress/prune/fixlake.py" "$R/t0e"

DV="$R/dfsverify"
if command -v g++ >/dev/null 2>&1; then
  g++ -O2 -std=c++17 -pthread -o "$DV" "$N/dfsverify/dfsverify.cpp"
else
  echo "ERROR: g++ is required to build dfsverify" >&2; exit 2
fi

t0=$(ts)
python3 -I "$N/normalize.py" "$R/t0e" --packages "$WSP" --toolchain-src "$TCS" --classes "${NORM_CLASSES:-imp,opt,optres}" --edits "$R/norm.tsv" --json "$R/norm.json" --graph-out "$R/g"
echo "normalize rc=$? $(echo "$(ts) - $t0" | bc) s"
"$DV" "$R/g.old.txt" "$R/g.new.txt" "$R/g.roots.txt" 16
rm -f "$R"/g.*.txt
python3 -I "$N/apply_tree.py" "$R/t0e" "$R/t1" "$R/norm.tsv"
cp "$R/t0/lake-manifest.json" "$R/t1/" 2>/dev/null || true

run_samedir_cm() {
  local IN_DIR=$1 OUT_DIR=$2 DENY_OUT=$3
  cat "${CM_DENY:-/dev/null}" > "$DENY_OUT"
  python3 -I "$N/chainmerge.py" "$IN_DIR" "$OUT_DIR" --same-dir --costs "$COSTS" --max-cost "$MAX_COST" --packages "$WSP" --toolchain-src "$TCS" --deny "$DENY_OUT"
  for it in 1 2 3 4 5 6; do
    python3 -I "$TOOLS/cm_deny.py" "$IN_DIR/src" "$OUT_DIR/.chainmerge.tsv" "$R/cm-deny.new"
    [ -s "$R/cm-deny.new" ] || break
    cat "$R/cm-deny.new" >> "$DENY_OUT"
    rm -rf "$OUT_DIR"
    python3 -I "$N/chainmerge.py" "$IN_DIR" "$OUT_DIR" --same-dir --costs "$COSTS" --max-cost "$MAX_COST" --packages "$WSP" --toolchain-src "$TCS" --deny "$DENY_OUT"
  done
  cp "$R/t0/lake-manifest.json" "$OUT_DIR/" 2>/dev/null || true
  python3 -I "$FV/tools/compress/prune/fixlake.py" "$OUT_DIR"
}

run_samedir_cm "$R/t1" "$R/t2_cm1" "$R/cm-deny.txt"
cp "$R/cm-deny.txt" "$C/cm-deny.txt"

python3 -I "$N/normalize.py" "$R/t2_cm1" --packages "$WSP" --toolchain-src "$TCS" --classes "${NORM_CLASSES:-imp,opt,optres}" --edits "$R/norm_cm1.tsv" --json "$R/norm_cm1.json" --graph-out "$R/gcm1"
"$DV" "$R/gcm1.old.txt" "$R/gcm1.new.txt" "$R/gcm1.roots.txt" 16
rm -f "$R"/gcm1.*.txt
python3 -I "$N/apply_tree.py" "$R/t2_cm1" "$R/t2_cm1_n" "$R/norm_cm1.tsv"
cp "$R/t0/lake-manifest.json" "$R/t2_cm1_n/" 2>/dev/null || true

if [ "$TOPIC_MODE" = "none" ]; then
  mv "$R/t2_cm1_n" "$R/t2"
  cp "$R/t2_cm1/.chainmerge.tsv" "$R/t2/.chainmerge.tsv" 2>/dev/null || true
else
  TC_FLAGS=(--max-lines "$MAX_LINES" --max-group-lines "$MAX_GROUP_LINES" --costs "$COSTS" --max-cost "$MAX_COST" --packages "$WSP" --toolchain-src "$TCS")
  [ "$TOPIC_MODE" = "g1" ] && TC_FLAGS+=(--same-importers)
  python3 -I "$N/topic_coalesce.py" "$R/t2_cm1_n" "$R/t2_tc" "${TC_FLAGS[@]}"
  cp "$R/t0/lake-manifest.json" "$R/t2_tc/" 2>/dev/null || true
  python3 -I "$FV/tools/compress/prune/fixlake.py" "$R/t2_tc"

  python3 -I "$N/normalize.py" "$R/t2_tc" --packages "$WSP" --toolchain-src "$TCS" --classes "${NORM_CLASSES:-imp,opt,optres}" --edits "$R/norm_tc.tsv" --json "$R/norm_tc.json" --graph-out "$R/gtc"
  "$DV" "$R/gtc.old.txt" "$R/gtc.new.txt" "$R/gtc.roots.txt" 16
  rm -f "$R"/gtc.*.txt
  python3 -I "$N/apply_tree.py" "$R/t2_tc" "$R/t2_tc_n" "$R/norm_tc.tsv"
  cp "$R/t0/lake-manifest.json" "$R/t2_tc_n/" 2>/dev/null || true

  run_samedir_cm "$R/t2_tc_n" "$R/t2_cm2" "$R/cm-deny2.txt"
  python3 -I "$N/normalize.py" "$R/t2_cm2" --packages "$WSP" --toolchain-src "$TCS" --classes "${NORM_CLASSES:-imp,opt,optres}" --edits "$R/norm_cm2.tsv" --json "$R/norm_cm2.json" --graph-out "$R/gcm2"
  "$DV" "$R/gcm2.old.txt" "$R/gcm2.new.txt" "$R/gcm2.roots.txt" 16
  rm -f "$R"/gcm2.*.txt
  python3 -I "$N/apply_tree.py" "$R/t2_cm2" "$R/t2" "$R/norm_cm2.tsv"
  cp "$R/t0/lake-manifest.json" "$R/t2/" 2>/dev/null || true
  python3 -I "$FV/tools/compress/prune/fixlake.py" "$R/t2"
  cat "$R/t2_cm1/.chainmerge.tsv" "$R/t2_tc/.topic_coalesce.tsv" "$R/t2_cm2/.chainmerge.tsv" 2>/dev/null > "$R/t2/.chainmerge.tsv" || true
fi

for t in "$R/rh" "$R/t0" "$R/t0e" "$R/t1" "$R/t2"; do
  echo "TREE $(basename "$t") files=$(find "$t/src" -name '*.lean' | wc -l) lines=$(find "$t/src" -name '*.lean' -print0 | xargs -0 cat | wc -l) bytes=$(find "$t/src" -name '*.lean' -print0 | xargs -0 cat | wc -c)"
done

cp "$R/t0/.apply-summary.json" "$C/apply-summary.json" 2>/dev/null || true
cp "$R/t0/.apply-conflicts.tsv" "$C/apply-conflicts.tsv" 2>/dev/null || true
cp "$R/norm.json" "$C/"
cp "$R/t2/.chainmerge.tsv" "$C/chainmerge.tsv" 2>/dev/null || true
cp "$R/t0e/.dropempty.txt" "$C/dropempty.txt" 2>/dev/null || true

t0=$(ts)
(cd "$R/t2" && tar --exclude=.lake -czf "$C/t2.tar.gz" .)
echo "tar $(echo "$(ts) - $t0" | bc) s $(du -sh "$C/t2.tar.gz")"
sha256sum "$C/t2.tar.gz"
echo "== done $(date -u +%FT%TZ)"
