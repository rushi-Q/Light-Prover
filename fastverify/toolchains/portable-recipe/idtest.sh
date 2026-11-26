#!/bin/bash
# idtest.sh FV OUT PROJ CHALLENGE PACKAGES THREADS TREE_A TREE_B [extra bin/fastverify args]
#   A/B identity test of two build toolchains (pinned names under /scratch/fastverify-next/tc, manifests in FV/toolchains/unofficial):
#   the SAME --preset sound run (all B3 items incl. zygote/zygote-prefix; only toolchain-T1 differs), sequentially, then
#   compare every built .olean/.ilean byte for byte (both arms run in the SAME directory OUT/run: some modules embed source paths), the export sha256, the verdict, and the zygote/T1 records.
set -u
FV=$1 OUT=$2 PROJ=$3 CH=$4 WS=$5 T=$6 A=$7 B=$8; shift 8
ITEMS="skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,merge,check-tail"
mkdir -p "$OUT"; : > "$OUT/summary.txt"
for n in "$A" "$B"; do
  o=$OUT/run; rm -rf "$o" "$OUT/run-$n"   # same absolute path for both arms (paths can end up in .olean files)
  t0=$(date +%s)
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$PROJ" "$CH" "$o" --preset sound \
     --unsafe "toolchain-T1=$n,$ITEMS" --threads "$T" --packages "$WS" --keep-work "$@" > "$OUT/run-$n.log" 2>&1
  echo "$n rc=$? wall=$(( $(date +%s) - t0 ))s" | tee -a "$OUT/summary.txt"
  (cd "$o/work" 2>/dev/null && find . -path '*/.lake/build/*' \( -name '*.olean' -o -name '*.ilean' \) -type f | sort | xargs -r sha256sum) > "$OUT/oleans-$n.sha256"
  python3 -I - "$o/result.json" "$n" >> "$OUT/summary.txt" <<'PY'
import json, sys
r = json.load(open(sys.argv[1])); e = r.get('export') or {}; b = r.get('build') or {}
print(f"  {sys.argv[2]}: verdict={r.get('verdict')} basis={str(r.get('verdict_basis'))[:80]} export={e.get('sha256')} build={b.get('mode')}/{b.get('option')} unsafe={b.get('unsafe') or (b.get('stage') or {}).get('unsafe')} stages={r.get('stage_seconds')}")
PY
  grep -h -o '"event": "zygote[a-z-]*"[^}]*' "$o"/log/build-fast/sched.out 2>/dev/null | head -4 | sed "s/^/  $n /" >> "$OUT/summary.txt"
  mv "$o" "$OUT/run-$n"
done
na=$(wc -l < "$OUT/oleans-$A.sha256"); nb=$(wc -l < "$OUT/oleans-$B.sha256")
if cmp -s "$OUT/oleans-$A.sha256" "$OUT/oleans-$B.sha256"; then echo "OLEANS IDENTICAL: $na files" | tee -a "$OUT/summary.txt"
else echo "OLEANS DIFFER: $na vs $nb files, $(diff "$OUT/oleans-$A.sha256" "$OUT/oleans-$B.sha256" | grep -c '^<') differing lines" | tee -a "$OUT/summary.txt"; fi
cat "$OUT/summary.txt"
