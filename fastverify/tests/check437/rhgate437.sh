#!/bin/bash
# rhgate437.sh HONEST_EXPORT CHALLENGE_EXPORT COMPARATOR_JSON OUTDIR [THREADS] [PKG]  - the RH-scale soundness check of the 4.37
# trusted check on the 4.37 community RH export: (1) the honest export -> must be ACCEPTED; (2) the four RH mutant
# classes M1-M4 (the published RH mutants) regenerated for THIS export by mk_rh437_specs.py + fvmut
# (M1/M2 theorem value := its own type, M3 fakeAx : False inserted + renumbering, M4 def RiemannZetaZerosOnLine := True and
# theorem riemannZeta_eq_zero_re := True.intro) -> all must be REJECTED. Runs on the host that holds the export (mutants are
# written next to OUTDIR: M3 is a full copy; M1/M2/M4 are reflink copies where the file system allows). Results: OUTDIR/rh437.tsv.
# Every check runs with --pins $PKG/check/sound/pins-437.env (the 4.37 judge).
set -u
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
H=$1; C=$2; CFG=$3; O=$4; T=${5:-$(nproc)}; PKG=${6:-$(cd "$HERE/../.." && pwd)}
D=$HERE; FVMUT=${FVMUT:-/scratch/fastverify-next/tools/fvmut}
[ -x "$FVMUT" ] || { echo "SKIP rhgate437: needs fvmut ($FVMUT) and the RH-scale exports of this gate, which are not part of the repository"; exit 0; }
CS=$PKG/check/sound/check-sound.sh; P37=${PINS437:-$PKG/check/sound/pins-437.env}; HIDEARG=(); [ -n "${HIDE:-}" ] && HIDEARG=(--hide "$HIDE")   # PINS437= / HIDE= env overrides
mkdir -p "$O/mut" "$O/w"; TSV=$O/rh437.tsv; echo -e "case\texpected\trc\tverdict\tseconds\treason_legs_rss" > "$TSV"
run() { # run NAME EXPORT EXPECTED
  local n=$1 e=$2 want=$3 t0 rc v why; t0=$(date +%s)
  /usr/bin/time -f "%e s wall, max RSS %M KB (largest process)" -o "$O/w/$n.time" "$CS" "$e" "$C" "$CFG" --threads "$T" --json "$O/w/$n.json" --log "$O/w/$n.log" --private-inputs --pins "$P37" "${HIDEARG[@]}" > "$O/w/$n.out" 2>&1; rc=$?
  v=$(/usr/bin/python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j["verdict"]); print((j.get("reason") or "")[:160], "| legs_ms", json.dumps(j.get("leg_ms")), "| compare_ms", j.get("compare_ms"))' "$O/w/$n.json" 2>/dev/null)
  echo -e "$n\t$want\t$rc\t$(echo "$v" | head -1)\t$(( $(date +%s) - t0 ))\t$(echo "$v" | tail -1) | $(cat "$O/w/$n.time" 2>/dev/null | tail -1)" | tee -a "$TSV"
}
TARGETS=$(/usr/bin/python3 -I -c 'import json,sys; print(",".join(json.load(open(sys.argv[1]))["theorem_names"]))' "$CFG")
echo "[rhgate437] honest check ($T threads)"; run honest "$H" ACCEPTED
echo "[rhgate437] specs"; /usr/bin/python3 -I "$D/mk_rh437_specs.py" "$H" "$O/specs" --targets "$TARGETS" --m4 RiemannZetaZerosOnLine riemannZeta_eq_zero_re || { echo "spec generation failed"; exit 2; }
for m in M1 M2 M4 M3; do
  echo "[rhgate437] fvmut $m"; /usr/bin/time -f "fvmut $m %e s" "$FVMUT" "$H" "$O/mut/$m.export" "$O/specs/$m.spec" --threads 16 || { echo "fvmut $m failed"; exit 2; }
  run "$m" "$O/mut/$m.export" REJECTED
done
echo "[rhgate437] done:"; cat "$TSV"
