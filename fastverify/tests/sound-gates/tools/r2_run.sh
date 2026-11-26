#!/bin/bash
# r2_run.sh PKG OUTROOT [THREADS] : the kernel-level mutation classes of specs/r2/ on the rh-mid reference export.
#  1. fvmut every specs/r2/*.spec (+ specs/midNatSubAdd.spec as class V1) into OUTROOT/mut/
#  2. label every mutant with the OFFICIAL Lean 4.36 comparator (PKG/check/official/check.sh, lean-only rh-mid config),
#     all in parallel (single-threaded each)
#  3. judge every mutant with PKG/check/sound/check-sound.sh (gates.py --gate mutants, expected = the official verdict)
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
PKG=${1:?pkg}; O=${2:?outroot}; T=${3:-32}
E=/scratch/bench-inputs/rh-mid/ref/solution.export; CH=/scratch/bench-inputs/rh-mid/challenge
mkdir -p "$O/mut" "$O/official"; F=$(fvmut_bin) || exit 2
for s in "$HERE"/specs/r2/r2-*.spec "$HERE/specs/midNatSubAdd.spec"; do
  c=$(basename "$s" .spec); c=${c#r2-}; [ "$c" = midNatSubAdd ] && c=V1
  [ -s "$O/mut/$c.export" ] || "$F" "$E" "$O/mut/$c.export" "$s" --threads 8 > "$O/mut/$c.fvmut.log" 2>&1 || echo "fvmut $c FAILED"
done
for m in "$O"/mut/*.export; do
  c=$(basename "$m" .export)
  ( t0=$(date +%s); "$PKG/check/official/check.sh" "$m" "$CH/challenge.export" "$CH/comparator.json" --json "$O/official/$c.json" \
      > "$O/official/$c.log" 2>&1; echo "$c $? $(( $(date +%s) - t0 ))" >> "$O/official/done.txt" ) &
done
wait
python3 -I - "$O" "$CH" <<'PY'
import json, os, sys
O, CH = sys.argv[1], sys.argv[2]
lab = {}
for l in open(os.path.join(O, "official", "done.txt")):
    c, rc, sec = l.split()
    lab[c] = {"0": "ACCEPTED", "1": "REJECTED"}.get(rc, "ERROR(%s)" % rc)
cases = [{"name": c, "export": os.path.join(O, "mut", c + ".export"), "expect": v,
          "challenge": CH + "/challenge.export", "config": CH + "/comparator.json"}
         for c, v in sorted(lab.items()) if not v.startswith("ERROR")]
json.dump({"mutants": cases}, open(os.path.join(O, "inputs.json"), "w"), indent=1)
json.dump(lab, open(os.path.join(O, "official-labels.json"), "w"), indent=1)
print("official labels:", lab)
PY
python3 -I "$HERE/gates.py" --out "$O/sound" --check "$PKG/check/sound/check-sound.sh" --gate mutants --inputs "$O/inputs.json" \
  --jobs 4 --threads "$T" --label "kernel mutation classes on rh-mid (expected = official comparator)"
