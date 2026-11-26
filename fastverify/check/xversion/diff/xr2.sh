#!/bin/bash
# xr2.sh TC EXPORT CHALLENGE_EXPORT COMPARATOR_JSON OUT [THREADS]
#   kernel-level mutation classes (tests/sound-gates/tools/mk_r2_specs.py + fvmut) on an honest export of release
#   TC; every mutant labelled by the release's OWN official `lake comparator` (TC/bin/lake, bundled kernels), then judged
#   by xvcheck.py + check/sound/check-sound.sh through gates.py (pass = verdict equals the official label;
#   FAIL-CRITICAL = sound accepts what the official comparator rejects).
set -u
TC=$(readlink -f "$1"); E=$(readlink -f "$2"); CE=$(readlink -f "$3"); CFG=$(readlink -f "$4"); O=$5; T=${6:-8}
PKG=${PKG:-$LIGHT_LEAN/fastverify}; G=$PKG/tests/sound-gates
XV=${XV:-$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)/xvcheck.py}
mkdir -p "$O/specs" "$O/mut" "$O/official"; O=$(readlink -f "$O")
python3 -I "$XV" "$CE" "$CFG" > "$O/xvcheck.json" || { echo "xvcheck refuses this challenge"; cat "$O/xvcheck.json"; exit 2; }
python3 -I "$G/tools/mk_r2_specs.py" "$E" "$CE" "$O/specs" > "$O/specs.log" 2>&1 || { echo "mk_r2_specs failed"; cat "$O/specs.log"; exit 2; }
F=${FVMUT:?directory of the fvmut mutation tool}
[ -x "$F" ] || g++ -O2 -std=c++17 -pthread -o "$F" "$G/tools/fvmut.cpp" || exit 2
for s in "$O"/specs/*.spec; do c=$(basename "$s" .spec)
  [ -s "$O/mut/$c.export" ] || "$F" "$E" "$O/mut/$c.export" "$s" --threads 8 > "$O/mut/$c.fvmut.log" 2>&1 || echo "fvmut $c FAILED"
done
: > "$O/official/done.txt"; mkdir -p "$O/cwd"
ls "$O"/mut/*.export | xargs -P "${PAR:-6}" -I{} bash -c 'm={}; c=$(basename "$m" .export); t0=$(date +%s); d=$(mktemp -d "$4/cwd/XXXX");
  ( cd "$d" && env -i PATH="$1/bin:/usr/bin:/bin" HOME="$d" LANG=C.UTF-8 timeout 3600 lake comparator --config "$3" \
      --challenge-from-export "$2" --solution-from-export "$m" > "$4/official/$c.log" 2>&1 ); rc=$?
  echo "$c $rc $(( $(date +%s) - t0 ))" >> "$4/official/done.txt"' _ "$TC" "$CE" "$CFG" "$O"
python3 -I - "$O" "$CE" "$CFG" <<'PY'
import json, os, sys
O, CE, CFG = sys.argv[1:4]
lab = {}
for l in open(os.path.join(O, "official", "done.txt")):
    c, rc, sec = l.split()
    lab[c] = {"0": "ACCEPTED", "1": "REJECTED"}.get(rc, "ERROR(%s)" % rc)
cases = [{"name": c, "export": os.path.join(O, "mut", c + ".export"), "expect": v, "challenge": CE, "config": CFG}
         for c, v in sorted(lab.items()) if not v.startswith("ERROR")]
json.dump({"mutants": cases}, open(os.path.join(O, "inputs.json"), "w"), indent=1)
json.dump(lab, open(os.path.join(O, "official-labels.json"), "w"), indent=1)
print("official labels:", json.dumps(lab))
PY
python3 -I "$G/gates.py" --out "$O/sound" --check "$PKG/check/sound/check-sound.sh" --gate mutants --inputs "$O/inputs.json" \
  --jobs 4 --threads "$T" --label "R2 mutation classes on a $(basename "$TC") export (expected = the release's own lake comparator)"
echo "== done"; cat "$O/sound/mutants.tsv" 2>/dev/null | cut -f1-8
