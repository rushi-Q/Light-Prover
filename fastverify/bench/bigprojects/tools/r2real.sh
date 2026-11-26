#!/bin/bash
# r2real.sh NAME EXPORT CHALLENGE_DIR OUT [THREADS] : kernel-level mutation classes (tests/sound-gates/tools/
# mk_r2_specs.py: theorem->axiom, universe params dropped/swapped, recursor rule rhs / K flag, constructor fields, inductive
# isRec, duplicate declaration, projection index, universe instantiation, binder info) on a REAL project's honest export;
# every mutant labelled by the OFFICIAL Lean 4.36 comparator (check/official/check.sh), then judged by the trusted
# check/sound/check-sound.sh via gates.py (pass = verdict equals the official label; FAIL-CRITICAL = sound accepts what
# the official comparator rejects).
set -u
N=$1 E=$2 CH=$3 O=$4 T=${5:-16}
PKG=${PKG:-$LIGHT_LEAN/fastverify}; G=$PKG/tests/sound-gates
mkdir -p "$O/specs" "$O/mut" "$O/official"
python3 -I "$G/tools/mk_r2_specs.py" "$E" "$CH/challenge.export" "$O/specs" > "$O/specs.log" 2>&1 || { echo "mk_r2_specs failed"; cat "$O/specs.log"; exit 2; }
F=${FVMUT:-$O/fvmut}
[ -x "$F" ] || g++ -O2 -std=c++17 -pthread -o "$F" "$G/tools/fvmut.cpp" || exit 2
for s in "$O"/specs/*.spec; do c=$(basename "$s" .spec)
  [ -s "$O/mut/$c.export" ] || "$F" "$E" "$O/mut/$c.export" "$s" --threads 8 > "$O/mut/$c.fvmut.log" 2>&1 || echo "fvmut $c FAILED"
done
ls "$O"/mut/*.export | xargs -P "${PAR:-12}" -I{} bash -c 'm={}; c=$(basename "$m" .export); t0=$(date +%s);
  "$0/check/official/check.sh" "$m" "$1/challenge.export" "$1/comparator.json" --json "$2/official/$c.json" > "$2/official/$c.log" 2>&1;
  echo "$c $? $(( $(date +%s) - t0 ))" >> "$2/official/done.txt"' "$PKG" "$CH" "$O"
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
python3 -I "$G/gates.py" --out "$O/sound" --check "$PKG/check/sound/check-sound.sh" --gate mutants --inputs "$O/inputs.json" \
  --jobs 4 --threads "$T" --label "kernel mutation classes on $N (expected = official comparator)"
echo "== $N done"; cat "$O/sound/mutants.tsv" 2>/dev/null | cut -f1-8
