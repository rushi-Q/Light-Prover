#!/bin/bash
# mk_attempt.sh DIR WS : a one-module `import Mathlib` proof attempt (project + challenge) on the trusted workspace WS
set -eu
D=$1; WS=$2
REV=$(python3 -I -c 'import json,sys; print([p["rev"] for p in json.load(open(sys.argv[1]))["packages"] if p["name"]=="mathlib"][0])' "$WS/lake-manifest.json")
URL=$(python3 -I -c 'import json,sys; print([p["url"] for p in json.load(open(sys.argv[1]))["packages"] if p["name"]=="mathlib"][0])' "$WS/lake-manifest.json")
mk() { local d=$1 n=$2 m=$3 pf=$4; mkdir -p "$d"
  printf 'name = "%s"\ndefaultTargets = ["%s"]\n\n[[require]]\nname = "mathlib"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "%s"\n' "$n" "$m" "$URL" "$REV" "$m" > "$d/lakefile.toml"
  python3 -I -c 'import json,sys; m=json.load(open(sys.argv[1])); m["name"]=sys.argv[3]; json.dump(m, open(sys.argv[2],"w"), indent=1)' "$WS/lake-manifest.json" "$d/lake-manifest.json" "$n"
  cp "$WS/lean-toolchain" "$d/lean-toolchain"
  printf 'import Mathlib\n\ntheorem d09_attempt (a b : Nat) (h : a < b) : a + 1 <= b := %s\n' "$pf" > "$d/$m.lean"; }
mk "$D/proj" d09attp Solution "by omega"
mk "$D/chal" d09attc Challenge "sorry"
printf '{"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["d09_attempt"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}\n' > "$D/chal/comparator.json"
echo "attempt project in $D"
