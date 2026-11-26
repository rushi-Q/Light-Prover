#!/bin/bash
# tests/build-j1-hints/run.sh [SCRATCH] : component test: the sound build item j1-saturated may
# put a module on -j1 only with an APPLICABLE cost hint (the module is hinted, or hints cover >= half of the plan); without
# hints for the project (the preset's cost-hints file is RH's) no module gets -j1. Tiny core-only project, 2 threads, so the
# ready queue is saturated: J.A is long (static estimate ~15 s), J.B..J.H short -> they have slack.
#   1. --preset sound (RH hints only, nhint = 0)          -> ACCEPTED, 0 modules with -j1
#   2. --preset sound + cost-hints for J.B..J.H (1 s each) -> ACCEPTED, >= 1 module with -j1, all of them hinted
# Prints PASS/FAIL rows and RESULT; exit 0 iff all PASS.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd)/bin/fastverify
S=$(mktemp -d "${1:-${TMPDIR:-/tmp}}/build-j1-hints.XXXXXX") || exit 2
trap 'chmod -R u+w "$S" 2>/dev/null; rm -rf "$S"' EXIT
P=$S/proj; C=$S/chal; mkdir -p $P/J $C
for d in $P $C; do echo "leanprover/lean4:v4.33.1" > $d/lean-toolchain; done
printf 'name = "jtest"\ndefaultTargets = ["J"]\n\n[[lean_lib]]\nname = "J"\n' > $P/lakefile.toml
printf '{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [], "name": "jtest", "lakeDir": ".lake"}\n' > $P/lake-manifest.json
printf 'name = "jchal"\ndefaultTargets = ["Challenge"]\n\n[[lean_lib]]\nname = "Challenge"\n' > $C/lakefile.toml
printf '{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [], "name": "jchal", "lakeDir": ".lake"}\n' > $C/lake-manifest.json
{ for i in $(seq 1 400); do echo "-- padding line $i (static cost estimate of the scheduler grows with sqrt(lines))"; done; echo "theorem jA : True := trivial"; } > $P/J/A.lean
for x in B C D E F G H; do echo "theorem j$x : True := trivial" > $P/J/$x.lean; done
{ for x in A B C D E F G H; do echo "import J.$x"; done; } > $P/J.lean
echo "theorem jA : True := sorry" > $C/Challenge.lean
printf '{"challenge_module": "Challenge", "solution_module": "J", "theorem_names": ["jA"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}\n' > $C/comparator.json
printf '{"J.B": 1.0, "J.C": 1.0, "J.D": 1.0, "J.E": 1.0, "J.F": 1.0, "J.G": 1.0, "J.H": 1.0}\n' > $S/hints.json
pass=0; fail=0
ok() { echo "PASS $1"; pass=$((pass+1)); }; bad() { echo "FAIL $1"; fail=$((fail+1)); }
run() { env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV" $P $C $S/$1 --preset sound --threads 2 "${@:2}" > $S/$1.log 2>&1; }
LIST=$(python3 -I -c 'import sys; sys.path.insert(0, sys.argv[1]); import fastverify as f; print(",".join(u for u in f.PRESETS["sound"]["unsafe"] if not u.startswith("cost-hints")))' "$H/../../lib" 2>/dev/null)
run nohint
run hinted --unsafe "$LIST,cost-hints=$S/hints.json"
for c in nohint hinted; do
  v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' $S/$c/result.json 2>/dev/null)
  so=$S/$c/log/build-fast/sched.out
  n=$(grep -c '"j1": true' $so 2>/dev/null); names=$(grep '"j1": true' $so 2>/dev/null | grep -o '"module": "[^"]*"' | cut -d'"' -f4 | tr '\n' ' ')
  [ "$v" = ACCEPTED ] && ok "build-j1-hints $c verdict ACCEPTED" || bad "build-j1-hints $c verdict '$v' ($(tail -1 $S/$c.log | cut -c1-200))"
  if [ $c = nohint ]; then [ "${n:-x}" = 0 ] && ok "build-j1-hints nohint: no module with -j1" || bad "build-j1-hints nohint: $n modules with -j1 ($names)"
  else
    if [ "${n:-0}" -ge 1 ] && ! echo "$names" | grep -qE '(^| )J(\.A)?( |$)'; then ok "build-j1-hints hinted: $n hinted modules with -j1 ($names)"
    else bad "build-j1-hints hinted: j1 modules '$names' (expected >= 1, only J.B..J.H)"; fi
  fi
done
echo "RESULT pass=$pass fail=$fail"; [ $fail = 0 ]
