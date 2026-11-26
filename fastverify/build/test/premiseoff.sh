#!/bin/bash
# build/test/premiseoff.sh [WORK] : component test of the B3 items premise-off + lean-path-order + sound-fast-path (sound preset; S07). No Mathlib, ~1 min.
#   1. sched.py's header parser (header_imports): plain headers parsed like Lean.Parser.Module.header; module/prelude/
#      public/meta/all/escaped names/unterminated comments -> None (module left untransformed)
#   2. projects/premise-off built with B1: Toy.A/Toy.B carry premise-selection metadata (sineQueNon/symbolFrequency
#      entries > 0) - the thing premise-off removes
#   3. the same with --preset B3 --unsafe premise-off: BUILT, Toy.A + Toy.B transformed (eligible), Toy.C (prelude) and
#      Toy.D (closure without Lean.LibrarySuggestions.Basic) untransformed, and every metadata entry of Toy.A/Toy.B is
#      empty, including the theorem whose type body head is a `let` (covered by the namespace-root deny only)
#   4. --unsafe premise-off,lean-path-order: LEAN_PATH = the same entries with the root lib first (Lake: last)
#   5. --unsafe sound-fast-path: no plancheck / dependency check / source digests; --lean-path-out = lake env's LEAN_PATH
#   6. --unsafe cost-hints=FILE: the file reaches sched.py inside the sandbox (start record: cost_hints_used)
#   7. --unsafe check-tail=FILE: idem (start record: check_tail_used)
# Prints PASS/FAIL per check and 'RESULT: PASS|FAIL'; exit 0 iff all pass.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); D=$(cd "$H/../.." && pwd)
W=${1:-/tmp/fv-potest-$$}; rm -rf "$W"; mkdir -p "$W/no-packages"; W=$(readlink -f "$W")
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
fail=0; ok() { echo "PASS $*"; }; bad() { echo "FAIL $*"; fail=1; }
# 1. parser
/usr/bin/python3 -I - "$D/build/sched.py" <<'PY' && ok "header parser (12 cases)" || bad "header parser"
import importlib.util, sys
spec = importlib.util.spec_from_file_location('sched', sys.argv[1]); s = importlib.util.module_from_spec(spec); spec.loader.exec_module(s)
H = s.header_imports
cases = [
 (b'import Mathlib\nimport A.B\n\ntheorem x : True := trivial\n', ['Mathlib', 'A.B']),
 (b'-- c\n/- doc /- nested -/ -/\nimport A -- trailing\nimport B\nnamespace X\n', ['A', 'B']),
 (b'/-! module doc -/\nimport A\nopen B\n', ['A']),
 (b'import A\n', ['A']),
 (b'theorem t : True := trivial\n', []),
 (b'import A.B\xe2\x82\x82\nset_option x 1\n', ['A.B₂']),
 (b'module\nimport A\n', None),
 (b'prelude\nimport Init.Core\n', None),
 (b'public import A\n', None),
 (b'import all A\n', None),
 (b'import \xc2\xabA b\xc2\xbb\n', None),
 (b'/- unterminated\nimport A\n', None),
]
bad = [(i, H(src), want) for i, (src, want) in enumerate(cases) if H(src) != want]
print('\n'.join(f'  case {i}: got {g!r}, want {w!r}' for i, g, w in bad)); sys.exit(1 if bad else 0)
PY
inspect() { # PROJ -> META lines
  env -i PATH=/usr/bin:/bin LEAN_PATH="$TC/lib/lean:$1/.lake/build/lib/lean" "$TC/bin/lean" "$H/projects/premise-off/Inspect.lean" 2>&1; }
# 2. B1 reference: metadata present
cp -a "$H/projects/premise-off" "$W/p1"; rm -f "$W/p1/Inspect.lean"
"$D/build/build.sh" "$W/p1" "$W/no-packages" "$TC" --log "$W/log1" --threads 4 > "$W/b1.json" 2>&1
m1=$(inspect "$W/p1"); echo "$m1" | sed 's/^/  B1: /'
if grep -q '"status": "BUILT"' "$W/b1.json" && echo "$m1" | grep -q '^META Toy.A sineQueNon [1-9]' && echo "$m1" | grep -q '^META Toy.A symbolFrequency [1-9]'
then ok "B1 build carries premise-selection metadata"; else bad "B1 reference: $(tail -1 "$W/b1.json" | cut -c1-200)"; fi
# 3. B3 premise-off
cp -a "$H/projects/premise-off" "$W/p3"; rm -f "$W/p3/Inspect.lean"
"$D/build/build.sh" "$W/p3" "$W/no-packages" "$TC" --log "$W/log3" --threads 4 --preset B3 --unsafe premise-off > "$W/b3.json" 2>&1
m3=$(inspect "$W/p3"); echo "$m3" | sed 's/^/  B3: /'
st=$(grep '"event": "summary"' "$W/log3/sched.out" | tail -1)
if grep -q '"status": "BUILT"' "$W/b3.json" && grep -q '"exact": false' "$W/b3.json"; then ok "B3 premise-off built, marked exact:false"; else bad "B3 premise-off: $(tail -1 "$W/b3.json" | cut -c1-300)"; fi
if echo "$st" | grep -q '"setup_transformed": 2, "setup_skipped": 2' && echo "$st" | grep -q 'Toy.C' && echo "$st" | grep -q 'Toy.D'
then ok "eligibility: Toy.A, Toy.B transformed; Toy.C (prelude), Toy.D (no LibrarySuggestions in closure) untouched"
else bad "eligibility: $(echo "$st" | cut -c1-400)"; fi
if [ "$(echo "$m3" | grep -c '^META')" = 4 ] && ! echo "$m3" | grep -q '^META .* [1-9]'; then ok "no premise-selection metadata in Toy.A/Toy.B (incl. the let-headed theorem)"
else bad "metadata left with premise-off"; fi
python3 -I -c 'import json,sys; s=json.load(open(sys.argv[1])); i=[x["module"] for x in s["imports"]]; sys.exit(0 if i==["Init","Init","Lean","FastverifyPremiseOff"] else 1)' \
  "$W/p3/.lake/build/ir/Toy/A.setup.json" && ok "Toy.A setup.json imports = Init, meta Init, Lean, FastverifyPremiseOff" || bad "Toy.A setup.json imports"
# 4. lean-path-order: same LEAN_PATH entries, root lib first (+ premise-off together: the helper olean is in the root lib)
cp -a "$H/projects/premise-off" "$W/p4"; rm -f "$W/p4/Inspect.lean"
"$D/build/build.sh" "$W/p4" "$W/no-packages" "$TC" --log "$W/log4" --threads 4 --preset B3 --unsafe premise-off,lean-path-order > "$W/b4.json" 2>&1
m4=$(inspect "$W/p4")
if grep -q '"status": "BUILT"' "$W/b4.json" && python3 -I -c 'import json,sys
st=json.loads(open(sys.argv[1]).readline()); pl=json.loads(open(sys.argv[2]).readline())
lp=st["lean_path"].split(":"); orig=pl["leanPath"].split(":")
root=[p["leanLibDir"] for p in pl["packages"] if p.get("isRoot")][0]
sys.exit(0 if sorted(lp)==sorted(orig) and lp[0]==root and orig[-1]==root else 1)' "$W/log4/sched.out" "$W/log4/plan.jsonl" && ! echo "$m4" | grep -q '^META .* [1-9]'
then ok "lean-path-order: same entries, root lib first (Lake: last); built with premise-off, metadata empty"
else bad "lean-path-order: $(tail -1 "$W/b4.json" | cut -c1-300)"; fi
# 5. sound-fast-path: exactness-only guards skipped, --lean-path-out from the plan header == what lake env prints
cp -a "$H/projects/premise-off" "$W/p5"; rm -f "$W/p5/Inspect.lean"
"$D/build/build.sh" "$W/p5" "$W/no-packages" "$TC" --log "$W/log5" --threads 4 --lean-path-out "$W/lp1.txt" > "$W/b5a.json" 2>&1
rm -rf "$W/p5"; cp -a "$H/projects/premise-off" "$W/p5"; rm -f "$W/p5/Inspect.lean"
"$D/build/build.sh" "$W/p5" "$W/no-packages" "$TC" --log "$W/log5s" --threads 4 --preset B3 --unsafe premise-off,sound-fast-path --lean-path-out "$W/lp2.txt" > "$W/b5.json" 2>&1
if grep -q '"status": "BUILT"' "$W/b5.json" && grep -q 'sound-fast-path: plancheck' "$W/log5s/plancheck.out" && [ ! -e "$W/log5s/src.before" ] \
   && [ -s "$W/lp1.txt" ] && cmp -s "$W/lp1.txt" "$W/lp2.txt"; then ok "sound-fast-path: built without plancheck/digests, LEAN_PATH out = lake env's"
else bad "sound-fast-path: $(tail -1 "$W/b5.json" | cut -c1-300) lp1=$(cat "$W/lp1.txt" 2>/dev/null) lp2=$(cat "$W/lp2.txt" 2>/dev/null)"; fi
# 6. cost-hints: a hint file is read inside the build sandbox; hinted modules are counted in the start record
cp -a "$H/projects/premise-off" "$W/p6"; rm -f "$W/p6/Inspect.lean"
printf '{"Toy.A": 30.0, "Toy.B": 2.5, "No.Such.Module": 1.0}' > "$W/hints.json"
"$D/build/build.sh" "$W/p6" "$W/no-packages" "$TC" --log "$W/log6" --threads 4 --preset B3 --unsafe premise-off,cost-hints="$W/hints.json" > "$W/b6.json" 2>&1
if grep -q '"status": "BUILT"' "$W/b6.json" && head -1 "$W/log6/sched.out" | grep -q '"cost_hints_used": 2'; then ok "cost-hints: built, 2 of 4 modules hinted"
else bad "cost-hints: $(tail -1 "$W/b6.json" | cut -c1-300) $(head -1 "$W/log6/sched.out" | grep -o '"cost_hints[^,]*,[^,]*')"; fi
# 7. check-tail: read inside the sandbox, counted in the start record (order only)
cp -a "$H/projects/premise-off" "$W/p7"; rm -f "$W/p7/Inspect.lean"
printf '{"Toy.A": 120.0, "No.Such.Module": 5.0}' > "$W/tail.json"
"$D/build/build.sh" "$W/p7" "$W/no-packages" "$TC" --log "$W/log7" --threads 4 --preset B3 --unsafe premise-off,cost-hints="$W/hints.json",check-tail="$W/tail.json" > "$W/b7.json" 2>&1
if grep -q '"status": "BUILT"' "$W/b7.json" && head -1 "$W/log7/sched.out" | grep -q '"check_tail_used": 1'; then ok "check-tail: built, 1 module with a kernel-check tail"
else bad "check-tail: $(tail -1 "$W/b7.json" | cut -c1-300)"; fi
[ $fail = 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL"
exit $fail
