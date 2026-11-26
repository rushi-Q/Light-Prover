#!/bin/bash
# xdiff434.sh TC WS CASES_DIR OUT [CASE...]   (env: T434 = dir with comparator/ and lean4export/ built for the release,
#                                               LANDRUN = landrun->bwrap shim, PAR, THREADS)
#   Cross-version differential for a release WITHOUT `lake comparator` (<= 4.34): the official judge of that era is the
#   external leanprover/comparator (d03acab for 4.34.x) + lean4export (tag v4.34.0), run exactly as its README says
#   (`lake env comparator CONFIG` in a workspace holding both the challenge and the solution module; landrun replaced by a
#   bwrap shim). Per case of CASES_DIR (xgen.py output): one combined project = the solution project + Challenge.lean +
#   a `Challenge` lean_lib; the comparator config is the case's minus external kernels (this release bundles no
#   nanoda). Then the challenge and solution exports are written by the same lean4export from the oleans the comparator's
#   own build produced (4.36 target list) and judged by xvcheck.py + check/sound/check-sound.sh.
set -u
TC=$(readlink -f "$1"); WS=$(readlink -f "$2"); CD=$(readlink -f "$3"); OUT=$4; shift 4
FV=${FV:-$LIGHT_LEAN/fastverify}
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
XV=${XV:-$(cd "$H/.." && pwd)/xvcheck.py}
T434=${T434:?dir with comparator/ and lean4export/ built for the release}; LANDRUN=${LANDRUN:?landrun-to-bwrap shim}
mkdir -p "$OUT"; OUT=$(readlink -f "$OUT")
TG_BASE="Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
[ $# -gt 0 ] || set -- $(python3 -I -c 'import json,sys; print(" ".join(json.load(open(sys.argv[1]))))' "$CD/cases.json")
runcase() {
  local c=$1 ch exp cfg P sm orc ov TG xrc src sv ag det t0
  [ -s "$OUT/row-$c.tsv" ] && return 0
  ch=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]]["challenge"])' "$CD/cases.json" "$c")
  exp=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]]["expected_official"])' "$CD/cases.json" "$c")
  P=$OUT/cmb-$c; rm -rf "$P"; cp -a "$CD/projects/$c" "$P"; rm -rf "$P/.lake"; mkdir -p "$P/.lake/packages"
  cp "$CD/challenges/$ch/Challenge.lean" "$P/"; printf '\n[[lean_lib]]\nname = "Challenge"\n' >> "$P/lakefile.toml"
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("external_kernels",None); c.pop("enable_nanoda",None)
json.dump(c, open(sys.argv[2],"w"), indent=1)' "$CD/challenges/$ch/comparator.json" "$P/comparator.json"
  cfg=$P/comparator.json
  for d in "$WS"/.lake/packages/*/; do ln -s "$WS/.lake/packages/$(basename "$d")" "$P/.lake/packages/$(basename "$d")"; done
  t0=$(date +%s.%N)
  env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dir /tmp/home --tmpfs /var \
    --dev /dev --proc /proc --unshare-user --unshare-ipc --unshare-pid --unshare-uts --unshare-net --die-with-parent \
    --new-session --ro-bind "$TC" "$TC" --ro-bind "$WS" "$WS" --ro-bind "$T434" "$T434" --ro-bind "$(dirname "$LANDRUN")" "$(dirname "$LANDRUN")" \
    --bind "$P" "$P" --chdir "$P" --setenv PATH "$TC/bin:$T434/comparator/.lake/build/bin:/usr/bin:/bin" --setenv HOME /tmp/home \
    --setenv LANG C.UTF-8 --setenv COMPARATOR_LANDRUN "$LANDRUN" --setenv COMPARATOR_LEAN4EXPORT "$T434/lean4export/.lake/build/bin/lean4export" \
    -- timeout 3600 lake env comparator comparator.json > "$OUT/p-$c.cmp" 2>&1; orc=$?
  echo "$(date +%s.%N) - $t0" | bc > "$OUT/p-$c.cmp.secs"
  ov=$([ $orc = 0 ] && echo ACCEPTED || echo REJECTED)
  # exports of the oleans the comparator's build produced, by the same official lean4export (4.36 target list)
  TG=$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); q=["Quot","Quot.mk","Quot.lift","Quot.ind"] if "Quot.sound" in c["permitted_axioms"] else []
print(" ".join(q+c["theorem_names"]+c["permitted_axioms"]+sys.argv[2].split()+c.get("definition_names",[])))' "$cfg" "$TG_BASE")
  sm=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$cfg")
  local LP="$P/.lake/build/lib/lean:$(for d in "$WS"/.lake/packages/*/; do printf '%s:' "$WS/.lake/packages/$(basename "$d")/.lake/build/lib/lean"; done)$TC/lib/lean"
  local ok=1
  for m in Challenge "$sm"; do
    [ -f "$P/.lake/build/lib/lean/$(echo "$m" | tr . /).olean" ] || { ok=0; break; }
    ( cd "$P" && env -i PATH="$TC/bin:/usr/bin:/bin" LEAN_PATH="$LP" LEAN_ABORT_ON_PANIC=1 \
        "$T434/lean4export/.lake/build/bin/lean4export" "$m" -- $TG > "$OUT/p-$c.$m.export" 2> "$OUT/p-$c.$m.export.err" ) || { ok=0; break; }
  done
  if [ $ok = 0 ]; then
    printf '%s\t%s\t%s\t%s\t-\t-\t-\t%s\t%s\n' "$c" "$exp" "$orc" "$ov" "$([ $ov = REJECTED ] && echo n/a || echo NO)" "no export (build/export failed)" > "$OUT/row-$c.tsv"; return 0; fi
  python3 -I "$XV" "$OUT/p-$c.Challenge.export" "$cfg" > "$OUT/p-$c.xv" 2>&1; xrc=$?
  if [ $xrc = 0 ]; then
    "$FV/check/sound/check-sound.sh" "$OUT/p-$c.$sm.export" "$OUT/p-$c.Challenge.export" "$cfg" --threads ${THREADS:-4} > "$OUT/p-$c.cs" 2>&1; src=$?
  else src=$xrc; fi
  sv=$(case $src in 0) echo ACCEPTED;; 1) echo REJECTED;; *) echo NO_VERDICT;; esac)
  ag=$([ "$ov" = "$sv" ] && echo yes || echo NO)
  det=$(grep -aE "okay|uncaught exception|error|rejects|Error" "$OUT/p-$c.cmp" | tail -n 1 | cut -c1-120 | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$c" "$exp" "$orc" "$ov" "$xrc" "$src" "$sv" "$ag" "$det" > "$OUT/row-$c.tsv"
}
export -f runcase; export TC WS CD OUT FV XV T434 LANDRUN TG_BASE THREADS
printf '%s\n' "$@" | xargs -P "${PAR:-1}" -I{} bash -c 'runcase "$1"' _ {}
{ printf 'case\texpected_v433\tofficial_rc\tofficial_verdict\txvcheck_rc\tcheck_sound_rc\tcheck_sound_verdict\tagree\tdetail\n'
  for c in "$@"; do cat "$OUT/row-$c.tsv" 2>/dev/null || printf '%s\tMISSING\n' "$c"; done; } > "$OUT/results.tsv"
cat "$OUT/results.tsv"
