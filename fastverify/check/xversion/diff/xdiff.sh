#!/bin/bash
# xdiff.sh TC WS CASES_DIR OUT [CASE...]
#   Cross-version differential of the sound check: for every case of CASES_DIR (xgen.py output) the OFFICIAL flow of the
#   release TC (sandboxed `lake build` of challenge and solution with the trusted workspace WS read-only, the release's own
#   bundled `leanexport`, the release's own `lake comparator` on those exports) versus the 4.36 trusted check on the SAME
#   exports (xvcheck.py gate + fastverify check/sound/check-sound.sh). One TSV row per case in OUT/results.tsv.
set -u
TC=$(readlink -f "$1"); WS=$(readlink -f "$2"); CD=$(readlink -f "$3"); OUT=$4; shift 4
FV=${FV:-$LIGHT_LEAN/fastverify}
XV=${XV:-$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)/xvcheck.py}
mkdir -p "$OUT"; OUT=$(readlink -f "$OUT")
TG_BASE="Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
sbx() { # sbx DIR CMD... : bwrap, no network, home hidden, DIR writable, WS packages read-only at DIR/.lake/packages/*
  local d=$1; shift; local b=()
  for p in "$WS"/.lake/packages/*; do b+=(--ro-bind "$(readlink -f "$p")" "$d/.lake/packages/$(basename "$p")"); done
  env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home \
    --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --unshare-all --die-with-parent --new-session \
    --ro-bind "$TC" "$TC" --bind "$d" "$d" "${b[@]}" --chdir "$d" \
    --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 -- "$@"; }
prep() { # prep SRC DST
  rm -rf "$2"; cp -a "$1" "$2"; rm -rf "$2/.lake"; mkdir -p "$2/.lake/packages"
  for p in "$WS"/.lake/packages/*; do mkdir -p "$2/.lake/packages/$(basename "$p")"; done; }
targets() { # targets COMPARATOR_JSON
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); q=["Quot","Quot.mk","Quot.lift","Quot.ind"] if "Quot.sound" in c["permitted_axioms"] else []
print(" ".join(q+c["theorem_names"]+c["permitted_axioms"]+sys.argv[2].split()+c.get("definition_names",[])))' "$1" "$TG_BASE"; }
bexp() { # bexp DIR MODULE TARGETS OUTFILE -> 0 ok, 1 build failed, 3 export failed
  local t0=$(date +%s.%N)
  sbx "$1" lake build > "$1.build.log" 2>&1 || return 1
  sbx "$1" env LEAN_PATH="$1/.lake/build/lib/lean:$(cd "$1" && for p in .lake/packages/*; do printf '%s:' "$1/$p/.lake/build/lib/lean"; done)$TC/lib/lean" \
      leanexport "$2" -- $3 > "$4" 2> "$4.err" || return 3
  echo "$(date +%s.%N) - $t0" | bc > "$4.secs"; }
[ $# -gt 0 ] || set -- $(python3 -I -c 'import json,sys; print(" ".join(json.load(open(sys.argv[1]))))' "$CD/cases.json")
chal_of() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]]["challenge"])' "$CD/cases.json" "$1"; }
# 1. the challenges (once)
for ch in $(for c in "$@"; do chal_of "$c"; done | sort -u); do
  cfg=$CD/challenges/$ch/comparator.json
  if [ ! -s "$OUT/chal-$ch.export" ]; then
    prep "$CD/challenges/$ch" "$OUT/chal-$ch"
    bexp "$OUT/chal-$ch" Challenge "$(targets "$cfg")" "$OUT/chal-$ch.export" || { echo "challenge $ch failed (rc $?)"; tail -n 20 "$OUT/chal-$ch.build.log"; exit 2; }
  fi
done
# 2. the cases (PAR at a time; a case whose row exists is not re-run)
runcase() {
  local c=$1 ch exp cfg TG sm brc orc ov xrc src sv ag det
  [ -s "$OUT/row-$c.tsv" ] && return 0
  ch=$(chal_of "$c")
  exp=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]]["expected_official"])' "$CD/cases.json" "$c")
  cfg=$CD/challenges/$ch/comparator.json; TG=$(targets "$cfg")
  sm=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$cfg")
  prep "$CD/projects/$c" "$OUT/p-$c"; bexp "$OUT/p-$c" "$sm" "$TG" "$OUT/p-$c.export"; brc=$?
  if [ $brc != 0 ]; then
    printf '%s\t%s\t%s\t%s\t-\t-\t-\t%s\t%s\n' "$c" "$exp" "$brc" REJECTED "n/a" "official build/export failed (rc $brc): no export to judge" > "$OUT/row-$c.tsv"; return 0; fi
  ( cd "$OUT/chal-$ch" && env -i PATH="$TC/bin:/usr/bin:/bin" HOME="$OUT/home" LANG=C.UTF-8 timeout 3600 lake comparator --config "$cfg" \
      --challenge-from-export "$OUT/chal-$ch.export" --solution-from-export "$OUT/p-$c.export" > "$OUT/p-$c.cmp" 2>&1 ); orc=$?
  ov=$([ $orc = 0 ] && echo ACCEPTED || echo REJECTED)
  python3 -I "$XV" "$OUT/chal-$ch.export" "$cfg" > "$OUT/p-$c.xv" 2>&1; xrc=$?
  if [ $xrc = 0 ]; then
    "$FV/check/sound/check-sound.sh" "$OUT/p-$c.export" "$OUT/chal-$ch.export" "$cfg" --threads ${THREADS:-8} > "$OUT/p-$c.cs" 2>&1; src=$?
  else src=$xrc; fi
  sv=$(case $src in 0) echo ACCEPTED;; 1) echo REJECTED;; *) echo NO_VERDICT;; esac)
  ag=$([ "$ov" = "$sv" ] && echo yes || echo NO)
  det=$(tail -n 1 "$OUT/p-$c.cmp" | cut -c1-120 | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$c" "$exp" "$orc" "$ov" "$xrc" "$src" "$sv" "$ag" "$det" > "$OUT/row-$c.tsv"
}
export -f runcase chal_of prep bexp sbx targets; export TC WS CD OUT FV XV TG_BASE THREADS
printf '%s\n' "$@" | xargs -P "${PAR:-1}" -I{} bash -c 'runcase "$1"' _ {}
{ printf 'case\texpected_v433\tofficial_rc\tofficial_verdict\txvcheck_rc\tcheck_sound_rc\tcheck_sound_verdict\tagree\tdetail\n'
  for c in "$@"; do cat "$OUT/row-$c.tsv" 2>/dev/null || printf '%s\tMISSING\n' "$c"; done; } > "$OUT/results.tsv"
cat "$OUT/results.tsv"
