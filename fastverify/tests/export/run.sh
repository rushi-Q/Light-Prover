#!/bin/bash
# tests/export/run.sh [WORK] [--heavy]  — component regression tests of the EXPORT stage
#
# For each case, .olean files are built with the OFFICIAL Lean 4.33.1 (`lean -o`, some with -Ddebug.skipKernelTC=true to
# obtain kernel-invalid oleans: the package's build never skips the kernel check, but the exporter must be exact on ANY
# oleans), then
#   OFFICIAL = the official lean4export (pinned) under env -i, LEAN_ABORT_ON_PANIC=1 (as bin/fastverify runs it)
#   NATIVE   = fastverify/export/export.sh (native-only exporter; exit 2 = declined)
#   STAGE    = fastverify/export/export.sh --official-fallback (what a decline turns into)
# PASS rules: expect=identical -> NATIVE exit 0 and bytes == OFFICIAL (official exit 0);
#             expect=decline   -> NATIVE exit 2 (no output) and STAGE == OFFICIAL (same exit class, same bytes if exit 0).
# Findings covered: 008 010 013 018 030 033 + new fail-closed paths (githash, missing target, options, equal duplicates).
# --heavy adds rh-mid (1.1 GB export, must be byte-identical to the reference export).  Prints one TSV row per case;
# exit 0 iff all PASS.  Any host; ~1 min (+~2 min heavy).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=$(cd "$H/../.." && pwd)
W=${1:-${SCRATCH:-${TMPDIR:-/tmp}}/$(whoami)-fvtest/export}; HEAVY=0; [ "${2:-}" = --heavy ] || [ "${1:-}" = --heavy ] && HEAVY=1
[ "${1:-}" = --heavy ] && W=${SCRATCH:-${TMPDIR:-/tmp}}/$(whoami)-fvtest/export
T33=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1
BI=${FV_BENCH_INPUTS:-/scratch/bench-inputs}   # bench inputs (only --heavy: rh-mid ref oleans + reference export)
EXS=$PKG/export/export.sh
OFF=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["official"]["path"])' "$PKG/export/components.json")
OFF=${OFF/\$LIGHT_LEAN/$(dirname "$PKG")}   # the template path, resolved as export/export.sh resolves it
# the official exporter this installation registered (tools/configure.py: config/components.json, sha256-verified) wins
CFGOFF=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["official_lean4export"]["path"])' "$PKG/config/components.json" 2>/dev/null)
OFF=${FV_OFFICIAL_EXPORTER:-${CFGOFF:-$OFF}}
NAT=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["native"]["path"])' "$PKG/export/components.json")
TG="$(cat "$H/targets-rh5.txt")"
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
FAIL=0
row() { printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$@"; [ "$6" = PASS ] || FAIL=1; }
build() {  # case dir, then "MOD[:skip]" ...
  local c=$1; shift; local b=$W/$c/build; mkdir -p "$b"; cp "$H/cases/$c"/*.lean "$b/"
  for m in "$@"; do
    local fl=(); [ "${m#*:}" = skip ] && fl=(-Ddebug.skipKernelTC=true); m=${m%%:*}
    (cd "$b" && env -i PATH=$T33/bin:/usr/bin:/bin "LEAN_PATH=$b:$T33/lib/lean" $T33/bin/lean "${fl[@]}" -o $m.olean $m.lean) > "$W/$c/build.$m.log" 2>&1 || echo "  (build of $c/$m exit $?)" >&2
  done
}
official() {  # case roots targets-file -> W/case/off.out, prints exit
  local c=$1 b=$W/$1/build; read -r -a R <<< "$2"; local T=()
  if [ "${TNL:-0}" = 1 ]; then while IFS= read -r t || [ -n "$t" ]; do [ -n "$t" ] && T+=("$t"); done < "$3"
  else read -r -d '' -a T < "$3"; fi
  (cd "$b" && env -i PATH=$T33/bin:/usr/bin:/bin HOME=/tmp "LEAN_PATH=$b:$T33/lib/lean" LEAN_ABORT_ON_PANIC=1 "$OFF" "${R[@]}" -- "${T[@]}") > "$W/$c/off.out" 2> "$W/$c/off.err"
  echo $?
}
stage() {  # case roots targets-file tag [extra]
  local c=$1 b=$W/$1/build roots=$2 tf=$3 tag=$4; shift 4
  local tflag=--targets-file; [ "${TNL:-0}" = 1 ] && tflag=--targets-nl
  "$EXS" --lean-path "$b:$T33/lib/lean" --module "$roots" $tflag "$tf" --toolchain "$T33" --project "$b" \
      --out "$W/$c/$tag.out" --json "$W/$c/$tag.json" "$@" > /dev/null 2>> "$W/$c/$tag.err"
  echo $?
}
runcase() {  # name expect roots targets-file
  local c=$1 exp=$2 roots=$3 tf=$4
  local orc nrc src; orc=$(official "$c" "$roots" "$tf")
  nrc=$(stage "$c" "$roots" "$tf" native)
  src=$(stage "$c" "$roots" "$tf" stage --official-fallback)
  local why; why=$(/usr/bin/python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print((j["native"].get("decline_reason") or "")[:70])' "$W/$c/native.json" 2>/dev/null)
  local same_stage=no; { [ "$src" != 0 ] && [ "$orc" != 0 ]; } || { [ "$src" = 0 ] && [ "$orc" = 0 ] && cmp -s "$W/$c/stage.out" "$W/$c/off.out"; } && same_stage=yes
  local verdict=FAIL
  if [ "$exp" = identical ]; then
    [ "$orc" = 0 ] && [ "$nrc" = 0 ] && cmp -s "$W/$c/native.out" "$W/$c/off.out" && [ $same_stage = yes ] && verdict=PASS
  else
    [ "$nrc" = 2 ] && [ ! -e "$W/$c/native.out" ] && [ $same_stage = yes ] && verdict=PASS
  fi
  row "$c" "expect=$exp" "official_exit=$orc" "native_exit=$nrc" "stage_exit=$src${why:+ ($why)}" "$verdict"
}
printf 'case\texpect\tofficial\tnative\tstage(+decline reason)\tresult\n'
# control: Init closure
mkdir -p "$W/control/build"; echo "Nat.add List.map" > "$W/control/tg"   # empty project dir: Init from the toolchain
runcase control identical Init "$W/control/tg"
# 008: projection index 2^32+1 (skipKernelTC build) -> the native core must not truncate it
build 008 Challenge:skip Main:skip;   echo "$TG" > "$W/008/tg"; runcase 008 decline Main "$W/008/tg"
# 010: invalid UTF-8 string literal (normal build)
build 010 Challenge Main;             echo "$TG" > "$W/010/tg"; runcase 010 decline Main "$W/010/tg"
# 013: duplicate names whose types differ (official: import error)
build 013 A B C D
echo foo > "$W/013/tg-foo"; echo ax > "$W/013/tg-ax"
mkdir -p "$W/013b" "$W/013c"; ln -s "$W/013/build" "$W/013b/build"; ln -s "$W/013/build" "$W/013c/build"
runcase 013b decline "A B" "$W/013/tg-foo"
runcase 013c decline "C D" "$W/013/tg-ax"
# duplicates Lean accepts (equal types incl. up to binder names/infos): resolved natively, byte-identical
build dupeq E F; echo "dupThm dupB dupC" > "$W/dupeq/tg"; runcase dupeq identical "E F" "$W/dupeq/tg"
# 018: Name.num component 2^64 (bignum) in the closure
build 018 N;                          echo main_thm > "$W/018/tg"; runcase 018 decline N "$W/018/tg"
# 030: free variable in a stored proof (skipKernelTC build) -> official exporter panics
build 030 Challenge:skip Main:skip;   echo "$TG" > "$W/030/tg"; runcase 030 decline Main "$W/030/tg"
# 033: universe metavariable (skipKernelTC build)
build 033 Challenge:skip Main:skip;   echo "$TG" > "$W/033/tg"; runcase 033 decline Main "$W/033/tg"
# githash: an .olean whose header githash is not 4.33.1's (official reader: 'incompatible header')
build githash G; echo gThm > "$W/githash/tg"
printf '0000000000000000000000000000000000000000' | dd of="$W/githash/build/G.olean" bs=1 seek=40 conv=notrunc status=none
runcase githash decline G "$W/githash/tg"
# IR parts: the official importModules (level .private) also reads X.ir.sig/X.ir of every module (header checks; X.ir
# must exist if X.ir.sig does); the native core used to ignore them.  module-system file M -> M.ir.sig + M.ir
build ir M; echo modThm > "$W/ir/tg"; runcase ir identical M "$W/ir/tg"
for v in irmissing irgithash irsigplanted; do mkdir -p "$W/$v"; cp -r "$W/ir/build" "$W/$v/build"; done
rm -f "$W/irmissing/build/M.ir"
printf '0000000000000000000000000000000000000000' | dd of="$W/irgithash/build/M.ir" bs=1 seek=40 conv=notrunc status=none
runcase irmissing decline M "$W/ir/tg"
runcase irgithash decline M "$W/ir/tg"
# a stray G.ir.sig next to a NON-module olean is read (and rejected) by the official reader as well
mkdir -p "$W/irsigplanted"; rm -rf "$W/irsigplanted/build"; cp -r "$W/githash/build" "$W/irsigplanted/build"
(cd "$W/irsigplanted/build" && rm -f G.olean && env -i PATH=$T33/bin:/usr/bin:/bin "LEAN_PATH=$W/irsigplanted/build:$T33/lib/lean" $T33/bin/lean -o G.olean G.lean > /dev/null 2>&1 && echo garbage > G.ir.sig)
runcase irsigplanted decline G "$W/githash/tg"
# missing target constant (official: PANIC 'Constant ... not found')
mkdir -p "$W/missing"; ln -s "$W/control/build" "$W/missing/build"; echo "Nat.add Nat.doesNotExist" > "$W/missing/tg"
runcase missing decline Init "$W/missing/tg"
# kitchen sink of valid constructs (strings with escapes/control chars/astral chars, «» names incl. spaces, big Nat
# literals, nested + mutual inductives, structures, classes, imax/max levels, let/have, Quot, structural + wf recursion,
# opaque/partial/unsafe/noncomputable, axioms): byte-identical; targets one per line (--targets-nl, names with spaces)
build kitchen K; cp "$H/cases/kitchen/targets.txt" "$W/kitchen/tg"
TNL=1 runcase kitchen identical K "$W/kitchen/tg"
# an UNSAFE target: the official exporter skips unsafe constants (no declaration record); the closure guard cannot tell
# that apart from a truncation, so E1 declines (documented limitation) and the E0 fallback gives the official bytes
# a real copy, not a symlink: the export sandbox binds the project path itself, so a symlink's target would not be visible
mkdir -p "$W/unsafe-target"; cp -a "$W/kitchen/build" "$W/unsafe-target/build"; printf 'thm1\nuns\n' > "$W/unsafe-target/tg"
TNL=1 runcase unsafe-target decline K "$W/unsafe-target/tg"
# the same targets through the whitespace-separated --targets-file: the split «...» name must make E1 decline
tr '\n' ' ' < "$W/kitchen/tg" > "$W/kitchen/tg-ws"; mkdir -p "$W/kitchen-ws"; ln -s "$W/kitchen/build" "$W/kitchen-ws/build"
nrc=$(stage kitchen-ws K "$W/kitchen/tg-ws" native); [ "$nrc" = 2 ] && r=PASS || r=FAIL
row kitchen-ws decline - "native_exit=$nrc" "(split «» name)" "$r"
# 059: a work directory path containing spaces (the old pipeline export.sh broke on it): byte-identical
c="space dir"; b="$W/$c/build"; mkdir -p "$b"; cp "$H/cases/githash/G.lean" "$b/"
(cd "$b" && env -i PATH=$T33/bin:/usr/bin:/bin LEAN_PATH="$b:$T33/lib/lean" $T33/bin/lean -o G.olean G.lean) > /dev/null 2>&1
echo gThm > "$W/$c/tg"; runcase "space dir" identical G "$W/$c/tg"
# internal error of the stage script (unbound variable under set -u, injected into a private copy): must be exit 2
# (declined -> E0), never 1 (= the official exporter failed = REJECT)
sed 's|^T0=$(date +%s.%N)$|T0=$(date +%s.%N); echo "$FV_INJECTED_UNBOUND"|' "$EXS" > "$W/export-injected.sh"; chmod +x "$W/export-injected.sh"
cp "$PKG/export/components.json" "$W/components.json"   # the copy reads components.json next to itself
irc=$("$W/export-injected.sh" --lean-path "$T33/lib/lean" --module Init --targets-file "$W/control/tg" --toolchain "$T33" \
      --project "$W/control/build" --out "$W/inj.out" --json "$W/inj.json" > /dev/null 2>&1; echo $?)
grep -q FV_INJECTED_UNBOUND "$W/export-injected.sh" && [ "$irc" = 2 ] && [ ! -e "$W/inj.out" ] && r=PASS || r=FAIL
row internal-error decline - "stage_exit=$irc" "(injected unbound variable)" "$r"
# closure guard: a (fake) native exporter that exits 0 with a WELL-FORMED but INCOMPLETE export (one declaration of a
# referenced constant dropped, like an earlier truncated export) must be caught by export.sh's closure guard -> decline
mkdir -p "$W/guard/stage"; cp "$EXS" "$W/guard/stage/export.sh"
# The export sandbox shows the native exporter's own file only (every other top-level directory is hidden), so the fake
# cannot call the real binary: it prints outputs the real native exporter produced here, embedded in the script (the
# preflight self-test output as is, the Init closure with its first declaration dropped)
NENV=(env -i PATH="$T33/bin:/usr/bin:/bin" HOME=/tmp LANG=C.UTF-8 LEAN_PATH="$T33/lib/lean" LEAN_ABORT_ON_PANIC=1 LEAN4EXPORT_VERBOSE=0)
PF64=$(cd / && "${NENV[@]}" "$NAT" Init -- Nat.add 2>/dev/null | base64 -w0)
TR64=$(cd "$W/control/build" && "${NENV[@]}" "$NAT" Init -- Nat.add List.map 2>/dev/null \
       | awk 'BEGIN{d=0} /^\{"def":/ && d==0 {d=1; next} {print}' | base64 -w0)
cat > "$W/guard/fake-native.sh" <<FAKE
#!/bin/bash
if [ "\$*" = "Init -- Nat.add" ]; then echo '$PF64' | base64 -d; else echo '$TR64' | base64 -d; fi
FAKE
chmod +x "$W/guard/fake-native.sh"
/usr/bin/python3 -I - "$PKG/export/components.json" "$W/guard/stage/components.json" "$W/guard/fake-native.sh" <<'PY'
import hashlib, json, sys
c = json.load(open(sys.argv[1])); c["native"]["path"] = sys.argv[3]
c["native"]["sha256"] = hashlib.sha256(open(sys.argv[3], "rb").read()).hexdigest()
json.dump(c, open(sys.argv[2], "w"))
PY
grc=$("$W/guard/stage/export.sh" --lean-path "$T33/lib/lean" --module Init --targets-file "$W/control/tg" --toolchain "$T33" \
      --project "$W/control/build" --out "$W/guard/out" --json "$W/guard/out.json" > /dev/null 2>&1; echo $?)
gwhy=$(/usr/bin/python3 -I -c 'import json,sys; print((json.load(open(sys.argv[1]))["native"].get("decline_reason") or "")[:70])' "$W/guard/out.json" 2>/dev/null)
[ "$grc" = 2 ] && [ ! -e "$W/guard/out" ] && case "$gwhy" in "closure guard:"*) true;; *) false;; esac && r=PASS || r=FAIL
row closure-guard decline - "stage_exit=$grc" "($gwhy)" "$r"
# options: the native-only binary declines (exit 2, nothing usable) on any lean4export option
orc=$(cd "$W/control/build" && env -i PATH=$T33/bin:/usr/bin:/bin LEAN_PATH=$W/control/build:$T33/lib/lean "$NAT" --export-mdata Init -- Nat.add > "$W/control/opt.out" 2>/dev/null; echo $?)
[ "$orc" = 2 ] && [ ! -s "$W/control/opt.out" ] && r=PASS || r=FAIL; row options decline - "binary_exit=$orc" "-" "$r"
if [ $HEAVY = 1 ]; then
  R=$BI/rh-mid/ref/proj; LP=$R/.lake/build/lib/lean
  for p in $R/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
  t0=$(date +%s.%N)
  "$EXS" --lean-path "$LP:$T33/lib/lean" --module Main --targets-file $BI/rh-mid/challenge/export-targets.txt \
      --toolchain "$T33" --project "$R" --out "$W/rhmid.out" --json "$W/rhmid.json" --threads 32 > /dev/null 2> "$W/rhmid.err"
  rc=$?; sec=$(echo "$(date +%s.%N) - $t0" | bc)
  [ $rc = 0 ] && cmp -s "$W/rhmid.out" $BI/rh-mid/ref/solution.export && r=PASS || r=FAIL
  row rh-mid identical "ref=original-Lean export" "stage_exit=$rc" "${sec}s" "$r"; rm -f "$W/rhmid.out"
fi
echo "RESULT: $([ $FAIL = 0 ] && echo PASS || echo FAIL)"
exit $FAIL
