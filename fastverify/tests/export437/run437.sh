#!/bin/bash
# tests/export437/run437.sh [WORK]  — component regression tests of the EXPORT stage for Lean 4.37.0-rc1
#
# The 4.33.1 suite (tests/export/run.sh) re-run on Lean 4.37.0-rc1, plus cases for what is new in 4.37
# (olean format v4, the per-module constant prefix trees of Lean PR #14362).  For each case, .olean files are built with
# the OFFICIAL Lean 4.37.0-rc1 (`lean -o`, some with -Ddebug.skipKernelTC=true), then
#   OFFICIAL = the release's bundled exporter $TC/bin/leanexport under env -i, LEAN_ABORT_ON_PANIC=1 (as bin/fastverify)
#   NATIVE   = export/export.sh (selects the 4.37 entry of components.json "natives_other"; exit 2 = declined)
#   STAGE    = export/export.sh --official-fallback (what a decline turns into)
# PASS rules: expect=identical -> NATIVE exit 0 and bytes == OFFICIAL (official exit 0);
#             expect=decline   -> NATIVE exit 2 (no output) and STAGE == OFFICIAL (same exit class, same bytes if exit 0);
#             expect=either    -> one of the two (crafted inputs where both behaviours are correct).
# Env: FV_TC437 = toolchain prefix (default ~/.elan/toolchains/leanprover--lean4---v4.37.0-rc1); FV_PKG = package root
# (default: this script's package).  Prints one TSV row per case; exit 0 iff all PASS.  Any host; ~1 min.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=${FV_PKG:-$(cd "$H/../.." && pwd)}
CASES=${FV_EXPORT_CASES:-$PKG/tests/export/cases}
W=${1:-${SCRATCH:-${TMPDIR:-/tmp}}/$(whoami)-fvtest/export437}
T=${FV_TC437:-${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.37.0-rc1}
EXS=$PKG/export/export.sh
OFF=$T/bin/leanexport
V=$(env -i PATH=/usr/bin:/bin "$T/bin/lean" --version) || { echo "no Lean at $T"; exit 2; }
NAT=$(/usr/bin/python3 -I -c 'import json,sys
for e in json.load(open(sys.argv[1])).get("natives_other", []):
    if e["lean_version"] == sys.argv[2]: print(e["path"]); break' "$PKG/export/components.json" "$V")
[ -n "$NAT" ] || { echo "no natives_other entry for '$V' in $PKG/export/components.json"; exit 2; }
TG="$(cat "$PKG/tests/export/targets-rh5.txt")"
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
FAIL=0
row() { printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$@"; [ "$6" = PASS ] || FAIL=1; }
build() {  # case dir, then "MOD[:skip]" ...
  local c=$1; shift; local b=$W/$c/build; mkdir -p "$b"; cp "$CASES/$c"/*.lean "$b/"
  for m in "$@"; do
    local fl=(); [ "${m#*:}" = skip ] && fl=(-Ddebug.skipKernelTC=true); m=${m%%:*}
    (cd "$b" && env -i PATH=$T/bin:/usr/bin:/bin "LEAN_PATH=$b:$T/lib/lean" $T/bin/lean "${fl[@]}" -o $m.olean $m.lean) > "$W/$c/build.$m.log" 2>&1 || echo "  (build of $c/$m exit $?)" >&2
  done
}
official() {  # case roots targets-file -> W/case/off.out, prints exit
  local c=$1 b=$W/$1/build; read -r -a R <<< "$2"; local TT=()
  if [ "${TNL:-0}" = 1 ]; then while IFS= read -r t || [ -n "$t" ]; do [ -n "$t" ] && TT+=("$t"); done < "$3"
  else read -r -d '' -a TT < "$3"; fi
  (cd "$b" && env -i PATH=$T/bin:/usr/bin:/bin HOME=/tmp "LEAN_PATH=$b:$T/lib/lean" LEAN_ABORT_ON_PANIC=1 "$OFF" "${R[@]}" -- "${TT[@]}") > "$W/$c/off.out" 2> "$W/$c/off.err"
  echo $?
}
stage() {  # case roots targets-file tag [extra]
  local c=$1 b=$W/$1/build roots=$2 tf=$3 tag=$4; shift 4
  local tflag=--targets-file; [ "${TNL:-0}" = 1 ] && tflag=--targets-nl
  "$EXS" --lean-path "$b:$T/lib/lean" --module "$roots" $tflag "$tf" --toolchain "$T" --project "$b" \
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
  local verdict=FAIL ident=no decl=no
  [ "$orc" = 0 ] && [ "$nrc" = 0 ] && cmp -s "$W/$c/native.out" "$W/$c/off.out" && [ $same_stage = yes ] && ident=yes
  [ "$nrc" = 2 ] && [ ! -e "$W/$c/native.out" ] && [ $same_stage = yes ] && decl=yes
  case "$exp" in identical) [ $ident = yes ] && verdict=PASS ;; decline) [ $decl = yes ] && verdict=PASS ;;
                 either) { [ $ident = yes ] || [ $decl = yes ]; } && verdict=PASS ;; esac
  row "$c" "expect=$exp" "official_exit=$orc" "native_exit=$nrc" "stage_exit=$src${why:+ ($why)}" "$verdict"
}
printf 'case\texpect\tofficial\tnative\tstage(+decline reason)\tresult\n'
mkdir -p "$W/control/build"; echo "Nat.add List.map" > "$W/control/tg"
runcase control identical Init "$W/control/tg"
build 008 Challenge:skip Main:skip;   echo "$TG" > "$W/008/tg"; runcase 008 decline Main "$W/008/tg"
build 010 Challenge Main;             echo "$TG" > "$W/010/tg"; runcase 010 either Main "$W/010/tg"
build 013 A B C D
echo foo > "$W/013/tg-foo"; echo ax > "$W/013/tg-ax"
mkdir -p "$W/013b" "$W/013c"; ln -s "$W/013/build" "$W/013b/build"; ln -s "$W/013/build" "$W/013c/build"
runcase 013b decline "A B" "$W/013/tg-foo"
runcase 013c decline "C D" "$W/013/tg-ax"
build dupeq E F; echo "dupThm dupB dupC" > "$W/dupeq/tg"; runcase dupeq identical "E F" "$W/dupeq/tg"
build 018 N;                          echo main_thm > "$W/018/tg"; runcase 018 decline N "$W/018/tg"
build 030 Challenge:skip Main:skip;   echo "$TG" > "$W/030/tg"; runcase 030 decline Main "$W/030/tg"
build 033 Challenge:skip Main:skip;   echo "$TG" > "$W/033/tg"; runcase 033 decline Main "$W/033/tg"
build githash G; echo gThm > "$W/githash/tg"
printf '0000000000000000000000000000000000000000' | dd of="$W/githash/build/G.olean" bs=1 seek=40 conv=notrunc status=none
runcase githash decline G "$W/githash/tg"
build ir M; echo modThm > "$W/ir/tg"; runcase ir identical M "$W/ir/tg"
for v in irmissing irgithash irsigplanted; do mkdir -p "$W/$v"; cp -r "$W/ir/build" "$W/$v/build"; done
rm -f "$W/irmissing/build/M.ir"
printf '0000000000000000000000000000000000000000' | dd of="$W/irgithash/build/M.ir" bs=1 seek=40 conv=notrunc status=none
runcase irmissing decline M "$W/ir/tg"
runcase irgithash decline M "$W/ir/tg"
rm -rf "$W/irsigplanted/build"; cp -r "$W/githash/build" "$W/irsigplanted/build"
(cd "$W/irsigplanted/build" && rm -f G.olean && env -i PATH=$T/bin:/usr/bin:/bin "LEAN_PATH=$W/irsigplanted/build:$T/lib/lean" $T/bin/lean -o G.olean G.lean > /dev/null 2>&1 && echo garbage > G.ir.sig)
runcase irsigplanted decline G "$W/githash/tg"
mkdir -p "$W/missing"; ln -s "$W/control/build" "$W/missing/build"; echo "Nat.add Nat.doesNotExist" > "$W/missing/tg"
runcase missing decline Init "$W/missing/tg"
build kitchen K; cp "$CASES/kitchen/targets.txt" "$W/kitchen/tg"
TNL=1 runcase kitchen identical K "$W/kitchen/tg"
mkdir -p "$W/unsafe-target"; ln -s "$W/kitchen/build" "$W/unsafe-target/build"; printf 'thm1\nuns\n' > "$W/unsafe-target/tg"
TNL=1 runcase unsafe-target decline K "$W/unsafe-target/tg"
tr '\n' ' ' < "$W/kitchen/tg" > "$W/kitchen/tg-ws"; mkdir -p "$W/kitchen-ws"; ln -s "$W/kitchen/build" "$W/kitchen-ws/build"
nrc=$(stage kitchen-ws K "$W/kitchen/tg-ws" native); [ "$nrc" = 2 ] && r=PASS || r=FAIL
row kitchen-ws decline - "native_exit=$nrc" "(split «» name)" "$r"
c="space dir"; b="$W/$c/build"; mkdir -p "$b"; cp "$CASES/githash/G.lean" "$b/"
(cd "$b" && env -i PATH=$T/bin:/usr/bin:/bin LEAN_PATH="$b:$T/lib/lean" $T/bin/lean -o G.olean G.lean) > /dev/null 2>&1
echo gThm > "$W/$c/tg"; runcase "space dir" identical G "$W/$c/tg"
# ---- new in 4.37: olean format v4 and the constant prefix trees (tests/export437/oleanv4.py crafts the copies);
# skipped for releases with the older olean format (FV_TC437 pointing at e.g. 4.36.0: the 4.33.1-era cases above only)
OV=$(od -An -tu1 -j5 -N1 "$W/kitchen/build/K.olean" | tr -d ' ')
if [ "$OV" = 4 ]; then
for a in data-size closures trie-none trie-hash trie-unsort trie-swapvals; do
  mkdir -p "$W/v4-$a"; cp -r "$W/kitchen/build" "$W/v4-$a/build"; /usr/bin/python3 -I "$H/oleanv4.py" "$W/v4-$a/build/K.olean" "$a"
done
for a in data-size closures trie-none trie-hash trie-unsort; do TNL=1 runcase "v4-$a" decline K "$W/kitchen/tg"; done
# values swapped between two leaves of the tree (keys != embedded names): the official lookup follows the TREE; the
# native exporter must follow it too (identical) or decline
TNL=1 runcase v4-trie-swapvals either K "$W/kitchen/tg"
# a private part whose isModule flag differs from the .olean part's (getData? vs irData? disagree): decline
mkdir -p "$W/v4-modflag"; cp -r "$W/ir/build" "$W/v4-modflag/build"
/usr/bin/python3 -I - "$W/v4-modflag/build/M.olean.private" <<'PY'
import struct, sys
p = sys.argv[1]; b = bytearray(open(p, "rb").read()); base = struct.unpack_from("<Q", b, 0x50)[0]
md = struct.unpack_from("<Q", b, 0x60)[0] - base
assert b[md + 7] == 0 and b[md + 6] == 7
b[md + 8 + 8 * 7] = 0   # ModuleData.isModule (the only scalar field) := false
open(p, "wb").write(b)
PY
runcase v4-modflag decline M "$W/ir/tg"
else echo "(olean format $OV: the v4 cases are skipped)"; fi
# closure guard: a fake native exporter that drops one declaration must be caught (export.sh's guard is release-independent)
mkdir -p "$W/guard/stage"; cp "$EXS" "$W/guard/stage/export.sh"
cat > "$W/guard/fake-native.sh" <<FAKE
#!/bin/bash
t=\$(mktemp /tmp/fake.XXXXXX); "$NAT" "\$@" > "\$t" 2> "\$t.err"; rc=\$?
if [ "\$*" = "Init -- Nat.add" ]; then cat "\$t"; else awk 'BEGIN{d=0} /^\{"def":/ && d==0 {d=1; next} {print}' "\$t"; fi
# stderr only after stdout: export.sh returns early once the native log says 'done' (the real binary has written
# everything by then; this wrapper writes afterwards) - forwarding the log first made the test timing-dependent
cat "\$t.err" >&2; rm -f "\$t" "\$t.err"; exit \$rc
FAKE
chmod +x "$W/guard/fake-native.sh"
/usr/bin/python3 -I - "$PKG/export/components.json" "$W/guard/stage/components.json" "$W/guard/fake-native.sh" "$V" <<'PY'
import hashlib, json, sys
c = json.load(open(sys.argv[1]))
for e in c["natives_other"]:
    if e["lean_version"] == sys.argv[4]:
        e["path"] = sys.argv[3]; e["sha256"] = hashlib.sha256(open(sys.argv[3], "rb").read()).hexdigest()
json.dump(c, open(sys.argv[2], "w"))
PY
grc=$("$W/guard/stage/export.sh" --lean-path "$T/lib/lean" --module Init --targets-file "$W/control/tg" --toolchain "$T" \
      --project "$W/control/build" --out "$W/guard/out" --json "$W/guard/out.json" > /dev/null 2>&1; echo $?)
gwhy=$(/usr/bin/python3 -I -c 'import json,sys; print((json.load(open(sys.argv[1]))["native"].get("decline_reason") or "")[:70])' "$W/guard/out.json" 2>/dev/null)
[ "$grc" = 2 ] && [ ! -e "$W/guard/out" ] && case "$gwhy" in "closure guard:"*) true;; *) false;; esac && r=PASS || r=FAIL
row closure-guard decline - "stage_exit=$grc" "($gwhy)" "$r"
# --official-fallback for a release WITHOUT a natives_other entry (4.33.1's default entry does have one; use 4.35.0 if
# installed, else skip): the stage must decline (exit 2), not run the official exporter of another release
T36=${FV_TC_NOENTRY:-${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.35.0}
if [ -x "$T36/bin/lean" ] && ! grep -q "$(env -i PATH=/usr/bin:/bin "$T36/bin/lean" --version)" "$PKG/export/components.json"; then
  orc=$("$EXS" --lean-path "$T36/lib/lean" --module Init --targets-file "$W/control/tg" --toolchain "$T36" --project "$W/control/build" \
        --out "$W/other.out" --json "$W/other.json" --official-fallback > /dev/null 2>&1; echo $?)
  [ "$orc" = 2 ] && [ ! -e "$W/other.out" ] && r=PASS || r=FAIL
  row other-release-fallback decline - "stage_exit=$orc" "(no entry for $(basename "$T36"))" "$r"
fi
orc=$(cd "$W/control/build" && env -i PATH=$T/bin:/usr/bin:/bin LEAN_PATH=$W/control/build:$T/lib/lean "$NAT" --export-mdata Init -- Nat.add > "$W/control/opt.out" 2>/dev/null; echo $?)
[ "$orc" = 2 ] && [ ! -s "$W/control/opt.out" ] && r=PASS || r=FAIL; row options decline - "binary_exit=$orc" "-" "$r"
# whole-environment mode (no target list): not supported natively for olean format 4 (4.37) -> the binary declines; for the
# older format (e.g. 4.36.0) the native whole-env order must equal the official exporter's
orc=$(cd "$W/control/build" && env -i PATH=$T/bin:/usr/bin:/bin LEAN_PATH=$W/control/build:$T/lib/lean "$NAT" Init > "$W/control/whole.out" 2>/dev/null; echo $?)
if [ "$OV" = 4 ]; then [ "$orc" = 2 ] && r=PASS || r=FAIL; row whole-env decline - "binary_exit=$orc" "-" "$r"
else
  wrc=$(cd "$W/control/build" && env -i PATH=$T/bin:/usr/bin:/bin LEAN_PATH=$W/control/build:$T/lib/lean "$OFF" Init > "$W/control/whole.off" 2>/dev/null; echo $?)
  [ "$orc" = 0 ] && [ "$wrc" = 0 ] && cmp -s "$W/control/whole.out" "$W/control/whole.off" && r=PASS || r=FAIL
  row whole-env identical "official_exit=$wrc" "binary_exit=$orc" "(Init, $(stat -c %s "$W/control/whole.off") B)" "$r"; rm -f "$W/control/whole.out" "$W/control/whole.off"
fi
echo "RESULT: $([ $FAIL = 0 ] && echo PASS || echo FAIL)"
exit $FAIL
