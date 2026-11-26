#!/bin/bash
# check/sound/test/svc.sh — regression test of the SERVICE VARIANT check-sound-svc.sh (--integrity-cache).
# ~2-3 min (copies the official 4.36 tree once, reflink if the filesystem has it).
# Every case prints 'PASS|FAIL <case>: ...'; last line 'RESULT pass=N fail=M'; exit 0 iff all PASS.
# What is tested: (1) verdicts of check-sound-svc.sh with and without the cache = check-sound.sh's on the self-test exports
# and their mutants (good / extra axiom / kernel-invalid / changed statement / missing declaration / missing target);
# (2) the integrity cache: preflight writes the record after a full verification; a judged run uses it (basis says so);
# a touched pinned file (same content) -> full verification -> ACCEPTED and the record is refreshed; a pinned file whose
# content changed (also with the mtime restored: ctime still changes) -> full verification -> DECLINED; an extra file in the
# 4.36 tree -> DECLINED; a record with another key, a symlinked record, a symlinked pin path -> no hit; a cache dir
# with group/other access -> DECLINED
# pins.env changed -> no hit. All on PRIVATE copies (pinned binaries, pins.env, 4.36 tree):
# the shared pinned files are never modified.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); PKG=$(cd "$H/../.." && pwd)
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$H/pins.env"; }
GOOD=$(pin selftest_good); BAD=$(pin selftest_bad); CHAL=$(pin selftest_challenge); CFG=$(pin selftest_comparator)
mkdir -p "${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}" 2>/dev/null   # the parent of the work dir may not exist yet
W=$(mktemp -d "${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}/checkSoundSvc-test.XXXXXX") || exit 2
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
fails=0; passes=0
ok() { echo "PASS $1: $2"; passes=$((passes+1)); }
no() { echo "FAIL $1: $2"; fails=$((fails+1)); }
run() {  # run SCRIPT ARGS... -> sets RC, OUT (last JSON line)
  "$@" > "$W/out" 2> "$W/err"; RC=$?; OUT=$(tail -1 "$W/out")
}
field() { printf '%s' "$OUT" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get(sys.argv[1],""))' "$1" 2>/dev/null; }
expect() {  # expect NAME RC BASIS_REGEX(or '') SCRIPT ARGS...
  local name=$1 want=$2 bre=$3; shift 3
  run "$@"
  local basis reason; basis=$(field basis); reason=$(field reason)
  if [ "$RC" = "$want" ] && { [ -z "$bre" ] || printf '%s' "$basis $reason" | grep -qE "$bre"; }; then
    ok "$name" "exit $RC :: ${reason:0:110}"
  else
    no "$name" "expected exit $want (basis ~ '$bre'), got $RC :: basis='${basis:0:90}' reason='${reason:0:200}'"
  fi
}
# ---- mutants of the good self-test export (as check/sound/test/run.sh) ----
sed 's/^{"app":{"arg":518,"fn":526},"ie":527}$/{"app":{"arg":512,"fn":526},"ie":527}/' "$GOOD" > "$W/kernel-bad.export"
sed 's/^{"ie":520,"natVal":"4"}$/{"ie":520,"natVal":"5"}/' "$GOOD" > "$W/stmt-bad.export"
grep -v '^{"def":{"all":\[2880\]' "$GOOD" > "$W/missing.export"
printf '%s' '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":["fvSelfTest","fvNoSuchTheorem"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}' > "$W/mt.json"
# ---- a private package copy: check/sound (both scripts), lib/toolchain.py, toolchains/, config/components.json; the
# pinned files and the 4.36 tree copied into $W (the copy's pins.env + components.json point there) ----
D=$W/pkg; mkdir -p "$D/check" "$D/lib" "$D/config" "$W/pins"
cp -r "$H" "$D/check/sound"; cp -r "$H/../xversion" "$D/check/"; cp "$PKG/lib/toolchain.py" "$D/lib/"; cp -r "$PKG/toolchains" "$D/"
TC36=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$PKG/config/components.json")
cp -a --reflink=auto "$TC36" "$W/tc36" || { no setup "cannot copy the 4.36 tree"; echo "RESULT pass=$passes fail=$fails"; exit 1; }
python3 -I - "$PKG/config/components.json" "$D/config/components.json" "$W/tc36" <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); c["comparator"]["prefix"] = sys.argv[3]; json.dump(c, open(sys.argv[2], "w"), indent=1)
PY
: > "$D/check/sound/pins.env.new"
while IFS= read -r ln; do
  set -- $ln
  if [ "${1:-}" = PIN ]; then cp --reflink=auto "$4" "$W/pins/$2"; chmod 555 "$W/pins/$2"; echo "PIN $2 $3 $W/pins/$2"; else printf '%s\n' "$ln"; fi
done < "$H/pins.env" > "$D/check/sound/pins.env.new"
mv "$D/check/sound/pins.env.new" "$D/check/sound/pins.env"
SVC=$D/check/sound/check-sound-svc.sh; ORIG=$D/check/sound/check-sound.sh
IC=$W/ic; mkdir -m 700 "$IC"
# ---- (1) verdict equality: orig / svc without cache / svc with a cache hit ----
expect preflight-writes-record 0 'record written' "$SVC" --preflight --integrity-cache "$IC"
[ -f "$IC/integrity.record" ] && ok record-exists "$(cut -c1-40 "$IC/integrity.record")..." || no record-exists "no record"
for c in "good:$GOOD:$CFG:0" "bad-axiom:$BAD:$CFG:1" "kernel-invalid:$W/kernel-bad.export:$CFG:1" \
         "statement-changed:$W/stmt-bad.export:$CFG:1" "missing-declaration:$W/missing.export:$CFG:1" "missing-target:$GOOD:$W/mt.json:1"; do
  IFS=: read -r n e cf want <<< "$c"
  run "$ORIG" "$e" "$CHAL" "$cf" --threads 4; r0=$RC
  run "$SVC" "$e" "$CHAL" "$cf" --threads 4; r1=$RC
  run "$SVC" "$e" "$CHAL" "$cf" --threads 4 --integrity-cache "$IC"; r2=$RC; b2=$(field basis)
  if [ "$r0" = "$want" ] && [ "$r1" = "$want" ] && [ "$r2" = "$want" ] && printf '%s' "$b2" | grep -q 'stamp of the fully verified'; then
    ok "verdict-$n" "orig=$r0 svc=$r1 svc+cache(hit)=$r2"
  else no "verdict-$n" "orig=$r0 svc=$r1 svc+cache=$r2 want=$want basis='${b2:0:80}'"; fi
done
# ---- (2) integrity cache ----
expect hit-good 0 'stamp of the fully verified' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
sleep 0.05; touch "$W/pins/ccmp"
expect touched-pin-full-verify 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
expect touched-pin-record-refreshed 0 'stamp of the fully verified' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
cp -p "$W/pins/gruszka" "$W/gruszka.orig"; chmod u+w "$W/pins/gruszka"; printf 'x' >> "$W/pins/gruszka"; chmod 555 "$W/pins/gruszka"
expect changed-pin-declined 2 'sha256 mismatch' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
chmod u+w "$W/pins/gruszka"; cp "$W/gruszka.orig" "$W/pins/gruszka"; chmod 555 "$W/pins/gruszka"
expect restored-pin-full-verify 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
# content change with the mtime restored (touch -r): the ctime still changes
cp -p "$W/pins/ccmp" "$W/ccmp.orig"; chmod u+w "$W/pins/ccmp"
python3 -I -c 'import sys; f=open(sys.argv[1],"r+b"); f.seek(-1,2); b=f.read(1); f.seek(-1,2); f.write(bytes([b[0]^1])); f.close()' "$W/pins/ccmp"
touch -r "$W/ccmp.orig" "$W/pins/ccmp"; chmod 555 "$W/pins/ccmp"; touch -r "$W/ccmp.orig" "$W/pins/ccmp"
expect changed-pin-mtime-restored-declined 2 'sha256 mismatch' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
chmod u+w "$W/pins/ccmp"; cp "$W/ccmp.orig" "$W/pins/ccmp"; chmod 555 "$W/pins/ccmp"
expect restored-ccmp-full-verify 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
# an extra file in the official 4.36 tree -> the full tree verification refuses it
touch "$W/tc36/bin/extra-file"
expect extra-tree-file-declined 2 'does not verify' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
rm -f "$W/tc36/bin/extra-file"
expect tree-restored-full-verify 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
# a record with another key (e.g. written for another pin set) is not used
read -r k s < "$IC/integrity.record"; printf '%s %s\n' "0000000000000000000000000000000000000000000000000000000000000000" "$s" > "$IC/integrity.record"
expect other-key-no-hit 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
# a symlinked record is not used
mv "$IC/integrity.record" "$W/rec"; ln -s "$W/rec" "$IC/integrity.record"
expect symlink-record-no-hit 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
[ -L "$IC/integrity.record" ] && no symlink-record-replaced "still a symlink" || ok symlink-record-replaced "the full verification wrote a regular record"
# pins.env changed (a comment line): another key -> no hit
echo "# changed" >> "$D/check/sound/pins.env"
expect pins-env-changed-no-hit 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
# a pinned path that is a symlink (found in review): the cache is neither used nor written (full verification every run)
mv "$W/pins/gruszka" "$W/gruszka.real"; ln -s "$W/gruszka.real" "$W/pins/gruszka"
expect symlinked-pin-full-verify 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
expect symlinked-pin-full-verify-again 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
rm "$W/pins/gruszka"; mv "$W/gruszka.real" "$W/pins/gruszka"
expect pin-regular-again-full 0 'integrity: full verification' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
expect pin-regular-again-hit 0 'stamp of the fully verified' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
# cache dir with group/other access -> refused (no verdict)
chmod 755 "$IC"
expect cache-dir-mode-declined 2 'mode 700' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC"
chmod 700 "$IC"
expect cache-missing-dir-declined 2 'not a directory' "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --integrity-cache "$W/nonexistent"
# a hit still runs the self-test: a broken self-test pin (fake gruszka failing it) -> DECLINED even with a valid record?
# (a changed pin can never hit; covered above). The preflight always verifies fully:
expect preflight-full-again 0 'verified fully' "$SVC" --preflight --integrity-cache "$IC"
echo "RESULT pass=$passes fail=$fails"
[ "$fails" = 0 ]
