#!/bin/bash
# tests/judge-args/run.sh [FASTVERIFY_ROOT]  -- regression test of judge argument handling
# in the judge scripts (check/sound/check-sound.sh, check-sound-svc.sh, check/lowmem/check-sound-lowmem.sh,
# check-sound-ultralowmem.sh). Fails on the earlier scripts, passes with the current ones.
#   padded/ rows: a zero-padded numeric option ('--threads 08', '--timeout 0900', '--mem-budget-mb 0900') must give a valid JSON
#          result with the plain number ("threads":8), '--threads 00' is refused, and a decline during argument parsing
#          still prints valid JSON.
#   pins/ rows: '--pins FILE' must be one of the judge's own pins*.env (after realpath): a self-consistent caller-made pins file
#          (fake comparator / kernels with matching sha256, a crafted evil_pins.env) and a byte-identical copy of the
#          package's pins file outside the package are refused (DECLINED, exit 2); a symlink that resolves to a package pins
#          file and the package's own pins-437.env still work
#          (fake_ccmp.sh / fake_plc.sh / fake_grz.sh below are the crafted fakes).
# Inputs: the package's pinned self-test files (check/sound/pins.env PIN selftest_*). Prints PASS/FAIL rows + RESULT line.
set -u
FV=$(readlink -f "${1:-$(dirname "$(readlink -f "$0")")/../..}")
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$FV/check/sound/pins.env"; }
GOOD=$(pin selftest_good); BAD=$(pin selftest_bad); CHAL=$(pin selftest_challenge); CFG=$(pin selftest_comparator)
# the work dir must be visible inside the judges' bwrap (which mounts tmpfs on /tmp, /home, /root, /run): /scratch or /var/tmp
WB=; for d in ${F2_TEST_WORKDIR:-} /scratch /var/tmp; do [ -d "$d" ] && [ -w "$d" ] && { WB=$d; break; }; done
[ -n "$WB" ] || { echo "FAIL setup: no writable /scratch or /var/tmp"; echo "RESULT pass=0 fail=1"; exit 1; }
W=$(mktemp -d "$WB/judge-args.XXXXXX"); trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1"; pass=$((pass+1)); }
no() { echo "FAIL $1: $2"; fail=$((fail+1)); }
CS=$FV/check/sound/check-sound.sh; SVC=$FV/check/sound/check-sound-svc.sh
LM=$FV/check/lowmem/check-sound-lowmem.sh; ULM=$FV/check/lowmem/check-sound-ultralowmem.sh
# js FILE -> "rc_json verdict threads" of the last stdout line ("BADJSON" if it does not parse)
js() { tail -n 1 "$1" | /usr/bin/python3 -I -c 'import json,sys
try: d=json.loads(sys.stdin.read())
except Exception: print("BADJSON - -"); sys.exit()
print(d.get("exit"), d.get("verdict"), d.get("threads"))'; }
row() {  # row NAME WANT_RC WANT_VERDICT WANT_THREADS(-=any) CMD...
  local n=$1 wrc=$2 wv=$3 wt=$4; shift 4; local f=$W/out.${1//\//_}.${n//\//_}
  "$@" > "$f.out" 2> "$f.err"; local rc=$?
  read -r jrc jv jt < <(js "$f.out")
  if [ "$rc" = "$wrc" ] && [ "$jrc" = "$wrc" ] && [ "$jv" = "$wv" ] && { [ "$wt" = - ] || [ "$jt" = "$wt" ]; }; then ok "$n"
  else no "$n" "rc=$rc json=($jrc $jv threads=$jt) want ($wrc $wv threads=$wt); $(tail -n 1 "$f.out" | cut -c1-220)"; fi
}

# ---------- zero-padded numeric options ----------
for j in CS SVC LM ULM; do
  s=${!j}
  row "padded/$j/threads-08" 0 ACCEPTED 8 "$s" "$GOOD" "$CHAL" "$CFG" --threads 08
  row "padded/$j/threads-00-refused" 2 DECLINED - "$s" "$GOOD" "$CHAL" "$CFG" --threads 00
  row "padded/$j/threads-08-then-bad-arg" 2 DECLINED None "$s" "$GOOD" "$CHAL" "$CFG" --threads 08 --no-such-option
  row "padded/$j/timeout-0900" 0 ACCEPTED 4 "$s" "$GOOD" "$CHAL" "$CFG" --threads 4 --timeout 0900
done
for j in LM ULM; do
  s=${!j}
  row "padded/$j/mem-budget-0900" 0 ACCEPTED 4 "$s" "$GOOD" "$CHAL" "$CFG" --threads 4 --mem-budget-mb 0900
done
# --kernel-grace / --kernel-jobs (check-sound.sh, -svc only) are capped at 9 digits like the
# other numeric options: an overlong value used to wrap in bash arithmetic (-8446744073709551617 for 19 nines; 20 nines wrap
# to a large POSITIVE --kernel-jobs that passed the >= 1 check); a padded 9-digit-or-less value still works.
for j in CS SVC; do
  s=${!j}
  row "padded/$j/kernel-grace-19-digits-refused" 2 DECLINED 4 "$s" "$GOOD" "$CHAL" "$CFG" --threads 4 --kernel-grace 9999999999999999999
  row "padded/$j/kernel-jobs-20-digits-refused" 2 DECLINED 4 "$s" "$GOOD" "$CHAL" "$CFG" --threads 4 --kernel-jobs 99999999999999999999
  row "padded/$j/kernel-grace-0900-kernel-jobs-008" 0 ACCEPTED 4 "$s" "$GOOD" "$CHAL" "$CFG" --threads 4 --kernel-grace 0900 --kernel-jobs 008
done

# ---------- a self-consistent fake pins file ----------
TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
cat > "$W/fake_ccmp.sh" <<'EOF'
#!/bin/sh
# Handles both check-sound.sh (TC CFG CHAL SOL) and check-sound-lowmem.sh (--compare-only CFG CHAL SOL)
for a do SOL=$a; done
case "$SOL" in
  *selftest*bad*|*bad_st.export)
    echo "error: Illegal axiom detected: 'fvCheat'"
    exit 1
    ;;
esac
echo "Comparison and axiom check passed!"
echo "Lean default kernel accepts the solution"
echo "gruszka (second kernel) kernel accepts the solution"
echo "Your solution is okay!"
if [ -n "${CCMP_LEANCHECKER:-}" ]; then
  "$CCMP_LEANCHECKER" "$SOL" >/dev/null 2>&1 || true
fi
python3 -I -c 'import json,sys,subprocess
c=json.load(open(sys.argv[1]))
for k,v in (c.get("external_kernels") or {}).items():
    subprocess.run(v+[sys.argv[2]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
' "$2" "$SOL" 2>/dev/null || true
exit 0
EOF
printf '#!/bin/sh\necho "Lean default kernel accepts the solution"\nexit 0\n' > "$W/fake_plc.sh"
printf '#!/bin/sh\necho "gruszka accepts"\nexit 0\n' > "$W/fake_grz.sh"
chmod 755 "$W/fake_ccmp.sh" "$W/fake_plc.sh" "$W/fake_grz.sh"
cp "$BAD" "$W/bad_st.export"; cp "$GOOD" "$W/good_st.export"
h() { sha256sum "$1" | cut -d' ' -f1; }
cat > "$W/evil_pins.env" <<EOF
SOUND_VERSION=evil-b4-demo
TC_VERSION=leanprover/lean4:v4.36.0
TC_LABEL=4.36
TC36=$TC36
PIN ccmp $(h "$W/fake_ccmp.sh") $W/fake_ccmp.sh
PIN ccmp_lowmem $(h "$W/fake_ccmp.sh") $W/fake_ccmp.sh
PIN pleanchecker $(h "$W/fake_plc.sh") $W/fake_plc.sh
PIN gruszka $(h "$W/fake_grz.sh") $W/fake_grz.sh
PIN selftest_comparator $(h "$CFG") $CFG
PIN selftest_challenge $(h "$CHAL") $CHAL
PIN selftest_good $(h "$W/good_st.export") $W/good_st.export
PIN selftest_bad $(h "$W/bad_st.export") $W/bad_st.export
EOF
for j in CS SVC LM; do
  s=${!j}
  row "pins/$j/evil-pins-bad-export-refused" 2 DECLINED 4 "$s" "$BAD" "$CHAL" "$CFG" --threads 4 --pins "$W/evil_pins.env"
done
row "pins/ULM/no-pins-option" 2 DECLINED 4 "$ULM" "$BAD" "$CHAL" "$CFG" --threads 4 --pins "$W/evil_pins.env"
# a byte-identical copy of the package's own pins file, outside the package: refused (only the package's files count)
cp "$FV/check/sound/pins.env" "$W/pins.env"; mkdir -p "$W/lm"; cp "$FV/check/lowmem/pins.env" "$W/lm/pins.env"
row "pins/CS/package-pins-copy-outside-refused" 2 DECLINED 4 "$CS" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$W/pins.env"
row "pins/SVC/package-pins-copy-outside-refused" 2 DECLINED 4 "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$W/pins.env"
row "pins/LM/package-pins-copy-outside-refused" 2 DECLINED 4 "$LM" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$W/lm/pins.env"
# the lowmem judge does not take the sound check's pins file (its own directory only)
row "pins/LM/sound-pins-refused" 2 DECLINED 4 "$LM" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$FV/check/sound/pins.env"
# controls: package pins files (directly, and through a symlink that resolves into the package) still work
ln -s "$FV/check/sound/pins-437.env" "$W/sym-pins-437.env"; ln -s "$FV/check/lowmem/pins.env" "$W/sym-lm-pins.env"
row "pins/CS/package-pins-437" 0 ACCEPTED 4 "$CS" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$FV/check/sound/pins-437.env"
row "pins/CS/symlink-into-package" 0 ACCEPTED 4 "$CS" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$W/sym-pins-437.env"
row "pins/SVC/package-pins" 0 ACCEPTED 4 "$SVC" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$FV/check/sound/pins.env"
row "pins/LM/symlink-into-package" 0 ACCEPTED 4 "$LM" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$W/sym-lm-pins.env"
row "pins/LM/package-pins-437" 0 ACCEPTED 4 "$LM" "$GOOD" "$CHAL" "$CFG" --threads 4 --pins "$FV/check/lowmem/pins-437.env"
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit $?
