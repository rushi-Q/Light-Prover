#!/bin/bash
# tests/pins-confinement/run.sh [WORKDIR] -- regression test: front ends never pass a caller --pins file to the judges (HIGH,
# Boundary B4): bin/fv check (default, --low-mem, --frontier) and tools/ci-action/fv-ci.sh passed ANY caller --pins file
# to the judge scripts, which verify their binaries only against the hashes inside that same file: a self-consistent
# pins file with fake ccmp/pleanchecker/gruszka scripts made `bin/fv check` report ACCEPTED (reward 1.0, trust sound) for
# the self-test's bad export (illegal axiom fvCheat; official lake comparator REJECTS), while bin/fastverify refuses such
# a --pins (exit 2). The reproduction is rebuilt below.
# The judge scripts themselves (check/*/check-*.sh accepting any --pins) are trusted code: not tested here.
# Rows: fv-check/{default,low-mem,frontier}-evil-pins (exit 2 ERROR refused, no judge run), fv-check/symlink-named-pins,
#   fv-ci/evil-pins (exit 2), fvwork/serve-evil-pins (refused), unit/resolve-* (the package's own pins files, the 436 /
#   437 shorthands and a package-relative path still resolve). Exit 0 iff every row PASS. FV_ROOT=<package> for another copy.
set -u
export FV_EXPERIMENTAL_CI=1   # the CI gate (fv-ci.sh / bin/fv ci) is EXPERIMENTAL in v0.1 and runs only when opted in
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/pins-confinement.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$FV/check/sound/pins.env"; }
ST_CH=$(pin selftest_challenge); ST_CFG=$(pin selftest_comparator); ST_BAD=$(pin selftest_bad); ST_GOOD=$(pin selftest_good)
TC36=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
# the evidence's self-consistent attacker pins file (fake judge legs that accept everything but the self-test's bad export)
cat > "$W/fake_ccmp.sh" <<'EOF'
#!/bin/sh
# (the evidence's fake ccmp, verbatim: also drives the leg / external-kernel hooks so check-sound.sh's default path accepts)
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
chmod 755 "$W"/fake_*.sh
cp "$ST_BAD" "$W/bad_st.export"; cp "$ST_GOOD" "$W/good_st.export"; cp "$ST_BAD" "$W/victim.export"
s() { sha256sum "$1" | cut -d' ' -f1; }
cat > "$W/evil_pins.env" <<EOF
SOUND_VERSION=evil-b4-demo
TC_VERSION=leanprover/lean4:v4.36.0
TC_LABEL=4.36
TC36=$TC36
PIN ccmp $(s "$W/fake_ccmp.sh") $W/fake_ccmp.sh
PIN ccmp_lowmem $(s "$W/fake_ccmp.sh") $W/fake_ccmp.sh
PIN pleanchecker $(s "$W/fake_plc.sh") $W/fake_plc.sh
PIN gruszka $(s "$W/fake_grz.sh") $W/fake_grz.sh
PIN selftest_comparator $(s "$ST_CFG") $ST_CFG
PIN selftest_challenge $(s "$ST_CH") $ST_CH
PIN selftest_good $(s "$W/good_st.export") $W/good_st.export
PIN selftest_bad $(s "$W/bad_st.export") $W/bad_st.export
EOF
mkdir -p "$W/fakepkg/check/sound"; ln -s "$W/evil_pins.env" "$W/fakepkg/check/sound/pins-evil.env"
PIN=$(s "$ST_CH"); CFGPIN=$(s "$ST_CFG")
fvcheck() {  # fvcheck ROW PINS [extra]: bin/fv check must refuse (exit 2, ERROR, 'Boundary B4'), the judge never decides
  local row=$1 pf=$2; shift 2
  "$FV/bin/fv" check "$W/victim.export" --challenge-export "$ST_CH" --comparator-json "$ST_CFG" --challenge-sha256 "$PIN" \
    --comparator-sha256 "$CFGPIN" --pins "$pf" --threads 2 --json "$@" > "$W/$row.json" 2> "$W/$row.err"; local rc=$?
  local v; v=$(python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j["verdict"], j["accepted"], "B4" in j["reason"])' "$W/$row.json" 2>/dev/null)
  [ "$rc" = 2 ] && [ "$v" = "ERROR False True" ] && ok "fv-check/$row" "exit 2, refused (Boundary B4)" \
    || ko "fv-check/$row" "exit $rc '$v' $(tail -c 200 "$W/$row.err")"
}
fvcheck default-evil-pins "$W/evil_pins.env"
fvcheck low-mem-evil-pins "$W/evil_pins.env" --low-mem
fvcheck frontier-evil-pins "$W/evil_pins.env" --frontier
fvcheck symlink-named-pins "$W/fakepkg/check/sound/pins-evil.env"
fvcheck confined-but-missing-pins "$FV/check/sound/pins-does-not-exist.env"
mkdir -p "$W/ci"; cp -a "$HERE/../unsafe-accept/data/chal437" "$W/ci_chal" 2>/dev/null || mkdir -p "$W/ci_chal"
"$FV/tools/ci-action/fv-ci.sh" --fv-root "$FV" --project "$W/ci_chal" --challenge "$W/ci_chal" --challenge-sha256 "$PIN" \
  --comparator-sha256 "$( [ -f "$W/ci_chal/comparator.json" ] && s "$W/ci_chal/comparator.json" || echo "$CFGPIN")" \
  --pins "$W/evil_pins.env" --out-dir "$W/ci" > "$W/ci.log" 2>&1; rc=$?
[ "$rc" = 2 ] && grep -q "Boundary B4" "$W/ci.log" && ok fv-ci/evil-pins "exit 2, refused (Boundary B4)" || ko fv-ci/evil-pins "exit $rc $(tail -c 200 "$W/ci.log")"
# the state records the comparator pin the CALLER gave at init (fvwork refuses a state without it)
mkdir -p "$W/fvw"; printf '{"fv": "%s", "threads": 2, "comparator_sha256": "%s", "comparator_pin_from_caller": true}\n' "$FV" "$CFGPIN" > "$W/fvw/config.json"
timeout 60 python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$W/fvw" --check sound --pins "$W/evil_pins.env" > "$W/fvw.log" 2>&1; rc=$?
[ "$rc" != 0 ] && grep -q "Boundary B4" "$W/fvw.log" && ok fvwork/serve-evil-pins "exit $rc, refused (Boundary B4)" || ko fvwork/serve-evil-pins "exit $rc $(tail -c 200 "$W/fvw.log")"
r=$(python3 -I -B - "$FV" <<'PY' 2>&1
import os, sys
sys.dont_write_bytecode = True
fv = sys.argv[1]
sys.path.insert(0, os.path.join(fv, "tools", "cli"))
import fv_cli as c
sd = os.path.realpath(os.path.join(fv, "check", "sound")); ld = os.path.realpath(os.path.join(fv, "check", "lowmem"))
for arg, low, want in (("437", False, os.path.join(sd, "pins-437.env")), ("436", False, os.path.join(sd, "pins.env")),
                       (os.path.join(fv, "check", "sound", "pins-437.env"), False, os.path.join(sd, "pins-437.env")),
                       ("check/sound/pins-437.env", False, os.path.join(sd, "pins-437.env")),
                       ("437", True, os.path.join(ld, "pins-437.env"))):
    if not os.path.isfile(want):
        print("SKIP %s" % arg); continue
    got = c._resolve_pins_arg(arg, lowmem=low)
    print(("PASS" if got == want else "FAIL") + " unit/resolve-%s%s: %s" % (arg.replace("/", "_"), "-lowmem" if low else "", got))
PY
)
while read -r ln; do case "$ln" in PASS*) ok "$(echo "${ln#PASS }" | cut -d: -f1)" "$(echo "$ln" | cut -d: -f2-)";; SKIP*) echo "$ln";;
  *) ko unit/resolve "$ln";; esac; done <<< "$r"
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
