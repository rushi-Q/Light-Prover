#!/bin/bash
# tests/incr-cold-path/run.sh [FV_ROOT] [WORK] — regression rows: `fv verify --incr-base` once
# rebuilt edited modules with a hard-coded Lean 4.33.1 (bin/fv's env -i drops INCR_TC) and reported the failed UNTRUSTED
# incremental build as REJECTED, trust sound, exit 1, empty reason, for every valid edit of a 4.36 / 4.37 project.
# Every bin/fv / incr-reverify.sh run is inside bwrap (no network, / read-only, private /tmp, only WORK writable). HOME is the
# real home for most rows, as for a user (the earlier package then showed the false REJECTED). Data: ../cli-mcp/data.
# Non-guard rows FAIL on the earlier tree and PASS now. Output: PASS/FAIL rows, then "RESULT: N PASS M FAIL".
set -u
HERE=$(cd "$(/usr/bin/dirname "$(/usr/bin/readlink -f "$0")")" && pwd)
FV=$(cd "${1:-$HERE/../..}" && pwd)
WORK=${2:-}
[ -n "$WORK" ] || WORK=$(mktemp -d /tmp/incr-cold-path.XXXXXX)
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
DATA=$HERE/../cli-mcp/data
P436=dae541f9e5e539b6251d3cc6249fa0b26469495e2ca95acac7c32786a0452a48
P437=76d3b313a7fa540eeb2c41393314fc522c1e9ea6293b88474f2a566cd3835d71
TC436=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.36.0"]["prefix"])' "$FV/config/components.json")
TC433=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json")
NPASS=0; NFAIL=0
pass() { echo "PASS $1"; NPASS=$((NPASS+1)); }
fail() { echo "FAIL $1: $2"; NFAIL=$((NFAIL+1)); }
# sbx HOMEDIR [--env K V]... -- cmd... : bwrap, no network, WORK writable
sbx() {
  local h=$1; shift; local ev=()
  while [ "$1" = "--env" ]; do ev+=(--setenv "$2" "$3"); shift 3; done
  [ "$1" = "--" ] && shift
  /usr/bin/bwrap --die-with-parent --unshare-all --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --bind "$WORK" "$WORK" \
    --clearenv --setenv PATH /usr/bin:/bin --setenv HOME "$h" --setenv LANG C.UTF-8 --setenv LEAN_NUM_THREADS 4 "${ev[@]}" \
    --chdir "$WORK" "$@"
}
jq_() { /usr/bin/python3 -I -c '
import json, sys
try:
    d = json.load(open(sys.argv[1], encoding="utf-8"))
except Exception:
    print("NOJSON"); sys.exit(0)
print(eval(sys.argv[2]))' "$1" "$2" 2>&1; }
FVB=$FV/bin/fv
echo "# incr-cold-path: FV_ROOT=$FV WORK=$WORK"
# projects: valid base, valid edit (proof term -> tactic), sorry edit, edit that does not compile
mk() { mkdir -p "$WORK/$1"; cp "$DATA/$2"/{lakefile.toml,lean-toolchain,lake-manifest.json} "$WORK/$1/"; echo "$3" > "$WORK/$1/Main.lean"; }
mk Main436 main436 '@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := Nat.add_zero n'
mk Edit436 main436 '@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := by simp'
mk Cheat436 main436 '@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := sorry'
mk Broken436 main436 '@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := Nat.add_zer n'
mk Main437 main437 '@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := Nat.add_zero n'
mk Edit437 main437 '@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := by simp'
mkdir -p "$WORK/C436" "$WORK/C437"
cp "$DATA/c436"/{challenge.export,comparator.json,lean-toolchain,lakefile.toml,lake-manifest.json,Challenge.lean} "$WORK/C436/"
cp "$DATA/c437"/{challenge.export,comparator.json,lean-toolchain,lakefile.toml,lake-manifest.json,Challenge.lean} "$WORK/C437/"
# base runs (cold, --keep-work), as documented for --incr-base
CS436=$(/usr/bin/sha256sum "$WORK/C436/comparator.json" | cut -d' ' -f1); CS437=$(/usr/bin/sha256sum "$WORK/C437/comparator.json" | cut -d' ' -f1)   # comparator pins
sbx "$HOME" -- "$FVB" verify "$WORK/Main436" -c "$WORK/C436" --challenge-sha256 $P436 --comparator-sha256 $CS436 --preset sound --keep-work --out "$WORK/base436" --json --threads 4 > "$WORK/base436.json" 2> "$WORK/base436.err"
sbx "$HOME" -- "$FVB" verify "$WORK/Main437" -c "$WORK/C437" --challenge-sha256 $P437 --comparator-sha256 $CS437 --keep-work --out "$WORK/base437" --json --threads 4 > "$WORK/base437.json" 2> "$WORK/base437.err"
v=$(jq_ "$WORK/base436.json" '(d.get("verdict"), d.get("exit_code"))'); w=$(jq_ "$WORK/base437.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$v" = "('ACCEPTED', 0)" ] && [ "$w" = "('ACCEPTED', 0)" ]; then pass cold-base-runs-accepted-guard; else fail cold-base-runs-accepted-guard "4.36 $v 4.37 $w"; fi
# a copy of the 4.36 base whose fast-exact plugin is corrupt: the UNTRUSTED incremental build of a VALID edit fails (build1)
cp -a "$WORK/base436" "$WORK/base436-badplugin"
head -c 4096 /dev/zero > "$WORK/base436-badplugin/log/build-fast/fastexact/libLightFastExact.so"

incr() {   # incr NAME HOMEDIR PROJECT CHALLENGE PIN BASE [TRY]
  sbx "$2" -- "$FVB" verify "$WORK/$3" -c "$WORK/$4" --challenge-sha256 "$5" --comparator-sha256 "$(/usr/bin/sha256sum "$WORK/$4/comparator.json" | cut -d' ' -f1)" \
    --incr-base "$WORK/$6" --out "$WORK/o-$1${7:-}" --json --threads 4 \
    > "$WORK/$1.json" 2> "$WORK/$1.err"; echo $?
}
# (v0.1) --incr-base takes the cold path with a warning: the same verification as without it
rc=$(incr edit436 "$HOME" Edit436 C436 $P436 base436)
v=$(jq_ "$WORK/edit436.json" '(d.get("verdict"), d.get("exit_code"), d.get("trust"), "experimental in v0.1 and was not used" in json.dumps(d))')
if [ "$rc" = 0 ] && [ "$v" = "('ACCEPTED', 0, 'sound', True)" ]; then pass v01/incr-base-436-valid-edit-cold-path-accepted-with-warning
else fail v01/incr-base-436-valid-edit-cold-path-accepted-with-warning "rc=$rc (verdict, exit, trust, warned)=$v"; fi

rc=$(incr edit436t /tmp Edit436 C436 $P436 base436); v=$(jq_ "$WORK/edit436t.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$rc" = 0 ] && [ "$v" = "('ACCEPTED', 0)" ]; then pass incr-436-valid-edit-accepted-home-without-elan
else fail incr-436-valid-edit-accepted-home-without-elan "rc=$rc $v"; fi

rc=$(incr cheat436 "$HOME" Cheat436 C436 $P436 base436); v=$(jq_ "$WORK/cheat436.json" '(d.get("verdict"), d.get("exit_code"), d.get("trust"))')   # cold-path verdict + trust
if [ "$rc" = 1 ] && [ "$v" = "('REJECTED', 1, 'sound')" ]; then pass incr-sorry-edit-rejected-by-trusted-check
else fail incr-sorry-edit-rejected-by-trusted-check "rc=$rc (verdict, exit, trust, names sorryAx)=$v"; fi

rc=$(incr bad436 "$HOME" Edit436 C436 $P436 base436-badplugin); v=$(jq_ "$WORK/bad436.json" '(d.get("verdict"), d.get("exit_code"), d.get("trust"))')   # cold-path verdict + trust
if [ "$rc" = 0 ] && [ "$v" = "('ACCEPTED', 0, 'sound')" ]; then pass incr-build-failure-of-valid-edit-not-rejected-cold-accepts
else fail incr-build-failure-of-valid-edit-not-rejected-cold-accepts "rc=$rc (verdict, exit, cold fallback)=$v"; fi

rc=$(incr broken436 "$HOME" Broken436 C436 $P436 base436); v=$(jq_ "$WORK/broken436.json" '(d.get("verdict"), d.get("exit_code"))')   # cold-path verdict (with either incr-reverify version)
if [ "$rc" = 1 ] && [ "$v" = "('REJECTED', 1)" ]; then pass incr-noncompiling-edit-rejected-only-by-official-build
else fail incr-noncompiling-edit-rejected-only-by-official-build "rc=$rc (verdict, exit, official build confirmed)=$v"; fi

rc=$(incr edit437 "$HOME" Edit437 C437 $P437 base437); v=$(jq_ "$WORK/edit437.json" '(d.get("verdict"), d.get("exit_code"), d.get("trust"))')
if [ "$rc" = 0 ] && [ "$v" = "('ACCEPTED', 0, 'sound')" ]; then pass incr-437-valid-edit-accepted
else fail incr-437-valid-edit-accepted "rc=$rc $v"; fi

# incr-reverify.sh directly (the CI action calls it with INCR_TC): an untrusted build failure is exit 2, never 1
# the newer incr-reverify.sh requires the caller's comparator pin next to the challenge pin: passed when the installed script takes it
CP=(); /usr/bin/grep -q -- '--comparator-sha256)' "$FV/tools/incr/incr-reverify.sh" && CP=(--comparator-sha256 "$CS436")
sbx "$HOME" --env INCR_TC "$TC436" -- "$FV/tools/incr/incr-reverify.sh" "$WORK/base436-badplugin" "$WORK/Edit436" "$WORK/C436" "$WORK/d-bad" \
  --challenge-sha256 $P436 "${CP[@]}" --packages /nonexistent --threads 4 > "$WORK/d-bad.out" 2> "$WORK/d-bad.err"
rc=$?; v=$(jq_ "$WORK/d-bad/summary.json" '(d.get("verdict"), d.get("mode"))')
# the older incr-reverify: an untrusted build failure is exit 2; the newer one (cold by default): bin/fastverify's verdict
# each branch consistent: the older one's no verdict (exit 2, NO VERDICT) or the newer one's cold ACCEPTED (exit 0, mode cold)
if { [ "$rc" = 2 ] && [ "$v" = "('NO VERDICT', None)" ]; } || { [ "$rc" = 0 ] && [ "$v" = "('ACCEPTED', 'cold')" ]; }; then pass incr-reverify-build-failure-exit2-not-rejected
else fail incr-reverify-build-failure-exit2-not-rejected "rc=$rc summary verdict=$v"; fi
# ... and a toolchain that is not the project's verified release (INCR_TC = 4.33.1 for a 4.36 project) is no verdict
sbx "$HOME" --env INCR_TC "$TC433" -- "$FV/tools/incr/incr-reverify.sh" "$WORK/base436" "$WORK/Edit436" "$WORK/C436" "$WORK/d-tc" \
  --challenge-sha256 $P436 "${CP[@]}" --packages /nonexistent --threads 4 > "$WORK/d-tc.out" 2> "$WORK/d-tc.err"
rc=$?; v=$(jq_ "$WORK/d-tc/summary.json" '(d.get("verdict"), d.get("mode"))')
# the older one: no verdict with the wrong release (exit 2, no summary or NO VERDICT); the newer one: INCR_TC is not used
# (cold ACCEPTED with bin/fastverify's own toolchain)
if { [ "$rc" = 2 ] && ! echo "$v" | grep -q "ACCEPTED\|REJECTED"; } || { [ "$rc" = 0 ] && [ "$v" = "('ACCEPTED', 'cold')" ]; }; then pass incr-reverify-wrong-release-toolchain-no-verdict; else fail incr-reverify-wrong-release-toolchain-no-verdict "rc=$rc"; fi

# ---- --incr-base must not drop options the cold path honours (--extra-arg=--require-sorried-holes / --require-kernel,
# --preset, ...): with any of them the project is judged by the cold path. Data: data/rshi (a 4.33.1 challenge whose
# definition hole `secret` is NOT sorried; the project redefines it).
RS=$HERE/data/rshi
mkdir -p "$WORK/RC"; cp "$RS/chal"/* "$RS/chal2/challenge.export" "$WORK/RC/"
PRS=$(/usr/bin/sha256sum "$WORK/RC/challenge.export" | cut -d' ' -f1); CRS=$(/usr/bin/sha256sum "$WORK/RC/comparator.json" | cut -d' ' -f1)
cp -r "$RS/proj" "$WORK/RP"; cp -r "$RS/proj2" "$WORK/RP2"
sbx "$HOME" -- "$FVB" verify "$WORK/RP" -c "$WORK/RC" --challenge-sha256 $PRS --comparator-sha256 $CRS --preset sound --keep-work --out "$WORK/baseRS" --json --threads 4 > "$WORK/baseRS.json" 2> "$WORK/baseRS.err"
sbx "$HOME" -- "$FVB" verify "$WORK/RP2" -c "$WORK/RC" --challenge-sha256 $PRS --comparator-sha256 $CRS --incr-base "$WORK/baseRS" --out "$WORK/o-rsh" --json --threads 4 \
  --extra-arg=--require-sorried-holes > "$WORK/rsh.json" 2> "$WORK/rsh.err"
rc=$?; v=$(jq_ "$WORK/rsh.json" '(d.get("verdict") in ("DECLINED", "ERROR", "NO-VERDICT"), d.get("exit_code"), d.get("accepted"), "require-sorried-holes" in json.dumps(d))')
if [ "$rc" = 2 ] && [ "$v" = "(True, 2, False, True)" ]; then pass incr-require-sorried-holes-honoured-declined
else fail incr-require-sorried-holes-honoured-declined "rc=$rc (verdict, exit, accepted, names the option)=$v"; fi
sbx "$HOME" -- "$FVB" verify "$WORK/RP2" -c "$WORK/RC" --challenge-sha256 $PRS --comparator-sha256 $CRS --incr-base "$WORK/baseRS" --out "$WORK/o-rk" --json --threads 4 \
  --extra-arg=--require-kernel=con-leche > "$WORK/rk.json" 2> "$WORK/rk.err"
rc=$?; v=$(jq_ "$WORK/rk.json" '(d.get("verdict"), "judged by the cold path" in d.get("verdict_basis", ""))')
if [ "$v" != NOJSON ] && echo "$v" | grep -q ", True)$"; then pass incr-require-kernel-goes-to-cold-path
else fail incr-require-kernel-goes-to-cold-path "rc=$rc (verdict, cold path)=$v"; fi
sbx "$HOME" -- "$FVB" verify "$WORK/RP2" -c "$WORK/RC" --challenge-sha256 $PRS --comparator-sha256 $CRS --incr-base "$WORK/baseRS" --out "$WORK/o-rs0" --json --threads 4 \
  > "$WORK/rs0.json" 2> "$WORK/rs0.err"
rc=$?; v=$(jq_ "$WORK/rs0.json" '(d.get("verdict"), d.get("exit_code"), "experimental in v0.1 and was not used" in json.dumps(d))')
if [ "$rc" = 0 ] && [ "$v" = "('ACCEPTED', 0, True)" ]; then pass v01/incr-base-433-edit-cold-path-accepted-with-warning
else fail v01/incr-base-433-edit-cold-path-accepted-with-warning "rc=$rc $v"; fi
# MCP fv_verify_project with incr_base: the full path, with the warning (the current server refuses it unless --allow-incr-base)
cat > "$WORK/mcpincr.py" <<'PY'
import json, subprocess, sys
import hashlib
fv, proj, chal, pin, base = sys.argv[1:6]
csha = hashlib.sha256(open(chal + "/comparator.json", "rb").read()).hexdigest()
req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
    "project_dir": proj, "challenge_dir": chal, "challenge_sha256": pin, "comparator_sha256": csha, "incr_base": base,
    "threads": 4}}}
p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", sys.argv[6], "--threads", "4"],
                   input=json.dumps(req) + "\n", text=True, capture_output=True, timeout=600)
m = json.loads([l for l in p.stdout.splitlines() if l.strip()][-1])
sc = (m.get("result") or {}).get("structuredContent") or {}
print(json.dumps({"verdict": sc.get("verdict"), "exit_code": sc.get("exit_code"), "warned": "experimental in v0.1" in json.dumps(sc),
                  "reason": sc.get("reason")}))
PY
sbx "$HOME" -- /usr/bin/python3 -I "$WORK/mcpincr.py" "$FV" "$WORK/Edit436" "$WORK/C436" $P436 "$WORK/base436" "$WORK" > "$WORK/mcpincr.out" 2> "$WORK/mcpincr.err"
v=$(jq_ "$WORK/mcpincr.out" '(d.get("verdict"), d.get("exit_code"), d.get("warned"))')
if [ "$v" = "('ACCEPTED', 0, True)" ]; then pass v01/mcp-verify-project-incr-base-full-path-with-warning
else fail v01/mcp-verify-project-incr-base-full-path-with-warning "$v $(head -c 200 "$WORK/mcpincr.err")"; fi

echo "RESULT: $NPASS PASS $NFAIL FAIL"
[ $NFAIL = 0 ]
