#!/bin/bash
# tests/cli-mcp/run.sh [FV_ROOT] [WORK] — regression rows for the bin/fv CLI and the MCP server:
# usage and output errors, audit, service and doctor errors, --quiet, per-judge timeouts, attempt diagnostics, MCP contract.
# Every row runs bin/fv / the MCP server of FV_ROOT inside bwrap (no network, / read-only, private /tmp, only WORK writable).
# Non-guard rows FAIL on the earlier tree and PASS now; rows named *-guard pass on both (behaviour that must not change).
# Output: one "PASS name" / "FAIL name: detail" line per row, then "RESULT: N PASS M FAIL". Exit 0 iff no FAIL.
# Needs: bwrap, the official toolchains v4.36.0 and v4.37.0-rc1 under ~/.elan/toolchains, the pinned judge binaries of FV_ROOT.
set -u
HERE=$(cd "$(/usr/bin/dirname "$(/usr/bin/readlink -f "$0")")" && pwd)
FV=$(cd "${1:-$HERE/../..}" && pwd)
WORK=${2:-}
[ -n "$WORK" ] || WORK=$(mktemp -d /tmp/cli-mcp.XXXXXX)
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
DATA=$HERE/data
TC436=${TC436:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}
TC437=${TC437:-$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1}
P436=dae541f9e5e539b6251d3cc6249fa0b26469495e2ca95acac7c32786a0452a48
C436=cea900972d29138d856ea445371e90f7c584bafc42bb5bc3ad4a985afa7c580c
P437=76d3b313a7fa540eeb2c41393314fc522c1e9ea6293b88474f2a566cd3835d71
NPASS=0; NFAIL=0; NSKIP=0
pass() { echo "PASS $1"; NPASS=$((NPASS+1)); }
skip() { echo "SKIP $1: $2"; NSKIP=$((NSKIP+1)); }   # neither PASS nor FAIL
fail() { echo "FAIL $1: $2"; NFAIL=$((NFAIL+1)); }
# sb RW [extra bwrap args --] cmd... : bwrap, no network, RW writable
sb() {
  local rw=$1; shift; local extra=()
  if [ "${1:-}" = "--extra" ]; then shift; while [ "$1" != "--" ]; do extra+=("$1"); shift; done; shift; fi
  mkdir -p "$rw"
  /usr/bin/bwrap --die-with-parent --unshare-all --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp \
    --bind "$rw" "$rw" "${extra[@]}" --clearenv --setenv PATH /usr/bin:/bin --setenv HOME /tmp --setenv LANG C.UTF-8 \
    --setenv FV_EXPERIMENTAL_CI 1 \
    --setenv LEAN_NUM_THREADS 4 --chdir "$rw" "$@"
}
# jq_ FILE EXPR : evaluate a python expression over the JSON document d (prints "NOJSON" if FILE is not one JSON value)
jq_() { /usr/bin/python3 -I -c '
import json, sys
try:
    d = json.load(open(sys.argv[1], encoding="utf-8"))
except Exception:
    print("NOJSON"); sys.exit(0)
print(eval(sys.argv[2]))' "$1" "$2" 2>&1; }
# envelope_err ROW RC OUT : the row passes iff RC=2 and OUT is one ERROR envelope with exit_code 2
envelope_err() {
  local v; v=$(jq_ "$3" '(d.get("verdict"), d.get("exit_code"), d.get("accepted"))')
  if [ "$2" = 2 ] && [ "$v" = "('ERROR', 2, False)" ]; then pass "$1"; else fail "$1" "rc=$2 envelope=$v"; fi
}
okfalse_err() {   # ROW RC OUT : RC=2 and {"ok": false, "error": ...}
  local v; v=$(jq_ "$3" '(d.get("ok"), bool(d.get("error")))')
  if [ "$2" = 2 ] && [ "$v" = "(False, True)" ]; then pass "$1"; else fail "$1" "rc=$2 json=$v"; fi
}
FVB=$FV/bin/fv
echo "# cli-mcp: FV_ROOT=$FV WORK=$WORK"

# ---------------------------------------------------------------- usage / input errors -> exit 2 + JSON
R=$WORK/cli; mkdir -p "$R"
sb "$R" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 abc --comparator-sha256 $C436 --json > "$R/2a.out" 2> "$R/2a.err"
rc=$?; v=$(jq_ "$R/2a.out" '(d.get("verdict"), d.get("exit_code"), "--challenge-sha256" in str(d.get("reason")))')
if [ $rc = 2 ] && [ "$v" = "('ERROR', 2, True)" ]; then pass check-malformed-pin-exit2-json; else fail check-malformed-pin-exit2-json "rc=$rc $v"; fi

mkdir -p "$R/sidecar"; cp "$DATA/c436/challenge.export" "$DATA/c436/comparator.json" "$DATA/c436/lean-toolchain" "$R/sidecar/"
: > "$R/sidecar/challenge.export.sha256"
sb "$R" "$FVB" verify "$DATA/main436" --challenge "$R/sidecar" --trust-challenge-sha256-file --json --threads 4 > "$R/2b.out" 2> "$R/2b.err"
envelope_err verify-empty-pin-sidecar-exit2-json $? "$R/2b.out"

sb "$R" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 xyz --json > "$R/2c.out" 2> "$R/2c.err"
envelope_err verify-malformed-comparator-pin-exit2-json $? "$R/2c.out"

sb "$R" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --json > "$R/2d.out" 2> "$R/2d.err"   # argparse: required option missing
envelope_err check-usage-error-json $? "$R/2d.out"

ln -sfn "$DATA/c436/comparator.json" "$R/cfg-link.json"
sb "$R" "$FVB" audit "$DATA/c436/challenge.export" --config "$R/cfg-link.json" --json > "$R/2e.out" 2> "$R/2e.err"
okfalse_err audit-refused-config-exit2-json $? "$R/2e.out"

echo 'theorem foo (n : Nat) : n + 0 = n := by sorry' > "$R/lemma.lean"; mkdir -p "$R/ws/.lake/packages"
sb "$R" "$FVB" triage --experimental "$R/lemma.lean" --toolchain /nonexistent/toolchain --packages "$R/ws" --json > "$R/2f.out" 2> "$R/2f.err"
rc=$?; v=$(jq_ "$R/2f.out" '(d.get("ok"), d.get("status"))')
if [ $rc = 2 ] && [ "$v" = "(False, None)" ]; then pass triage-unrunnable-toolchain-exit2-not-refuted
else fail triage-unrunnable-toolchain-exit2-not-refuted "rc=$rc json=$v"; fi

# ---------------------------------------------------------------- fv audit could not run -> ERROR, exit 2
sb "$R" "$FVB" audit "$DATA/c436/challenge.export" --config "$DATA/c436/missing.json" --json > "$R/3.out" 2> "$R/3.err"
okfalse_err audit-missing-config-exit2 $? "$R/3.out"

sb "$R" "$FVB" audit "$DATA/c436" --challenge-sha256 $P436 --reading-set "$DATA/main436/Main.lean/ReadingSet.lean" --json > "$R/15.out" 2> "$R/15.err"
okfalse_err audit-deep-error-exit2 $? "$R/15.out"

# the deep audit builds expaudit with cargo (the sandbox PATH is /usr/bin:/bin) unless tools/audit/bin/expaudit is prebuilt
if [ ! -x "$FV/tools/audit/bin/expaudit" ] && ! PATH=/usr/bin:/bin command -v cargo > /dev/null 2>&1; then
  skip audit-clean-challenge-ok-guard "no cargo on /usr/bin:/bin and no prebuilt tools/audit/bin/expaudit (needed by the deep audit)"
else
  sb "$R" "$FVB" audit "$DATA/c436" --challenge-sha256 $P436 --json > "$R/15g.out" 2> "$R/15g.err"
  rc=$?; v=$(jq_ "$R/15g.out" '(d.get("ok"), d.get("error"))')
  if [ $rc = 0 ] && [ "$v" = "(True, None)" ]; then pass audit-clean-challenge-ok-guard; else fail audit-clean-challenge-ok-guard "rc=$rc json=$v"; fi
fi

# ---------------------------------------------------------------- no service -> ERROR exit 2 + JSON
sb "$R" "$FVB" attempt "$DATA/attempt/correct.lean" --state /tmp/absent-daemon --pset qa --theorem qaAddZero --json --timeout 2 > "$R/102a.out" 2> "$R/102a.err"
envelope_err attempt-no-fvserve-daemon-exit2-json $? "$R/102a.out"
sb "$R" "$FVB" attempt "$DATA/attempt/correct.lean" --http http://127.0.0.1:9 --pset qa --theorem qaAddZero --json --timeout 2 > "$R/102b.out" 2> "$R/102b.err"
envelope_err attempt-unreachable-fvapi-exit2-json $? "$R/102b.out"

# ---------------------------------------------------------------- output error -> ERROR exit 2 (documented rule)
CHK=(check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --threads 4 --json)
sb "$R" "$FVB" "${CHK[@]}" --json-out "$R/103-first.json" --sarif /usr/cli-mcp-not-writable/out.sarif > "$R/103.out" 2> "$R/103.err"
rc=$?; v=$(jq_ "$R/103.out" '(d.get("verdict"), d.get("exit_code"))'); w=$(jq_ "$R/103-first.json" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 2 ] && [ "$v" = "('ERROR', 2)" ] && [ "$w" = "('ERROR', 2)" ]; then pass check-output-error-exit2-json-no-stale-verdict-file
else fail check-output-error-exit2-json-no-stale-verdict-file "rc=$rc stdout=$v json-out-file=$w"; fi
sb "$R" "$FVB" "${CHK[@]}" --json-out /usr/cli-mcp-not-writable/result.json > "$R/103b.out" 2> "$R/103b.err"
envelope_err check-json-out-unwritable-exit2-json $? "$R/103b.out"
sb "$R" "$FVB" "${CHK[@]}" --json-out "$R/103g.json" --sarif "$R/103g.sarif" --lsp-out "$R/103g.lsp" > "$R/103g.out" 2> "$R/103g.err"
rc=$?; v=$(jq_ "$R/103g.out" '(d.get("verdict"), d.get("exit_code"), d.get("trust"))'); w=$(jq_ "$R/103g.json" 'd.get("verdict")')
if [ $rc = 0 ] && [ "$v" = "('ACCEPTED', 0, 'sound')" ] && [ "$w" = ACCEPTED ] && [ -s "$R/103g.sarif" ] && [ -s "$R/103g.lsp" ]; then
  pass check-writable-outputs-accepted-guard; else fail check-writable-outputs-accepted-guard "rc=$rc stdout=$v file=$w"; fi

# ---------------------------------------------------------------- fv verify --quiet writes nothing to the terminal
sb "$R" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --preset sound-auto --threads 4 \
  --out /tmp/out --quiet --json-out "$R/107.json" > "$R/107.out" 2> "$R/107.err"
rc=$?; w=$(jq_ "$R/107.json" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 0 ] && [ "$w" = "('ACCEPTED', 0)" ] && [ ! -s "$R/107.out" ] && [ ! -s "$R/107.err" ]; then pass verify-quiet-no-terminal-output
else fail verify-quiet-no-terminal-output "rc=$rc file=$w stdout=$(wc -c < "$R/107.out")B stderr=$(wc -c < "$R/107.err")B"; fi

# ---------------------------------------------------------------- per-judge --timeout scope documented
sb "$R" "$FVB" check --help > "$R/110.help" 2>&1
if tr -s ' \n' ' ' < "$R/110.help" | grep -q -- "--low-mem is ONE budget counted from the judge's start" &&
   tr -s ' \n' ' ' < "$FV/tools/cli/README.md" | grep -q "one budget counted from the judge's start"; then
  pass check-timeout-scope-documented-help-and-readme; else fail check-timeout-scope-documented-help-and-readme "no per-judge timeout text"; fi

# ---------------------------------------------------------------- fvserve attempt diagnostics (e2e)
S=$WORK/svc; mkdir -p "$S"
cat > "$S/pair.sh" <<'EOF'
#!/bin/bash
fv=$1; data=$2; out=$3; tc=$4; pin=$5
mkdir -p /tmp/ws/.lake/packages; cd "$fv" || exit 2
/usr/bin/python3 -I tools/fvserve/fvserve.py serve --state /tmp/svc --pset "qa=$data/c437:$pin" --max-inflight 1 --par 1 \
  --export-dir /tmp --threads 4 --toolchain "$tc" --packages /tmp/ws --snapshot-header '' --pins check/sound/pins-437.env > "$out/start.log" 2>&1 &
d=$!; trap 'kill $d 2>/dev/null; wait $d 2>/dev/null' EXIT
for i in $(seq 1 240); do [ -S /tmp/svc/sock ] && break; kill -0 $d 2>/dev/null || exit 3; sleep 1; done
"$fv/bin/fv" attempt "$data/attempt/typo.lean" --state /tmp/svc --pset qa --theorem qaAddZero --timeout 180 --json > "$out/typo.json" 2> "$out/typo.err"; a=$?
"$fv/bin/fv" attempt "$data/attempt/correct.lean" --state /tmp/svc --pset qa --theorem qaAddZero --timeout 180 --json > "$out/correct.json" 2> "$out/correct.err"; b=$?
echo "$a $b" > "$out/rcs"
/usr/bin/python3 -I tools/fvserve/fvserve.py stop --state /tmp/svc > /dev/null 2>&1
EOF
sb "$S" bash "$S/pair.sh" "$FV" "$DATA" "$S" "$TC437" $P437 > "$S/log" 2>&1
sb "$S" "$TC437/bin/lean" "$DATA/attempt/typo.lean" > "$S/official-typo.log" 2>&1
read -r RA RB < "$S/rcs" 2>/dev/null || { RA=x; RB=x; }
LCOL=$(sed -n 's/^.*typo\.lean:1:\([0-9][0-9]*\): error.*$/\1/p' "$S/official-typo.log" | head -1)   # official Lean: 0-based column
v=$(jq_ "$S/typo.json" '[(x["file"], x["line"], x["column"]) for x in d.get("diagnostics") or [] if x.get("severity") == "error"][:1]')
if [ "$RA" = 1 ] && echo "$v" | grep -q "^\[('$DATA/attempt/typo.lean', 1, "; then pass attempt-diagnostic-names-client-file
else fail attempt-diagnostic-names-client-file "rc=$RA diag=$v"; fi
if [ -n "$LCOL" ] && echo "$v" | grep -q ", 1, $((LCOL+1)))]$"; then pass attempt-diagnostic-column-is-lean-column-plus-1
else fail attempt-diagnostic-column-is-lean-column-plus-1 "official Lean col(0-based)=$LCOL diag=$v"; fi
w=$(jq_ "$S/correct.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$RB" = 0 ] && [ "$w" = "('ACCEPTED', 0)" ]; then pass attempt-correct-accepted-guard; else fail attempt-correct-accepted-guard "rc=$RB $w"; fi

# ---------------------------------------------------------------- fv doctor, optional component missing
D=$WORK/doctor; mkdir -p "$D/empty"
OVL=$(awk '$1=="PIN" && $2=="snapshot_exporter" {print $4}' "$FV/check/sound/pins.env"); OVL=${OVL%/*}
GRU=$(awk '$1=="PIN" && $2=="gruszka" {print $4}' "$FV/check/sound/pins.env"); GRU=${GRU%/*}
sb "$D" --extra --ro-bind "$D/empty" "$OVL" -- "$FVB" doctor --json > "$D/opt.out" 2> "$D/opt.err"
rc=$?; v=$(jq_ "$D/opt.out" '(d.get("ok"), "snapshot_exporter" in (d["checks"]["sound_pins"].get("optional_missing") or []))')
if [ $rc = 0 ] && [ "$v" = "(True, True)" ]; then pass doctor-optional-overlap-exporter-missing-ok
else fail doctor-optional-overlap-exporter-missing-ok "rc=$rc (ok, listed optional)=$v"; fi
sb "$D" --extra --ro-bind "$D/empty" "$GRU" -- "$FVB" doctor --json > "$D/req.out" 2> "$D/req.err"
rc=$?; v=$(jq_ "$D/req.out" 'd.get("ok")')
if [ $rc = 2 ] && [ "$v" = False ]; then pass doctor-required-pin-missing-fails-guard; else fail doctor-required-pin-missing-fails-guard "rc=$rc ok=$v"; fi

# ---------------------------------------------------------------- MCP tool contract and diagnostics
M=$WORK/mcp; mkdir -p "$M"
printf '%s\n' 'def x : Nat := 1' '#check missingConstantHere' > "$M/Example.lean"
(cd "$M" && sb "$M" "$TC436/bin/lean" Example.lean > "$M/lean.out" 2>&1)
cat > "$M/client.py" <<'EOF'
import json, subprocess, sys
fv, out = sys.argv[1], sys.argv[2]
reqs = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2024-11-05", "capabilities": {},
         "clientInfo": {"name": "t", "version": "0"}}},
        {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
        {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_parse_diagnostics",
         "arguments": {"compiler_output": open(sys.argv[3]).read()}}}]
p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--threads", "4"],
                   input="".join(json.dumps(r) + "\n" for r in reqs), text=True, capture_output=True, timeout=120)
res = {}
for ln in p.stdout.splitlines():
    try:
        m = json.loads(ln)
    except ValueError:
        continue
    res[m.get("id")] = m
tools = {t["name"]: t for t in res[2]["result"]["tools"]}
diag = json.loads(res[3]["result"]["content"][0]["text"])
json.dump({"fv_check_export": tools["fv_check_export"], "diag": diag}, open(out, "w"))
EOF
sb "$M" /usr/bin/python3 -I "$M/client.py" "$FV" "$M/mcp.json" "$M/lean.out" > "$M/client.log" 2>&1
v=$(jq_ "$M/mcp.json" '(lambda t: ("never ACCEPTED" not in t) and ("ACCEPTED" in t))(json.dumps(d["fv_check_export"]))')
if [ "$v" = True ]; then pass mcp-frontier-description-allows-ACCEPTED; else fail mcp-frontier-description-allows-ACCEPTED "$v"; fi
LC=$(sed -n 's/^Example\.lean:2:\([0-9][0-9]*\): error.*$/\1/p' "$M/lean.out" | head -1)
v=$(jq_ "$M/mcp.json" '(d["diag"]["diagnostics"][0]["column"], d["diag"]["lsp"]["files"]["Example.lean"][0]["range"]["start"]["character"], d["diag"]["sarif"]["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["region"]["startColumn"])')
if [ "$LC" = 7 ] && [ "$v" = "($((LC+1)), $LC, $((LC+1)))" ]; then pass mcp-parse-diagnostics-lsp-sarif-columns-match-lean
else fail mcp-parse-diagnostics-lsp-sarif-columns-match-lean "official Lean col(0-based)=$LC (column, lsp char, sarif startColumn)=$v"; fi

# ================================================================ output streams, stale outputs, audit errors, comparator config, shell functions, signals
G=$WORK/part1; mkdir -p "$G"
# --- a full / closed stdout or stderr never turns the exit into 120 or 1
sb "$G" /bin/sh -c '"$@" > /dev/full' sh "$FVB" "${CHK[@]}" 2> "$G/full.err"
rc=$?; if [ $rc = 2 ]; then pass stdout-full-device-accepted-run-exit2; else fail stdout-full-device-accepted-run-exit2 "rc=$rc"; fi
sb "$G" /bin/sh -c '"$@" 2>&-' sh "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 abc --json > "$G/cl.out"
rc=$?; envelope_err stderr-closed-input-error-exit2-json $rc "$G/cl.out"
sb "$G" /bin/sh -c '"$@" >&-' sh "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 abc --json 2> "$G/so.err"
rc=$?; if [ $rc = 2 ]; then pass stdout-closed-input-error-exit2; else fail stdout-closed-input-error-exit2 "rc=$rc"; fi
# --- no requested output file keeps the verdict of an earlier run when this run ends without a result
cp "$R/103g.json" "$G/stale.json"   # an ACCEPTED envelope of the guard run above
sb "$G" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --json-out "$G/stale.json" --bogus-option > /dev/null 2>&1
rc=$?; w=$(jq_ "$G/stale.json" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass usage-error-rewrites-stale-json-out; else fail usage-error-rewrites-stale-json-out "rc=$rc file=$w"; fi
cp "$R/103g.json" "$G/stale2.json"; ln -sfn "$DATA/main436" "$G/proj-link"
sb "$G" "$FVB" verify "$G/proj-link/../main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --json-out "$G/stale2.json" --threads 4 \
  --pins /nonexistent/pins.env > /dev/null 2>&1   # refused before any result (bad --pins)
rc=$?; w=$(jq_ "$G/stale2.json" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass refused-input-rewrites-stale-json-out; else fail refused-input-rewrites-stale-json-out "rc=$rc file=$w"; fi
# --- fv audit with a malformed --challenge-sha256 is an input error
sb "$G" "$FVB" audit "$DATA/c436" --challenge-sha256 xyz --json > "$G/g1.out" 2> "$G/g1.err"
okfalse_err clierr-1/audit-malformed-pin-exit2-json $? "$G/g1.out"
# --- the installed deep audit engine leaving no result is an audit that could not run (unit row)
sb "$G" /usr/bin/python3 -I -c '
import sys, argparse; A = sys.argv[:]; sys.path.insert(0, A[1] + "/tools/cli"); sys.argv = ["fv"]
import fv_cli
fv_cli.mcp_server.audit_challenge_dir = lambda *a, **k: {"ok": True, "findings": [], "theorem_count": 1, "deep_audit": None}
ns = argparse.Namespace(challenge=A[2], challenge_sha256=None, probe=False, packages=None, reading_set=None,
                        conjecture_mode=False, solution_mode=False, config=None, json=True)
print("RC", fv_cli.cmd_audit(ns))' "$FV" "$DATA/c436" > "$G/g6.out" 2> "$G/g6.err"
if grep -q "^RC 2$" "$G/g6.out"; then pass clierr-6/audit-engine-without-result-exit2; else fail clierr-6/audit-engine-without-result-exit2 "$(tail -n 1 "$G/g6.out")"; fi
# --- `fv --json` (no subcommand) prints the JSON error object
sb "$G" "$FVB" --json > "$G/g5.out" 2> "$G/g5.err"
okfalse_err clierr-5/fv-json-without-subcommand-json-error $? "$G/g5.out"
# --- fv attempt --http: diagnostics of fvapi's private Attempt/<theorem>.lean name the caller's file
cat > "$G/fakeapi.py" <<'PY'
import json, sys, http.server, threading
env = {"api_version": "1.0", "mode": "attempt", "verdict": "REJECTED", "accepted": False, "reward": 0.0, "exit_code": 1,
       "trust": "sound", "verdict_basis": "rejected", "timing": {"total_s": 0.1},
       "diagnostics": [{"rule_id": "FV001", "severity": "error", "file": "/srv/x/proj/Attempt/qaAddZero.lean", "line": 1,
                        "column": 52, "end_line": None, "end_column": None, "message": "unknown constant", "source": "lean"}]}
class H(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        self.rfile.read(int(self.headers.get("Content-Length") or 0)); b = json.dumps(env).encode()
        self.send_response(200); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(b)))
        self.end_headers(); self.wfile.write(b)
    def log_message(self, *a): pass
s = http.server.HTTPServer(("127.0.0.1", 0), H); print(s.server_address[1], flush=True); s.serve_forever()
PY
cat > "$G/g3.sh" <<'SH'
/usr/bin/python3 -I "$1/fakeapi.py" > "$1/port" & sv=$!
for i in $(seq 1 50); do [ -s "$1/port" ] && break; sleep 0.1; done
"$2" attempt "$3" --http "http://127.0.0.1:$(cat "$1/port")" --pset qa --theorem qaAddZero --json --timeout 10 > "$1/g3.out" 2> "$1/g3.err"
echo $? > "$1/g3.rc"; kill $sv
SH
sb "$G" bash "$G/g3.sh" "$G" "$FVB" "$DATA/attempt/typo.lean"
v=$(jq_ "$G/g3.out" '[x["file"] for x in d.get("diagnostics") or []]')
if [ "$(cat "$G/g3.rc" 2>/dev/null)" = 1 ] && [ "$v" = "['$DATA/attempt/typo.lean']" ]; then pass clierr-3/attempt-http-diagnostic-names-client-file
else fail clierr-3/attempt-http-diagnostic-names-client-file "rc=$(cat "$G/g3.rc" 2>/dev/null) files=$v"; fi
# --- an array-shaped comparator config is a configuration error (exit 2 + ERROR envelope), CLI and MCP
mkdir -p "$G/arr"; cp "$DATA/c436/challenge.export" "$G/arr/"; echo '[]' > "$G/arr/comparator.json"
ASHA=$(/usr/bin/sha256sum "$G/arr/comparator.json" | cut -d' ' -f1)
sb "$G" "$FVB" check "$DATA/main436/main.export" --challenge "$G/arr" --challenge-sha256 $P436 --comparator-sha256 $ASHA --json --json-out "$G/arr.json" > "$G/arr.out" 2> "$G/arr.err"
rc=$?; w=$(jq_ "$G/arr.json" '(d.get("verdict"), d.get("exit_code"))'); v=$(jq_ "$G/arr.out" '"JSON object is required" in d.get("reason", "")')
if [ $rc = 2 ] && [ "$w" = "('ERROR', 2)" ] && [ "$v" = True ]; then pass check-array-config-exit2-error-envelope
else fail check-array-config-exit2-error-envelope "rc=$rc json-out=$w names-config-error=$v"; fi
ASHA=$(/usr/bin/sha256sum "$G/arr/comparator.json" | cut -d' ' -f1)
cat > "$G/mcparr.py" <<'PY'
import json, subprocess, sys
fv, d, exp, pin, csha = sys.argv[1:6]
req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
    "export_file": exp, "challenge_export": d + "/challenge.export", "comparator_json": d + "/comparator.json",
    "challenge_sha256": pin, "comparator_sha256": csha}}}
p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", d, "--allow-root", exp.rsplit("/", 1)[0],
                    "--threads", "4"], input=json.dumps(req) + "\n", text=True, capture_output=True, timeout=120)
m = json.loads([l for l in p.stdout.splitlines() if l.strip()][-1])
sc = (m.get("result") or {}).get("structuredContent") or {}
print(json.dumps({"verdict": sc.get("verdict"), "exit_code": sc.get("exit_code"), "reason": sc.get("reason"), "error": m.get("error")}))
PY
sb "$G" /usr/bin/python3 -I "$G/mcparr.py" "$FV" "$G/arr" "$DATA/main436/main.export" $P436 $ASHA > "$G/mcparr.out" 2> "$G/mcparr.err"
v=$(jq_ "$G/mcparr.out" '(d.get("verdict"), d.get("exit_code"), "JSON object is required" in str(d.get("reason")))')
if [ "$v" = "('ERROR', 2, True)" ]; then pass mcp-check-export-array-config-error-envelope; else fail mcp-check-export-array-config-error-envelope "$v $(head -c 200 "$G/mcparr.err")"; fi
# --- `bash bin/fv` / `bash bin/fastverify` with exported functions or BASH_ENV-defined functions
cat > "$G/hijack.sh" <<'SH'
exec() { return 0; }; cd() { builtin cd /; }; exit() { return 0; }; builtin() { return 0; }; command() { return 0; }; shift() { return 0; }
SH
sb "$G" /bin/bash -c '. "$1"; export -f exec cd exit builtin command shift; bash "$2" verify /nonexistent -c /nonexistent --json > "$3/hj1.out" 2>/dev/null; echo $? > "$3/hj1.rc"' _ "$G/hijack.sh" "$FVB" "$G"
v=$(jq_ "$G/hj1.out" '(d.get("verdict"), d.get("exit_code"))')
if [ "$(cat "$G/hj1.rc")" = 2 ] && [ "$v" = "('ERROR', 2)" ]; then pass bash-bin-fv-exported-functions-cannot-change-result
else fail bash-bin-fv-exported-functions-cannot-change-result "rc=$(cat "$G/hj1.rc") $v"; fi
echo 'echo sourced > "$MARK"' > "$G/benv.sh"
sb "$G" /bin/bash -c 'MARK="$3/benv.mark" BASH_ENV="$1" "$2" verify /nonexistent -c /nonexistent --json > "$3/hj2.out" 2>/dev/null; echo $? > "$3/hj2.rc"' _ "$G/benv.sh" "$FVB" "$G"
v=$(jq_ "$G/hj2.out" '(d.get("verdict"), d.get("exit_code"))')
if [ "$(cat "$G/hj2.rc")" = 2 ] && [ "$v" = "('ERROR', 2)" ] && [ ! -e "$G/benv.mark" ]; then pass direct-bin-fv-ignores-bash-env-guard
else fail direct-bin-fv-ignores-bash-env-guard "rc=$(cat "$G/hj2.rc") $v mark=$([ -e "$G/benv.mark" ] && echo present)"; fi
# --- a signal to the started PID stops the orchestrator (no orphaned verification) and the run is ERROR
cat > "$G/sig.sh" <<'SH'
# sig.sh MODE G FV DATA PIN CPIN : MODE fv-term | fv-kill | fastverify-term
m=$1; G=$2; FV=$3; DATA=$4; PIN=$5; CPIN=$6
cp -r "$DATA/main436" "$G/sig-$m-proj" 2>/dev/null; rm -f "$G/sig-$m-proj/main.export"
if [ "$m" = fastverify-term ]; then
  "$FV/bin/fastverify" "$G/sig-$m-proj" "$DATA/c436" "$G/sig-$m-out" --preset sound --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --threads 4 > "$G/sig-$m.log" 2>&1 & pid=$!
else
  "$FV/bin/fv" verify "$G/sig-$m-proj" --challenge "$DATA/c436" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --threads 4 --json --json-out "$G/sig-$m.json" \
    > "$G/sig-$m.out" 2> "$G/sig-$m.err" & pid=$!
fi
for i in $(seq 1 200); do /usr/bin/pgrep -f 'lib/fastverify.py' > /dev/null && break; sleep 0.1; done
# past the orchestrator's start-up (sound-auto planning runs before its signal handler and its OUT exist)
for i in $(seq 1 300); do ls -d /tmp/fv-run.*/out "$G/sig-$m-out" > /dev/null 2>&1 && break; ls -d /tmp/fv-run.*/out > /dev/null 2>&1 && break; [ -d "$G/sig-$m-out" ] && break; sleep 0.1; done
sleep 2
if [ "$m" = fv-kill ]; then kill -KILL $pid; else kill -TERM $pid; fi
wait $pid; echo $? > "$G/sig-$m.rc"
for i in $(seq 1 150); do /usr/bin/pgrep -f 'lib/fastverify.py' > /dev/null || break; sleep 0.2; done
/usr/bin/pgrep -f 'lib/fastverify.py' > /dev/null && echo orphan > "$G/sig-$m.orphan"
# the orchestrator's own record (bin/fv's temporary OUT survives a SIGKILL of bin/fv): did it get a signal, or run to its end?
cat /tmp/fv-run.*/out/result.json > "$G/sig-$m.orch.json" 2>/dev/null
exit 0
SH
for m in fv-term fv-kill fastverify-term; do sb "$G" bash "$G/sig.sh" $m "$G" "$FV" "$DATA" $P436 $C436 > /dev/null 2>&1; done
w=$(jq_ "$G/sig-fv-term.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$(cat "$G/sig-fv-term.rc")" = 2 ] && [ "$w" = "('ERROR', 2)" ] && [ ! -e "$G/sig-fv-term.orphan" ]; then pass sigterm-bin-fv-stops-orchestrator-records-error
else fail sigterm-bin-fv-stops-orchestrator-records-error "rc=$(cat "$G/sig-fv-term.rc") json-out=$w $(cat "$G/sig-fv-term.orphan" 2>/dev/null)"; fi
w=$(jq_ "$G/sig-fv-kill.orch.json" '(d.get("verdict"), "interrupted" in d)')
if [ ! -e "$G/sig-fv-kill.orphan" ] && [ "$w" = "('ERROR', True)" ]; then pass sigkill-bin-fv-orchestrator-stopped-by-pdeathsig
else fail sigkill-bin-fv-orchestrator-stopped-by-pdeathsig "orchestrator record=$w $(cat "$G/sig-fv-kill.orphan" 2>/dev/null) (it should get SIGTERM when bin/fv dies, not run to its end)"; fi
w=$(jq_ "$G/sig-fastverify-term-out/result.json" '(d.get("verdict"), "interrupted" in json.dumps(d))')
if [ ! -e "$G/sig-fastverify-term.orphan" ] && echo "$w" | grep -q ", True)$" && ! echo "$w" | grep -q "ACCEPTED\|REJECTED"; then
  pass sigterm-bin-fastverify-pid-is-orchestrator-records-interruption-guard
else fail sigterm-bin-fastverify-pid-is-orchestrator-records-interruption-guard "result=$w $(cat "$G/sig-fastverify-term.orphan" 2>/dev/null)"; fi
# --- `fv watch | head` ends when the pipe closes
cp -r "$DATA/main436" "$G/watchproj"; rm -f "$G/watchproj/main.export"
sb "$G" /usr/bin/timeout 150 /bin/bash -c '"$1" watch --experimental "$2" --challenge "$3" --challenge-sha256 "$4" --comparator-sha256 "$6" --interval 1 --threads 4 | head -n 1 > "$5/watch.head"' _ "$FVB" "$G/watchproj" "$DATA/c436" $P436 "$G" $C436 > /dev/null 2>&1
rc=$?
if [ $rc != 124 ] && [ -s "$G/watch.head" ]; then pass watch-ends-when-pipe-closes-guard; else fail watch-ends-when-pipe-closes-guard "rc=$rc (124 = still running after 150 s)"; fi
sb "$G" /bin/bash -c '. "$1"; export -f exec cd exit builtin command shift; bash "$2" /nonexistent /nonexistent "$3/fvout" > /dev/null 2>&1; echo $? > "$3/hj3.rc"' _ "$G/hijack.sh" "$FV/bin/fastverify" "$G"
if [ "$(cat "$G/hj3.rc")" = 2 ]; then pass bash-bin-fastverify-exported-functions-cannot-change-result
else fail bash-bin-fastverify-exported-functions-cannot-change-result "rc=$(cat "$G/hj3.rc")"; fi

# ================================================================ used --out, usage-error recovery, empty pins, undelivered output, signals
H3=$WORK/part3; mkdir -p "$H3"
# --- a used --out is refused before either route (previously it got a second, contradicting verdict)
mkdir -p "$H3/usedout"; echo '{"verdict": "REJECTED", "exit": 1}' > "$H3/usedout/summary.json"
sb "$H3" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --incr-base "$H3/no-such-base" --out "$H3/usedout" \
  --json --threads 4 > "$H3/uo.out" 2> "$H3/uo.err"
rc=$?; v=$(jq_ "$H3/uo.out" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 2 ] && [ "$v" = "('ERROR', 2)" ] && [ "$(ls "$H3/usedout")" = summary.json ]; then pass used-out-dir-refused-no-second-verdict-guard
else fail used-out-dir-refused-no-second-verdict-guard "rc=$rc $v out=[$(ls "$H3/usedout" | tr '\n' ' ')]"; fi
# --- usage-error recovery: nothing after `--` is written; an abbreviated option's destination is rewritten
( cd "$H3" && sb "$H3" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --json -- --json-out "$H3/separator-unused.json" > /dev/null 2>&1 )
if [ ! -e "$H3/separator-unused.json" ]; then pass usage-error-operand-after-double-dash-not-written-guard
else fail usage-error-operand-after-double-dash-not-written-guard "a positional operand was opened for writing"; fi
cp "$R/103g.json" "$H3/abbrev.json"
sb "$H3" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --json-o "$H3/abbrev.json" --bogus > /dev/null 2>&1
w=$(jq_ "$H3/abbrev.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$w" = "('ERROR', 2)" ]; then pass usage-error-abbreviated-json-out-rewritten; else fail usage-error-abbreviated-json-out-rewritten "file=$w"; fi
cp "$R/103g.json" "$H3/lead.json"
sb "$H3" "$FVB" --json check "$DATA/main436/main.export" --challenge "$DATA/c436" --json-out "$H3/lead.json" > "$H3/lead.out" 2> /dev/null
rc=$?; w=$(jq_ "$H3/lead.json" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass leading-json-usage-error-rewrites-json-out; else fail leading-json-usage-error-rewrites-json-out "rc=$rc file=$w"; fi
# --- an explicitly empty pin is malformed (audit; check --comparator-sha256=)
sb "$H3" "$FVB" audit "$DATA/c436" --challenge-sha256= --json > "$H3/ep1.out" 2> /dev/null
rc=$?; v=$(jq_ "$H3/ep1.out" '(d.get("ok"), "64 lowercase hex" in str(d.get("error")))')
if [ $rc = 2 ] && [ "$v" = "(False, True)" ]; then pass audit-empty-challenge-pin-exit2-json; else fail audit-empty-challenge-pin-exit2-json "rc=$rc $v"; fi
sb "$H3" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256= --json --threads 4 > "$H3/ep2.out" 2> /dev/null
envelope_err check-empty-comparator-pin-exit2-json $? "$H3/ep2.out"
# --- an undelivered stdout is an output error even when the run itself had no verdict (exit 2)
sb "$H3" /bin/sh -c '"$@" > /dev/full' sh "$FVB" "${CHK[@]}" --guard wall=1 --json-out "$H3/full2.json" 2> /dev/null
rc=$?; w=$(jq_ "$H3/full2.json" '(d.get("verdict"), "stdout could not be written" in d.get("reason", ""))')
if [ $rc = 2 ] && [ "$w" = "('ERROR', True)" ]; then pass stdout-failure-after-no-verdict-error-envelope
else fail stdout-failure-after-no-verdict-error-envelope "rc=$rc file=$w"; fi
# --- triage with a toolchain whose bin/lean is a directory is an input error, never REFUTED
mkdir -p "$H3/tcdir/bin/lean" "$H3/ws/.lake/packages"; echo 'theorem foo (n : Nat) : n + 0 = n := by sorry' > "$H3/lemma.lean"
sb "$H3" "$FVB" triage --experimental "$H3/lemma.lean" --toolchain "$H3/tcdir" --packages "$H3/ws" --json > "$H3/tri.out" 2> /dev/null
rc=$?; v=$(jq_ "$H3/tri.out" '(d.get("ok"), d.get("status"))')
if [ $rc = 2 ] && [ "$v" = "(False, None)" ]; then pass triage-lean-is-a-directory-exit2-not-refuted
else fail triage-lean-is-a-directory-exit2-not-refuted "rc=$rc json=$v"; fi
# --- fvapi's partial response: nothing published but one ERROR envelope
sed 's/^env = {.*/env = {"timing": {"total_s": 0.1}, "status": "warming up"}/; /^       "trust": "sound"/d; /^       "diagnostics"/d; /^                        "column": 52/d' "$G/fakeapi.py" > "$H3/partial.py"
/usr/bin/python3 -I - "$H3/partial.py" <<'PY'
import sys; p = sys.argv[1]; s = open(p).read()
i = s.index("env = "); j = s.index("class H")
open(p, "w").write(s[:i] + 'env = {"timing": {"total_s": 0.1}, "status": "warming up"}\n' + s[j:])
PY
cp "$G/g3.sh" "$H3/g3.sh"; sed -i 's#fakeapi.py#partial.py#' "$H3/g3.sh"
sb "$H3" bash "$H3/g3.sh" "$H3" "$FVB" "$DATA/attempt/correct.lean"
n=$(/usr/bin/python3 -I -c '
import json, sys
s = open(sys.argv[1]).read(); d = json.JSONDecoder(); i = 0; n = 0; last = None
while i < len(s):
    while i < len(s) and s[i].isspace(): i += 1
    if i >= len(s): break
    last, i = d.raw_decode(s, i); n += 1
print(n, last.get("verdict") if isinstance(last, dict) else None)' "$H3/g3.out" 2>&1)
if [ "$(cat "$H3/g3.rc")" = 2 ] && [ "$n" = "1 ERROR" ]; then pass attempt-http-partial-response-one-error-envelope
else fail attempt-http-partial-response-one-error-envelope "rc=$(cat "$H3/g3.rc") objects,verdict=$n"; fi
# --- SIGTERM to the launched PID of `fv attempt` waiting on stdin: the process ends, ERROR exit 2
cat > "$H3/stdin.sh" <<'SH'
mkfifo "$1/fifo"; exec 7<>"$1/fifo"
"$2" attempt - --state /tmp/nosvc --pset qa --theorem qaAddZero --json < "$1/fifo" > "$1/stdin.out" 2>/dev/null & pid=$!
sleep 2; kill -TERM $pid; wait $pid; echo $? > "$1/stdin.rc"
sleep 1; /usr/bin/pgrep -f 'fv_cli.py attempt' > /dev/null && echo alive > "$1/stdin.alive"; exit 0
SH
sb "$H3" bash "$H3/stdin.sh" "$H3" "$FVB"
v=$(jq_ "$H3/stdin.out" '(d.get("verdict"), d.get("exit_code"))')
if [ "$(cat "$H3/stdin.rc")" = 2 ] && [ "$v" = "('ERROR', 2)" ] && [ ! -e "$H3/stdin.alive" ]; then pass sigterm-attempt-waiting-on-stdin-stops-error
else fail sigterm-attempt-waiting-on-stdin-stops-error "rc=$(cat "$H3/stdin.rc") $v $(cat "$H3/stdin.alive" 2>/dev/null)"; fi
# --- incr-reverify.sh: an option without its value is a usage error (exit 2), never exit 1
sb "$H3" "$FV/tools/incr/incr-reverify.sh" "$H3/a" "$H3/b" "$H3/c" "$H3/d" --threads > /dev/null 2>&1
rc=$?; if [ $rc = 2 ]; then pass incr-reverify-option-without-value-exit2; else fail incr-reverify-option-without-value-exit2 "rc=$rc"; fi

# ================================================================ comparator pin, MCP patch modes, signals during output
H4=$WORK/part4; mkdir -p "$H4"
# --- --comparator-sha256 is required wherever --challenge-sha256 is (missing -> refused; wrong -> refused)
sb "$H4" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --threads 4 --json > "$H4/cp1.out" 2> /dev/null
envelope_err check-missing-comparator-pin-refused $? "$H4/cp1.out"
sb "$H4" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $(printf '0%.0s' $(seq 64)) --threads 4 --json > "$H4/cp2.out" 2> /dev/null
envelope_err check-wrong-comparator-pin-refused-guard $? "$H4/cp2.out"
sb "$H4" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --threads 4 --json > "$H4/cp3.out" 2> /dev/null
rc=$?; v=$(jq_ "$H4/cp3.out" '(d.get("verdict"), d.get("exit_code"), "--comparator-sha256" in str(d.get("reason")))')
if [ $rc = 2 ] && [ "$v" = "('ERROR', 2, True)" ]; then pass verify-missing-comparator-pin-refused; else fail verify-missing-comparator-pin-refused "rc=$rc $v"; fi
sb "$H4" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $(printf '0%.0s' $(seq 64)) --threads 4 --json > "$H4/cp4.out" 2> /dev/null
envelope_err verify-wrong-comparator-pin-refused-guard $? "$H4/cp4.out"
# MCP: the pin is required even on a server started with --allow-unpinned-comparator
cat > "$H4/mcpcp.py" <<'PY'
import json, subprocess, sys
fv, exp, d, pin = sys.argv[1:5]
req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
    "export_file": exp, "challenge_export": d + "/challenge.export", "comparator_json": d + "/comparator.json", "challenge_sha256": pin}}}
p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", d, "--allow-root", exp.rsplit("/", 1)[0],
                    "--allow-unpinned-comparator", "--threads", "4"], input=json.dumps(req) + "\n", text=True, capture_output=True, timeout=300)
m = json.loads([l for l in p.stdout.splitlines() if l.strip()][-1])
sc = (m.get("result") or {}).get("structuredContent") or {}
print(json.dumps({"verdict": sc.get("verdict"), "exit_code": sc.get("exit_code"), "reason": sc.get("reason")}))
PY
sb "$H4" /usr/bin/python3 -I "$H4/mcpcp.py" "$FV" "$DATA/main436/main.export" "$DATA/c436" $P436 > "$H4/mcpcp.out" 2> /dev/null
v=$(jq_ "$H4/mcpcp.out" '(d.get("verdict"), d.get("exit_code"), "comparator_sha256" in str(d.get("reason")))')
if [ "$v" = "('ERROR', 2, True)" ]; then pass mcp-check-export-missing-comparator-pin-refused-despite-allow-flag
else fail mcp-check-export-missing-comparator-pin-refused-despite-allow-flag "$v"; fi
# --- MCP fv_verify_patch: an explicit optimistic / interface mode is run exact (full) and says so (a fake fvwork records it)
cat > "$H4/fakework.py" <<'PY'
import json, os, socket, sys
st = sys.argv[1]; os.makedirs(st, exist_ok=True)
s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.bind(os.path.join(st, "sock")); s.listen(4)
open(os.path.join(st, "ready"), "w").close()
while True:
    c, _ = s.accept(); buf = b""
    while not buf.endswith(b"\n"):
        x = c.recv(65536)
        if not x: break
        buf += x
    open(os.path.join(st, "req.json"), "ab").write(buf)
    c.sendall((json.dumps({"verdict": "ACCEPTED", "ok": True, "error": None}) + "\n").encode()); c.close()
PY
cat > "$H4/patch.sh" <<'SH'
/usr/bin/python3 -I "$1/fakework.py" "$1/fw" & sv=$!
for i in $(seq 1 50); do [ -e "$1/fw/ready" ] && break; sleep 0.1; done
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"fv_verify_patch","arguments":{"mode":"optimistic","files":{"Main.lean":"theorem t : True := trivial\n"}}}}' |
  "$2/tools/mcp/fastverify-mcp" --fv-root "$2" --fvwork-state "$1/fw" --threads 2 > "$1/patch.out" 2> "$1/patch.err"
kill $sv
SH
sb "$H4" bash "$H4/patch.sh" "$H4" "$FV"
mode=$(/usr/bin/python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().splitlines()[0]).get("mode"))' "$H4/fw/req.json" 2>&1)
warned=$(grep -c "experimental in v0.1 and was not used" "$H4/patch.out" 2>/dev/null)
if [ "$mode" = full ] && [ "${warned:-0}" -ge 1 ]; then pass mcp-verify-patch-optimistic-request-runs-exact-with-warning
else fail mcp-verify-patch-optimistic-request-runs-exact-with-warning "mode sent to fvwork=$mode warned=$warned"; fi
# --- SIGTERM while the final stdout delivery blocks: ERROR in the result file, exit 2 (previously: death by signal, ACCEPTED left)
cat > "$H4/blocked.sh" <<'SH'
# blocked.sh H SIG ARGS... : stdout = a pipe already full (nobody reads), send SIG once the --json-out file exists
h=$1; sig=$2; shift 2; mkfifo "$h/fifo-$sig"; exec 8<>"$h/fifo-$sig"
/usr/bin/timeout 20 /usr/bin/python3 -I -c '
import fcntl, os
fd = 8; fcntl.fcntl(fd, fcntl.F_SETFL, fcntl.fcntl(fd, fcntl.F_GETFL) | os.O_NONBLOCK)
try:
    while True:
        os.write(fd, b"\0" * 4096)
except BlockingIOError:
    pass
fcntl.fcntl(fd, fcntl.F_SETFL, fcntl.fcntl(fd, fcntl.F_GETFL) & ~os.O_NONBLOCK)' 8>&8 || exit 3   # full, whatever its size
"$@" >&8 2>/dev/null & pid=$!
# the file holds the pre-written "has not completed" ERROR from the start: wait for the run's own record
for i in $(seq 1 600); do [ -s "$h/blk-$sig.json" ] && ! grep -q "has not completed" "$h/blk-$sig.json" && break; sleep 0.1; done; sleep 1
kill -$sig $pid; wait $pid; echo $? > "$h/blk-$sig.rc"
SH
sb "$H4" bash "$H4/blocked.sh" "$H4" TERM "$FVB" "${CHK[@]}" --json-out "$H4/blk-TERM.json"
w=$(jq_ "$H4/blk-TERM.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$(cat "$H4/blk-TERM.rc")" = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass sigterm-during-final-delivery-error-file-exit2
else fail sigterm-during-final-delivery-error-file-exit2 "rc=$(cat "$H4/blk-TERM.rc") file=$w"; fi
# --- a signal while an error is being reported: exit 2, never the rejection status 1
sb "$H4" bash "$H4/blocked.sh" "$H4" HUP "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 abc \
  --comparator-sha256 $C436 --json --json-out "$H4/blk-HUP.json"
w=$(jq_ "$H4/blk-HUP.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$(cat "$H4/blk-HUP.rc")" = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass signal-during-error-reporting-exit2
else fail signal-during-error-reporting-exit2 "rc=$(cat "$H4/blk-HUP.rc") file=$w"; fi
# --- a broken stderr pipe does not kill `fv watch` before it saves its input error
cp "$R/103g.json" "$H4/wst.json"
sb "$H4" /usr/bin/python3 -I -c '
import os, subprocess, sys
r, w = os.pipe(); os.close(r)
p = subprocess.run([sys.argv[1], "watch", "--experimental", "/nonexistent/path", "--once", "--json-out", sys.argv[2]], stderr=w, stdout=subprocess.DEVNULL)
print(p.returncode)' "$FVB" "$H4/wst.json" > "$H4/wst.rc" 2> /dev/null
w=$(jq_ "$H4/wst.json" '(d.get("verdict"), d.get("exit_code"))')
if [ "$(cat "$H4/wst.rc")" = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass watch-broken-stderr-still-exit2-error-file
else fail watch-broken-stderr-still-exit2-error-file "rc=$(cat "$H4/wst.rc") file=$w"; fi
# --- cancelling `fv ci` stops the whole verification tree (fv-ci.sh, its guard, the orchestrator)
cat > "$H4/ci.sh" <<'SH'
# ci.sh H FV DATA PIN CPIN SIG
h=$1; FV=$2; DATA=$3; sig=$6; cp -r "$DATA/main436" "$h/ciproj-$sig"; rm -f "$h/ciproj-$sig/main.export"
"$FV/bin/fv" ci --project "$h/ciproj-$sig" --challenge "$DATA/c436" --challenge-sha256 "$4" --comparator-sha256 "$5" --out-dir "$h/ciout-$sig" \
  --threads 4 > "$h/ci-$sig.log" 2>&1 & pid=$!
for i in $(seq 1 600); do /usr/bin/pgrep -f 'lib/fastverify.py' > /dev/null && break; sleep 0.1; done
/usr/bin/pgrep -f 'lib/fastverify.py' > /dev/null && touch "$h/ci-$sig.started"   # the run really started
sleep 4   # a fixed delay after the orchestrator started (`fv ci` publishes run/ only at the end)
kill -$sig $pid; wait $pid; echo $? > "$h/ci-$sig.rc"
for i in $(seq 1 450); do /usr/bin/pgrep -f 'lib/fastverify.py' > /dev/null || break; sleep 0.2; done
/usr/bin/pgrep -f 'lib/fastverify.py' > /dev/null && echo orphan > "$h/ci-$sig.orphan"
# the verification must not have gone on to publish a verdict after the cancel (previously: ACCEPTED, no interruption recorded)
/usr/bin/python3 -I -c '
import json, sys
try:
    d = json.load(open(sys.argv[1]))
except Exception:
    sys.exit(0)
if d.get("verdict") in ("ACCEPTED", "REJECTED") and not d.get("interrupted"):
    print("published %s after the cancel" % d.get("verdict"))' "$h/ciout-$sig/run/result.json" >> "$h/ci-$sig.orphan.tmp"
[ -s "$h/ci-$sig.orphan.tmp" ] && cat "$h/ci-$sig.orphan.tmp" >> "$h/ci-$sig.orphan"; exit 0
SH
for sg in TERM KILL; do sb "$H4" bash "$H4/ci.sh" "$H4" "$FV" "$DATA" $P436 $C436 $sg > /dev/null 2>&1; done
if [ ! -e "$H4/ci-TERM.orphan" ] && [ "$(cat "$H4/ci-TERM.rc")" = 2 ] && [ -e "$H4/ci-TERM.started" ]; then pass fv-ci-sigterm-stops-the-tree
else fail fv-ci-sigterm-stops-the-tree "rc=$(cat "$H4/ci-TERM.rc") $(cat "$H4/ci-TERM.orphan" 2>/dev/null)"; fi
if [ "$(cat "$H4/ci-KILL.rc" 2>/dev/null)" = 137 ] && [ -e "$H4/ci-KILL.started" ] && [ ! -e "$H4/ci-KILL.orphan" ]; then
  pass fv-ci-sigkill-stops-the-tree
else fail fv-ci-sigkill-stops-the-tree "orchestrator still running after bin/fv ci was SIGKILLed"; fi

# ================================================================ fv watch pins, fv ci group guard
H5=$WORK/part5; mkdir -p "$H5"
# --- fv watch without --once ends (exit 2) on a missing comparator pin, as --once does
cp -r "$DATA/main436" "$H5/wproj"; rm -f "$H5/wproj/main.export"
sb "$H5" /usr/bin/timeout 60 "$FVB" watch --experimental "$H5/wproj" --challenge "$DATA/c436" --challenge-sha256 $P436 --interval 1 \
  --json-out "$H5/w.json" > /dev/null 2>&1
rc=$?; w=$(jq_ "$H5/w.json" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass watch-without-once-missing-comparator-pin-exit2
else fail watch-without-once-missing-comparator-pin-exit2 "rc=$rc (124 = still watching after 60 s) file=$w"; fi
# --- the fv ci group guard installs its handlers before it starts the tree (SIGTERM at 0-60 ms after start)
cat > "$H5/race.py" <<'PY'
import ast, os, signal, subprocess, sys, time
src = open(sys.argv[1]).read()
G = next(n.value.value for n in ast.parse(src).body if isinstance(n, ast.Assign) and getattr(n.targets[0], "id", "") == "_GROUP_GUARD")
def survivors():
    res = []
    for d in os.listdir("/proc"):
        if d.isdigit():
            try:
                if b"97.31" in open(f"/proc/{d}/cmdline", "rb").read():
                    st = open(f"/proc/{d}/stat").read()
                    if st[st.rindex(")") + 2] != "Z":
                        res.append(int(d))
            except OSError:
                pass
    return res
hits = 0
for d_us in range(0, 60000, 500):
    g = subprocess.Popen(["/usr/bin/python3", "-I", "-c", G, "/bin/sleep", "97.31"], start_new_session=True)
    time.sleep(d_us / 1e6); os.kill(g.pid, signal.SIGTERM); g.wait(); time.sleep(0.05)
    s = survivors()
    if s:
        hits += 1
        for p in s:
            os.kill(p, signal.SIGKILL)
print(hits)
PY
sb "$H5" /usr/bin/python3 -I "$H5/race.py" "$FV/tools/cli/fv_cli.py" > "$H5/race.out" 2> "$H5/race.err"
if [ "$(cat "$H5/race.out")" = 0 ]; then pass ci-guard-no-orphan-when-signalled-at-start
else fail ci-guard-no-orphan-when-signalled-at-start "orphaned trees in 120 tries: $(cat "$H5/race.out") $(tail -n 1 "$H5/race.err")"; fi
# --- bin/fv's grace and the guard's: a stage that ignores SIGTERM is still stopped (guard sweep at 50 s, then
# bin/fv kills the guard's whole group at 60 s), never orphaned after bin/fv exits
cat > "$H5/grace.py" <<'PY'
import os, signal, subprocess, sys, time
sys.path.insert(0, sys.argv[1] + "/tools/cli"); sys.argv = ["fv"]
import fv_cli
def slow():
    out = []
    for d in os.listdir("/proc"):
        if d.isdigit():
            try:
                if b"slowstage-77" in open(f"/proc/{d}/cmdline", "rb").read():
                    st = open(f"/proc/{d}/stat").read()
                    if st[st.rindex(")") + 2] != "Z":
                        out.append(int(d))
            except OSError:
                pass
    return out
fv_cli._CLI_STATE["pid"] = os.getpid()
g = subprocess.Popen(["/usr/bin/python3", "-I", "-c", fv_cli._GROUP_GUARD, "/bin/bash", "-c",
                      "trap '' TERM; exec -a slowstage-77 /bin/sleep 300"], start_new_session=True)
time.sleep(1.5)
try:
    fv_cli._on_signal(signal.SIGTERM, None)
except SystemExit:
    pass
time.sleep(2)
print("left", len(slow()))
for p in slow():
    os.kill(p, signal.SIGKILL)
PY
sb "$H5" /usr/bin/timeout 150 /usr/bin/python3 -I "$H5/grace.py" "$FV" > "$H5/grace.out" 2> "$H5/grace.err"
if [ "$(cat "$H5/grace.out")" = "left 0" ]; then pass ci-tree-stage-ignoring-sigterm-stopped-within-grace
else fail ci-tree-stage-ignoring-sigterm-stopped-within-grace "$(cat "$H5/grace.out") $(tail -n 1 "$H5/grace.err")"; fi

# --- project watch, trusted sidecars, fv ci option values, 4.37 checks, MCP patch modes, usage recovery, triage
# daemon-backed project watch is not offered in v0.1 (its default is incremental and it cannot check the caller's pins)
mkdir -p "$H5/fwstate"
sb "$H5" "$FVB" watch --experimental "$H5/wproj" --fvwork-state "$H5/fwstate" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 \
  --once --json-out "$H5/fw.json" > /dev/null 2>&1
rc=$?; w=$(jq_ "$H5/fw.json" '(d.get("verdict"), d.get("exit_code"), "v0.1" in str(d.get("reason")))')
if [ $rc = 2 ] && [ "$w" = "('ERROR', 2, True)" ]; then pass watch-fvwork-daemon-refused-in-v01; else fail watch-fvwork-daemon-refused-in-v01 "rc=$rc file=$w"; fi
# an explicitly trusted challenge sidecar that is missing: refused (verify and watch), never a silently unpinned run
mkdir -p "$H5/nosidecar"; cp "$DATA/c436"/{comparator.json,lean-toolchain,lakefile.toml,lake-manifest.json,Challenge.lean} "$H5/nosidecar/"
sb "$H5" "$FVB" verify "$H5/wproj" --challenge "$H5/nosidecar" --trust-challenge-sha256-file --comparator-sha256 $C436 --json > "$H5/ns.out" 2> /dev/null
rc=$?; v=$(jq_ "$H5/ns.out" '(d.get("verdict"), d.get("exit_code"), "does not exist" in str(d.get("reason")))')
if [ $rc = 2 ] && [ "$v" = "('ERROR', 2, True)" ]; then pass verify-trusted-sidecar-missing-refused; else fail verify-trusted-sidecar-missing-refused "rc=$rc $v"; fi
sb "$H5" /usr/bin/timeout 60 "$FVB" watch --experimental "$H5/wproj" --challenge "$H5/nosidecar" --trust-challenge-sha256-file --interval 1 \
  --json-out "$H5/ns2.json" > /dev/null 2>&1
rc=$?; w=$(jq_ "$H5/ns2.json" '(d.get("verdict"), d.get("exit_code"))')
if [ $rc = 2 ] && [ "$w" = "('ERROR', 2)" ]; then pass watch-trusted-sidecar-request-kept-refused; else fail watch-trusted-sidecar-request-kept-refused "rc=$rc file=$w"; fi
# fv ci: a missing option value and a missing comparator pin are usage errors (exit 2), never fv-ci.sh's exit 1
sb "$H5" "$FVB" ci --project "$H5/wproj" --threads > /dev/null 2>&1; rc1=$?
sb "$H5" "$FVB" ci --project "$H5/wproj" --challenge "$DATA/c436" --challenge-sha256 $P436 --out-dir "$H5/ciout0" > /dev/null 2>&1; rc2=$?
if [ $rc1 = 2 ] && [ $rc2 = 2 ] && [ ! -e "$H5/ciout0/run/result.json" ]; then pass ci-missing-value-and-missing-comparator-pin-exit2
else fail ci-missing-value-and-missing-comparator-pin-exit2 "rc(missing value)=$rc1 rc(no comparator pin)=$rc2"; fi
# fv check with no --pins on a 4.37 challenge uses the 4.37 trusted check (sound-auto's rule), never the default 4.36 judge
C437=$(/usr/bin/sha256sum "$DATA/c437/comparator.json" | cut -d' ' -f1)
sb "$H5" "$FVB" check "$DATA/c437/challenge.export" --challenge "$DATA/c437" --challenge-sha256 $P437 --comparator-sha256 $C437 \
  --threads 4 --json --include-raw > "$H5/c437.out" 2> /dev/null
rc=$?; v=$(jq_ "$H5/c437.out" '(d.get("verdict"), "pins-437" in json.dumps(d))')
if [ $rc = 0 ] && [ "$v" = "('ACCEPTED', True)" ]; then pass check-437-challenge-selects-437-judge; else fail check-437-challenge-selects-437-judge "rc=$rc (verdict, pins-437 named)=$v"; fi
# MCP fv_verify_patch: an out-of-schema mode is an input error; without fvwork no verification is claimed
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"fv_verify_patch","arguments":{"mode":"ful","files":{"A.lean":"x"}}}}' \
  '{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"fv_verify_patch","arguments":{"mode":"interface","files":{"A.lean":"x"}}}}' > "$H5/mm.in"
sb "$H5" /bin/sh -c '"$1/tools/mcp/fastverify-mcp" --fv-root "$1" --threads 2 < "$2" > "$3"' sh "$FV" "$H5/mm.in" "$H5/mm.out" 2> /dev/null
v=$(/usr/bin/python3 -I -c '
import json, sys
r = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
a = json.loads(r[0]["result"]["content"][0]["text"]); b = json.loads(r[1]["result"]["content"][0]["text"])
print(a.get("verdict"), "invalid mode" in str(a.get("reason")), b.get("verdict"), "no verification ran" in json.dumps(b), "was verified" in json.dumps(b))' "$H5/mm.out" 2>&1)
if [ "$v" = "ERROR True ERROR True False" ]; then pass mcp-patch-invalid-mode-refused-no-false-verified-claim
else fail mcp-patch-invalid-mode-refused-no-false-verified-claim "$v"; fi
# usage-error recovery: a negative-number file name (argparse takes it as the value) is rewritten too
( cd "$H5" && cp "$R/103g.json" "$H5/-1" && sb "$H5" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --json-out -1 --bogus > /dev/null 2>&1 )
w=$(jq_ "$H5/-1" '(d.get("verdict"), d.get("exit_code"))')
if [ "$w" = "('ERROR', 2)" ]; then pass usage-error-negative-number-output-name-rewritten; else fail usage-error-negative-number-output-name-rewritten "file=$w"; fi
# triage: a regular executable bin/lean that cannot start (missing interpreter) is an input error, never REFUTED
mkdir -p "$H5/tcbad/bin" "$H5/ws/.lake/packages"; printf '#!/nonexistent/interp\n' > "$H5/tcbad/bin/lean"; chmod +x "$H5/tcbad/bin/lean"
echo 'theorem foo (n : Nat) : n = n := rfl' > "$H5/t.lean"
sb "$H5" "$FVB" triage --experimental "$H5/t.lean" --toolchain "$H5/tcbad" --packages "$H5/ws" --json > "$H5/tri.out" 2> /dev/null
rc=$?; v=$(jq_ "$H5/tri.out" '(d.get("ok"), d.get("status"))')
if [ $rc = 2 ] && [ "$v" = "(False, None)" ]; then pass triage-lean-that-cannot-start-exit2; else fail triage-lean-that-cannot-start-exit2 "rc=$rc $v"; fi

# --- the v1 validator accepts the documented batch_attempt summary (MCP fv_verify_batch, two ACCEPTED attempts)
/usr/bin/python3 -I "$FV/schemas/fv_schema.py" validate "$DATA/batch-summary/batch-response.json" > "$H5/b21.out" 2>&1; rc=$?
/usr/bin/python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); d["accepted_count"]=3; json.dump(d, open(sys.argv[2],"w"))' \
  "$DATA/batch-summary/batch-response.json" "$H5/b21-bad.json"
/usr/bin/python3 -I "$FV/schemas/fv_schema.py" validate "$H5/b21-bad.json" > "$H5/b21b.out" 2>&1; rcb=$?
if [ $rc = 0 ] && grep -q '"valid": true' "$H5/b21.out"; then pass validator-accepts-batch-attempt-summary; else fail validator-accepts-batch-attempt-summary "rc=$rc $(head -c 200 "$H5/b21.out")"; fi
if [ $rcb = 1 ]; then pass validator-rejects-inconsistent-batch-summary-guard; else fail validator-rejects-inconsistent-batch-summary-guard "rc=$rcb"; fi

# ================================================================ empty pins, 4.37 MCP checks, batch validator
H6=$WORK/part6; mkdir -p "$H6"; cp -r "$DATA/main436" "$H6/proj"; rm -f "$H6/proj/main.export"
# --- `fv ci` with an EMPTY (or malformed / `--opt=`) pin is refused before anything starts
sb "$H6" "$FVB" ci --project "$H6/proj" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 "" --out-dir "$H6/o1" > /dev/null 2>&1; r1=$?
sb "$H6" "$FVB" ci --project "$H6/proj" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256=$C436 --out-dir "$H6/o2" > /dev/null 2>&1; r2=$?
if [ $r1 = 2 ] && [ $r2 = 2 ] && [ ! -e "$H6/o1/run/result.json" ] && [ ! -e "$H6/o2/run/result.json" ]; then pass ci-empty-or-equals-spelled-comparator-pin-refused
else fail ci-empty-or-equals-spelled-comparator-pin-refused "rc(empty)=$r1 rc(--opt=)=$r2"; fi
# --- MCP fv_check_export with no pins on a 4.37 challenge uses the 4.37 trusted check
C437=$(/usr/bin/sha256sum "$DATA/c437/comparator.json" | cut -d' ' -f1)
cat > "$H6/m437.py" <<'PY'
import json, subprocess, sys
fv, d, pin, cpin = sys.argv[1:5]
req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
    "export_file": d + "/challenge.export", "challenge_export": d + "/challenge.export", "comparator_json": d + "/comparator.json",
    "challenge_sha256": pin, "comparator_sha256": cpin, "include_raw": True, "threads": 4}}}
p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", d, "--threads", "4"],
                   input=json.dumps(req) + "\n", text=True, capture_output=True, timeout=600)
m = json.loads([l for l in p.stdout.splitlines() if l.strip()][-1])
sc = (m.get("result") or {}).get("structuredContent") or {}
print(json.dumps({"verdict": sc.get("verdict"), "pins437": "pins-437" in json.dumps(sc)}))
PY
sb "$H6" /usr/bin/python3 -I "$H6/m437.py" "$FV" "$DATA/c437" $P437 $C437 > "$H6/m437.out" 2> /dev/null
v=$(jq_ "$H6/m437.out" '(d.get("verdict"), d.get("pins437"))')
if [ "$v" = "('ACCEPTED', True)" ]; then pass mcp-check-export-437-selects-437-judge; else fail mcp-check-export-437-selects-437-judge "$v"; fi
# --- the batch validator rejects a boolean best_accepted_index and a nested batch summary as an item
/usr/bin/python3 -I -c '
import json, sys
d = json.load(open(sys.argv[1]))
a = json.loads(json.dumps(d)); a["best_accepted_index"] = True
b = json.loads(json.dumps(d)); b["results"][0]["result"] = json.loads(json.dumps(d))
json.dump(a, open(sys.argv[2], "w")); json.dump(b, open(sys.argv[3], "w"))' "$DATA/batch-summary/batch-response.json" "$H6/bool.json" "$H6/nested.json"
/usr/bin/python3 -I "$FV/schemas/fv_schema.py" validate "$H6/bool.json" > /dev/null 2>&1; ra=$?
/usr/bin/python3 -I "$FV/schemas/fv_schema.py" validate "$H6/nested.json" > /dev/null 2>&1; rb=$?
/usr/bin/python3 -I "$FV/schemas/fv_schema.py" validate "$DATA/batch-summary/batch-response.json" > /dev/null 2>&1; rc0=$?
if [ $ra = 1 ] && [ $rb = 1 ] && [ $rc0 = 0 ]; then pass validator-rejects-bool-index-and-nested-batch
else fail validator-rejects-bool-index-and-nested-batch "rc(bool)=$ra rc(nested)=$rb rc(valid)=$rc0"; fi

# ================================================================ experimental surface, release rule, signals, output records, pins
H7=$WORK/part7; mkdir -p "$H7"; cp -r "$DATA/main436" "$H7/proj"; rm -f "$H7/proj/main.export"
# --- scope: fv watch and fv triage are EXPERIMENTAL in v0.1 (refused without --experimental, exit 2)
echo 'theorem foo (n : Nat) : n = n := rfl' > "$H7/t.lean"
sb "$H7" "$FVB" watch "$H7/proj" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --once > /dev/null 2> "$H7/w.out"; rw=$?
sb "$H7" "$FVB" triage "$H7/t.lean" --static-only --json > "$H7/t.out" 2> /dev/null; rt=$?
if [ $rw = 2 ] && [ $rt = 2 ] && grep -q EXPERIMENTAL "$H7/w.out" && grep -q EXPERIMENTAL "$H7/t.out"; then pass watch-and-triage-refused-without-experimental
else fail watch-and-triage-refused-without-experimental "rc(watch)=$rw rc(triage)=$rt"; fi
# --- (experimental surface) the file-attempt watch refuses a caller's challenge identity (never ignored)
sb "$H7" /usr/bin/timeout 60 "$FVB" watch --experimental "$H7/t.lean" --challenge "$DATA/c436" --challenge-sha256 $P436 \
  --comparator-sha256 $C436 --fvserve-state "$H7/nostate" --pset qa --theorem foo --once > /dev/null 2> "$H7/wf.err"; rwf=$?
if [ $rwf = 2 ] && grep -q "attempt mode" "$H7/wf.err"; then pass watch-file-attempt-refuses-challenge-identity
else fail watch-file-attempt-refuses-challenge-identity "rc=$rwf $(head -c 160 "$H7/wf.err")"; fi
# --- (stable surface) one release rule: --notary on a 4.37 challenge is declined, an empty --pins is refused
C437=$(/usr/bin/sha256sum "$DATA/c437/comparator.json" | cut -d' ' -f1)
sb "$H7" "$FVB" check "$DATA/c437/challenge.export" --challenge "$DATA/c437" --challenge-sha256 $P437 --comparator-sha256 $C437 --notary \
  --threads 4 --json > "$H7/n437.out" 2> /dev/null; rn=$?
sb "$H7" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --pins "" \
  --threads 4 --json > "$H7/pe.out" 2> /dev/null; rp=$?
vn=$(jq_ "$H7/n437.out" '(d.get("verdict"), "notary" in str(d.get("reason")))'); vp=$(jq_ "$H7/pe.out" 'd.get("verdict")')
if [ $rn = 2 ] && [ "$vn" = "('ERROR', True)" ] && [ $rp = 2 ] && [ "$vp" = ERROR ]; then pass check-notary-437-declined-and-empty-pins-refused
else fail check-notary-437-declined-and-empty-pins-refused "notary: rc=$rn $vn; --pins '': rc=$rp $vp"; fi
# --- (stable surface) a signal on entry to argument parsing writes ERROR to the requested output (from argv), exit 2
echo '{"api_version": "1.0", "mode": "export_in", "verdict": "ACCEPTED", "exit_code": 0}' > "$H7/ps.json"   # an earlier fv record
cat > "$H7/psig.py" <<'PY'
import os, signal, sys
fvroot, out = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(fvroot, "tools", "cli"))
sys.argv = ["fv", "check", "/nonexistent/x.export", "--challenge", "/nonexistent/c", "--challenge-sha256", "0" * 64,
            "--comparator-sha256", "1" * 64, "--json-out", out, "--json"]
import fv_cli
orig = fv_cli._CliArgumentParser.parse_args
def pa(self, *a, **k):
    os.kill(os.getpid(), signal.SIGTERM)
    return orig(self, *a, **k)
fv_cli._CliArgumentParser.parse_args = pa
sys.exit(fv_cli._run_cli())
PY
sb "$H7" /usr/bin/python3 -I "$H7/psig.py" "$FV" "$H7/ps.json" > "$H7/ps.out" 2> "$H7/ps.err"; rps=$?
vf=$(jq_ "$H7/ps.json" '(d.get("verdict"), "signal" in str(d.get("reason")))'); vo=$(jq_ "$H7/ps.out" 'd.get("verdict")')
if [ $rps = 2 ] && [ "$vf" = "('ERROR', True)" ] && [ "$vo" = ERROR ]; then pass signal-during-argument-parsing-writes-error
else fail signal-during-argument-parsing-writes-error "rc=$rps file=$vf stdout=$vo"; fi
# --- every requested output file is replaced by an ERROR record as soon as
# its path is known; only this run's completed verdict overwrites it: a run killed by SIGKILL never leaves an earlier ACCEPTED
echo '{"api_version": "1.0", "mode": "project", "verdict": "ACCEPTED", "accepted": true, "reward": 1.0, "exit_code": 0}' > "$H7/k.json"
cp "$H7/k.json" "$H7/k.sarif"
sb "$H7" /bin/bash -c '"$1" verify "$2" --challenge "$3" --challenge-sha256 "$4" --comparator-sha256 "$5" --threads 4 --json-out "$6/k.json" \
  --sarif "$6/k.sarif" > /dev/null 2>&1 & p=$!; sleep 3; kill -9 $p; wait $p; echo $? > "$6/k.rc"; sleep 2' _ "$FVB" "$DATA/main436" "$DATA/c436" $P436 $C436 "$H7"
vk=$(jq_ "$H7/k.json" 'd.get("verdict")'); vs=$(jq_ "$H7/k.sarif" '"ACCEPTED" not in json.dumps(d)')
if [ "$(cat "$H7/k.rc")" = 137 ] && [ "$vk" = ERROR ] && [ "$vs" = True ]; then pass killed-run-leaves-no-earlier-verdict-in-outputs
else fail killed-run-leaves-no-earlier-verdict-in-outputs "killed child status=$(cat "$H7/k.rc") json-out=$vk sarif-clean=$vs"; fi
# --- --incr-base without a challenge pin and malformed pins are usage errors (exit 2, never 1)
sb "$H7" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --incr-base "$H7/nobase" --json > "$H7/m6a.out" 2> /dev/null; r6a=$?
sb "$H7" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 NOTHEX --comparator-sha256 $C436 --json > "$H7/m6b.out" 2> /dev/null; r6b=$?
sb "$H7" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 NOTHEX --comparator-sha256 $C436 --json \
  > "$H7/m6c.out" 2> /dev/null; r6c=$?
v6=$(for f in m6a m6b m6c; do jq_ "$H7/$f.out" 'd.get("verdict")'; done | tr '\n' ' ')
if [ $r6a = 2 ] && [ $r6b = 2 ] && [ $r6c = 2 ] && [ "$v6" = "ERROR ERROR ERROR " ]; then pass incr-base-without-pin-and-malformed-pins-exit2
else fail incr-base-without-pin-and-malformed-pins-exit2 "rc=$r6a/$r6b/$r6c verdicts=$v6"; fi
# --- MCP's incremental project call forwards the CALLER's verified comparator pin to
# incr-reverify, or refuses without one (in-process: the v0.1 public tool never reaches it; incr-reverify stubbed)
rm -rf "$H7/chal"; cp -r "$DATA/c436" "$H7/chal"
cat > "$H7/psrv.py" <<'PY'
import json, os, subprocess, sys
fv, h, pin, cpin = sys.argv[1:5]
sys.path.insert(0, os.path.join(fv, "tools", "mcp")); sys.path.insert(0, os.path.join(fv, "schemas"))
import mcp_server as m
cap = {}
class Stop(Exception):
    pass
orig = m.McpServer
class Grab(orig):
    def __init__(self, args):
        cap["args"] = args
        raise Stop()
m.McpServer = Grab
sys.argv = ["fastverify-mcp", "--fv-root", fv, "--allow-root", h, "--allow-incr-base", "--challenge", "reg=%s/chal:%s" % (h, pin)]
try:
    m.main()
except Stop:
    pass
m.McpServer = orig
srv = orig(cap["args"])
cmds = []
def fake(fv_root, cmd, timeout, grace=5.0):
    cmds.append(list(cmd))
    return subprocess.CompletedProcess(cmd, 2, "", "stub")
m.run_subprocess_guarded = fake
base = os.path.join(h, "ibase"); os.makedirs(base, exist_ok=True)
srv._tool_fv_verify_project({"project_dir": h + "/proj", "challenge_dir": h + "/chal", "challenge_sha256": pin,
                             "comparator_sha256": cpin, "incr_base": base})
a = bool(cmds) and "--comparator-sha256" in cmds[-1] and cmds[-1][cmds[-1].index("--comparator-sha256") + 1] == cpin
n = len(cmds)
env_b, _ = srv._tool_fv_verify_project({"project_dir": h + "/proj", "challenge_id": "reg", "incr_base": base})
b = len(cmds) == n and env_b.get("verdict") == "ERROR" and "comparator_sha256" in str(env_b.get("reason"))
print(json.dumps({"forwarded": a, "refused_without_pin": b}))
PY
sb "$H7" /usr/bin/python3 -I "$H7/psrv.py" "$FV" "$H7" $P436 $C436 > "$H7/psrv.out" 2> "$H7/psrv.err"
vi=$(jq_ "$H7/psrv.out" '(d.get("forwarded"), d.get("refused_without_pin"))')
if [ "$vi" = "(True, True)" ]; then pass mcp-incremental-forwards-caller-comparator-pin-or-refuses
else fail mcp-incremental-forwards-caller-comparator-pin-or-refuses "$vi $(tail -c 200 "$H7/psrv.err")"; fi
# --- MCP fv_triage_sublemma is opt-in: refused (isError, says why) unless the server runs with
# --experimental or FV_EXPERIMENTAL=1 (a label is not enough: MCP clients call tools without reading labels)
cat > "$H7/mtri.py" <<'PY'
import json, os, subprocess, sys
fv, h = sys.argv[1:3]
reqs = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
        {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_triage_sublemma", "arguments": {
            "source": "theorem q (n : Nat) : n + 0 = n := by sorry\n", "static_only": True}}}]
inp = "".join(json.dumps(r) + "\n" for r in reqs)
res = {}
for mode, extra, env in (("none", [], {}), ("flag", ["--experimental"], {}), ("env", [], {"FV_EXPERIMENTAL": "1"})):
    e = {k: v for k, v in os.environ.items() if k != "FV_EXPERIMENTAL"}; e.update(env)
    p = subprocess.run([os.path.join(fv, "tools", "mcp", "fastverify-mcp"), "--allow-root", h] + extra, input=inp,
                       capture_output=True, text=True, timeout=120, env=e, cwd=h)
    res[mode] = None
    for ln in p.stdout.splitlines():
        try:
            o = json.loads(ln)
        except ValueError:
            continue
        if o.get("id") == 2:
            r = o.get("result") or {}
            sc = r.get("structuredContent") or {}
            res[mode] = (bool(r.get("isError")), "EXPERIMENTAL" in str(sc.get("error")) and "--experimental" in str(sc.get("error")))
print(json.dumps(res))
PY
sb "$H7" /usr/bin/python3 -I "$H7/mtri.py" "$FV" "$H7" > "$H7/mtri.out" 2> "$H7/mtri.err"
vt=$(jq_ "$H7/mtri.out" '(d.get("none"), d.get("flag"), d.get("env"))')
if [ "$vt" = "([True, True], [False, False], [False, False])" ]; then pass mcp-triage-refused-without-experimental-opt-in
else fail mcp-triage-refused-without-experimental-opt-in "(none, --experimental, FV_EXPERIMENTAL=1) = $vt"; fi
# --- an explicit --pins / MCP pins that is not the challenge release's own judge is
# refused (ERROR, exit 2) on fv check (sound / --low-mem / --frontier) and MCP fv_check_export; the release's own profile runs
C437=$(/usr/bin/sha256sum "$DATA/c437/comparator.json" | cut -d' ' -f1)
b1=""
for ex in "--pins 436" "--pins default" "--pins check/sound/pins.env" "--low-mem --pins 436" "--frontier --pins 436"; do
  sb "$H7" "$FVB" check "$DATA/c437/challenge.export" --challenge "$DATA/c437" --challenge-sha256 $P437 --comparator-sha256 $C437 \
    $ex --threads 4 --json > "$H7/b1.out" 2> /dev/null; rb=$?
  b1="$b1 $rb:$(jq_ "$H7/b1.out" '(d.get("verdict"), "own trusted check" in str(d.get("reason")))')"
done
sb "$H7" "$FVB" check "$DATA/c437/challenge.export" --challenge "$DATA/c437" --challenge-sha256 $P437 --comparator-sha256 $C437 \
  --pins 437 --threads 4 --json > "$H7/b1ok.out" 2> /dev/null; rok=$?
vok=$(jq_ "$H7/b1ok.out" 'd.get("verdict")')
want=" 2:('ERROR', True) 2:('ERROR', True) 2:('ERROR', True) 2:('ERROR', True) 2:('ERROR', True)"
if [ "$b1" = "$want" ] && [ $rok = 0 ] && [ "$vok" = ACCEPTED ]; then pass check-explicit-other-release-pins-refused
else fail check-explicit-other-release-pins-refused "436/default/path/low-mem/frontier:$b1; --pins 437: rc=$rok $vok"; fi
cat > "$H7/mb1.py" <<'PY'
import json, subprocess, sys
fv, d, pin, cpin = sys.argv[1:5]
out = {}
for k, extra in (("436", {"pins": "436"}), ("436lm", {"pins": "436", "low_mem": True}), ("437", {"pins": "437"})):
    req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": dict({
        "export_file": d + "/challenge.export", "challenge_export": d + "/challenge.export", "comparator_json": d + "/comparator.json",
        "challenge_sha256": pin, "comparator_sha256": cpin, "threads": 4}, **extra)}}
    p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", d, "--threads", "4"],
                       input=json.dumps(req) + "\n", text=True, capture_output=True, timeout=600)
    m = json.loads([l for l in p.stdout.splitlines() if l.strip()][-1])
    sc = (m.get("result") or {}).get("structuredContent") or {}
    out[k] = [sc.get("verdict"), "own trusted check" in str(sc.get("reason"))]
print(json.dumps(out))
PY
sb "$H7" /usr/bin/python3 -I "$H7/mb1.py" "$FV" "$DATA/c437" $P437 $C437 > "$H7/mb1.out" 2> /dev/null
vm=$(jq_ "$H7/mb1.out" '(d.get("436"), d.get("436lm"), d.get("437"))')
if [ "$vm" = "(['ERROR', True], ['ERROR', True], ['ACCEPTED', False])" ]; then pass mcp-check-export-explicit-other-release-pins-refused
else fail mcp-check-export-explicit-other-release-pins-refused "(436, 436 low_mem, 437) = $vm"; fi
# --- validate_v1 never accepts mode batch_attempt as a single envelope (the CLI validator routes by mode)
/usr/bin/python3 -I -c 'import json, sys; json.dump({"api_version": "1.0", "mode": "batch_attempt", "verdict": "ACCEPTED", "accepted": True,
  "reward": 1.0, "exit_code": 0, "trust": "sound", "verdict_basis": "accepted", "timing": {"total_s": 0.1}, "diagnostics": []},
  open(sys.argv[1], "w"))' "$H7/bsingle.json"
sb "$H7" /usr/bin/python3 -I "$FV/schemas/fv_schema.py" validate "$H7/bsingle.json" > "$H7/bv.out" 2> /dev/null; rbv=$?
vbv=$(jq_ "$H7/bv.out" 'd.get("valid")')
if [ $rbv = 1 ] && [ "$vbv" = False ]; then pass validator-rejects-batch-mode-single-envelope
else fail validator-rejects-batch-mode-single-envelope "rc=$rbv valid=$vbv"; fi
# --- an output that cannot be replaced is refused BEFORE anything runs (exit 2), the others get ERROR
mkdir -p "$H7/sarif-is-a-dir"; echo '{"api_version": "1.0", "verdict": "ACCEPTED", "exit_code": 0}' > "$H7/n3.json"
sb "$H7" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 \
  --json-out "$H7/n3.json" --sarif "$H7/sarif-is-a-dir" --json > "$H7/n3.out" 2> /dev/null; rn3=$?
vn3=$(jq_ "$H7/n3.out" '(d.get("verdict"), "refused before running" in str(d.get("reason")))'); fn3=$(jq_ "$H7/n3.json" 'd.get("verdict")')
if [ $rn3 = 2 ] && [ "$vn3" = "('ERROR', True)" ] && [ "$fn3" = ERROR ]; then pass unreplaceable-output-refused-before-running
else fail unreplaceable-output-refused-before-running "rc=$rn3 stdout=$vn3 json-out=$fn3"; fi
# --- an output path that is (inside) an input is refused before anything is written; the input
# stays byte-identical (verify: --json-out PROJECT/Main.lean; check: --json-out = the export file)
rm -rf "$H7/cproj"; cp -r "$DATA/main436" "$H7/cproj"; rm -f "$H7/cproj/main.export"; cp "$DATA/main436/main.export" "$H7/cexp.export"
m0=$(/usr/bin/sha256sum < "$H7/cproj/Main.lean"); e0=$(/usr/bin/sha256sum < "$H7/cexp.export")
sb "$H7" "$FVB" verify "$H7/cproj" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --threads 4 \
  --json-out "$H7/cproj/Main.lean" --json > "$H7/col1.out" 2> /dev/null; rc1=$?
sb "$H7" "$FVB" check "$H7/cexp.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --threads 4 \
  --json-out "$H7/cexp.export" --json > "$H7/col2.out" 2> /dev/null; rc2=$?
m1=$(/usr/bin/sha256sum < "$H7/cproj/Main.lean"); e1=$(/usr/bin/sha256sum < "$H7/cexp.export")
v1=$(jq_ "$H7/col1.out" 'd.get("verdict")'); v2=$(jq_ "$H7/col2.out" 'd.get("verdict")')
if [ $rc1 = 2 ] && [ $rc2 = 2 ] && [ "$v1" = ERROR ] && [ "$v2" = ERROR ] && [ "$m0" = "$m1" ] && [ "$e0" = "$e1" ]; then
  pass output-colliding-with-input-refused-input-untouched
else fail output-colliding-with-input-refused-input-untouched "verify rc=$rc1 $v1, check rc=$rc2 $v2, Main.lean same=$([ "$m0" = "$m1" ] && echo y), export same=$([ "$e0" = "$e1" ] && echo y)"; fi
# --- a report inside a fresh (absent or empty) --out does not make --out "used": the run is judged
mkdir -p "$H7/freshout"
sb "$H7" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --threads 4 \
  --out "$H7/freshout" --json-out "$H7/freshout/envelope.json" --json > "$H7/fo.out" 2> /dev/null; rfo=$?
vfo=$(jq_ "$H7/fo.out" 'd.get("verdict")'); ffo=$(jq_ "$H7/freshout/envelope.json" 'd.get("verdict")')
if [ $rfo = 0 ] && [ "$vfo" = ACCEPTED ] && [ "$ffo" = ACCEPTED ]; then pass report-inside-fresh-out-dir-runs-guard
else fail report-inside-fresh-out-dir-runs-guard "rc=$rfo stdout=$vfo file=$ffo"; fi
# --- --frontier with --notary (two judges) is refused on fv check and MCP fv_check_export
sb "$H7" "$FVB" check "$DATA/c437/challenge.export" --challenge "$DATA/c437" --challenge-sha256 $P437 --comparator-sha256 $C437 \
  --frontier --notary --json > "$H7/fn.out" 2> /dev/null; rfn=$?
vfn=$(jq_ "$H7/fn.out" 'd.get("verdict")')
cat > "$H7/mfn.py" <<'PY'
import json, subprocess, sys
fv, d, pin, cpin = sys.argv[1:5]
req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
    "export_file": d + "/challenge.export", "challenge_export": d + "/challenge.export", "comparator_json": d + "/comparator.json",
    "challenge_sha256": pin, "comparator_sha256": cpin, "frontier": True, "notary": True, "threads": 4}}}
p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", d, "--threads", "4"],
                   input=json.dumps(req) + "\n", text=True, capture_output=True, timeout=600)
m = json.loads([l for l in p.stdout.splitlines() if l.strip()][-1])
print(json.dumps({"verdict": ((m.get("result") or {}).get("structuredContent") or {}).get("verdict")}))
PY
sb "$H7" /usr/bin/python3 -I "$H7/mfn.py" "$FV" "$DATA/c437" $P437 $C437 > "$H7/mfn.out" 2> /dev/null
vmfn=$(jq_ "$H7/mfn.out" 'd.get("verdict")')
if [ $rfn = 2 ] && [ "$vfn" = ERROR ] && [ "$vmfn" = ERROR ]; then pass frontier-plus-notary-refused
else fail frontier-plus-notary-refused "cli rc=$rfn $vfn, mcp $vmfn"; fi
# --- `fv ci` is EXPERIMENTAL on every variant: refused without --experimental / FV_EXPERIMENTAL_CI=1
sb "$H7" /usr/bin/env -u FV_EXPERIMENTAL_CI "$FVB" ci --project "$H7/proj" --challenge "$DATA/c436" --challenge-sha256 $P436 \
  --comparator-sha256 $C436 --out-dir "$H7/cig" > /dev/null 2> "$H7/cig.err"; rcg=$?
if [ $rcg = 2 ] && grep -q "EXPERIMENTAL" "$H7/cig.err" && [ ! -e "$H7/cig/result-v1.json" ]; then pass ci-refused-without-experimental-opt-in
else fail ci-refused-without-experimental-opt-in "rc=$rcg $(head -c 160 "$H7/cig.err")"; fi
# --- MCP fv_verify_attempt publishes a backend envelope only if it is one valid single attempt
cat > "$H7/matt.py" <<'PY'
import json, os, sys
fv, h = sys.argv[1:3]
sys.path.insert(0, os.path.join(fv, "tools", "mcp")); sys.path.insert(0, os.path.join(fv, "schemas"))
import mcp_server as m
cap = {}
class Stop(Exception):
    pass
orig = m.McpServer
class Grab(orig):
    def __init__(self, args):
        cap["args"] = args
        raise Stop()
m.McpServer = Grab
sys.argv = ["fastverify-mcp", "--fv-root", fv, "--allow-root", h, "--default-pset", "qa"]
try:
    m.main()
except Stop:
    pass
m.McpServer = orig
srv = orig(cap["args"])
batch = {"api_version": "1.0", "mode": "batch_attempt", "verdict": "ACCEPTED", "accepted": True, "reward": 1.0, "exit_code": 0,
         "trust": "sound", "verdict_basis": "accepted", "timing": {"total_s": 0.1}, "diagnostics": [], "results": []}
res = []
for reply in (dict(batch), [], None):   # a list / null reply too: an ERROR envelope, never a crash
    srv.call_fvserve = lambda req, timeout=None, r=reply: r
    env, _ = srv.tool_fv_verify_attempt({"theorem": "qaAddZero", "source": "theorem qaAddZero (n : Nat) : n + 0 = n := rfl\n"})
    res.append((env.get("mode"), env.get("verdict"), env.get("exit_code")))
print(json.dumps({"mode": res[0][0], "verdict": res[0][1], "exit_code": res[0][2], "all": [list(r) for r in res]}))
PY
sb "$H7" /usr/bin/python3 -I "$H7/matt.py" "$FV" "$H7" > "$H7/matt.out" 2> "$H7/matt.err"
vat=$(jq_ "$H7/matt.out" '(d.get("mode"), d.get("verdict"), d.get("exit_code"), all(r == ["attempt", "ERROR", 2] for r in d.get("all") or []))')
if [ "$vat" = "('attempt', 'ERROR', 2, True)" ]; then pass mcp-verify-attempt-refuses-non-single-backend-envelope
else fail mcp-verify-attempt-refuses-non-single-backend-envelope "$vat $(tail -c 160 "$H7/matt.err")"; fi
# --- a failed retry never leaves an earlier ACCEPTED: a read-only (0444) --json-out in a
# writable directory is replaced atomically, and the verdict records in a used --out directory are replaced by ERROR
rm -rf "$H7/uo4"; mkdir -p "$H7/uo4"; echo '{"api_version": "1.0", "verdict": "ACCEPTED", "exit_code": 0}' > "$H7/uo4/result.json"
echo '{"api_version": "1.0", "mode": "export_in", "verdict": "ACCEPTED", "exit_code": 0}' > "$H7/ro.json"; chmod 0444 "$H7/ro.json"
sb "$H7" "$FVB" check "$H7/no-such.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 \
  --json-out "$H7/ro.json" --json > "$H7/ro.out" 2> /dev/null; rro=$?
sb "$H7" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --threads 4 \
  --out "$H7/uo4" --json > "$H7/uo4.out" 2> /dev/null; ruo=$?
vro=$(jq_ "$H7/ro.json" 'd.get("verdict")'); vuo=$(jq_ "$H7/uo4/result.json" 'd.get("verdict")')
if [ $rro = 2 ] && [ "$vro" = ERROR ] && [ $ruo = 2 ] && [ "$vuo" = ERROR ]; then pass failed-retry-replaces-readonly-report-and-out-dir-verdict
else fail failed-retry-replaces-readonly-report-and-out-dir-verdict "0444 json-out: rc=$rro $vro; used --out: rc=$ruo result.json=$vuo"; fi
# --- (incr-reverify requires the caller's comparator pin) the (v0.1-unreachable) incremental branch of
# `fv verify --incr-base` forwards the caller's verified --comparator-sha256 (in-process, incremental switched on, child stubbed)
mkdir -p "$H7/ibase2"; chmod 700 "$H7/ibase2"   # a base tree is controlled by the caller alone
cat > "$H7/vincr.py" <<'PY'
import json, os, subprocess, sys
fv, h, proj, chal, pin, cpin = sys.argv[1:7]
sys.path.insert(0, os.path.join(fv, "tools", "cli"))
sys.argv = ["fv", "verify", proj, "--challenge", chal, "--challenge-sha256", pin, "--comparator-sha256", cpin,
            "--incr-base", os.path.join(h, "ibase2"), "--out", os.path.join(h, "vincr-out"), "--json"]
import fv_cli
fv_cli._INCR_IN_BIN_FV = True
fv_cli._incr_toolchain = lambda p, c: ("/nonexistent-tc", None)
if hasattr(fv_cli, "cli_scan_no_links"):   # the base-tree scan (its own rows test it) is not what this row checks
    fv_cli.cli_scan_no_links = lambda path, what, create=False: os.path.realpath(path)
seen = []
orig = subprocess.run
def fake(cmd, *a, **k):
    if any(str(x).endswith("incr-reverify.sh") for x in cmd):
        seen.append(list(cmd))
        return subprocess.CompletedProcess(cmd, 2, "", "")
    return orig(cmd, *a, **k)
fv_cli.subprocess.run = fake
try:
    fv_cli.main()
except BaseException:
    pass
c = seen[0] if seen else []
json.dump({"called": bool(seen), "forwarded": "--comparator-sha256" in c and c[c.index("--comparator-sha256") + 1] == cpin},
          open(os.path.join(h, "vincr.res"), "w"))
PY
sb "$H7" /usr/bin/python3 -I "$H7/vincr.py" "$FV" "$H7" "$DATA/main436" "$DATA/c436" $P436 $C436 > "$H7/vincr.out" 2> "$H7/vincr.err"
vvi=$(jq_ "$H7/vincr.res" '(d.get("called"), d.get("forwarded"))')
if [ "$vvi" = "(True, True)" ]; then pass verify-incr-branch-forwards-caller-comparator-pin
else fail verify-incr-branch-forwards-caller-comparator-pin "$vvi $(tail -c 160 "$H7/vincr.err")"; fi
# --- the notary judge is EXPERIMENTAL in v0.1: `fv check --notary` needs --experimental, MCP
# fv_check_export notary needs the server's opt-in (--experimental / FV_EXPERIMENTAL=1); both refuse with exit 2 / ERROR and say why
sb "$H7" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 \
  --notary --threads 4 --json > "$H7/ng1.out" 2> /dev/null; rng1=$?
sb "$H7" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 \
  --notary --experimental --threads 4 --json > "$H7/ng2.out" 2> /dev/null; rng2=$?
vng1=$(jq_ "$H7/ng1.out" '(d.get("verdict"), "EXPERIMENTAL" in str(d.get("reason")))')
vng2=$(jq_ "$H7/ng2.out" '"is EXPERIMENTAL" in str(d.get("reason"))')
if [ $rng1 = 2 ] && [ "$vng1" = "('ERROR', True)" ] && [ "$vng2" = False ]; then pass check-notary-needs-experimental
else fail check-notary-needs-experimental "no flag: rc=$rng1 $vng1; --experimental: rc=$rng2 gate-refused=$vng2"; fi
cat > "$H7/mng.py" <<'PY'
import json, os, subprocess, sys
fv, d, pin, cpin, ex = sys.argv[1:6]
req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
    "export_file": d + "/main436/main.export", "challenge_export": d + "/c436/challenge.export",
    "comparator_json": d + "/c436/comparator.json", "challenge_sha256": pin, "comparator_sha256": cpin, "notary": True, "threads": 4}}}
out = {}
for k, extra in (("none", []), ("opted", ["--experimental"])):
    p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", d, "--threads", "4"] + extra,
                       input=json.dumps(req) + "\n", text=True, capture_output=True, timeout=900)
    m = json.loads([l for l in p.stdout.splitlines() if l.strip()][-1])
    sc = (m.get("result") or {}).get("structuredContent") or {}
    out[k] = [sc.get("verdict"), "is EXPERIMENTAL" in str(sc.get("reason"))]
print(json.dumps(out))
PY
sb "$H7" /usr/bin/python3 -I "$H7/mng.py" "$FV" "$DATA" $P436 $C436 x > "$H7/mng.out" 2> /dev/null
vmng=$(jq_ "$H7/mng.out" '(d.get("none"), (d.get("opted") or [None, None])[1])')
if [ "$vmng" = "(['ERROR', True], False)" ]; then pass mcp-check-export-notary-needs-experimental
else fail mcp-check-export-notary-needs-experimental "(no opt-in, opted-in gate-refused) = $vmng"; fi
# --- the usage-error recovery writes an ERROR record only where nothing else is
# touched: never onto / inside another path of the command line, never onto a file that is not an fv record, never via a link
rm -rf "$H7/ue"; mkdir -p "$H7/ue"; cp "$DATA/main436/main.export" "$H7/ue/exp.export"; cp -r "$DATA/main436" "$H7/ue/proj"
rm -f "$H7/ue/proj/main.export"; echo 'theorem a : True := trivial' > "$H7/ue/a.lean"; echo 'my notes' > "$H7/ue/notes.txt"
h0=$(cd "$H7/ue" && /usr/bin/sha256sum exp.export proj/Main.lean a.lean notes.txt)
sb "$H7" "$FVB" check "$H7/ue/exp.export" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 \
  --json-out "$H7/ue/exp.export" --no-such-option > /dev/null 2>&1; u1=$?
sb "$H7" "$FVB" verify "$H7/ue/proj" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 \
  --json-out "$H7/ue/proj/Main.lean" --threads > /dev/null 2>&1; u2=$?
sb "$H7" "$FVB" attempt "$H7/ue/a.lean" --json-out "$H7/ue/a.lean" --bogus > /dev/null 2>&1; u3=$?
sb "$H7" "$FVB" check "$H7/ue/exp.export" --challenge "$DATA/c436" --json-out "$H7/ue/notes.txt" --bogus > /dev/null 2>&1; u4=$?
h1=$(cd "$H7/ue" && /usr/bin/sha256sum exp.export proj/Main.lean a.lean notes.txt)
if [ "$u1$u2$u3$u4" = 2222 ] && [ "$h0" = "$h1" ]; then pass usage-error-recovery-never-touches-inputs-or-foreign-files-guard
else fail usage-error-recovery-never-touches-inputs-or-foreign-files-guard "rc=$u1$u2$u3$u4 inputs unchanged=$([ "$h0" = "$h1" ] && echo y || echo n)"; fi
# --- the single-attempt HTTP endpoint refuses a batch summary (one ERROR envelope, exit 2)
sed 's#^env = .*#env = json.load(open(sys.argv[2]))#' "$G/fakeapi.py" > "$H7/batchapi.py"
/usr/bin/python3 -I - "$H7/batchapi.py" <<'PY'
import sys; p = sys.argv[1]; s = open(p).read()
i = s.index("env = "); j = s.index("class H")
open(p, "w").write(s[:i] + 'env = json.load(open(sys.argv[1]))\n' + s[j:])
PY
cat > "$H7/b.sh" <<'SH'
/usr/bin/python3 -I "$1/batchapi.py" "$4" > "$1/port" & sv=$!
for i in $(seq 1 50); do [ -s "$1/port" ] && break; sleep 0.1; done
"$2" attempt "$3" --http "http://127.0.0.1:$(cat "$1/port")" --pset qa --theorem qaAddZero --json --timeout 10 > "$1/b.out" 2> "$1/b.err"
echo $? > "$1/b.rc"; kill $sv
SH
# a batch summary that also carries every single-envelope key (verdict ACCEPTED): it passes a shape-only check
/usr/bin/python3 -I -c 'import json, sys; json.dump({"api_version": "1.0", "mode": "batch_attempt", "verdict": "ACCEPTED", "accepted": True,
  "reward": 1.0, "exit_code": 0, "trust": "sound", "verdict_basis": "accepted", "timing": {"total_s": 0.1}, "diagnostics": [],
  "items": [], "n_items": 0}, open(sys.argv[1], "w"))' "$H7/batch-shaped.json"
sb "$H7" bash "$H7/b.sh" "$H7" "$FVB" "$DATA/attempt/correct.lean" "$H7/batch-shaped.json"
v=$(jq_ "$H7/b.out" '(d.get("verdict"), d.get("exit_code"), "single-attempt" in str(d.get("reason")) or "single result envelope" in str(d.get("reason")))')
if [ "$(cat "$H7/b.rc")" = 2 ] && [ "$v" = "('ERROR', 2, True)" ]; then pass attempt-http-batch-summary-refused-as-single
else fail attempt-http-batch-summary-refused-as-single "rc=$(cat "$H7/b.rc") $v"; fi
# --- CI --out-dir that is a file; MCP explicit null patch mode; usage recovery with the file name '-'
: > "$H7/notadir"
sb "$H7" "$FVB" ci --project "$H7/proj" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --out-dir "$H7/notadir" > /dev/null 2>&1; rc=$?
if [ $rc = 2 ] && [ ! -s "$H7/notadir" ]; then pass ci-out-dir-regular-file-exit2; else fail ci-out-dir-regular-file-exit2 "rc=$rc"; fi
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"fv_verify_patch","arguments":{"mode":null,"files":{"A.lean":"x"}}}}' > "$H7/nm.in"
sb "$H7" /bin/sh -c '"$1/tools/mcp/fastverify-mcp" --fv-root "$1" --threads 2 < "$2" > "$3"' sh "$FV" "$H7/nm.in" "$H7/nm.out" 2> /dev/null
v=$(/usr/bin/python3 -I -c 'import json,sys; r=json.loads(open(sys.argv[1]).readline()); a=json.loads(r["result"]["content"][0]["text"]); print(a.get("verdict"), "invalid mode" in str(a.get("reason")))' "$H7/nm.out" 2>&1)
if [ "$v" = "ERROR True" ]; then pass mcp-patch-null-mode-refused; else fail mcp-patch-null-mode-refused "$v"; fi
( cd "$H7" && cp "$R/103g.json" "$H7/-" && sb "$H7" "$FVB" check "$DATA/main436/main.export" --challenge "$DATA/c436" --json-out - --bogus > /dev/null 2>&1 )
w=$(jq_ "$H7/-" '(d.get("verdict"), d.get("exit_code"))')
if [ "$w" = "('ERROR', 2)" ]; then pass usage-error-dash-output-name-rewritten; else fail usage-error-dash-output-name-rewritten "file=$w"; fi
# --- (triage, experimental) the toolchain's startup check runs inside the sandbox, never on the host
mkdir -p "$H7/tcfake/bin" "$H7/ws/.lake/packages"
printf '#!/bin/sh\necho escaped > %s/escaped-marker 2>/dev/null\necho "Lean (version 4.36.0)"\nexit 0\n' "$H7" > "$H7/tcfake/bin/lean"; chmod +x "$H7/tcfake/bin/lean"
sb "$H7" "$FVB" triage --experimental "$H7/t.lean" --toolchain "$H7/tcfake" --packages "$H7/ws" --json > /dev/null 2>&1
if [ ! -e "$H7/escaped-marker" ]; then pass triage-startup-check-sandboxed-guard; else fail triage-startup-check-sandboxed-guard "the toolchain's lean ran on the host and wrote outside"; fi

# ---------------------------------------------------------------- end-to-end guards: honest ACCEPTED (0), cheat REJECTED (1)
E=$WORK/e2e; mkdir -p "$E"
sb "$E" "$FVB" verify "$DATA/main436" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --threads 4 --json > "$E/honest.out" 2> "$E/honest.err"
rc=$?; v=$(jq_ "$E/honest.out" '(d.get("verdict"), d.get("exit_code"), d.get("trust"), d.get("accepted"))')
if [ $rc = 0 ] && [ "$v" = "('ACCEPTED', 0, 'sound', True)" ]; then pass e2e/honest-verify-accepted-exit0-guard; else fail e2e/honest-verify-accepted-exit0-guard "rc=$rc $v"; fi
sb "$E" "$FVB" verify "$DATA/cheat" --challenge "$DATA/c436" --challenge-sha256 $P436 --comparator-sha256 $C436 --threads 4 --json > "$E/cheat.out" 2> "$E/cheat.err"
rc=$?; v=$(jq_ "$E/cheat.out" '(d.get("verdict"), d.get("exit_code"), d.get("accepted"))')
if [ $rc = 1 ] && [ "$v" = "('REJECTED', 1, False)" ]; then pass e2e/cheat-sorry-verify-rejected-exit1-guard; else fail e2e/cheat-sorry-verify-rejected-exit1-guard "rc=$rc $v"; fi

echo "RESULT: $NPASS PASS $NFAIL FAIL$([ $NSKIP = 0 ] || echo " $NSKIP SKIP")"
[ $NFAIL = 0 ]
