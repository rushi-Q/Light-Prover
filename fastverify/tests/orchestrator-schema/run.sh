#!/bin/bash
# tests/orchestrator-schema/run.sh [FASTVERIFY_ROOT] [WORK_DIR] [THREADS] [ROWS]
#
# Regression rows for the orchestrator, result schema, C0, CI action and batchverify (the bin/fv CLI and MCP rows are
# in tests/cli-mcp): every row prints PASS or FAIL and the script ends with "RESULT: N PASS M FAIL". A row named *-guard checks an
# invariant that must hold before AND after the change (a refusal / rejection that must stay); every other row FAILS on the
# earlier package and PASSES now. INFO rows are printed but not counted.
# FASTVERIFY_ROOT defaults to this package; the inputs are tests/orchestrator-schema/data (fixtures, SHA256SUMS).
# ROWS (optional) = a grep -E pattern of row-group names to run (default: all), e.g. 'schema|cli' .
# Untrusted Lean code only runs inside the package's own bwrap sandboxes (bin/fastverify, judges, batchverify) or in a
# bwrap without network (fixture builds are not part of this script).
set -u
export FV_EXPERIMENTAL_CI=1   # the CI check (fv-ci.sh / bin/fv ci) is EXPERIMENTAL in v0.1 and runs only when opted in
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(readlink -f "${1:-$HERE/../..}")
WORK=${2:-}
THR=${3:-8}
ONLY=${4:-.}
D=$HERE/data
TC36=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
[ -n "$WORK" ] || WORK=$(mktemp -d /tmp/orchestrator-schema.XXXXXX)
mkdir -p "$WORK"; WORK=$(readlink -f "$WORK")
PASS=0; FAILN=0
row() { # cond(0/1) name detail
  if [ "$1" = 0 ]; then PASS=$((PASS+1)); echo "PASS $2 :: $3"; else FAILN=$((FAILN+1)); echo "FAIL $2 :: $3"; fi
}
info() { echo "INFO $1 :: $2"; }
want() { echo "$1" | grep -qE "$ONLY"; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
PY=/usr/bin/python3
FVB="$FV/bin/fastverify"
FVC="$FV/bin/fv"
jget() { "$PY" -I -c 'import json,sys
try:
    r=json.load(open(sys.argv[1]))
except Exception as e:
    print("<unreadable: %s>" % e); sys.exit()
for k in sys.argv[2].split("."):
    r = r.get(k) if isinstance(r, dict) else None
print(r if not isinstance(r,(dict,list)) else json.dumps(r))' "$1" "$2"; }
fresh() { rm -rf "$WORK/$1"; echo "$WORK/$1"; }
# an empty trusted workspace for batchverify rows that never reach a compile (they test refusals before it)
EWS=$(fresh empty-ws); mkdir -p "$EWS/.lake/packages"
echo "orchestrator-schema: FV=$FV WORK=$WORK THREADS=$THR"
( cd "$D" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL data/SHA256SUMS mismatch"; echo "RESULT: 0 PASS 1 FAIL"; exit 1; }
mkdir -p "$WORK/emptyproj"

# a bin/fastverify export-in run: fvx NAME CHALLENGE_DIR SOLUTION PRESET [extra args...]  (result in $WORK/NAME/result.json)
fvx() { local n=$1 c=$2 s=$3 p=$4; shift 4; local o; o=$(fresh "$n")
  local cfg="$c/comparator.json" x prev=; for x in "$@"; do [ "$prev" = --comparator-config ] && cfg=$x; prev=$x; done
  local cpin=(--comparator-sha256 "$(sha "$cfg")"); case " $* " in *" --comparator-sha256 "*) cpin=();; esac
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset "$p" --from-export "$s" \
    --challenge-sha256 "$(sha "$c/challenge.export")" "${cpin[@]}" --threads "$THR" --export-dir none --build-cache none "$@" \
    > "$o.log" 2>&1; echo $? > "$o.rc"; }
rc_of() { cat "$WORK/$1.rc" 2>/dev/null; }
verdict_of() { jget "$WORK/$1/result.json" verdict; }

# ======================================================================================== quoted axiom names
if want names; then
  c=$D/quoted-axiom
  for p in sound sound-auto; do
    fvx qax-$p "$c" "$c/solution.export" "$p" --comparator-config "$c/quoted-axiom.json"
    v=$(verdict_of qax-$p); row $([ "$v" = ACCEPTED ] && [ "$(rc_of qax-$p)" = 0 ] && echo 0 || echo 1) "$p-quoted-propext-accepted" "verdict=$v rc=$(rc_of qax-$p) (official 4.36 comparator: accepted)"
  done
  out=$("$FVC" check "$c/solution.export" --challenge-export "$c/challenge.export" --comparator-json "$c/quoted-axiom.json" --challenge-sha256 "$(sha "$c/challenge.export")" --comparator-sha256 "$(sha "$c/quoted-axiom.json")" --threads "$THR" --json 2>/dev/null); r=$?
  s2=$(echo "$out" | "$PY" -I -c 'import json,sys; e=json.loads(sys.stdin.read()); print(e["verdict"], e["trust"], e["exit_code"])' 2>&1)
  row $([ "$r" = 0 ] && [ "$s2" = "ACCEPTED sound 0" ] && echo 0 || echo 1) "fv-check-quoted-propext-accepted" "rc=$r $s2"
  g=$(fresh qax-guard-cfg); mkdir -p "$g"
  for bad in '["«Quot.sound»"]' '["propext", "sorryAx"]' '["«propext»", "Lean.ofReduceBool"]' '["prop«ext»"]'; do
    tag=$(echo "$bad" | md5sum | cut -c1-6)
    "$PY" -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["permitted_axioms"]=json.loads(sys.argv[2]); json.dump(c,open(sys.argv[3],"w"),ensure_ascii=False)' "$c/comparator.json" "$bad" "$g/$tag.json"
    fvx qax-guard-$tag "$c" "$c/solution.export" sound --comparator-config "$g/$tag.json"
    v=$(verdict_of qax-guard-$tag)
    row $([ "$v" = ERROR ] && [ "$(rc_of qax-guard-$tag)" = 2 ] && grep -q "outside GOAL S1(3)" "$WORK/qax-guard-$tag.log" && echo 0 || echo 1) \
      "S1-set-not-widened-guard $bad" "verdict=$v rc=$(rc_of qax-guard-$tag) (must stay refused)"
  done

# ======================================================================================== export-targets.txt
  c=$D/export-targets
  for p in sound sound-auto; do
    fvx tgt-$p "$c" "$c/solution.export" "$p"
    v=$(verdict_of tgt-$p); row $([ "$v" = ACCEPTED ] && echo 0 || echo 1) "$p-target-list-with-quoted-space-name" "verdict=$v rc=$(rc_of tgt-$p) (official: accepted)"
  done
  g=$(fresh tgt-guard); mkdir -p "$g/swap" "$g/rh" "$g/split"
  for v2 in swap rh split; do cp "$c/challenge.export" "$c/comparator.json" "$c/lean-toolchain" "$g/$v2/"; done
  "$PY" -I - "$c/export-targets.txt" "$g" <<'PY'
import sys
L = open(sys.argv[1], encoding="utf-8").read().split("\n")
L = [x for x in L if x]
sw = L[:]; sw[1], sw[2] = sw[2], sw[1]
open(sys.argv[2] + "/swap/export-targets.txt", "w", encoding="utf-8").write("\n".join(sw) + "\n")
# RH layout: several names per line, separated by spaces (the quoted name keeps its inner spaces)
open(sys.argv[2] + "/rh/export-targets.txt", "w", encoding="utf-8").write(L[0] + "\n" + " ".join(L[1:14]) + "\n" + " ".join(L[14:]) + "\n")
# the name written without its guillemets: three tokens, not the theorem
open(sys.argv[2] + "/split/export-targets.txt", "w", encoding="utf-8").write("\n".join([L[0].replace("«", "").replace("»", "")] + L[1:]) + "\n")
PY
  fvx tgt-guard-swap "$g/swap" "$c/solution.export" sound
  row $([ "$(verdict_of tgt-guard-swap)" = ERROR ] && grep -q "export-targets.txt differs" "$WORK/tgt-guard-swap.log" && echo 0 || echo 1) "wrong-order-refused-guard" "verdict=$(verdict_of tgt-guard-swap)"
  fvx tgt-guard-split "$g/split" "$c/solution.export" sound
  row $([ "$(verdict_of tgt-guard-split)" = ERROR ] && grep -q "export-targets.txt differs" "$WORK/tgt-guard-split.log" && echo 0 || echo 1) "unquoted-space-name-refused-guard" "verdict=$(verdict_of tgt-guard-split)"
  fvx tgt-rh "$g/rh" "$c/solution.export" sound
  row $([ "$(verdict_of tgt-rh)" = ACCEPTED ] && echo 0 || echo 1) "several-names-per-line-layout-accepted" "verdict=$(verdict_of tgt-rh) (RH challenge layout, quoted name with spaces kept)"
fi

# ======================================================================================== release selection
if want release; then
  e=$(fresh eo437); mkdir -p "$e"; cp "$D/export-437/challenge.export" "$e/"; cp "$D/export-437/comparator-noaxioms.json" "$e/comparator.json"
  fvx auto437-auto "$e" "$D/export-437/solution.export" sound-auto
  v=$(verdict_of auto437-auto); tcv=$(jget "$WORK/auto437-auto/result.json" checks.sound.stage.toolchain)
  row $([ "$v" = ACCEPTED ] && [ "$tcv" = "leanprover/lean4:v4.37.0-rc1" ] && echo 0 || echo 1) "export-only-437-selects-437-judge" "verdict=$v judge=$tcv (official 4.37 comparator: accepted)"
  e2=$(fresh eo437b); mkdir -p "$e2"; cp "$D/export-only-437/"* "$e2/"
  fvx dir437-auto "$e2" "$D/project-4.37.0-rc1/Main/main.export" sound-auto
  v=$(verdict_of dir437-auto); tcv=$(jget "$WORK/dir437-auto/result.json" checks.sound.stage.toolchain)
  row $([ "$v" = ACCEPTED ] && [ "$tcv" = "leanprover/lean4:v4.37.0-rc1" ] && echo 0 || echo 1) "export-only-437-challenge-dir-selects-437-judge" "verdict=$v judge=$tcv"
  e3=$(fresh eo-badmeta); mkdir -p "$e3"; cp "$D/export-437/comparator-noaxioms.json" "$e3/comparator.json"
  "$PY" -I -c 'import sys; b=open(sys.argv[1],"rb").read(); i=b.index(b"\n"); open(sys.argv[2],"wb").write(b[:i].replace(b"0b77e12952ad39077d80d8bd6b66d601f225c321", b"0"*40)+b[i:])' "$D/export-437/challenge.export" "$e3/challenge.export"
  fvx auto437-guard-unknown "$e3" "$D/export-437/solution.export" sound-auto
  row $([ "$(verdict_of auto437-guard-unknown)" = ERROR ] && [ "$(rc_of auto437-guard-unknown)" = 2 ] && echo 0 || echo 1) "unknown-release-no-verdict-guard" "verdict=$(verdict_of auto437-guard-unknown) rc=$(rc_of auto437-guard-unknown)"
  # --preset sound on a 4.37 challenge uses the 4.37 judge (the 4.36 replay rejected it)
  fvx e437-sound "$e" "$D/export-437/solution.export" sound
  tcv=$(jget "$WORK/e437-sound/result.json" checks.sound.stage.toolchain)
  row $([ "$(verdict_of e437-sound)" = ACCEPTED ] && [ "$tcv" = "leanprover/lean4:v4.37.0-rc1" ] && echo 0 || echo 1) "preset-sound-437-challenge-uses-437-judge" "verdict=$(verdict_of e437-sound) judge=$tcv"
  fvx e437-pins436 "$e" "$D/export-437/solution.export" sound --pins check/sound/pins.env
  row $([ "$(verdict_of e437-pins436)" = ERROR ] && grep -q "never judged by another release's judge" "$WORK/e437-pins436.log" && echo 0 || echo 1) "explicit-436-pins-refused-for-437-challenge" "verdict=$(verdict_of e437-pins436)"
  fvx e437-notary "$e" "$D/export-437/solution.export" notary --experimental
  row $([ "$(verdict_of e437-notary)" = ERROR ] && grep -q "notary judge has only the Lean 4.36" "$WORK/e437-notary.log" && echo 0 || echo 1) "notary-refused-for-437-challenge" "verdict=$(verdict_of e437-notary)"
fi

# ======================================================================================== provenance
if want provenance; then
  P=$D/project-4.37.0-rc1
  pj=$(fresh p437); mkdir -p "$pj"; cp -r "$P/Main" "$P/Challenge" "$pj/"
  o=$(fresh claim437-auto)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset sound-auto --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1
  cl=$(jget "$o/result.json" soundness.claim)
  row $([ "$(jget "$o/result.json" verdict)" = ACCEPTED ] && echo "$cl" | grep -q "Lean 4.37.0-rc1 comparator judge code" && ! echo "$cl" | grep -q "4.36" && echo 0 || echo 1) "native-437-claim-names-437" "verdict=$(jget "$o/result.json" verdict) claim=...$(echo "$cl" | grep -o 'official Lean [^ ]* comparator' | head -1)"
  o=$(fresh ref437-ref)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset reference --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1
  lk=$(jget "$o/result.json" 'components.comparator:bin/lake'); lc=$(jget "$o/result.json" 'components.comparator:bin/leanchecker')
  row $([ "$(jget "$o/result.json" verdict)" = ACCEPTED ] && echo "$lk$lc" | grep -q "v4.37.0-rc1" && ! echo "$lk$lc" | grep -q "v4.36.0" && echo 0 || echo 1) "437-reference-manifest-names-437-comparator" "verdict=$(jget "$o/result.json" verdict) comparator:bin/lake=$(echo "$lk" | grep -o 'leanprover--lean4---v[^/]*' | head -1)"
  P=$D/project-4.36.0
  pj=$(fresh p436); mkdir -p "$pj"; cp -r "$P/Main" "$P/Challenge" "$pj/"
  o=$(fresh preflight-pre)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset reference --preflight-only --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 0 ] && [ "$(jget "$o/result.json" verdict)" = PREFLIGHT_OK ] && [ "$(jget "$o/result.json" exit)" = 0 ] && echo 0 || echo 1) "preflight-only-records-exit" "rc=$r verdict=$(jget "$o/result.json" verdict) exit=$(jget "$o/result.json" exit)"
fi

# ======================================================================================== stage reports / end-of-run pins
if want stage; then
  "$PY" -I - "$FV" > "$WORK/stage-unit.out" 2>&1 <<'PY'
import importlib.util, os, sys, json, tempfile, types
fv = sys.argv[1]
spec = importlib.util.spec_from_file_location("fvmod", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class A(types.SimpleNamespace):
    def __getattr__(self, k):
        return None
def mkrun():
    r = m.Run.__new__(m.Run)
    import threading
    r.lock = threading.Lock()
    r.a = A(threads=2, unsafe_check=[], checks=["C0"], extra_kernel=[], require_kernel=[], skip_extra_kernel=[])
    r.cfg = json.load(open(os.path.join(fv, "config", "components.json")))
    r.available = {"C0": (True, "ok"), "CN": (True, "ok"), "CS": (True, "ok")}
    r.res = {"checks": {}, "stage_seconds": {}, "warnings": [], "inputs": {}}
    r.logdir = tempfile.mkdtemp(); r.challenge_export = "/nonexistent"; r.cfgp = "/nonexistent"
    r.save = lambda: None; r.warn = lambda msg: r.res["warnings"].append(msg)
    r.await_cs_preflight = lambda: None
    return r
def run_check(opt, rc, j):
    r = mkrun()
    r.run_stage = lambda name, argv, logfile, timeout=None: (rc, 0.1, j)
    r.check(opt, "/nonexistent.export")
    return r, r.res["checks"][m.CHECK_OPTS[opt][0]]
for opt in ("C0", "CN"):
    for rc, j, want, tag in ((0, None, "ERROR", "exit0-no-report"),
                             (0, {"verdict": "REJECTED", "exit": 1}, "ERROR", "exit0-report-rejected"),
                             (0, {"verdict": "ACCEPTED", "exit": "0"}, "ERROR", "exit0-report-exit-string"),
                             (1, None, "ERROR", "exit1-no-report"),
                             (0, {"verdict": "ACCEPTED", "exit": 0}, "ACCEPTED", "exit0-consistent-guard"),
                             (1, {"verdict": "REJECTED", "exit": 1}, "REJECTED", "exit1-consistent-guard"),
                             (2, None, "DECLINED", "exit2-no-report-guard")):
        r, c = run_check(opt, rc, j)
        print(("ok" if c["verdict"] == want else "BAD"), f"stage-report-{opt}-{tag}", c["verdict"])
# decide_notary on a CN exit 0 without a report: never ACCEPTED / trust counted
r, c = run_check("CN", 0, None)
r.a.notary = True
r.decide_notary()
print(("ok" if r.res["verdict"] != "ACCEPTED" else "BAD"), "notary-exit0-no-report-not-accepted", r.res["verdict"])
# end-of-run re-hash: a recorded component that vanished / is no longer a regular file is a change
r = mkrun()
d = tempfile.mkdtemp()
r.res["components"] = {"stage:gone": {"path": os.path.join(d, "gone.sh"), "sha256": "5e" * 32},
                       "stage:dir": {"path": d, "sha256": "ab" * 32}}
ch = r.verify_components_end()
print(("ok" if len(ch) == 2 else "BAD"), "end-check-vanished-component", json.dumps(ch)[:200])
f = os.path.join(d, "same.sh"); open(f, "w").write("x")
r.res["components"] = {"stage:same": {"path": f, "sha256": m.sha256_file(f)}}
print(("ok" if r.verify_components_end() == [] else "BAD"), "end-check-unchanged-guard", "")
PY
  while read -r st nm rest; do
    case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac
  done < "$WORK/stage-unit.out"
  grep -q "end-check-unchanged-guard" "$WORK/stage-unit.out" || row 1 "stage/unit-harness" "$(tail -3 "$WORK/stage-unit.out" | tr '\n' ' ')"
fi

# ======================================================================================== schema (further schema rows in tests/cli-mcp)
if want schema; then
  o=$("$PY" -IB "$FV/schemas/fv_schema.py" validate "$D/schema/wrong-exit.json" 2>&1); r=$?
  row $([ "$r" = 1 ] && echo "$o" | grep -q '"valid": false' && echo 0 || echo 1) "validator-rejects-REJECTED-with-exit-3" "rc=$r $o"
  o=$("$PY" -IB "$FV/schemas/fv_schema.py" validate "$D/schema/mode-list.json" 2>&1); r=$?
  row $([ "$r" = 1 ] && echo "$o" | grep -q '"valid": false' && ! echo "$o" | grep -q Traceback && echo 0 || echo 1) "validator-array-mode-invalid-not-crash" "rc=$r $(echo "$o" | tail -1 | cut -c1-160)"
  o=$("$PY" -I - "$FV" "$D" <<'PY' 2>&1
import sys, os, json
sys.path.insert(0, os.path.join(sys.argv[1], "schemas")); import fv_schema as S
ok = []
for env in (S.make_envelope("attempt", "REJECTED", "sound", "b", 0.1), S.make_envelope("attempt", "ACCEPTED", "sound", "b", 0.1),
            S.make_envelope("project", "ACCEPTED", "official", "b", 0.1), S.make_envelope("frontier", "CONDITIONAL", "sound-conditional", "b", 0.1),
            S.from_error("export_in", "x")):
    ok.append(not S.validate_v1(env))
bad = S.make_envelope("attempt", "ERROR", "none", "b", 0.1); bad["exit_code"] = 1
ok.append(bool(S.validate_v1(bad)))
weird = S.make_envelope("attempt", "REJECTED", "sound", "b", 0.1); weird["trust"] = ["sound"]; weird["verdict"] = {"a": 1}
ok.append(bool(S.validate_v1(weird)))
print("ok" if all(ok) else "BAD", ok)
PY
)
  row $(echo "$o" | grep -q '^ok' && echo 0 || echo 1) "validator-exit-table-consistent-envelopes" "$o"
  # anchored validators: `$` with re.match accepted a trailing line feed
  o=$("$PY" -I - "$FV" "$D/namespaced/Challenge/challenge.export" <<'PY' 2>&1
import importlib.util, os, sys
sys.path.insert(0, os.path.join(sys.argv[1], "schemas")); import fv_schema as S
spec = importlib.util.spec_from_file_location("bv", os.path.join(sys.argv[1], "tools", "batchverify.py"))
bv = importlib.util.module_from_spec(spec); spec.loader.exec_module(bv)
res = {"thm-lf": S.validate_theorem_name("qaAddZero\n"), "thm-lf-simple": S.validate_theorem_name("qaAddZero\n", allow_dotted=False),
       "sha-lf": S.validate_sha256("a" * 64 + "\n"), "batch-lf": bv.export_declares_theorem(sys.argv[2], "QACheck.addZero\n")}
guard = {"thm": S.validate_theorem_name("qaAddZero"), "sha": S.validate_sha256("a" * 64), "batch": bv.export_declares_theorem(sys.argv[2], "QACheck.addZero")}
print(("ok" if not any(res.values()) else "BAD"), res, ("gok" if all(guard.values()) else "gBAD"), guard)
PY
)
  row $(echo "$o" | grep -q '^ok' && echo 0 || echo 1) "validators-reject-trailing-line-feed" "$(echo "$o" | cut -c1-160)"
  row $(echo "$o" | grep -q 'gok' && echo 0 || echo 1) "validators-accept-plain-names-guard" "$(echo "$o" | grep -o "gok.*\|gBAD.*" | cut -c1-120)"
fi

# ======================================================================================== MCP (further MCP rows in tests/cli-mcp)
if want mcp; then
  c=$D/project-4.36.0/Challenge
  mcp() { "$PY" -I - "$FV" "$c" "$(sha "$c/challenge.export")" "$(sha "$c/comparator.json")" "$1" <<'PY'
import json, subprocess, sys
fv, c, cs, fs, req = sys.argv[1:6]
p = subprocess.run([fv + "/tools/mcp/fastverify-mcp", "--fv-root", fv, "--allow-root", c, "--threads", "2",
                    "--challenge", f"qa={c}:{cs}:{fs}"], input=req + "\n", text=True, capture_output=True, timeout=120)
print(p.stdout.strip().splitlines()[-1] if p.stdout.strip() else "<no output> " + p.stderr[-300:])
PY
  }
  o=$(mcp '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"fv_verify_attempt","arguments":{"pset":"qa","theorem":"QACheck.addZero","source":"theorem QACheck.addZero (n : Nat) : n + 0 = n := Nat.add_zero n\n"}}}')
  s=$(echo "$o" | "$PY" -I -c 'import json,sys; r=json.loads(sys.stdin.read())["result"]["structuredContent"]; print(r["verdict"], r["trust"], r["exit_code"])' 2>&1)
  row $(echo "$s" | grep -qv "^REJECTED" && [ "$(echo "$s" | cut -d' ' -f3)" = 2 ] && echo 0 || echo 1) "mcp-unsupported-theorem-name-no-verdict" "$s"
fi

# ======================================================================================== C0 JSON artifact
if want c0; then
  P=$D/project-4.36.0
  o=$(fresh c0); mkdir -p "$o"
  out=$("$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$P/Challenge/comparator.json" --threads 4 --json "$o/absent-dir/stage.json" 2>"$o/err"); r=$?
  row $([ "$r" = 2 ] && echo "$out" | tail -1 | grep -q '"verdict": "ERROR"' && echo 0 || echo 1) "c0-unwritable-json-exit2" "rc=$r last=$(echo "$out" | tail -1 | cut -c1-140)"
  out=$("$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$P/Challenge/comparator.json" --threads 4 --json "$o/stage.json" 2>"$o/err2"); r=$?
  row $([ "$r" = 0 ] && [ "$(jget "$o/stage.json" verdict)" = ACCEPTED ] && echo 0 || echo 1) "c0-writable-json-accepted-guard" "rc=$r"
  : > "$o/occupied"   # --workdir names an existing regular file
  out=$("$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$P/Challenge/comparator.json" --threads 4 --workdir "$o/occupied" --json "$o/wd.json" 2>"$o/err3"); r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/wd.json" verdict)" = ERROR ] && echo 0 || echo 1) "c0-workdir-setup-failure-is-error" "rc=$r verdict=$(jget "$o/wd.json" verdict)"
  mkdir -p "$o/wd-ok"
  out=$("$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$P/Challenge/comparator.json" --threads 4 --workdir "$o/wd-ok" --json "$o/wd2.json" 2>"$o/err4"); r=$?
  row $([ "$r" = 0 ] && [ "$(jget "$o/wd2.json" verdict)" = ACCEPTED ] && echo 0 || echo 1) "c0-usable-workdir-accepted-guard" "rc=$r"
fi

# ======================================================================================== CI action defaults
if want ci; then
  P=$D/project-4.36.0; cs=$(sha "$P/Challenge/challenge.export")
  # emulate the composite action: the inputs' defaults from action.yml, the `with:` block of the SHIPPED README example
  # workflow (project: .), the run step's script with github.action_path / runner.temp substituted, cwd = the checkout
  # (GITHUB_WORKSPACE), RUNNER_TEMP set. ci_emul NAME [drop-key ...]: run twice (the 2nd run sees the 1st run's cache)
  ci_emul() { local n=$1; shift; local g; g=$(fresh "$n"); mkdir -p "$g/ws/proj" "$g/runner-temp"
    cp "$D/ci-example/"* "$g/ws/proj/"; cp -r "$P/Challenge" "$g/ws/proj/challenge"
    "$PY" -I - "$FV/tools/ci-action/action.yml" "$FV/tools/ci-action/README.md" "$g/run.sh" "$FV/tools/ci-action" "$cs" "$THR" "$g/runner-temp" "$(sha "$P/Challenge/comparator.json")" "$@" <<'PY'
import re, sys
act, readme, out, adir, pin, thr, rt, cfgpin = sys.argv[1:9]
drop = set(sys.argv[9:])
t = open(act).read()
ins = re.search(r"^inputs:\n(.*?)^outputs:", t, re.S | re.M).group(1)
dflt = {m.group(1): m.group(2) for m in re.finditer(r"^  ([a-z0-9-]+):\n(?:    .*\n)*?    default: \"(.*)\"", ins, re.M)}
env = re.search(r"^      env:\n((?:        .*\n)+)", t, re.M).group(1)
run = re.search(r"^      run: \|\n((?:        .*\n|\n)+)", t, re.M).group(1)
ex = open(readme).read()
# the README example block, at whatever indentation the README uses
bm = re.search(r"uses: \./fastverify/tools/ci-action\n([ \t]*)with:\n((?:\1[ \t]+\S.*\n)+)", ex)
blk = bm.group(2)
withs = {}
for ln in blk.splitlines():
    m = re.match(r"[ \t]+([a-z0-9-]+): (.*)$", ln)
    if m:
        withs[m.group(1)] = re.sub(r"\s+#.*$", "", m.group(2)).strip().strip('"')   # a trailing YAML comment is not part of the value
withs["challenge-sha256"] = pin; withs["packages"] = ""; withs["threads"] = thr
withs["comparator-sha256"] = cfgpin
for k in drop:
    withs.pop(k, None)
lines = ["#!/bin/bash"]
for m in re.finditer(r"^        (FV_[A-Z0-9_]+): \$\{\{ inputs\.([a-z0-9-]+) \}\}", env, re.M):
    v = withs.get(m.group(2), dflt.get(m.group(2), "")).replace("${{ runner.temp }}", rt)
    lines.append(f"export {m.group(1)}='{v}'")
body = "\n".join(l[8:] for l in run.splitlines()).replace("${{ github.action_path }}", adir)
open(out, "w").write("\n".join(lines) + "\n" + body + "\n")
PY
    for k in 1 2; do
      ( cd "$g/ws/proj" && env -i PATH=/usr/bin:/bin HOME=/tmp FV_EXPERIMENTAL_CI=1 RUNNER_TEMP="$g/runner-temp" GITHUB_OUTPUT="$g/gh-output" bash "$g/run.sh" > "$g/ci$k.out" 2> "$g/ci$k.err" ); echo $? > "$g/ci$k.rc"
    done; }
  civ() { tail -1 "$WORK/$1/ci$2.out" | "$PY" -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("verdict"))' 2>/dev/null; }
  ci_emul ci-example
  row $([ "$(cat "$WORK/ci-example/ci1.rc")" = 0 ] && [ "$(civ ci-example 1)" = ACCEPTED ] && echo 0 || echo 1) "shipped-example-workflow-runs" "rc=$(cat "$WORK/ci-example/ci1.rc") verdict=$(civ ci-example 1) (README example: project: .)"
  nest=$(find "$WORK/ci-example/ws/proj" -name .fastverify-ci-cache -o -name fastverify-ci-cache -o -name fastverify-ci-out | head -3 | tr '\n' ' ')
  row $([ "$(civ ci-example 2)" = ACCEPTED ] && [ -z "$nest" ] && echo 0 || echo 1) "example-cache-and-output-outside-checkout" "2nd run verdict=$(civ ci-example 2); inside the checkout: ${nest:-nothing}"
  ci_emul ci-defaults out-dir cache-dir
  nest=$(find "$WORK/ci-defaults/ws/proj" -name '*fastverify-ci*' | head -3 | tr '\n' ' ')
  row $([ "$(civ ci-defaults 1)" = ACCEPTED ] && [ "$(civ ci-defaults 2)" = ACCEPTED ] && [ -z "$nest" ] && echo 0 || echo 1) "action-defaults-out-and-cache-outside-project" "verdicts=$(civ ci-defaults 1),$(civ ci-defaults 2); inside the checkout: ${nest:-nothing}"
  # the action is EXPERIMENTAL in v0.1: only the `experimental` input opts in (default "false"); FV_EXPERIMENTAL_CI
  # in the runner's environment (set in this emulation's env) does not
  ci_emul ci-noexp experimental
  dexp=$(awk '/^  experimental:/{f=1} f&&/default:/{print $2; exit}' "$FV/tools/ci-action/action.yml")
  row $([ "$(cat "$WORK/ci-noexp/ci1.rc")" = 2 ] && grep -q "fastverify CI action: the CI gate is EXPERIMENTAL" "$WORK/ci-noexp/ci1.err" && [ "$dexp" = '"false"' ] && echo 0 || echo 1) "action-refuses-by-itself-without-experimental-input" "rc=$(cat "$WORK/ci-noexp/ci1.rc") default=$dexp $(grep -o 'CI action: the CI gate is EXPERIMENTAL[^:]*' "$WORK/ci-noexp/ci1.err" | head -1)"
  o=$(fresh ci-inside); mkdir -p "$o/proj"; cp "$D/ci-example/"* "$o/proj/"
  ( cd "$o/proj" && env -i PATH=/usr/bin:/bin HOME=/tmp FV_EXPERIMENTAL_CI=1 "$FV/tools/ci-action/fv-ci.sh" --project . --challenge "$P/Challenge" --challenge-sha256 "$cs" --comparator-sha256 "$(sha "$P/Challenge/comparator.json")" --out-dir inside-out --threads "$THR" > "$o/out" 2>&1 ); r=$?
  row $([ "$r" = 2 ] && echo 0 || echo 1) "out-dir-inside-project-still-refused-guard" "rc=$r"
fi

# ======================================================================================== batchverify / fvserve
if want batch; then
  N=$D/namespaced-attempts; cs=$(sha "$N/Challenge/challenge.export"); ws=$(fresh ws); mkdir -p "$ws/.lake/packages"
  bv() { local o; o=$(fresh "$1"); "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$2" --attempts "$3" --out "$o" --challenge-sha256 "$4" --threads "$THR" --jobs 2 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$o.log" 2>&1; echo $? > "$o.rc"; }
  bvv() { jget "$WORK/$1/batch.json" "attempts" | "$PY" -I -c 'import json,sys; d=json.loads(sys.stdin.read() or "{}"); print((d.get(sys.argv[1]) or {}).get("verdict"))' "$2" 2>/dev/null; }
  bv b105 "$D/namespaced/Challenge" "$D/namespaced/attempts" "$(sha "$D/namespaced/Challenge/challenge.export")"
  row $([ "$(bvv b105 QACheck.addZero)" = ACCEPTED ] && echo 0 || echo 1) "batch-namespaced-theorem-accepted" "verdict=$(bvv b105 QACheck.addZero) checks=$(jget "$WORK/b105/batch.json" n_checks) (fixture; official: accepted)"
  bv bcredit "$N/Challenge" "$N/attempts-credit" "$cs"
  row $([ "$(bvv bcredit QACheck.addZero)" = ACCEPTED ] && echo 0 || echo 1) "batch-namespaced-credit-own-attempt" "QACheck.addZero=$(bvv bcredit QACheck.addZero)"
  row $([ "$(bvv bcredit QACheck.zeroAdd)" != ACCEPTED ] && echo 0 || echo 1) "batch-namespaced-no-credit-to-other-attempt-guard" "QACheck.zeroAdd=$(bvv bcredit QACheck.zeroAdd) (its file declares another theorem; the proof is in QACheck.addZero.lean)"
  bv bwrong "$N/Challenge" "$N/attempts-wrong" "$cs"
  row $([ "$(bvv bwrong QACheck.addZero)" != ACCEPTED ] && echo 0 || echo 1) "batch-namespaced-sorry-not-accepted-guard" "QACheck.addZero(sorry)=$(bvv bwrong QACheck.addZero)"
  row $([ "$(bvv bwrong QACheck.addZero)" = REJECTED ] && [ "$(bvv bwrong QACheck.zeroAdd)" = ACCEPTED ] && echo 0 || echo 1) "batch-namespaced-sorry-rejected-valid-accepted" "addZero=$(bvv bwrong QACheck.addZero) zeroAdd=$(bvv bwrong QACheck.zeroAdd)"
  bv bnames "$N/Challenge" "$N/attempts-names" "$cs"
  row $([ "$(bvv bnames QACheck.nope)" = NO-VERDICT ] && [ "$(bvv bnames 'bad name')" = NO-VERDICT ] && echo 0 || echo 1) "batch-unresolvable-target-no-verdict" "QACheck.nope=$(bvv bnames QACheck.nope) 'bad name'=$(bvv bnames 'bad name') (never REJECTED)"
  # fvserve: an unsupported (dotted) theorem name is NO-VERDICT, never REJECTED with sound trust
  # (+ quoted axiom names) its problem set's comparator.json spells propext as «propext»: the service starts (before: refused)
  st=$(fresh svc-state); sl=$WORK/svc.log; ps=$(fresh svc-pset); cp -r "$D/project-4.36.0/Challenge" "$ps"
  "$PY" -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["permitted_axioms"]=["«propext»","Quot.sound","Classical.choice"]; json.dump(c,open(sys.argv[1],"w"),ensure_ascii=False)' "$ps/comparator.json"
  "$PY" -I "$FV/tools/fvserve/fvserve.py" serve --state "$st" --pset "qa=$ps:$(sha "$ps/challenge.export")" --packages "$ws" --toolchain "$TC36" --threads 4 --snapshot-header '' --par 1 --max-inflight 1 --export-dir "$WORK" > "$sl" 2>&1 &
  dp=$!
  for i in $(seq 1 120); do [ -S "$st/sock" ] && break; kill -0 $dp 2>/dev/null || break; sleep 1; done
  out=$("$FVC" attempt "$D/namespaced/attempts/QACheck.addZero.lean" --state "$st" --pset qa --theorem QACheck.addZero --timeout 60 --json 2>/dev/null); r=$?
  out2=$("$FVC" attempt "$D/project-4.36.0/Main/Main.lean" --state "$st" --pset qa --theorem qaAddZero --timeout 120 --json 2>/dev/null); r2=$?
  "$PY" -I "$FV/tools/fvserve/fvserve.py" stop --state "$st" > /dev/null 2>&1; sleep 1; kill $dp 2>/dev/null; wait $dp 2>/dev/null
  s=$(echo "$out" | "$PY" -I -c 'import json,sys; e=json.loads(sys.stdin.read()); print(e["verdict"], e["exit_code"])' 2>&1)
  row $([ "$r" = 2 ] && echo "$s" | grep -q "^NO-VERDICT 2" && echo 0 || echo 1) "fvserve-unsupported-name-no-verdict" "rc=$r $s"
  s=$(echo "$out2" | "$PY" -I -c 'import json,sys; e=json.loads(sys.stdin.read()); print(e["verdict"], e["trust"], e["exit_code"])' 2>&1)
  row $([ "$r2" = 0 ] && [ "$s" = "ACCEPTED sound 0" ] && echo 0 || echo 1) "fvserve-quoted-propext-pset-accepts" "rc=$r2 $s ($(grep -o 'permitted_axioms outside GOAL S1(3)' "$sl" | head -1))"
fi

# ======================================================================================== signals, resource limits, sorried holes, conjunction of checks
if want signals; then
  # --- signal hygiene: started with SIGCHLD ignored, a failing child must still fail (no hang, no ACCEPTED)
  e3=$(fresh hi-badmeta); mkdir -p "$e3"; cp "$D/export-437/comparator-noaxioms.json" "$e3/comparator.json"
  "$PY" -I -c 'import sys; b=open(sys.argv[1],"rb").read(); i=b.index(b"\n"); open(sys.argv[2],"wb").write(b[:i].replace(b"0b77e12952ad39077d80d8bd6b66d601f225c321", b"0"*40)+b[i:])' "$D/export-437/challenge.export" "$e3/challenge.export"
  o=$(fresh hi-sigchld-bad); echo 4.37 > /dev/null
  timeout 300 "$PY" -I -c 'import os,signal,sys; signal.signal(signal.SIGCHLD, signal.SIG_IGN); os.execv(sys.argv[1], sys.argv[1:])' \
    "$FVB" "$WORK/emptyproj" "$e3" "$o" --preset sound --from-export "$D/export-437/solution.export" --challenge-sha256 "$(sha "$e3/challenge.export")" --comparator-sha256 "$(sha "$e3/comparator.json")" \
    --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" = ERROR ] && echo 0 || echo 1) "sigchld-ignored-failing-gate-is-error" "rc=$r (124 = hang) verdict=$(jget "$o/result.json" verdict)"
  c=$D/quoted-axiom; o=$(fresh hi-sigchld-good)
  timeout 300 "$PY" -I -c 'import os,signal,sys; signal.signal(signal.SIGCHLD, signal.SIG_IGN); os.execv(sys.argv[1], sys.argv[1:])' \
    "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$c/solution.export" --challenge-sha256 "$(sha "$c/challenge.export")" --comparator-sha256 "$(sha "$c/comparator.json")" \
    --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 0 ] && [ "$(jget "$o/result.json" verdict)" = ACCEPTED ] && echo 0 || echo 1) "sigchld-ignored-honest-accepted" "rc=$r verdict=$(jget "$o/result.json" verdict)"
  # --- SIGHUP / SIGINT keep the inherited disposition: a run under nohup survives a hangup
  c=$D/quoted-axiom; o=$(fresh hi-nohup)
  nohup env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$c/solution.export" \
    --challenge-sha256 "$(sha "$c/challenge.export")" --comparator-sha256 "$(sha "$c/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1 &
  fp=$!; for i in $(seq 1 100); do grep -q "check sound started" "$o.log" 2>/dev/null && break; sleep 0.2; done; kill -HUP $fp 2>/dev/null; wait $fp; r=$?
  row $([ "$r" = 0 ] && [ "$(jget "$o/result.json" verdict)" = ACCEPTED ] && echo 0 || echo 1) "nohup-run-survives-SIGHUP-guard" "rc=$r verdict=$(jget "$o/result.json" verdict)"
  # --- a signal during planning (before Run exists) writes an ERROR result.json into a usable OUT only
  cat > "$WORK/early-sig.py" <<'PYX'
import importlib.util, os, signal, sys, types, time
fv, out = sys.argv[1], sys.argv[2]
spec = importlib.util.spec_from_file_location("fvm", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
if not hasattr(m, "install_early_signal_handlers"):
    sys.exit(9)
m.install_early_signal_handlers(types.SimpleNamespace(out=out, project="/nonexistent-p", challenge="/nonexistent-c"))
os.kill(os.getpid(), signal.SIGTERM); time.sleep(5); sys.exit(7)
PYX
  o=$(fresh hi-early); "$PY" -I "$WORK/early-sig.py" "$FV" "$o" 2>/dev/null; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" = ERROR ] && [ "$(jget "$o/result.json" exit)" = 2 ] && echo 0 || echo 1) "signal-during-planning-writes-error" "rc=$r verdict=$(jget "$o/result.json" verdict)"
  o=$(fresh hi-early-busy); mkdir -p "$o"; echo keep > "$o/marker"; "$PY" -I "$WORK/early-sig.py" "$FV" "$o" 2>/dev/null; r=$?
  row $([ "$r" != 0 ] && [ ! -e "$o/result.json" ] && [ "$(cat "$o/marker")" = keep ] && echo 0 || echo 1) "non-empty-OUT-untouched-guard" "rc=$r"
  # --- --require-sorried-holes is applied by the INITIAL gate: a build error can no longer turn the refused challenge REJECTED
  y=$D/sorried-holes; pj=$(fresh hi-holes); mkdir -p "$pj"; cp -r "$y/challenge" "$y/solution" "$pj/"; o=$(fresh hi-holes-out)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/solution" "$pj/challenge" "$o" --preset sound --build B0 --require-sorried-holes \
    --challenge-sha256 "$(sha "$pj/challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" != REJECTED ] && [ "$(jget "$o/result.json" inputs.challenge_export.xversion.verdict)" = DECLINED ] && echo 0 || echo 1) "require-sorried-holes-declined-by-initial-gate" "rc=$r verdict=$(jget "$o/result.json" verdict) gate=$(jget "$o/result.json" inputs.challenge_export.xversion.verdict)"
  # --- a host resource limit (ulimit -f) stopping a stage is no verdict, never REJECTED
  # (a) a limit below the challenge export's size (~1 MB): the private snapshot of the
  # challenge inputs fails first -> no verdict, the signal is named; (b) a limit above it (1450 KB) but below the padded
  # solution export (+1.3 MB string in the target's closure): the exporter STAGE is stopped -> no verdict
  P=$D/project-4.36.0; pj=$(fresh hi-ulimit); mkdir -p "$pj"; cp -r "$P/Main" "$P/Challenge" "$pj/"; rm -f "$pj/Main/main.export"; o=$(fresh hi-ulimit-out)
  ( ulimit -f 600; env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset sound --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" \
      --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1 ); r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" != REJECTED ] && jget "$o/result.json" verdict_basis | grep -q "private snapshot (cp killed by signal" && echo 0 || echo 1) "ulimit-f-snapshot-failure-not-rejected" "rc=$r verdict=$(jget "$o/result.json" verdict) basis=$(jget "$o/result.json" verdict_basis | cut -c1-140)"
  pj=$(fresh hi-ulimit2); mkdir -p "$pj"; cp -r "$P/Main" "$P/Challenge" "$pj/"; rm -f "$pj/Main/main.export"; o=$(fresh hi-ulimit2-out)
  "$PY" -I -c 'import sys
p = sys.argv[1]; s = open(p).read(); s2 = s.replace(":= Nat.add_zero n", ":= (fun (_ : String) => Nat.add_zero n) fvPadding")
assert s2 != s; open(p, "w").write("def fvPadding : String := \"" + "x" * 1300000 + "\"\n" + s2)' "$pj/Main/Main.lean"   # 1.3 MB in the target closure
  ( ulimit -f 1450; env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset sound --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" \
      --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1 ); r=$?
  b=$(jget "$o/result.json" verdict_basis)
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" != REJECTED ] && echo "$b" | grep -q "exporter failed" && echo 0 || echo 1) "ulimit-f-stage-failure-not-rejected" "rc=$r verdict=$(jget "$o/result.json" verdict) basis=$(echo "$b" | cut -c1-140)"
  # --- sound-auto, a valid `grind +suggestions` project (the transformed build B3 fails): ACCEPTED via the exact rebuild
  y=$D/grind-suggestions; pj=$(fresh hi-grind); mkdir -p "$pj"; cp -r "$y/chal" "$y/proj2" "$pj/"; o=$(fresh hi-grind-out)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/proj2" "$pj/chal" "$o" --preset sound-auto --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 0 ] && [ "$(jget "$o/result.json" verdict)" = ACCEPTED ] && echo 0 || echo 1) "sound-auto-transformed-build-failure-not-rejected" "rc=$r verdict=$(jget "$o/result.json" verdict) build=$(jget "$o/result.json" build.option) confirmed_by=$(jget "$o/result.json" build.confirmed_by)"
  # --- --check CS,CN = conjunction; --modulo-frontier with CN refused
  o=$(fresh hi-judgepair-mf); c=$D/quoted-axiom
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --check CS,CN --experimental --modulo-frontier auto --from-export "$c/solution.export" --challenge-sha256 "$(sha "$c/challenge.export")" --comparator-sha256 "$(sha "$c/comparator.json")" --threads "$THR" > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && grep -q "cannot be combined with the notary" "$o.log" && echo 0 || echo 1) "modulo-frontier-with-CN-refused" "rc=$r"
  "$PY" -I - "$FV" > "$WORK/hi-unit.out" 2>&1 <<'PY'
import importlib.util, os, sys, json, tempfile, types, threading
fv = sys.argv[1]
spec = importlib.util.spec_from_file_location("fvmod2", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class A(types.SimpleNamespace):
    def __getattr__(self, k):
        return None
def mk(checks):
    r = m.Run.__new__(m.Run); r.lock = threading.Lock()
    r.a = A(threads=2, unsafe_check=[], checks=checks, sound="CS" in checks, notary="CN" in checks, extra_kernel=[],
            require_kernel=["nanoda"], skip_extra_kernel=[], unsafe_build=[], challenge_sha256="ab" * 32)
    r.res = {"checks": {}, "stage_seconds": {}, "warnings": [], "inputs": {"challenge_export": {"sha256": "ab" * 32}}}
    r.out = tempfile.mkdtemp(); r.warn = lambda msg: None
    return r
# CS DECLINED (a required kernel could not run) + CN ACCEPTED -> never ACCEPTED
r = mk(["CS", "CN"])
r.res["checks"] = {"sound": {"verdict": "DECLINED", "stage": {"reason": "required kernel nanoda failed"}},
                   "notary": {"verdict": "ACCEPTED", "stage": {"basis": "notary ok"}}}
r.decide()
print(("ok" if r.res["verdict"] != "ACCEPTED" else "BAD"), "CS-declined-CN-accepted-not-accepted", r.res["verdict"], r.res.get("trust"))
r = mk(["CS", "CN"])
r.res["checks"] = {"sound": {"verdict": "ACCEPTED", "stage": {"basis": "sound ok"}}, "notary": {"verdict": "ACCEPTED", "stage": {"basis": "notary ok"}}}
r.decide()
print(("ok" if r.res["verdict"] == "ACCEPTED" else "BAD"), "both-accepted-accepted-guard", r.res["verdict"])
# a decided verdict is written as PENDING until the run is final; Infinity never reaches result.json
r = mk(["CS"]); r.res.update(verdict="ACCEPTED", trust="sound", weird=float("inf"), nan=float("nan"))
r.save(); d = json.loads(open(os.path.join(r.out, "result.json")).read(), parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
print(("ok" if d["verdict"] == "PENDING" and d.get("verdict_pending") == "ACCEPTED" else "BAD"), "decided-verdict-pending-until-final", d["verdict"])
print(("ok" if d["weird"] is None and d["nan"] is None else "BAD"), "result-json-finite-numbers", d["weird"], d["nan"])
r.final = True; r.save(); d = json.load(open(os.path.join(r.out, "result.json")))
print(("ok" if d["verdict"] == "ACCEPTED" else "BAD"), "final-save-writes-verdict-guard", d["verdict"])
sys.path.insert(0, os.path.join(fv, "schemas")); import fv_schema as S
e = S.from_fastverify_result({"verdict": "ACCEPTED", "trust": "sound", "mode": {"sound": True, "check": ["CS"]}, "interrupted": "signal 15", "exit": 2})
print(("ok" if e["verdict"] == "ERROR" and not e["accepted"] else "BAD"), "interrupted-result-not-counted", e["verdict"], e["accepted"])
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/hi-unit.out"
  grep -q "interrupted-result-not-counted" "$WORK/hi-unit.out" || row 1 "signals/unit-harness" "$(tail -3 "$WORK/hi-unit.out" | tr '\n' ' ')"
  # --- behavioural: SIGTERM while the run is going -> ERROR, exit 2, never the decided verdict
  c=$D/quoted-axiom; o=$(fresh hi-sigterm)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$c/solution.export" --challenge-sha256 "$(sha "$c/challenge.export")" --comparator-sha256 "$(sha "$c/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1 &
  fp=$!; for i in $(seq 1 100); do grep -q "check sound started" "$o.log" 2>/dev/null && break; sleep 0.2; done; sleep 1; kill -TERM $fp 2>/dev/null; wait $fp; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" = ERROR ] && echo 0 || echo 1) "sigterm-during-run-is-error-guard" "rc=$r verdict=$(jget "$o/result.json" verdict)"
fi

# ======================================================================================== challenge release, source-only challenges, pins, unit rows
if want challenge-release; then
  # --- a lean-toolchain beside the pinned challenge export that names another release -> refused (never the 4.36 judge)
  e=$(fresh c5-rel436); mkdir -p "$e"; cp "$D/export-437/challenge.export" "$e/"; cp "$D/export-437/comparator-noaxioms.json" "$e/comparator.json"; echo "leanprover/lean4:v4.36.0" > "$e/lean-toolchain"
  fvx c5-rel436-auto "$e" "$D/export-437/solution.export" sound-auto
  row $([ "$(verdict_of c5-rel436-auto)" = ERROR ] && grep -q "inconsistent challenge directory" "$WORK/c5-rel436-auto.log" && echo 0 || echo 1) "conflicting-lean-toolchain-refused" "verdict=$(verdict_of c5-rel436-auto) rc=$(rc_of c5-rel436-auto)"
  fvx c5-rel436-ok "$D/export-437" "$D/export-437/solution.export" sound-auto
  row $([ "$(verdict_of c5-rel436-ok)" = ACCEPTED ] && echo 0 || echo 1) "consistent-lean-toolchain-accepted-guard" "verdict=$(verdict_of c5-rel436-ok)"
  # --- a source-only challenge (built in this run): claim + basis say so, the build stage is in the inventory
  P=$D/project-4.36.0; c=$(fresh c5-src); mkdir -p "$c"; cp "$P/Challenge/"* "$c/"; rm -f "$c/challenge.export"; o=$(fresh c5-src-out)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$P/Main/main.export" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1
  cl=$(jget "$o/result.json" soundness.claim); vb=$(jget "$o/result.json" verdict_basis)
  row $([ "$(jget "$o/result.json" verdict)" = ACCEPTED ] && echo "$cl" | grep -q "built in this run" && ! echo "$vb" | grep -q "checked by the caller" && echo 0 || echo 1) "source-built-challenge-provenance-text" "verdict=$(jget "$o/result.json" verdict)"
  row $([ "$(jget "$o/result.json" 'components.stage:challenge_build')" != None ] && echo 0 || echo 1) "challenge-build-stage-in-inventory" "$(jget "$o/result.json" 'components.stage:challenge_build' | cut -c1-120)"
  # --- an explicit --pins of the default judge is recorded
  c=$D/quoted-axiom; fvx c5-pins "$c" "$c/solution.export" sound --pins check/sound/pins.env
  row $([ "$(verdict_of c5-pins)" = ACCEPTED ] && [ "$(jget "$WORK/c5-pins/result.json" check_pins.selected_by)" = "--pins" ] && echo 0 || echo 1) "explicit-default-pins-recorded" "check_pins.selected_by=$(jget "$WORK/c5-pins/result.json" check_pins.selected_by)"
  # --- --comparator-sha256 pins the config (mismatch refused, match accepted)
  fvx c5-cfgpin-bad "$c" "$c/solution.export" sound --comparator-sha256 "$(printf '%064d' 0)"
  row $([ "$(verdict_of c5-cfgpin-bad)" = ERROR ] && grep -q "comparator-sha256" "$WORK/c5-cfgpin-bad.log" && echo 0 || echo 1) "comparator-pin-mismatch-refused" "verdict=$(verdict_of c5-cfgpin-bad)"
  fvx c5-cfgpin-ok "$c" "$c/solution.export" sound --comparator-sha256 "$(sha "$c/comparator.json")"
  row $([ "$(verdict_of c5-cfgpin-ok)" = ACCEPTED ] && echo 0 || echo 1) "comparator-pin-match-accepted" "verdict=$(verdict_of c5-cfgpin-ok)"
  # --- unit rows: deciding check not run -> ERROR with reason; release rule -> FV007; confirm-reject default
  "$PY" -I - "$FV" > "$WORK/c5-unit.out" 2>&1 <<'PY'
import importlib.util, os, sys, json, tempfile, types, threading
fv = sys.argv[1]
spec = importlib.util.spec_from_file_location("fvmod3", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class A(types.SimpleNamespace):
    def __getattr__(self, k):
        return None
r = m.Run.__new__(m.Run); r.lock = threading.Lock()
r.a = A(threads=2, unsafe_check=[], checks=["CS"], sound=True, unsafe_build=[], challenge_sha256="ab" * 32)
r.res = {"checks": {"sound": {"option": "CS", "exit": 2, "verdict": "NOT_RUN", "detail": "preflight failed: pinned file missing: /x/ccmp", "seconds": 0}},
         "stage_seconds": {}, "warnings": [], "inputs": {"challenge_export": {"sha256": "ab" * 32, "source": "given"}}}
r.decide()
print(("ok" if r.res["verdict"] == "ERROR" and "pinned file missing" in r.res["verdict_basis"] else "BAD"), "judge-not-run-is-error-with-reason", r.res["verdict"], r.res["verdict_basis"][:120])
# the CS preflight command carries the run's --threads (subprocess.run mocked: nothing is executed)
import subprocess as _sp
seen = []
def fake_run(argv, *a, **k):
    seen.append(list(argv))
    out = "" if k.get("text") else b""
    return _sp.CompletedProcess(argv, 0, out, out)
r2 = m.Run.__new__(m.Run); r2.lock = threading.Lock()
r2.a = A(threads=3, checks=["CS"], export="/x.export", build="B3", export_opt="E1", unsafe_check=[], extra_kernel=[],
         require_kernel=[], skip_extra_kernel=[], sound=True)
r2.cfg = json.load(open(os.path.join(fv, "config", "components.json")))
r2.res = {"inputs": {"toolchain": None}, "stage_seconds": {}, "warnings": [], "components": {}}
r2.tmp = tempfile.mkdtemp(); r2.save = lambda: None; r2.warn = lambda msg: None
real = m.subprocess.run; m.subprocess.run = fake_run
try:
    r2.preflight()
finally:
    m.subprocess.run = real
cs = [x for x in seen if x and os.path.basename(x[0]) in ("check-sound.sh", "check-sound-svc.sh") and "--preflight" in x]
ok = bool(cs) and all("--threads" in x and x[x.index("--threads") + 1] == "3" for x in cs)
print(("ok" if ok else "BAD"), "cs-preflight-gets-thread-budget", (cs[0][-6:] if cs else seen[:2]))
sys.path.insert(0, os.path.join(fv, "schemas")); import fv_schema as S
d = S.classify_verdict_diagnostic("REJECTED", "Challenge definition is not sorried: 'chooseNat' (rule of the official Lean 4.37.0-rc1 comparator, Lake/Check/Compare.lean)")
print(("ok" if d and d[0]["rule_id"] == "FV007" else "BAD"), "release-rule-rejection-not-build-error", d[0]["rule_id"] if d else None)
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/c5-unit.out"
  grep -q "release-rule-rejection-not-build-error" "$WORK/c5-unit.out" || row 1 "challenge-release/unit-harness" "$(tail -3 "$WORK/c5-unit.out" | tr '\n' ' ')"
  row $([ "$(jget "$WORK/c5-pins/result.json" mode.confirm_reject)" = True ] && echo 0 || echo 1) "sound-preset-confirm-reject-on" "mode.confirm_reject=$(jget "$WORK/c5-pins/result.json" mode.confirm_reject)"
fi

# ======================================================================================== conjunction, confirm-reject, unreadable .olean, schema, SIGCHLD
if want conjunction; then
  DD=$D/batch-items
  # --- unit rows: (1) every selected check must accept; (3) confirm-reject completion; (6) unreadable .olean; (12) schema; ignored SIGCHLD
  "$PY" -I - "$FV" "$D" > "$WORK/conj-unit.out" 2>&1 <<'PY'
import importlib.util, os, sys, json, tempfile, types, threading, signal
fv, D = sys.argv[1], sys.argv[2]
spec = importlib.util.spec_from_file_location("fvm5d", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class A(types.SimpleNamespace):
    def __getattr__(self, k):
        return None
def mk(checks):
    r = m.Run.__new__(m.Run); r.lock = threading.Lock()
    r.a = A(threads=2, unsafe_check=[], checks=checks, sound="CS" in checks, notary="CN" in checks, extra_kernel=[],
            require_kernel=[], skip_extra_kernel=[], unsafe_build=[], challenge_sha256="ab" * 32, project="/p", threads_=1)
    r.res = {"checks": {}, "stage_seconds": {}, "warnings": [], "inputs": {"challenge_export": {"sha256": "ab" * 32, "source": "given"}}}
    r.out = tempfile.mkdtemp(); r.logdir = tempfile.mkdtemp(); r.warn = lambda msg: None; r.save = lambda: None
    return r
for checks, votes, want in ((["CS", "CN", "C0"], {"sound": "ACCEPTED", "notary": "ACCEPTED", "official": "DECLINED"}, "DECLINED"),
                            (["CS", "C0"], {"sound": "ACCEPTED", "official": "ERROR"}, "DECLINED"),
                            (["CS", "C3"], {"sound": "ACCEPTED", "checkB": "NOT_RUN"}, "DECLINED"),
                            (["CS", "C0"], {"sound": "ACCEPTED", "official": "ACCEPTED"}, "ACCEPTED"),
                            (["CS", "C0"], {"sound": "ACCEPTED", "official": "REJECTED"}, "REJECTED")):
    r = mk(checks); r.res["checks"] = {k: {"verdict": v, "stage": {}} for k, v in votes.items()}
    r.decide()
    tag = "-guard" if want != "DECLINED" else ""
    print(("ok" if r.res["verdict"] == want else "BAD"), f"selected-checks-{'+'.join(checks)}-{'-'.join(votes.values())}{tag}", r.res["verdict"])
# (3) confirm-reject: a confirmation that cannot complete is no verdict; a confirmed exact failure is REJECTED
def confirm_case(b1, b0, export_rc, b1_report=None):
    r = mk(["CS"]); r.a.project = tempfile.mkdtemp(); r.a.keep_work = False
    r.res.update(build={"option": "B3", "exit": 0, "attempts": []}, export={"path": "/nonexistent"}, verdict="REJECTED",
                 verdict_basis="SOUND: rejected by sound")
    r.proj = tempfile.mkdtemp(); r.packages_ws = "/x"; r.tc = "/x"; r.cc = {"solution_module": "Main"}
    r.overlap_kill = lambda: None; r.stage_path = lambda k: "/bin/true"
    m.rmtree_force = lambda p: None; m.copy_project = lambda a, b: None
    def run_stage(name, argv, log, timeout=None):
        if name == "build_confirm_b1":
            rc = b1
        else:
            rc = b0
        if rc == 0:
            open(os.path.join(r.logdir, "lean_path.txt"), "w").write("/x\n")
        return rc, 0.1, (b1_report if name == "build_confirm_b1" and b1_report is not None else {"exit": rc})
    r.run_stage = run_stage
    r.export = lambda: export_rc
    r.confirm_reject()
    return r.res["verdict"]
for b1, b0, erc, want, tag in ((137, 2, 0, "DECLINED", "b1-killed-b0-declined"), (2, 2, 0, "DECLINED", "b1-declined-b0-declined"),
                               (0, None, 2, "DECLINED", "b1-ok-export-failed"), (2, 1, 0, "REJECTED", "b1-declined-b0-confirms-guard"),
                               (1, None, 0, "REJECTED", "b1-confirms-guard")):
    got = confirm_case(b1, b0, erc)
    print(("ok" if got == want else "BAD"), f"confirm-reject-{tag}", got)
got = confirm_case(1, None, 0, b1_report={"exit": 0})
print(("ok" if got == "DECLINED" else "BAD"), "confirm-reject-b1-exit1-without-matching-report", got)
# (6) an unreadable .olean never awards credit
bspec = importlib.util.spec_from_file_location("bv5d", os.path.join(fv, "tools", "batchverify.py"))
bv = importlib.util.module_from_spec(bspec); bspec.loader.exec_module(bv)
b = bv.Batch.__new__(bv.Batch); b.lib = tempfile.mkdtemp(); os.makedirs(os.path.join(b.lib, "Attempt", "A.olean"))
f = getattr(b, "olean_may_hold", None)
print(("ok" if f is not None and f("A", b"t\x00") is True else "BAD"), "unreadable-olean-may-hold", f and f("A", b"t\x00"))
# (12) schema: exit true / array verdict -> structured ERROR
sys.path.insert(0, os.path.join(fv, "schemas")); import fv_schema as S
out = []
for res in ({"mode": {"sound": True, "check": ["CS"]}, "verdict": "REJECTED", "exit": True},
            {"mode": {"sound": True, "check": ["CS"]}, "verdict": ["REJECTED"], "exit": 1}):
    try:
        e = S.from_fastverify_result(res)
        out.append(e["verdict"])
    except Exception as ex:
        out.append(type(ex).__name__)
print(("ok" if out == ["ERROR", "ERROR"] else "BAD"), "normalizer-malformed-exit-and-verdict", out)
# batchverify / fvserve / MCP reset an ignored SIGCHLD
res = {}
for nm, rel in (("batchverify", "tools/batchverify.py"), ("fvserve", "tools/fvserve/fvserve.py"), ("mcp", "tools/mcp/mcp_server.py")):
    sp = importlib.util.spec_from_file_location("n6" + nm, os.path.join(fv, rel)); mm = importlib.util.module_from_spec(sp)
    try:
        sp.loader.exec_module(mm)
        signal.signal(signal.SIGCHLD, signal.SIG_IGN); mm.reset_child_signals()
        res[nm] = signal.getsignal(signal.SIGCHLD) == signal.SIG_DFL
    except Exception as ex:
        res[nm] = type(ex).__name__
print(("ok" if all(v is True for v in res.values()) else "BAD"), "entry-points-reset-sigchld", res)
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/conj-unit.out"
  grep -q "entry-points" "$WORK/conj-unit.out" || row 1 "conjunction/unit-harness" "$(tail -3 "$WORK/conj-unit.out" | tr '\n' ' ')"
  # --- (2) sound-auto --no-confirm-build-failure: the unconfirmed B3 failure is no verdict (the grind +suggestions project; B1 would accept)
  y=$D/grind-suggestions; pj=$(fresh d-grind); mkdir -p "$pj"; cp -r "$y/chal" "$y/proj2" "$pj/"; o=$(fresh d-grind-out)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/proj2" "$pj/chal" "$o" --preset sound-auto --no-confirm-build-failure --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  # with the current package the transformed build of this project succeeds (ACCEPTED, as B1 would): the invariant is
  # that an unconfirmed transformed-build failure is never REJECTED
  row $({ [ "$r" = 2 ] || [ "$r" = 0 ]; } && [ "$(jget "$o/result.json" verdict)" != REJECTED ] && echo 0 || echo 1) "unconfirmed-transformed-build-failure-no-verdict" "rc=$r verdict=$(jget "$o/result.json" verdict)"
  # --- (3) real: sorry project, sound preset (Lake 4.36: B1 declines) -> the official B0 confirms the REJECTED
  P=$D/project-4.36.0; pj=$(fresh d-sorry); mkdir -p "$pj/proj"; cp "$P/Main/"{lakefile.toml,lake-manifest.json,lean-toolchain} "$pj/proj/"; cp -r "$P/Challenge" "$pj/chal"
  printf '@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := by sorry\n' > "$pj/proj/Main.lean"; o=$(fresh d-sorry-out)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/proj" "$pj/chal" "$o" --preset sound --challenge-sha256 "$(sha "$pj/chal/challenge.export")" --comparator-sha256 "$(sha "$pj/chal/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 1 ] && [ "$(jget "$o/result.json" verdict)" = REJECTED ] && jget "$o/result.json" confirm_reject.result | grep -q "exact build's export: REJECTED" && echo 0 || echo 1) "sorry-project-rejection-confirmed-by-exact-build" "rc=$r verdict=$(jget "$o/result.json" verdict) confirm=$(jget "$o/result.json" confirm_reject.result | cut -c1-80)"
  # --- (4) C0: a kernel killed by its time limit (nanoda exited with 143) is ERROR, not REJECTED
  o=$(fresh d-kern); mkdir -p "$o"
  "$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$DD/kernel-budget.json" --threads 4 --json "$o/stage.json" > "$o/out" 2> "$o/err"; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/stage.json" verdict)" = ERROR ] && echo 0 || echo 1) "c0-killed-kernel-is-error" "rc=$r verdict=$(jget "$o/stage.json" verdict) ($(grep -o 'nanoda exited with [0-9]*' "$o/err" | head -1))"
  # --- the comparator pin is required with a given challenge export in sound / notary mode
  c=$D/quoted-axiom; o=$(fresh d-pin-missing)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$c/solution.export" --challenge-sha256 "$(sha "$c/challenge.export")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" = ERROR ] && grep -q "needs --comparator-sha256" "$o.log" && [ "$(jget "$o/result.json" checks)" = "{}" ] && echo 0 || echo 1) "pin/missing-comparator-pin-refused-before-anything-runs" "rc=$r verdict=$(jget "$o/result.json" verdict)"
  for pr in sound-auto notary; do o=$(fresh d-pin-missing-$pr)
    env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset $pr --experimental --from-export "$c/solution.export" --challenge-sha256 "$(sha "$c/challenge.export")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
    row $([ "$r" = 2 ] && grep -q "needs --comparator-sha256" "$o.log" && echo 0 || echo 1) "pin/missing-comparator-pin-refused-$pr" "rc=$r"
  done
  fvx d-pin-wrong "$c" "$c/solution.export" sound --comparator-sha256 "$(printf 'f%.0s' $(seq 64))"
  row $([ "$(verdict_of d-pin-wrong)" = ERROR ] && [ "$(rc_of d-pin-wrong)" = 2 ] && grep -q "!= --comparator-sha256" "$WORK/d-pin-wrong.log" && echo 0 || echo 1) "pin/wrong-comparator-pin-refused-guard" "verdict=$(verdict_of d-pin-wrong)"
  fvx d-pin-ok "$c" "$c/solution.export" sound
  row $([ "$(verdict_of d-pin-ok)" = ACCEPTED ] && [ "$(jget "$WORK/d-pin-ok/result.json" inputs.comparator_config.pinned_sha256)" = "$(sha "$c/comparator.json")" ] && echo 0 || echo 1) "pin/correct-pin-honest-accepted-and-pin-recorded" "verdict=$(verdict_of d-pin-ok)"
  # --- a malformed pin value is a usage error (exit 2) in every mode, also when empty (it was "no pin")
  bad=0; det=
  for v in "--challenge-sha256=" "--comparator-sha256=" "--comparator-sha256=HEX" "--challenge-sha256=$(printf 'A%.0s' $(seq 64))"; do
    o=$(fresh d-malf); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset reference --from-export "$c/solution.export" "$v" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
    det="$det [${v:0:22}] rc=$r"; { [ "$r" = 2 ] && grep -q "must be 64 lowercase hex digits" "$o.log"; } || bad=1
  done
  row $bad "malformed-pin-value-exit-2-in-every-mode" "$det"
  spin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$FV/check/sound/pins.env"; }   # the judge's pinned self-test inputs
  st=$(fresh d-pin-st-chal); mkdir -p "$st"; cp "$(spin selftest_challenge)" "$st/challenge.export"; cp "$(spin selftest_comparator)" "$st/comparator.json"
  fvx d-pin-cheat "$st" "$(spin selftest_bad)" sound
  row $([ "$(verdict_of d-pin-cheat)" = REJECTED ] && [ "$(rc_of d-pin-cheat)" = 1 ] && [ "$(jget "$WORK/d-pin-cheat/result.json" inputs.comparator_config.pinned_sha256)" = "$(sha "$st/comparator.json")" ] && echo 0 || echo 1) "pin/correct-pin-cheat-rejected-and-pin-recorded" "verdict=$(verdict_of d-pin-cheat) rc=$(rc_of d-pin-cheat)"
  o=$(fresh d-ci-nopin); mkdir -p "$o/proj"; cp "$D/ci-example/"* "$o/proj/"
  ( cd "$o/proj" && env -i PATH=/usr/bin:/bin HOME=/tmp FV_EXPERIMENTAL_CI=1 "$FV/tools/ci-action/fv-ci.sh" --project . --challenge "$P/Challenge" --challenge-sha256 "$(sha "$P/Challenge/challenge.export")" --out-dir "$o/out" --threads "$THR" > "$o/log" 2>&1 ); r=$?
  row $([ "$r" = 2 ] && grep -q -- "--comparator-sha256 HEX" "$o/log" && grep -q "^  comparator-sha256:" "$FV/tools/ci-action/action.yml" && awk '/^  comparator-sha256:/{f=1} f&&/required:/{print; exit}' "$FV/tools/ci-action/action.yml" | grep -q true && echo 0 || echo 1) "pin/ci-runner-and-action-require-comparator-pin" "rc=$r"
  # --- a host view without /run/user: the upstream comparator's kernel sandbox cannot start; never REJECTED
  o=$(fresh d-norun); mkdir -p "$o"
  /usr/bin/bwrap --dev-bind / / --tmpfs /run -- "$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$P/Challenge/comparator.json" --threads 4 --json "$o/stage.json" > "$o/out" 2> "$o/err"; r=$?
  row $([ "$(jget "$o/stage.json" verdict)" != REJECTED ] && [ "$r" != 1 ] && echo 0 || echo 1) "c0-without-run-user-never-rejected" "rc=$r verdict=$(jget "$o/stage.json" verdict)"
  # --- (5) batchverify under a 4 KiB file-size limit: the stopped compile is NO-VERDICT, never REJECTED
  ws=$(fresh d-ws); mkdir -p "$ws/.lake/packages"; o=$(fresh d-bcap)
  ( ulimit -f 4; "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$D/namespaced/Challenge" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" --threads "$THR" --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$o.log" 2>&1 )
  v=$(jget "$o/batch.json" attempts | "$PY" -I -c 'import json,sys; print((json.loads(sys.stdin.read() or "{}").get("QACheck.addZero") or {}).get("verdict"))' 2>/dev/null)
  row $([ "$v" != REJECTED ] && [ "$v" != ACCEPTED ] && echo 0 || echo 1) "batch-file-size-kill-no-verdict" "verdict=$v"
  # --- (7) a signal at the final commit: the process exit equals the exit recorded in the final result.json
  c=$D/quoted-axiom
  for mode in final-after final-before; do o=$(fresh d-sig-$mode)
    env -i PATH=/usr/bin:/bin HOME=/tmp "$PY" -I "$HERE/sigwrap.py" $mode "$FV" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$c/solution.export" --challenge-sha256 "$(sha "$c/challenge.export")" --comparator-sha256 "$(sha "$c/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
    fe=$(jget "$o/result.json" exit); fv_=$(jget "$o/result.json" verdict)
    row $([ "$r" = "$fe" ] && [ "$fv_" = ACCEPTED ] && echo 0 || echo 1) "signal-at-final-commit-$mode-exit-matches-artifact" "process rc=$r result.json verdict=$fv_ exit=$fe"
  done
  # --- (8) judge selection does not depend on the optimizer; the selection's release is bound to the hashed bytes
  e=$(fresh d-noat); mkdir -p "$e"; cp "$D/export-437/challenge.export" "$e/"; cp "$D/export-437/comparator-noaxioms.json" "$e/comparator.json"; o=$(fresh d-noat-out)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$PY" -I "$HERE/sigwrap.py" no-autotune "$FV" "$WORK/emptyproj" "$e" "$o" --preset sound-auto --from-export "$D/export-437/solution.export" --challenge-sha256 "$(sha "$e/challenge.export")" --comparator-sha256 "$(sha "$e/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 0 ] && [ "$(jget "$o/result.json" checks.sound.stage.toolchain)" = "leanprover/lean4:v4.37.0-rc1" ] && echo 0 || echo 1) "selection-without-autotune-still-437" "rc=$r verdict=$(jget "$o/result.json" verdict) judge=$(jget "$o/result.json" checks.sound.stage.toolchain)"
  "$PY" -I - "$FV" "$D/quoted-axiom" > "$WORK/conj-bind.out" 2>&1 <<'PY'
import importlib.util, os, sys, types, threading
fv, cdir = sys.argv[1], sys.argv[2]
spec = importlib.util.spec_from_file_location("fvm5db", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class A(types.SimpleNamespace):
    def __getattr__(self, k):
        return None
r = m.Run.__new__(m.Run); r.lock = threading.Lock(); r.res = {"inputs": {}}
r.a = A(challenge=cdir, sound=True, challenge_sha256=m.sha256_file(os.path.join(cdir, "challenge.export")))
r.selection_release = ("4.37.0-rc1", "0b77e12952ad39077d80d8bd6b66d601f225c321")   # selected earlier from other bytes
try:
    r.prepare_challenge_export(); print("BAD selection-bound-to-hashed-bytes no refusal")
except m.Refuse as e:
    print(("ok" if "changed during the run" in str(e) else "BAD"), "selection-bound-to-hashed-bytes", str(e)[:100])
except Exception as e:
    print("BAD selection-bound-to-hashed-bytes", type(e).__name__, str(e)[:100])
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/conj-bind.out"
  # --- (9) the C0 preflight of a 4.37 challenge needs only the 4.37 comparator (the 4.36 tree hidden)
  em=$(fresh d-empty36); mkdir -p "$em"
  bwrap --die-with-parent --unshare-all --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --bind "$WORK" "$WORK" --ro-bind "$em" "$TC36" "$FV/check/official/check.sh" --preflight --release 4.37.0-rc1 > "$WORK/d-c0pf.out" 2>&1; r=$?
  row $([ "$r" = 0 ] && echo 0 || echo 1) "c0-preflight-437-without-436" "rc=$r $(tail -1 "$WORK/d-c0pf.out" | cut -c1-100)"
  # --- (10) a finite but unhit CPU limit does not hide a confirmed type error
  pj=$(fresh d-te); mkdir -p "$pj"; cp -r "$DD/type-error" "$pj/proj"; cp -r "$P/Challenge" "$pj/chal"; o=$(fresh d-te-out)
  ( ulimit -t 86400; env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/proj" "$pj/chal" "$o" --preset sound --challenge-sha256 "$(sha "$pj/chal/challenge.export")" --comparator-sha256 "$(sha "$pj/chal/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1 ); r=$?
  row $([ "$r" = 1 ] && [ "$(jget "$o/result.json" verdict)" = REJECTED ] && echo 0 || echo 1) "unhit-cpu-limit-type-error-rejected" "rc=$r verdict=$(jget "$o/result.json" verdict)"
  # --- (11) batch: QACheck.addZero.lean resolves to the configured QACheck.«addZero» (Lean names)
  o=$(fresh d-alias)
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$DD/batch-alias" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256 "$(sha "$DD/batch-alias/challenge.export")" --threads "$THR" --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$o.log" 2>&1
  v=$(jget "$o/batch.json" attempts | "$PY" -I -c 'import json,sys; print((json.loads(sys.stdin.read() or "{}").get("QACheck.addZero") or {}).get("verdict"))' 2>/dev/null)
  row $([ "$v" = ACCEPTED ] && echo 0 || echo 1) "batch-target-by-lean-name" "verdict=$v"
fi

# ======================================================================================== pins, snapshots, wrappers, option arity, exit codes
if want pins; then
  P=$D/project-4.36.0; DD=$D/batch-items; D1=$D/kernel-timeout; c=$D/quoted-axiom; CS1=$(sha "$c/challenge.export"); CC1=$(sha "$c/comparator.json")
  mkdir -p "$WORK/emptyproj"
  # --- (a) --challenge-sha256 without --comparator-sha256 is refused also when the challenge is BUILT
  b=$(fresh e-built); mkdir -p "$b"; cp "$c/comparator.json" "$c/lean-toolchain" "$b/"; o=$(fresh e-built-out)
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$b" "$o" --preset sound --from-export "$c/solution.export" --challenge-sha256 "$CS1" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && grep -q "needs --comparator-sha256" "$o.log" && [ "$(jget "$o/result.json" checks)" = "{}" ] && echo 0 || echo 1) "challenge-pin-without-comparator-pin-refused-for-a-built-challenge" "rc=$r"
  # --- (b) the challenge inputs are snapshotted ONCE; later changes of the caller's directory are ignored;
  #     a given export without the comparator pin is refused again at the pin check
  d1=$(fresh e-snap1); mkdir -p "$d1"; cp "$c/comparator.json" "$c/lean-toolchain" "$d1/"
  d2=$(fresh e-snap2); mkdir -p "$d2"; cp "$c/comparator.json" "$c/lean-toolchain" "$c/challenge.export" "$d2/"
  "$PY" -I - "$FV" "$d1" "$d2" "$c/challenge.export" "$D/export-437/challenge.export" "$CS1" "$CC1" > "$WORK/e-snap.out" 2>&1 <<'PY'
import importlib.util, os, shutil, sys, tempfile, threading, types
fv, d1, d2, ce, other, cs, cc = sys.argv[1:8]
spec = importlib.util.spec_from_file_location("fvm51", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class A(types.SimpleNamespace):
    def __getattr__(self, k):
        return None
def mk(d, **k):
    r = m.Run.__new__(m.Run); r.lock = threading.Lock(); r.res = {"inputs": {}}; r.tmp = tempfile.mkdtemp()
    r.a = A(challenge=d, export="/x.export", sound=True, challenge_sha256=cs, comparator_sha256=cc, **k); return r
try:
    r = mk(d1); r.read_inputs(); shutil.copyfile(ce, os.path.join(d1, "challenge.export"))   # appears after the snapshot
    print(("ok" if r.given_challenge_export() is None else "BAD"), "export-appearing-after-the-snapshot-is-ignored")
except Exception as e:
    print("BAD export-appearing-after-the-snapshot-is-ignored", type(e).__name__, str(e)[:120])
try:
    r = mk(d2); r.read_inputs(); shutil.copyfile(other, os.path.join(d2, "challenge.export"))   # replaced after the snapshot
    r.prepare_challenge_export()
    print(("ok" if r.res["inputs"]["challenge_export"]["sha256"] == cs else "BAD"), "export-replaced-after-the-snapshot-is-ignored")
except Exception as e:
    print("BAD export-replaced-after-the-snapshot-is-ignored", type(e).__name__, str(e)[:120])
try:
    shutil.copyfile(ce, os.path.join(d2, "challenge.export")); r = mk(d2); r.read_inputs(); r.a.comparator_sha256 = None
    r.prepare_challenge_export(); print("BAD given-export-without-comparator-pin-refused-at-the-pin-check no refusal")
except m.Refuse as e:
    print(("ok" if "--comparator-sha256" in str(e) else "BAD"), "given-export-without-comparator-pin-refused-at-the-pin-check", str(e)[:90])
except Exception as e:
    print("BAD given-export-without-comparator-pin-refused-at-the-pin-check", type(e).__name__, str(e)[:120])
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/e-snap.out"
  grep -q "pin-check" "$WORK/e-snap.out" || row 1 "pins/snapshot-harness" "$(tail -3 "$WORK/e-snap.out" | tr '\n' ' ')"
  # --- an identity option given twice (here through an abbreviation) is a usage error; wrappers refuse forwarded ones
  o=$(fresh e-dup); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --comparator-sha="$CC1" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && grep -q "given more than once" "$o.log" && [ ! -e "$o/result.json" ] && echo 0 || echo 1) "identity-option-twice-usage-error" "rc=$r"
  bash "$FV/tools/rh-sound.sh" "$(fresh e-rh)" 2 --comparator-sha=0000 > "$WORK/e-rh.log" 2>&1; r1=$?
  "$PY" -I "$FV/tools/claims.py" verify "$WORK/emptyproj" "$WORK/emptyproj" "$WORK/emptyproj" "$(fresh e-cl)" -- --preset=fastest > "$WORK/e-cl.log" 2>&1; r2=$?
  row $([ "$r1" = 2 ] && grep -q "refused" "$WORK/e-rh.log" && [ "$r2" = 2 ] && grep -q "refused" "$WORK/e-cl.log" && echo 0 || echo 1) "wrappers-refuse-forwarded-identity-options" "rh-sound rc=$r1 claims rc=$r2"
  # --- a trusted preset whose deciding check was overridden away is refused
  o=$(fresh e-pc); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --check C4 --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && grep -q "must stay selected" "$o.log" && echo 0 || echo 1) "sound-preset-without-CS-refused" "rc=$r"
  # --- an incomplete pin pair skips the tuner (no planning before the refusal)
  o=$(fresh e-at); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound-auto --from-export "$c/solution.export" --challenge-sha256 "$CS1" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && jget "$o/result.json" autotune.skipped | grep -q "pin pair is incomplete" && echo 0 || echo 1) "incomplete-pin-pair-refused-before-planning" "rc=$r autotune=$(jget "$o/result.json" autotune | cut -c1-80)"
  # --- check B (C3) on a 4.37 challenge is refused (it would run the 4.36 tree's nanoda)
  e=$D/export-437; o=$(fresh e-c3); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$e" "$o" --preset sound --check CS,C3 --from-export "$e/solution.export" --challenge-sha256 "$(sha "$e/challenge.export")" --comparator-sha256 "$(sha "$e/comparator.json")" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && grep -q "cannot judge a 4.37+ challenge" "$o.log" && echo 0 || echo 1) "c3-refused-for-437-challenge" "rc=$r"
  # --- a result.json verdict without an integer exit is not final
  "$PY" -I - "$FV" > "$WORK/e-norm.out" 2>&1 <<'PY'
import importlib.util, os, sys
spec = importlib.util.spec_from_file_location("fvs51", os.path.join(sys.argv[1], "schemas", "fv_schema.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
vs = [m.from_fastverify_result({"verdict": v, "trust": "sound", "mode": {"sound": True, "check": ["CS"]}})["verdict"] for v in ("ACCEPTED", "REJECTED", "CONDITIONAL")]
print(("ok" if vs == ["ERROR"] * 3 else "BAD"), "verdict-without-exit-not-final", vs)
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/e-norm.out"
  # --- fv-ci.sh option without its value -> exit 2; an earlier invocation's reports are retired
  "$FV/tools/ci-action/fv-ci.sh" --project "$WORK/emptyproj" --challenge "$c" --challenge-sha256 "$CS1" --out-dir "$(fresh e-ci0)" --comparator-sha256 > "$WORK/e-ci0.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && grep -q "needs a value" "$WORK/e-ci0.log" && echo 0 || echo 1) "ci-option-without-value-exit-2" "rc=$r"
  o=$(fresh e-cistale); mkdir -p "$o/proj" "$o/out"; cp "$D/ci-example/"* "$o/proj/"
  printf '{"verdict": "ACCEPTED", "exit": 0, "frontier": [], "claim": "stale report of an earlier run"}\n' > "$o/out/frontier-check.json"
  printf '{"verdict": "ACCEPTED"}\n' > "$o/out/result-v1.json"
  ( cd "$o/proj" && env -i PATH=/usr/bin:/bin HOME=/tmp FV_EXPERIMENTAL_CI=1 "$FV/tools/ci-action/fv-ci.sh" --project . --challenge "$P/Challenge" --challenge-sha256 "$(printf '0%.0s' $(seq 64))" --comparator-sha256 "$(sha "$P/Challenge/comparator.json")" --out-dir "$o/out" --threads "$THR" > "$o/log" 2>&1 ); r=$?
  row $([ "$r" != 0 ] && [ ! -e "$o/out/frontier-check.json" ] && [ "$(jget "$o/out/result-v1.json" accepted)" != True ] && echo 0 || echo 1) "ci-earlier-reports-retired" "rc=$r stale-frontier=$([ -e "$o/out/frontier-check.json" ] && echo kept || echo removed) v1.accepted=$(jget "$o/out/result-v1.json" accepted)"
  # --- a truncated stage report gives the error envelope, exit 2
  printf '{"verdict": "ACC' > "$WORK/e-trunc.json"
  "$PY" -I "$FV/tools/ci-action/render_ci_report.py" --input-kind fastverify --input "$WORK/e-trunc.json" --out-json "$WORK/e-trunc-v1.json" --out-sarif "$WORK/e-trunc.sarif" --out-md "$WORK/e-trunc.md" > "$WORK/e-trunc.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$WORK/e-trunc-v1.json" verdict)" = ERROR ] && echo 0 || echo 1) "truncated-report-error-envelope" "rc=$r verdict=$(jget "$WORK/e-trunc-v1.json" verdict)"
  # --- C0, an external kernel stopped by timeout (exit 124) is ERROR, not REJECTED
  o=$(fresh e-k124); mkdir -p "$o"
  "$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$D1/kernel-timeout.json" --threads 4 --json "$o/stage.json" > "$o/out" 2> "$o/err"; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/stage.json" verdict)" = ERROR ] && echo 0 || echo 1) "c0-kernel-timeout-124-is-error" "rc=$r verdict=$(jget "$o/stage.json" verdict) ($(grep -o 'nanoda exited with [0-9]*' "$o/err" | head -1))"
  # --- C0 option without value -> exit 2 (no loop); preflight of an unregistered 4.37+ release refused
  timeout 20 "$FV/check/official/check.sh" a b c --threads > /dev/null 2>&1; r1=$?
  timeout 60 "$FV/check/official/check.sh" --preflight --release 4.37.99 > /dev/null 2>&1; r2=$?
  row $([ "$r1" = 2 ] && [ "$r2" = 2 ] && echo 0 || echo 1) "c0-option-arity-and-unregistered-release-preflight" "arity rc=$r1 preflight rc=$r2"
  # --- batchverify, an empty / malformed challenge pin is a usage error before OUT exists
  o=$(fresh e-bvpin); "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --packages "$EWS" --pset "$D/namespaced/Challenge" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256= > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && [ ! -e "$o" ] && echo 0 || echo 1) "batch-empty-challenge-pin-usage-error" "rc=$r out=$([ -e "$o" ] && echo created || echo absent)"
  # --- a 4.37 problem set: the 4.36 judge is refused; without --pins the 4.37 judge is selected
  ps=$(fresh e-ps437); mkdir -p "$ps"; cp "$D/export-437/challenge.export" "$D/export-437/comparator.json" "$ps/"; o=$(fresh e-bv437)
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --packages "$EWS" --pset "$ps" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256 "$(sha "$ps/challenge.export")" --pins check/sound/pins.env > "$o.log" 2>&1; r=$?
  sel=$("$PY" -I -c 'import importlib.util,os,sys,types
s=importlib.util.spec_from_file_location("bv51", os.path.join(sys.argv[1], "tools", "batchverify.py")); m=importlib.util.module_from_spec(s); s.loader.exec_module(m)
a=types.SimpleNamespace(fv=sys.argv[1], pset=sys.argv[2], pins=None); m.pset_judge(a); print(os.path.basename(a.pins or "none"))' "$FV" "$ps" 2>&1 | tail -1)
  row $([ "$r" = 2 ] && grep -q "judged only by its own release" "$o.log" && [ ! -e "$o" ] && [ "$sel" = pins-437.env ] && echo 0 || echo 1) "batch-437-problem-set-uses-437-judge" "explicit 4.36 rc=$r; default selects $sel"
  # --- an ownership export that cannot be read is no verdict (not "absent")
  ox=$WORK/e-own.export; cp "$D/namespaced/Main/main.export" "$ox"; chmod 000 "$ox"
  own=$("$PY" -I -c 'import importlib.util,os,sys
s=importlib.util.spec_from_file_location("bv52", os.path.join(sys.argv[1], "tools", "batchverify.py")); m=importlib.util.module_from_spec(s); s.loader.exec_module(m)
print(m.export_declares_theorem(sys.argv[2], "QACheck.addZero"))' "$FV" "$ox" 2>&1 | tail -1); chmod 644 "$ox"
  row $([ "$own" = None ] && echo 0 || echo 1) "unreadable-ownership-export-is-not-absent" "export_declares_theorem -> $own"
  # --- a compiler that cannot start (empty toolchain dir) gives NO-VERDICT, never REJECTED
  ws=$(fresh e-ws); mkdir -p "$ws/.lake/packages"; etc=$(fresh e-tc); mkdir -p "$etc/bin"; o=$(fresh e-bvnotc)
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$D/namespaced/Challenge" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" --threads "$THR" --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$etc" > "$o.log" 2>&1
  v=$(jget "$o/batch.json" attempts | "$PY" -I -c 'import json,sys; print((json.loads(sys.stdin.read() or "{}").get("QACheck.addZero") or {}).get("verdict"))' 2>/dev/null)
  # an unrecognisable --toolchain is refused at job level (exit 2, no report): also no verdict
  row $({ [ "$v" = NO-VERDICT ] || { [ ! -e "$o/batch.json" ] && grep -q "refuse (no verdict)" "$o.log"; }; } && echo 0 || echo 1) "batch-compiler-not-started-no-verdict" "verdict=${v:-none} $(grep -o 'refuse (no verdict)' "$o.log" | head -1)"
  # --- notary with B3, an unconfirmed transformed-build failure is no verdict (the grind +suggestions project; B1 would accept)
  y=$D/grind-suggestions; pj=$(fresh e-grind); mkdir -p "$pj"; cp -r "$y/chal" "$y/proj2" "$pj/"; o=$(fresh e-grind-out)
  UNS="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo-portable lean4-d5e35ef223-pgo-portable lean4-7586a50cec-nopgo lean4-7586a50cec-nopgo-portable,skip-kernel-tc,linter-off,retries,premise-off,j1-saturated,closure-only,sound-fast-path"   # sound-auto's choice for this project
  env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/proj2" "$pj/chal" "$o" --preset notary --experimental --build B3 --unsafe "$UNS" --no-confirm-build-failure --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/result.json" verdict)" != REJECTED ] && echo 0 || echo 1) "notary-unconfirmed-transformed-build-failure-no-verdict" "rc=$r verdict=$(jget "$o/result.json" verdict) build=$(jget "$o/result.json" build.option)"
fi

# ======================================================================================== ownership exports, job-level exit codes, CI cold path, private snapshots
if want ownership; then
  P=$D/project-4.36.0
  # --- an unreadable ownership export is NO-VERDICT whatever the theorem is called (here: missing_case)
  "$PY" -I - "$FV" > "$WORK/own-own.out" 2>&1 <<'PY'
import importlib.util, os, sys, tempfile, types
spec = importlib.util.spec_from_file_location("bv52own", os.path.join(sys.argv[1], "tools", "batchverify.py"))
bv = importlib.util.module_from_spec(spec); spec.loader.exec_module(bv)
d = tempfile.mkdtemp(prefix="own-")
def run(names):
    b = bv.Batch.__new__(bv.Batch); b.a = types.SimpleNamespace(par=2)
    b.res = {"checks": [{"exit": 0, "theorems": list(names), "tag": "s0", "reason": ""}], "attempts": {n: {} for n in names}}
    b.olean_may_hold = lambda n, key: True
    def export(root, ns, tag, thr):
        p = os.path.join(d, tag + ".export"); open(p, "w").write("{}\n"); os.chmod(p, 0); return p, None
    b.export = export
    b.verdicts()
    return {n: b.res["attempts"][n]["verdict"] for n in names}
v = run(["missing_case", "not_found_lemma"])
print(("ok" if set(v.values()) == {"NO-VERDICT"} else "BAD"), "unreadable-ownership-export-no-verdict-whatever-the-name", v)
print(("ok" if not bv.target_missing("export of Attempt.missing_case declined: exit 1", "missing_case")
       and bv.target_missing("unknown constant 'missing_case'", "missing_case") else "BAD"), "exporter-text-matched-without-the-theorem-name")
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/own-own.out"
  grep -q "exporter-text" "$WORK/own-own.out" || row 1 "ownership/own-harness" "$(tail -3 "$WORK/own-own.out" | tr '\n' ' ')"
  # --- a job-level Python exception (an existing --out) is exit 2, never 1
  o=$(fresh f2-exists); mkdir -p "$o"
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --packages "$EWS" --pset "$D/namespaced/Challenge" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" > "$o.log" 2>&1; r1=$?
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --packages "$EWS" --pset /nonexistent-pset --attempts "$D/namespaced/attempts" --out "$(fresh f2-nopset)" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" > "$WORK/f2-nopset.log" 2>&1; r2=$?
  row $([ "$r1" = 2 ] && [ "$r2" = 2 ] && echo 0 || echo 1) "batch-job-level-exception-exit-2" "existing --out rc=$r1, missing problem set rc=$r2"
  # --- v0.1 CI always takes the cold path: a valid cached base + an incr-reverify.sh that takes --comparator-sha256
  #     (stub, writes a marker) never switch it on
  view=$(fresh f2-view); mkdir -p "$view"; cp -as "$FV/." "$view/" 2>/dev/null
  rm -f "$view/tools/incr/incr-reverify.sh"; mkdir -p "$view/tools/incr"
  printf '#!/bin/bash\n# stub: options --challenge-sha256) --comparator-sha256) as the incremental entry point\ntouch "%s"\nexit 2\n' "$WORK/f2-incr-called" > "$view/tools/incr/incr-reverify.sh"; chmod 755 "$view/tools/incr/incr-reverify.sh"
  rm -f "$WORK/f2-incr-called"; cache=$(fresh f2-cache); mkdir -p "$cache/base/work/proj" "$cache/base/log/build-fast"; : > "$cache/base/log/export-targets.txt"; : > "$cache/base/log/build-fast/plan.jsonl"
  printf '{"inputs": {"challenge_export": {"sha256": "%s"}, "comparator_config": {"sha256": "%s"}}, "build": {"option": "B3"}}\n' "$(sha "$P/Challenge/challenge.export")" "$(sha "$P/Challenge/comparator.json")" > "$cache/base/result.json"
  o=$(fresh f2-ci); mkdir -p "$o/proj"; cp "$D/ci-example/"* "$o/proj/"
  ( cd "$o/proj" && env -i PATH=/usr/bin:/bin HOME=/tmp FV_EXPERIMENTAL_CI=1 "$view/tools/ci-action/fv-ci.sh" --fv-root "$view" --project . --challenge "$P/Challenge" --challenge-sha256 "$(sha "$P/Challenge/challenge.export")" --comparator-sha256 "$(sha "$P/Challenge/comparator.json")" --preset sound --cache-dir "$cache" --out-dir "$o/out" --threads "$THR" > "$o/log" 2>&1 ); r=$?
  row $([ ! -e "$WORK/f2-incr-called" ] && [ "$r" = 0 ] && echo 0 || echo 1) "ci-always-cold-path" "rc=$r incr-reverify $([ -e "$WORK/f2-incr-called" ] && echo CALLED || echo 'not called')"  # ---------------------------------------------------------------- snapshot privacy, wrappers, pins, CI reports
  c=$D/quoted-axiom; CS1=$(sha "$c/challenge.export"); CC1=$(sha "$c/comparator.json"); mkdir -p "$WORK/emptyproj"
  # --- the snapshot and its parents are private (umask 0002 run; OUT loses group write, tmp + snapshot 0700)
  d1=$(fresh f2-snapmode); mkdir -p "$d1"; cp "$c/comparator.json" "$c/lean-toolchain" "$c/challenge.export" "$d1/"
  ( umask 0002; "$PY" -I - "$FV" "$d1" "$CS1" "$CC1" "$(fresh f2-snapmode-out)" ) > "$WORK/f2-snapmode.out" 2>&1 <<'PY'
import importlib.util, os, stat, sys, threading, types
fv, d, cs, cc, out = sys.argv[1:6]
spec = importlib.util.spec_from_file_location("fvm52", os.path.join(fv, "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class A(types.SimpleNamespace):
    def __getattr__(self, k):
        return None
os.makedirs(os.path.join(out, "tmp"))   # created under umask 0002: group-writable
r = m.Run.__new__(m.Run); r.lock = threading.Lock(); r.res = {"inputs": {}}; r.out = out; r.tmp = os.path.join(out, "tmp")
r.a = A(challenge=d, export="/x.export", sound=True, challenge_sha256=cs, comparator_sha256=cc)
try:
    r.read_inputs()
    md = {p: stat.S_IMODE(os.stat(p).st_mode) for p in (out, r.tmp, r.snap)}
    ok = not (md[out] & 0o022) and md[r.tmp] == 0o700 and md[r.snap] == 0o700
    print(("ok" if ok else "BAD"), "private-snapshot-and-parents-not-group-writable", {os.path.basename(k) or k: oct(v) for k, v in md.items()})
except Exception as e:
    print("BAD private-snapshot-and-parents-not-group-writable", type(e).__name__, str(e)[:120])
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/f2-snapmode.out"
  grep -q "private-snapshot-and-parents-not-group-writable" "$WORK/f2-snapmode.out" || row 1 "ownership/snapmode-harness" "$(tail -3 "$WORK/f2-snapmode.out" | tr '\n' ' ')"
  # --- C3 / C4 on their own are refused for a 4.37 challenge
  e=$D/export-437; r3=; for ck in C3 C4; do o=$(fresh f2-$ck); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$e" "$o" --check $ck --from-export "$e/solution.export" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
    { [ "$r" = 2 ] && grep -q "cannot judge a 4.37+ challenge" "$o.log"; } || r3="$r3 $ck:rc=$r"; done
  row $([ -z "$r3" ] && echo 0 || echo 1) "standalone-c3-c4-refused-for-437" "${r3:-both refused}"
  # --- the wrappers forward tuning options only (an existing-export option is refused)
  bash "$FV/tools/rh-sound.sh" "$(fresh f2-rh)" 2 --from-export /nonexistent > "$WORK/f2-rh.log" 2>&1; r1=$?
  "$PY" -I "$FV/tools/claims.py" verify "$WORK/emptyproj" "$WORK/emptyproj" "$WORK/emptyproj" "$(fresh f2-cl)" -- --export=/nonexistent > "$WORK/f2-cl.log" 2>&1; r2=$?
  row $([ "$r1" = 2 ] && grep -q "not a tuning option" "$WORK/f2-rh.log" && [ "$r2" = 2 ] && grep -q "not a tuning option" "$WORK/f2-cl.log" && echo 0 || echo 1) "wrappers-refuse-solution-source-options" "rh-sound rc=$r1 claims rc=$r2"
  # --- a valid-looking but WRONG comparator digest skips the planner as well
  o=$(fresh f2-at); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound-auto --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$(printf 'f%.0s' $(seq 64))" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && jget "$o/result.json" autotune.skipped | grep -q "does not match" && echo 0 || echo 1) "wrong-comparator-digest-refused-before-planning" "rc=$r"
  # --- C0 preflight of a malformed release spelling
  timeout 30 "$FV/check/official/check.sh" --preflight --release 4.37.1oops > /dev/null 2>&1; r=$?
  row $([ "$r" = 2 ] && echo 0 || echo 1) "c0-preflight-malformed-release-refused" "rc=$r"
  # --- batchverify reads the release from its private copy and refuses an unreadable one (pin = those bytes)
  ps=$(fresh f2-psbad); mkdir -p "$ps"; { echo '{"not a meta line": true}'; tail -n +2 "$D/namespaced/Challenge/challenge.export"; } > "$ps/challenge.export"; cp "$D/namespaced/Challenge/comparator.json" "$ps/"; o=$(fresh f2-bvbad)
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --packages "$EWS" --pset "$ps" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256 "$(sha "$ps/challenge.export")" > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && grep -q "release cannot be read" "$o.log" && [ ! -e "$o" ] && [ -z "$(ls -A "$(dirname "$o")" | grep '^\.batchverify-pset\.')" ] && echo 0 || echo 1) "batch-unreadable-release-refused-from-private-copy" "rc=$r out=$([ -e "$o" ] && echo created || echo absent)"
  # --- a damaged installed dependency (empty .olean, reported at the attempt's import line) is NO-VERDICT
  ws=$(fresh f2-ws); mkdir -p "$ws/.lake/packages/qadep/.lake/build/lib/lean"; : > "$ws/.lake/packages/qadep/.lake/build/lib/lean/QaDep.olean"
  att=$(fresh f2-att); mkdir -p "$att"; printf 'import QaDep\ntheorem QACheck.addZero (n : Nat) : n + 0 = n := Nat.add_zero n\n' > "$att/QACheck.addZero.lean"; o=$(fresh f2-bvdep)
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$D/namespaced/Challenge" --attempts "$att" --out "$o" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" --threads "$THR" --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$o.log" 2>&1
  v=$(jget "$o/batch.json" attempts | "$PY" -I -c 'import json,sys; print((json.loads(sys.stdin.read() or "{}").get("QACheck.addZero") or {}).get("verdict"))' 2>/dev/null)
  row $([ "$v" = NO-VERDICT ] && echo 0 || echo 1) "batch-damaged-dependency-no-verdict" "verdict=$v ($(grep -o 'failed to read file[^)]*\|invalid header' "$o/log/Attempt.QACheck.addZero.build.log" 2>/dev/null | head -1 | cut -c1-60))"
  # --- notary scope check: a scope check that DECLINES stops a notary run before the cross-version gate / build / CN;
  #     a notary stage without --scope-check (scope check not installed) falls through unchanged
  nv=$(fresh f2-nview); mkdir -p "$nv"; cp -as "$FV/." "$nv/" 2>/dev/null; rm -f "$nv/check/notary/check-notary.sh"
  printf '#!/bin/bash\n# stub: --scope-check DECLINES; anything else -> the real stage (--challenge-sha256) --comparator-sha256))\ncase " $* " in *" --scope-check "*) echo %s; exit 2;; esac\nexec "%s" "$@"\n' \
    "'{\"checker\":\"checkNotary\",\"verdict\":\"DECLINED\",\"exit\":2,\"reason\":\"stub: outside the notary v0.1 scope\"}'" "$(readlink -f "$FV/check/notary/check-notary.sh")" > "$nv/check/notary/check-notary.sh"
  chmod 755 "$nv/check/notary/check-notary.sh"
  for f in bin/fastverify lib/fastverify.py; do rm -f "$nv/$f"; cp -p "$FV/$f" "$nv/$f"; done   # ROOT = the view
  o=$(fresh f2-nscope); env -i PATH=/usr/bin:/bin HOME=/tmp "$nv/bin/fastverify" "$WORK/emptyproj" "$c" "$o" --preset notary --experimental --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none > "$o.log" 2>&1; r1=$?
  o3=$(fresh f2-nscope-cs); env -i PATH=/usr/bin:/bin HOME=/tmp "$nv/bin/fastverify" "$WORK/emptyproj" "$c" "$o3" --preset notary --experimental --check CN,CS --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none > "$o3.log" 2>&1; r3=$?
  row $([ "$r3" = 2 ] && [ "$(jget "$o3/result.json" notary_scope.verdict)" = DECLINED ] && [ "$(jget "$o3/result.json" checks)" = "{}" ] && echo 0 || echo 1) "notary-scope-gate-also-with-CN-CS" "rc=$r3 scope=$(jget "$o3/result.json" notary_scope.verdict) verdict=$(jget "$o3/result.json" verdict)"
  o2=$(fresh f2-nold); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o2" --preset notary --experimental --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none > "$o2.log" 2>&1; r2=$?
  sk=$(jget "$o2/result.json" notary_scope.skipped)
  if grep -q -- "--scope-check" "$FV/check/notary/check-notary.sh"; then sk="(installed checker has --scope-check)"; fi
  row $([ "$r1" = 2 ] && [ "$(jget "$o/result.json" notary_scope.verdict)" = DECLINED ] && [ "$(jget "$o/result.json" checks)" = "{}" ] && echo "$sk" | grep -q "scope" && echo 0 || echo 1) "notary-scope-gate-before-gate-and-build" "declined: rc=$r1 scope=$(jget "$o/result.json" notary_scope.verdict); old checker: rc=$r2 verdict=$(jget "$o2/result.json" verdict) ($sk)"
  # --- the REJECTED branch of decide_sound_and_notary (--check CS,CN), with a kill probe
  "$PY" -I - "$FV" > "$WORK/f2-judgepair.out" 2>&1 <<'PY'
import importlib.util, os, sys, tempfile, threading, types
spec = importlib.util.spec_from_file_location("fvlib_y43", os.path.join(sys.argv[1], "lib", "fastverify.py"))
m = importlib.util.module_from_spec(spec); sys.argv = [sys.argv[0]]; spec.loader.exec_module(m)
A = types.SimpleNamespace
def mk():
    r = m.Run.__new__(m.Run); r.lock = threading.Lock()
    r.a = A(threads=2, unsafe_check=[], checks=["CS", "CN"], sound=True, notary=True, extra_kernel=[], require_kernel=[],
            skip_extra_kernel=[], unsafe_build=[], challenge_sha256="ab" * 32)
    r.res = {"checks": {}, "stage_seconds": {}, "warnings": [], "inputs": {"challenge_export": {"sha256": "ab" * 32}}}
    r.out = tempfile.mkdtemp(); r.warn = lambda msg: None
    return r
for cs, cn in (("REJECTED", "ACCEPTED"), ("ACCEPTED", "REJECTED"), ("REJECTED", "REJECTED"), ("REJECTED", "DECLINED")):
    r = mk(); r.res["checks"] = {"sound": {"verdict": cs, "stage": {"reason": "x", "basis": "b"}},
                                 "notary": {"verdict": cn, "stage": {"reason": "y", "basis": "b"}}}
    try:
        r.decide(); v = r.res["verdict"]
    except Exception as e:
        v = type(e).__name__
    print(("ok" if v == "REJECTED" else "BAD"), "CS-%s-CN-%s-rejected-guard" % (cs, cn), v)
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/f2-judgepair.out"
  grep -q "CS-REJECTED-CN-DECLINED" "$WORK/f2-judgepair.out" || row 1 "ownership/judge-pair-harness" "$(tail -3 "$WORK/f2-judgepair.out" | tr '\n' ' ')"
  # --- a C0 host failure (no private work directory can be created) exits 2 with ERROR (never 0)
  o=$(fresh f2-c0host); mkdir -p "$o"; P=$D/project-4.36.0
  TMPDIR=/nonexistent-f5-tmpdir "$FV/check/official/check.sh" "$P/Main/main.export" "$P/Challenge/challenge.export" "$P/Challenge/comparator.json" --threads 2 --json "$o/s.json" > "$o/out" 2> "$o/err"; r=$?
  row $([ "$r" = 2 ] && [ "$(jget "$o/s.json" verdict)" = ERROR ] && [ "$(jget "$o/s.json" exit)" = 2 ] && echo 0 || echo 1) "c0-host-failure-exit-2-guard" "rc=$r verdict=$(jget "$o/s.json" verdict)"
  # --- fv-ci.sh pins must be 64 lowercase hex; an identity option twice is refused; a refused run retires
  #     the previous run's reports first
  P=$D/project-4.36.0
  "$FV/tools/ci-action/fv-ci.sh" --project "$WORK/emptyproj" --challenge "$P/Challenge" --challenge-sha256 "$(sha "$P/Challenge/challenge.export")" --comparator-sha256 "$(sha "$P/Challenge/comparator.json")x" --out-dir "$(fresh f2-ci1)" > "$WORK/f2-ci1.log" 2>&1; r1=$?
  "$FV/tools/ci-action/fv-ci.sh" --project "$WORK/emptyproj" --challenge "$P/Challenge" --challenge-sha256 "$(sha "$P/Challenge/challenge.export")" --challenge-sha256 "$(sha "$P/Challenge/challenge.export")" --comparator-sha256 "$(sha "$P/Challenge/comparator.json")" --out-dir "$(fresh f2-ci2)" > "$WORK/f2-ci2.log" 2>&1; r2=$?
  o=$(fresh f2-ci3); mkdir -p "$o/out"; printf '{"verdict": "ACCEPTED", "accepted": true}\n' > "$o/out/result-v1.json"
  "$FV/tools/ci-action/fv-ci.sh" --project "$WORK/emptyproj" --challenge "$P/Challenge" --challenge-sha256 "$(sha "$P/Challenge/challenge.export")" --comparator-sha256 "$(printf 'e%.0s' $(seq 64))" --out-dir "$o/out" > "$WORK/f2-ci3.log" 2>&1; r3=$?
  row $([ "$r1" = 2 ] && grep -q "64 lowercase hex" "$WORK/f2-ci1.log" && [ "$r2" = 2 ] && grep -q "given more than once" "$WORK/f2-ci2.log" && [ "$r3" = 2 ] && [ ! -e "$o/out/result-v1.json" ] && echo 0 || echo 1) "ci-pin-format-duplicates-and-refusal-retires-reports" "hex rc=$r1 dup rc=$r2 refused rc=$r3 stale-v1=$([ -e "$o/out/result-v1.json" ] && echo kept || echo removed)"
fi

# ======================================================================================== wrapper forwarding, CI report retirement, declined ownership exports
if want wrappers; then
  P=$D/project-4.36.0
  # --- INFO: rh-sound.sh / amdjob-sound.sh forward pure tuning options (--threads, --build, --keep-work) with both RH pins
  RHP=$LIGHT_LEAN/alpoge-rh/lean; RHC=$LIGHT_LEAN/verify/challenge
  if [ -d "$RHP" ] && [ -f "$RHC/challenge.export" ]; then
    o=$(fresh f3-rh); ( cd "$FV" && RH_PROJECT="$RHP" RH_CHALLENGE="$RHC" bash tools/rh-sound.sh "$o" "$THR" --threads "$THR" --build B3 --keep-work --preflight-only > "$o.log" 2>&1 ); r=$?
    row $([ "$r" = 0 ] && [ "$(jget "$o/result.json" verdict)" = PREFLIGHT_OK ] && [ "$(jget "$o/result.json" inputs.comparator_config.pinned_sha256)" = d419c0d8cd8696eb6c3ebc01deb500038fb5820f04c6edc2b1b4ec24673b84c0 ] && echo 0 || echo 1) "rh-sound-forwards-tuning-options-with-both-pins" "rc=$r verdict=$(jget "$o/result.json" verdict) build=$(jget "$o/result.json" mode.build)"
  else info "rh-sound-forwards-tuning-options-with-both-pins" "SKIP: no RH project / challenge on this host"; fi
  # --- fv-ci.sh retires the previous run's reports right after argument parsing, before a --preset / usage refusal
  o=$(fresh f3-ci); mkdir -p "$o/out"; printf '{"verdict": "ACCEPTED", "accepted": true}\n' > "$o/out/result-v1.json"
  "$FV/tools/ci-action/fv-ci.sh" --project "$WORK/emptyproj" --challenge "$P/Challenge" --challenge-sha256 "$(sha "$P/Challenge/challenge.export")" --comparator-sha256 "$(sha "$P/Challenge/comparator.json")" --preset fastest --out-dir "$o/out" > "$o.log" 2>&1; r=$?
  row $([ "$r" = 2 ] && [ ! -e "$o/out/result-v1.json" ] && echo 0 || echo 1) "ci-reports-retired-before-a-preset-refusal" "rc=$r stale-v1=$([ -e "$o/out/result-v1.json" ] && echo kept || echo removed)"
  # --- an ownership export that the exporter declined is NO-VERDICT, whatever its text says
  "$PY" -I - "$FV" > "$WORK/f3-own.out" 2>&1 <<'PY'
import importlib.util, os, sys, types
spec = importlib.util.spec_from_file_location("bv53own", os.path.join(sys.argv[1], "tools", "batchverify.py"))
bv = importlib.util.module_from_spec(spec); spec.loader.exec_module(bv)
b = bv.Batch.__new__(bv.Batch); b.a = types.SimpleNamespace(par=2); names = ["QACheck.addZero", "other"]
b.res = {"checks": [{"exit": 0, "theorems": names, "tag": "s0", "reason": ""}], "attempts": {n: {} for n in names}}
b.olean_may_hold = lambda n, key: True
b.fv = sys.argv[1]
b.export = lambda root, ns, tag, thr: (None, "lean4export: unknown constant 'QACheck.addZero' (exit 1); target not found / missing")
b.verdicts()
v = {n: b.res["attempts"][n]["verdict"] for n in names}
print(("ok" if set(v.values()) == {"NO-VERDICT"} else "BAD"), "declined-ownership-export-no-verdict", v)
# the exporter's own structured decline for exactly the requested target (the module loaded, t is not in it) still rejects
b2 = bv.Batch.__new__(bv.Batch); b2.a = types.SimpleNamespace(par=2); b2.fv = sys.argv[1]; names2 = ["QACheck.addZero", "missing_case"]
b2.res = {"checks": [{"exit": 0, "theorems": names2, "tag": "s0", "reason": ""}], "attempts": {n: {} for n in names2}}
b2.olean_may_hold = lambda n, key: True
b2.export = lambda root, ns, tag, thr: (None, "target constant QACheck.«addZero» not found in environment (declining)")
b2.verdicts()
v2 = {n: b2.res["attempts"][n]["verdict"] for n in names2}
print(("ok" if v2 == {"QACheck.addZero": "REJECTED", "missing_case": "NO-VERDICT"} else "BAD"), "structured-target-absent-decline-rejects-exactly-that-target", v2)
PY
  while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/f3-own.out"
  grep -q "declined-ownership-export-no-verdict" "$WORK/f3-own.out" || row 1 "wrappers/own-harness" "$(tail -3 "$WORK/f3-own.out" | tr '\n' ' ')"  # ---------------------------------------------------------------- batch items, solution module absent from the export
  c=$D/quoted-axiom; CS1=$(sha "$c/challenge.export"); CC1=$(sha "$c/comparator.json"); mkdir -p "$WORK/emptyproj"
  # --- after a successful EXACT build, the solution module absent from the export -> REJECTED (official answer);
  #     the same after the transformed build B3 -> no verdict (unconfirmed)
  pj=$(fresh f3-nomod); mkdir -p "$pj"; cp -r "$P/Main" "$P/Challenge" "$pj/"; rm -f "$pj/Main/main.export"; mv "$pj/Main/Main.lean" "$pj/Main/Other.lean"
  sed -i 's/"Main"/"Other"/g' "$pj/Main/lakefile.toml"
  o=$(fresh f3-nomod-b0); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset sound --build B0 --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r1=$?
  o2=$(fresh f3-nomod-b3); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o2" --preset sound --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o2.log" 2>&1; r2=$?
  # B0 / B1 build the solution module by name (as lake comparator): a project without its source then
  # fails the official build -> REJECTED there; a B3 failure is REJECTED only after the exact builds confirm it
  b3att=$(jget "$o2/result.json" build.attempts | "$PY" -I -c 'import json,sys; print(",".join("%s:%s" % (a["option"], a["exit"]) for a in json.loads(sys.stdin.read() or "[]")))' 2>/dev/null)
  row $([ "$r1" = 1 ] && jget "$o/result.json" verdict_basis | grep -qE "no source for the solution module Main|the official lake build fails" && { [ "$r2" != 1 ] || echo "$b3att" | grep -qE "B0:1|B1:1"; } && echo 0 || echo 1) "exact-build-solution-module-absent-rejected-b3-not" "B0: rc=$r1 $(jget "$o/result.json" verdict); B3: rc=$r2 $(jget "$o2/result.json" verdict)"
  # --- a missing dependency (empty package dir: 'unknown module prefix' at the import line) -> NO-VERDICT
  ws=$(fresh f3-ws); mkdir -p "$ws/.lake/packages"; att=$(fresh f3-att); mkdir -p "$att"; printf 'import QaDep\ntheorem QACheck.addZero (n : Nat) : n + 0 = n := Nat.add_zero n\n' > "$att/QACheck.addZero.lean"; o=$(fresh f3-bvdep)
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$D/namespaced/Challenge" --attempts "$att" --out "$o" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" --threads "$THR" --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$o.log" 2>&1; r=$?
  v=$(jget "$o/batch.json" attempts | "$PY" -I -c 'import json,sys; print((json.loads(sys.stdin.read() or "{}").get("QACheck.addZero") or {}).get("verdict"))' 2>/dev/null)
  row $([ "$v" = NO-VERDICT ] && [ "$r" = 2 ] && echo 0 || echo 1) "batch-missing-dependency-no-verdict-exit-2" "verdict=$v rc=$r"
  # --- the batch compiler follows the problem set's release (4.37 set -> the 4.37 toolchain, 4.36 set -> 4.36)
  sel=$("$PY" -I -c 'import importlib.util,os,sys,types
s=importlib.util.spec_from_file_location("bv53tc", os.path.join(sys.argv[1], "tools", "batchverify.py")); m=importlib.util.module_from_spec(s); s.loader.exec_module(m)
out=[]
for ps in sys.argv[2:4]:
    a=types.SimpleNamespace(fv=sys.argv[1], pset=ps, pins=None, toolchain=None); m.pset_judge(a); out.append(os.path.basename(a.toolchain or "none"))
print(" ".join(out))' "$FV" "$D/export-437" "$D/namespaced/Challenge" 2>&1 | tail -1)
  row $([ "$sel" = "leanprover--lean4---v4.37.0-rc1 leanprover--lean4---v4.36.0" ] && echo 0 || echo 1) "batch-compiler-follows-problem-set-release" "$sel"
  # --- a new nested OUT hierarchy is created; SIGTERM -> exit 2, the private problem-set copy removed
  nb=$(fresh f3-nest); o="$nb/a/b/out"
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$D/namespaced/Challenge" --attempts "$D/namespaced/attempts" --out "$o" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" --threads 2 --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$nb.log" 2>&1; r1=$?
  sb=$(fresh f3-sig); mkdir -p "$sb"
  "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$D/namespaced/Challenge" --attempts "$D/namespaced/attempts" --out "$sb/out" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" --threads "$THR" --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$sb.log" 2>&1 & bp=$!
  for _ in $(seq 100); do [ -e "$sb/out" ] && break; sleep 0.1; done; sleep 0.5; kill -TERM $bp; wait $bp; r2=$?
  left=$(ls -A "$sb" | grep -c '^\.batchverify-pset\.')
  row $([ -d "$o" ] && [ -f "$o/batch.json" ] && ! grep -q "cannot create the private" "$nb.log" && [ "$r2" = 2 ] && [ "$left" = 0 ] && echo 0 || echo 1) "batch-nested-out-and-sigterm-teardown" "nested: rc=$r1 out=$([ -d "$o" ] && echo created || echo missing); SIGTERM: rc=$r2 leftover-copies=$left"
  # --- OUT and its run dirs private, result.json 0644, a batch's per-check config 0600 in a 0700 OUT
  o=$(fresh f3-modes); ( umask 0002; env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset sound --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none --keep-work > "$o.log" 2>&1 )
  md=$(stat -c '%a' "$o" "$o/work" "$o/log" "$o/result.json" 2>/dev/null | tr '\n' ' ')
  bo=$(fresh f3-bvmodes); ( umask 0002; "$PY" -I "$FV/tools/batchverify.py" --fv "$FV" --pset "$D/namespaced/Challenge" --attempts "$D/namespaced/attempts" --out "$bo" --challenge-sha256 "$(sha "$D/namespaced/Challenge/challenge.export")" --threads "$THR" --jobs 1 --par 1 --snapshot-header '' --packages "$ws" --toolchain "$TC36" > "$bo.log" 2>&1 )
  bm=$(stat -c '%a' "$bo" $(ls "$bo"/comparator.*.json 2>/dev/null | head -1) 2>/dev/null | tr '\n' ' ')
  row $([ "$md" = "755 700 700 644 " ] && [ "$bm" = "700 600 " ] && echo 0 || echo 1) "private-out-run-dirs-report-and-batch-config-modes" "fastverify OUT/work/log/result.json: $md; batch OUT/config: $bm"
  # --- a missing notary checker is refused (not skipped); a malformed --notary-kernels is a usage error
  nv=$(fresh f3-nview); mkdir -p "$nv"; cp -as "$FV/." "$nv/" 2>/dev/null; rm -f "$nv/check/notary/check-notary.sh"; for f in bin/fastverify lib/fastverify.py; do rm -f "$nv/$f"; cp -p "$FV/$f" "$nv/$f"; done
  o=$(fresh f3-nmiss); env -i PATH=/usr/bin:/bin HOME=/tmp "$nv/bin/fastverify" "$WORK/emptyproj" "$c" "$o" --preset notary --experimental --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none > "$o.log" 2>&1; r1=$?
  o2=$(fresh f3-nk); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o2" --preset notary --experimental --notary-kernels unknown --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" > "$o2.log" 2>&1; r2=$?
  row $([ "$r1" = 2 ] && [ "$(jget "$o/result.json" verdict)" != ACCEPTED ] && [ "$r2" = 2 ] && grep -q "notary-kernels unknown" "$o2.log" && echo 0 || echo 1) "notary-missing-checker-and-bad-kernels-refused" "missing checker: rc=$r1 $(jget "$o/result.json" verdict); kernels: rc=$r2"
fi
# ======================================================================================== solution module not a default target; notary opt-in
if want solution-module; then
  P=$D/project-4.36.0; c=$D/quoted-axiom; CS1=$(sha "$c/challenge.export"); CC1=$(sha "$c/comparator.json"); mkdir -p "$WORK/emptyproj"
  # --- the solution module HAS a source but is not a default target (the official comparator builds it by name):
  #     an exact build's export without it is no verdict, never REJECTED (sound --build B1, reference)
  pj=$(fresh f4-nodef); mkdir -p "$pj"; cp -r "$P/Main" "$P/Challenge" "$pj/"; rm -f "$pj/Main/main.export"
  printf 'name = "Main"\ndefaultTargets = ["Other"]\n\n[[lean_lib]]\nname = "Other"\n\n[[lean_lib]]\nname = "Main"\n' > "$pj/Main/lakefile.toml"
  printf 'def other : Nat := 1\n' > "$pj/Main/Other.lean"
  res=""; for pr in "sound --build B1" "reference"; do o=$(fresh "f4-nodef-${pr%% *}")
    env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset $pr --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
    res="$res [$pr] rc=$r $(jget "$o/result.json" verdict)"; done
  row $(echo "$res" | grep -q "REJECTED" && echo 1 || echo 0) "solution-module-not-a-default-target-never-rejected" "$res"
  # --- the notary check is EXPERIMENTAL in v0.1: refused without --experimental (preset notary, --check CN, --check CS,CN)
  res=""; for ck in "--preset notary" "--check CN" "--check CS,CN"; do o=$(fresh f4-nexp)
    env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" $ck --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none > "$o.log" 2>&1; r=$?
    { [ "$r" = 2 ] && grep -q "EXPERIMENTAL in v0.1: pass --experimental" "$o.log" && [ ! -e "$o/result.json" ]; } || res="$res [$ck] rc=$r"; done
  o=$(fresh f4-nexp-ok); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$WORK/emptyproj" "$c" "$o" --preset notary --experimental --from-export "$c/solution.export" --challenge-sha256 "$CS1" --comparator-sha256 "$CC1" --threads "$THR" --export-dir none --preflight-only > "$o.log" 2>&1; r=$?
  row $([ -z "$res" ] && [ "$r" = 0 ] && echo 0 || echo 1) "notary-refused-without-experimental" "${res:-all three refused}; with --experimental preflight rc=$r"
fi
# ======================================================================================== fvserve --fork-server compile errors
if want fork-server; then
  # a plain compile error under fvserve --fork-server is REJECTED (the fork child compiles a private copy; its diagnostics are
  # mapped back to the attempt's own file), an honest attempt ACCEPTED, both compiled by the fork server (no fallback)
  TC433=$("$PY" -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json")
  fk=$(fresh f6-fk); "$FV/tools/fvserve/fork/build.sh" "$TC433" "$fk" > "$fk.log" 2>&1
  if [ ! -x "$fk/fvfork" ]; then info "fork-server-compile-error-rejected" "SKIP: fvfork not built here ($fk.log)"
  else
    "$PY" -I -B - "$FV" "$(fresh f6-svc)" "$D/fork-pset/pset" "$TC433" "$fk/fvfork" > "$WORK/f6.out" 2>&1 <<'PY'
import hashlib, json, os, shutil, socket, subprocess, sys, time
fv, w, data, tc, fvfork = sys.argv[1:6]
os.makedirs(w); pset = os.path.join(w, "pset"); shutil.copytree(data, pset)
chsha = hashlib.sha256(open(os.path.join(pset, "challenge.export"), "rb").read()).hexdigest()
ws = os.path.join(w, "ws"); os.makedirs(os.path.join(ws, ".lake", "packages", "dummy", ".lake", "build", "lib", "lean"))
state = os.path.join(w, "st")
srv = subprocess.Popen(["python3", "-I", os.path.join(fv, "tools", "fvserve", "fvserve.py"), "serve", "--state", state,
                        "--pset", f"demo={pset}:{chsha}", "--toolchain", tc, "--packages", ws, "--threads", "4", "--keep", "10",
                        "--linger", "0.05", "--snapshot-header", "import Init\n", "--fork-server", fvfork],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
for _ in range(600):
    if os.path.exists(os.path.join(state, "sock")) or srv.poll() is not None:
        break
    time.sleep(0.5)
def req(obj, timeout=600):
    s = socket.socket(socket.AF_UNIX); s.settimeout(timeout); s.connect(os.path.join(state, "sock"))
    s.sendall((json.dumps(obj) + "\n").encode()); s.shutdown(socket.SHUT_WR)
    b = b""
    while True:
        c = s.recv(65536)
        if not c:
            break
        b += c
    return json.loads(b.decode())
try:
    r1 = req({"pset": "demo", "theorem": "thmA", "source": "import Init\ntheorem thmA : True := trivial\n"})
    r2 = req({"pset": "demo", "theorem": "thmB", "source": "import Init\ntheorem thmB : True := (1 : Nat)\n"})
    st = (req({"op": "stats"}, 60).get("verdicts") or {})
    ok = r1.get("verdict") == "ACCEPTED" and r2.get("verdict") == "REJECTED" and st.get("fork_compiles", 0) >= 2 and not st.get("fork_fallback")
    print(("ok" if ok else "BAD"), "fork-server-compile-error-rejected",
          f"honest {r1.get('verdict')}, compile error {r2.get('verdict')} ({str(r2.get('why'))[:90]}), fork_compiles {st.get('fork_compiles')}, fallback {st.get('fork_fallback')}")
finally:
    subprocess.run(["python3", "-I", os.path.join(fv, "tools", "fvserve", "fvserve.py"), "stop", "--state", state], capture_output=True)
    try:
        srv.wait(30)
    except subprocess.TimeoutExpired:
        srv.kill()
PY
    while read -r st nm rest; do case "$st" in ok) row 0 "$nm" "$rest";; BAD) row 1 "$nm" "$rest";; esac; done < "$WORK/f6.out"
    grep -q "fork-server-compile-error-rejected" "$WORK/f6.out" || row 1 "fork-server/driver" "$(tail -3 "$WORK/f6.out" | tr '\n' ' ')"
  fi
fi
# ======================================================================================== export-absence REJECTED
if want export-absence; then
  # after a successful EXACT build (B0), the official exporter reports that a TARGET is absent (the project's solution module
  # builds but does not declare the challenge theorem): REJECTED, the official comparator's answer (lib export_absence, the
  # target half; the module half is preceded by the official build of the module by name)
  P=$D/project-4.36.0; pj=$(fresh f8-notarget); mkdir -p "$pj"; cp -r "$P/Main" "$P/Challenge" "$pj/"; rm -f "$pj/Main/main.export"
  sed -i 's/theorem qaAddZero /theorem qaAddZeroRenamed /' "$pj/Main/Main.lean"
  o=$(fresh f8-notarget-b0); env -i PATH=/usr/bin:/bin HOME=/tmp "$FVB" "$pj/Main" "$pj/Challenge" "$o" --preset sound --build B0 --challenge-sha256 "$(sha "$pj/Challenge/challenge.export")" --comparator-sha256 "$(sha "$pj/Challenge/comparator.json")" --threads "$THR" --export-dir none --build-cache none > "$o.log" 2>&1; r=$?
  att=$(jget "$o/result.json" build.attempts | "$PY" -I -c 'import json,sys; print(",".join("%s:%s" % (a["option"], a["exit"]) for a in json.loads(sys.stdin.read() or "[]")))' 2>/dev/null)
  row $([ "$r" = 1 ] && [ "$(jget "$o/result.json" verdict)" = REJECTED ] && jget "$o/result.json" verdict_basis | grep -q "export failed: the target qaAddZero is not declared" && echo 0 || echo 1) "exact-build-target-absent-from-export-rejected" "rc=$r verdict=$(jget "$o/result.json" verdict) build=$att basis=$(jget "$o/result.json" verdict_basis | cut -c1-110)"
fi
echo "RESULT: $PASS PASS $FAILN FAIL"
[ "$FAILN" = 0 ]
