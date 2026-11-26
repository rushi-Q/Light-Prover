#!/bin/bash
# run.sh [WORK] — regression test suite for the user-facing interfaces:
#   * schemas/result-v1.schema.json + fv_schema.py (invariants, LSP 3.17, SARIF 2.1.0)
#   * tools/triage/triage.py (static + live bwrap Lean probes: OK, REFUTED, VACUOUS, ELAB_ERROR, duplicate)
#   * bin/fv (doctor, audit, triage, init-challenge, mint, verify, check, watch --once, attempt)
#   * tools/mcp/fastverify-mcp (MCP protocol revisions 2025-11-25 with newline framing AND 2024-11-05 with Content-Length framing, all tools/resources/prompts)
#   * tools/http/fvapi.py (/health, /metrics, /v1/verify, /v1/verify/batch, /verify, /api/check Kimina format)
#   * tools/ci-action/fv-ci.sh (cold -> incremental cache -> statement drift PR -> sorry PR -> cache retention)
# Env: FV_ROOT, FV_PACKAGES (node-local ws recommended), TC433, EVAL_THREADS (default 8)
set -u
export FV_EXPERIMENTAL_CI=1   # the CI check (fv-ci.sh / bin/fv ci) is EXPERIMENTAL in v0.1 and runs only when opted in
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
LL=$(dirname "$FV")
WS=${FV_PACKAGES:-$LL/verify/challenge}
TC=${TC433:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
T=${EVAL_THREADS:-8}
W=${1:-/tmp/interfaces-test-$$}
rm -rf "$W"; mkdir -p "$W"
BAD=0
ok() { echo "PASS $*"; }
no() { echo "FAIL $*"; BAD=1; }
skip() { echo "SKIP $*"; }   # neither PASS nor FAIL
# rows that need inputs or tools outside the repository: the trusted packages workspace (triage probes) and cargo or a
# prebuilt binary (the expaudit deep audit, the expdiff export diff)
HAVE_WS=0; [ -d "$WS/.lake/packages" ] && HAVE_WS=1
HAVE_CARGO=0; command -v cargo > /dev/null 2>&1 && HAVE_CARGO=1
HAVE_EXPAUDIT=$HAVE_CARGO; { [ -x "$FV/tools/audit/bin/expaudit" ] || [ -x "${EXPAUDIT_BIN:-}" ]; } && HAVE_EXPAUDIT=1
HAVE_EXPDIFF=$HAVE_CARGO; [ -x "${EXPDIFF_BIN:-}" ] && HAVE_EXPDIFF=1
export IFACE_HAVE_WS=$HAVE_WS IFACE_HAVE_EXPAUDIT=$HAVE_EXPAUDIT IFACE_HAVE_EXPDIFF=$HAVE_EXPDIFF

# --------------------------------------------------------------------------- 1. Schema, LSP, SARIF unit checks
python3 -I - "$FV" <<'PY' && ok "schema v1 invariants + LSP 3.17 + SARIF 2.1.0" || no "schema v1 tests"
import json, os, sys
fv = sys.argv[1]
sys.path.insert(0, os.path.join(fv, "schemas"))
import fv_schema

# Validate JSON schema file parses cleanly
schema = json.load(open(os.path.join(fv, "schemas", "result-v1.schema.json")))
assert schema["$schema"].startswith("https://json-schema.org/draft/2020-12")

# Test reward invariants across EVERY verdict
for v, exp_acc, exp_rew, exp_rc in [
    ("ACCEPTED", True, 1.0, 0),
    ("REJECTED", False, 0.0, 1),
    ("CONDITIONAL", False, 0.0, 3),
    ("ACCEPTED_MODULO_FRONTIER", False, 0.0, 3),
    ("DECLINED", False, 0.0, 2),
    ("NO-VERDICT", False, 0.0, 2),
    ("ERROR", False, 0.0, 2),
    ("PENDING", False, 0.0, 2),
]:
    env = fv_schema.make_envelope("project", v, "sound", "basis", 1.23, reason="test reason")
    assert env["accepted"] is exp_acc, (v, env["accepted"])
    assert env["reward"] == exp_rew, (v, env["reward"])
    assert env["exit_code"] == exp_rc, (v, env["exit_code"])
    errs = fv_schema.validate_v1(env)
    assert not errs, (v, errs)

# Test Lean diagnostic parser + LSP + SARIF
sample = (
    "/proj/Foo.lean:12:4: error: unknown identifier 'bar'\n"
    "  additional context line\n"
    "/proj/Foo.lean:20:2: warning: declaration uses 'sorry'\n"
)
diags = fv_schema.parse_lean_diagnostics(sample, strip_prefix="/proj")
assert len(diags) == 2
# Lean prints a 0-based column (12:4 = the 5th character); the schema's column is 1-based
assert diags[0]["file"] == "Foo.lean" and diags[0]["line"] == 12 and diags[0]["column"] == 5
assert "additional context line" in diags[0]["message"]
assert diags[1]["severity"] == "warning"

env_rej = fv_schema.make_envelope("attempt", "REJECTED", "sound", "rejected", 0.5, diagnostics=diags)
lsp = fv_schema.to_lsp_diagnostics(env_rej)
assert "Foo.lean" in lsp["files"] and lsp["files"]["Foo.lean"][0]["range"]["start"] == {"line": 11, "character": 4}
sarif = fv_schema.to_sarif_210(env_rej)
assert sarif["version"] == "2.1.0" and len(sarif["runs"][0]["results"]) == 2
assert sarif["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["region"]["startLine"] == 12

# Verify from_incr_summary extracts nested attempt["check"]["reason"] -> FV002 / FV003
inc_drift = fv_schema.from_incr_summary({
    "verdict": "REJECTED", "total_s": 13.1,
    "attempts": [{"dirty": 1, "check": {"verdict": "REJECTED", "reason": "error: Challenge and solution theorem statement do not match: 'powerfree_neg'"}}],
})
assert inc_drift["diagnostics"][0]["rule_id"] == "FV002", inc_drift
inc_sorry = fv_schema.from_incr_summary({
    "verdict": "REJECTED", "total_s": 13.5,
    "attempts": [{"dirty": 1, "check": {"verdict": "REJECTED", "reason": "error: Illegal axiom detected: 'sorryAx'"}}],
})
assert inc_sorry["diagnostics"][0]["rule_id"] == "FV003", inc_sorry

# Verify sound-auto build.failed_modules -> structured diagnostics + frontier base_status -> dropped alert
fv_fail = fv_schema.from_fastverify_result({
    "verdict": "REJECTED", "exit": 1, "trust": "sound", "verdict_basis": "build failed",   # a final result carries its exit
    "build": {"option": "B3", "confirmed_by": "exact-retry", "failed_modules": [
        {"module": "Foo.Bar", "rc": 1, "error": "Bar.lean:42:10: error: unsolved goals"}
    ]},
})
assert any(d["file"] == "Bar.lean" and d["line"] == 42 and "unsolved goals" in d["message"] for d in fv_fail["diagnostics"]), fv_fail
fr_drop = fv_schema.from_check_frontier_result({
    "verdict": "CONDITIONAL", "exit": 3, "wall_s": 1.2, "reason": "ok",
    "frontier": [{"name": "lem_b"}],
    "base_status": {"still_open": ["lem_b"], "proved": ["lem_a"], "dropped": ["lem_bypassed"]},
})
assert fr_drop["frontier"]["base_status"]["dropped"] == ["lem_bypassed"], fr_drop
sys.path.insert(0, os.path.join(fv, "tools", "ci-action"))
import render_ci_report
md_drop = render_ci_report.render_markdown(fr_drop)
assert "FRONTIER LEMMA DROPPED FROM CLOSURE" in md_drop and "lem_bypassed" in md_drop, md_drop
PY

# --------------------------------------------------------------------------- 2. bin/fv doctor + static & live triage
"$FV/bin/fv" doctor --json > "$W/doctor.json"
python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); assert d["ok"] is True and d["checks"]["bwrap"]["ok"] is True' "$W/doctor.json" \
  && ok "fv doctor JSON ok" || no "fv doctor failed"

# Triage corpus (Init-only so probes finish in < 1s each without Mathlib load)
mkdir -p "$W/triage_repo"
cat > "$W/triage_repo/Existing.lean" <<'EOF'
theorem existing_comm : ∀ a b : Nat, a + b = b + a := by omega
EOF
cat > "$W/t_good.lean" <<'EOF'
theorem good_add (n : Nat) : n + 0 = n := by sorry
EOF
cat > "$W/t_false_natsub.lean" <<'EOF'
theorem bad_natsub (n : Nat) : n - 5 + 5 = n := by sorry
EOF
cat > "$W/t_vacuous.lean" <<'EOF'
theorem vacuous_thm (n : Nat) (h1 : n < 3) (h2 : n > 5) : n = 999 := by sorry
EOF
cat > "$W/t_autoimp.lean" <<'EOF'
theorem typo_thm : ∀ n : Nat, n = m := by sorry
EOF
cat > "$W/t_dup.lean" <<'EOF'
theorem dup_comm : ∀ a b : Nat, a + b = b + a := by sorry
EOF

if [ $HAVE_WS = 1 ]; then
"$FV/bin/fv" triage --experimental "$W/t_good.lean" --toolchain "$TC" --packages "$WS" --json > "$W/tr_good.json"
"$FV/bin/fv" triage --experimental "$W/t_false_natsub.lean" --toolchain "$TC" --packages "$WS" --json > "$W/tr_false.json" || true
"$FV/bin/fv" triage --experimental "$W/t_vacuous.lean" --toolchain "$TC" --packages "$WS" --json > "$W/tr_vac.json" || true
"$FV/bin/fv" triage --experimental "$W/t_autoimp.lean" --toolchain "$TC" --packages "$WS" --json > "$W/tr_auto.json" || true
"$FV/bin/fv" triage --experimental "$W/t_dup.lean" --repo "$W/triage_repo" --static-only --json > "$W/tr_dup.json" || true

python3 -I - "$W" <<'PY' && ok "triage: good=OK, false_natsub=REFUTED, vacuous=VACUOUS, typo=ELAB_ERROR, dup detected" || no "triage probe checks"
import json, os, sys
w = sys.argv[1]
g = json.load(open(os.path.join(w, "tr_good.json")))
f = json.load(open(os.path.join(w, "tr_false.json")))
v = json.load(open(os.path.join(w, "tr_vac.json")))
a = json.load(open(os.path.join(w, "tr_auto.json")))
d = json.load(open(os.path.join(w, "tr_dup.json")))
assert g["status"] == "OK" and g["dispatch_recommended"] is True, g
assert f["status"] == "REFUTED" and f["dispatch_recommended"] is False and f["probe"]["refuted"] is True, f
assert any(x["kind"] == "hazard_nat_sub" for x in f["findings"]), f
assert v["status"] == "VACUOUS" and v["dispatch_recommended"] is False and v["probe"]["vacuous_premises"] is True, v
assert a["status"] == "ELAB_ERROR" and a["dispatch_recommended"] is False, a
assert len(d["duplicates"]) == 1 and d["duplicates"][0]["name"] == "existing_comm", d
PY
else skip "triage probe checks: no trusted packages workspace at $WS (set FV_PACKAGES)"; fi

# --------------------------------------------------------------------------- 3. Tiny Init-only project: init-challenge, mint, verify, check, watch, ci-action
mkdir -p "$W/proj_chal" "$W/proj_good" "$W/proj_drift" "$W/proj_sorry" "$W/proj_bp" "$W/proj_ax"
for d in proj_chal proj_good proj_drift proj_sorry proj_bp proj_ax; do
  printf 'leanprover/lean4:v4.33.1\n' > "$W/$d/lean-toolchain"
  cat > "$W/$d/lakefile.toml" <<'EOF'
name = "Mini"
defaultTargets = ["Mini"]
[[lean_lib]]
name = "Mini"
EOF
  printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$W/$d/lake-manifest.json"
done

cat > "$W/proj_chal/Mini.lean" <<'EOF'
theorem mini_add : ∀ a b : Nat, a + b = b + a := by sorry
theorem mini_mul : ∀ a : Nat, a * 1 = a := by sorry
EOF
cat > "$W/proj_chal/comparator.json" <<'EOF'
{
  "challenge_module": "Mini",
  "solution_module": "Mini",
  "theorem_names": ["mini_add", "mini_mul"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF

cat > "$W/proj_good/Mini.lean" <<'EOF'
theorem mini_add : ∀ a b : Nat, a + b = b + a := by intro a b; exact Nat.add_comm a b
theorem mini_mul : ∀ a : Nat, a * 1 = a := by intro a; exact Nat.mul_one a
EOF
cat > "$W/proj_drift/Mini.lean" <<'EOF'
theorem mini_add : ∀ a : Nat, a + 0 = a := by intro a; exact Nat.add_zero a
theorem mini_mul : ∀ a : Nat, a * 1 = a := by intro a; exact Nat.mul_one a
EOF
cat > "$W/proj_sorry/Mini.lean" <<'EOF'
theorem mini_add : ∀ a b : Nat, a + b = b + a := by sorry
theorem mini_mul : ∀ a : Nat, a * 1 = a := by intro a; exact Nat.mul_one a
EOF
cat > "$W/proj_bp/Mini.lean" <<'EOF'
theorem helper_comm : ∀ a b : Nat, a + b = b + a := by sorry
theorem mini_add : ∀ a b : Nat, a + b = b + a := fun a b => helper_comm a b
theorem mini_mul : ∀ a : Nat, a * 1 = a := by intro a; exact Nat.mul_one a
EOF
cat > "$W/proj_ax/Mini.lean" <<'EOF'
axiom known_comm : ∀ a b : Nat, a + b = b + a
theorem mini_add : ∀ a b : Nat, a + b = b + a := fun a b => known_comm a b
theorem mini_mul : ∀ a : Nat, a * 1 = a := by intro a; exact Nat.mul_one a
EOF
printf 'known_comm\n' > "$W/proj_axioms.txt"
printf 'sorryAx\n' > "$W/bad_axioms.txt"

# 3a. fv init-challenge
"$FV/bin/fv" init-challenge "$W/proj_chal" "$W/pinned_chal" --threads "$T" --json > "$W/init.json"
PIN=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); assert d["ok"]; print(d["challenge_sha256"])' "$W/init.json") \
  && CFG_PIN=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); assert len(d["comparator_sha256"])==64; print(d["comparator_sha256"])' "$W/init.json") \
  && ok "fv init-challenge pinned sha256=${PIN:0:12}... cfg=${CFG_PIN:0:12}..." || no "fv init-challenge failed"

# 3b. fv audit (static JSON + human deep_audit + --probe on clean AND vacuous challenges)
"$FV/bin/fv" audit "$W/pinned_chal" --challenge-sha256 "$PIN" --json > "$W/audit.json"
"$FV/bin/fv" audit "$W/pinned_chal" --challenge-sha256 "$PIN" > "$W/audit.human.txt"
"$FV/bin/fv" audit "$W/pinned_chal" --challenge-sha256 "$PIN" --probe --json > "$W/audit_probe_clean.json"
mkdir -p "$W/vac_chal"
printf 'leanprover/lean4:v4.33.1\n' > "$W/vac_chal/lean-toolchain"
cat > "$W/vac_chal/lakefile.toml" <<'EOF'
name = "Vac"
defaultTargets = ["Vac"]
[[lean_lib]]
name = "Vac"
EOF
printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$W/vac_chal/lake-manifest.json"
cat > "$W/vac_chal/Vac.lean" <<'EOF'
theorem vac_impossible (n : Nat) (h1 : n < 2) (h2 : n > 5) : n = 99 := by sorry
EOF
cat > "$W/vac_chal/comparator.json" <<'EOF'
{"challenge_module":"Vac","solution_module":"Vac","theorem_names":["vac_impossible"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}
EOF
"$FV/bin/fv" audit "$W/vac_chal" --probe --json > "$W/audit_probe_vac.json" || true
if [ $HAVE_EXPAUDIT = 1 ]; then
python3 -I - "$W" <<'PY' && ok "fv audit (static, human deep_audit=CLEAN, --probe clean=OK vs vacuous=CRITICAL)" || no "fv audit failed"
import json, os, sys
w = sys.argv[1]
d = json.load(open(os.path.join(w, "audit.json")))
assert d["ok"] and d["challenge_export"]["pin_matches"], d
hum = open(os.path.join(w, "audit.human.txt")).read()
assert "deep_audit=CLEAN" in hum, hum
pc = json.load(open(os.path.join(w, "audit_probe_clean.json")))
assert pc["ok"] is True and (pc.get("deep_audit") or {}).get("status") == "CLEAN", pc
pv = json.load(open(os.path.join(w, "audit_probe_vac.json")))
assert pv["ok"] is False and (pv.get("deep_audit") or {}).get("status") == "CRITICAL", pv
PY
else skip "fv audit: the deep audit needs cargo (or a prebuilt tools/audit/bin/expaudit / EXPAUDIT_BIN)"; fi

# 3c. fv mint (sub-challenge minting from blueprint sorry lemma)
"$FV/bin/fv" mint "$W/proj_bp" --out "$W/minted" --module Mini --for-fvserve --threads "$T" --json > "$W/mint.json"
python3 -I -c 'import json,os,sys; d=json.load(open(sys.argv[1])); assert d["ok"] and d["count"]==1 and d["subchallenges"][0]["theorem"]=="helper_comm" and os.path.isfile(os.path.join(d["subchallenges"][0]["dir"],"challenge.export"))' "$W/mint.json" \
  && ok "fv mint minted pinned sub-challenge for helper_comm" || no "fv mint failed"

# 3d. fv verify default --preset sound-auto + --comparator-sha256 + fv check --low-mem + fv diff (expdiff)
"$FV/bin/fv" verify "$W/proj_good" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --export-dir none --out "$W/out_good" --threads "$T" --json --json-out "$W/ver_good.json" --sarif "$W/ver_good.sarif" --lsp-out "$W/ver_good.lsp.json" > /dev/null
rc=$?
"$FV/bin/fv" verify "$W/proj_good" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" \
  --comparator-sha256 "0000000000000000000000000000000000000000000000000000000000000000" \
  --threads "$T" --json > "$W/ver_badcfg.json"
rc_bc=$?
python3 -I - "$FV" "$W/ver_good.json" "$W/ver_good.sarif" "$W/ver_badcfg.json" "$rc_bc" <<'PY' && [ "$rc" = 0 ] && ok "fv verify default sound-auto ACCEPTED + comparator-sha256 pin + valid v1 JSON + SARIF" || no "fv verify good rc=$rc"
import json, os, sys
sys.path.insert(0, os.path.join(sys.argv[1], "schemas"))
import fv_schema
env = json.load(open(sys.argv[2]))
assert not fv_schema.validate_v1(env)
assert env["verdict"] == "ACCEPTED" and env["accepted"] is True and env["reward"] == 1.0
sarif = json.load(open(sys.argv[3]))
assert sarif["version"] == "2.1.0" and sarif["runs"][0]["invocations"][0]["properties"]["accepted"] is True
bc = json.load(open(sys.argv[4]))
assert int(sys.argv[5]) == 2 and bc["verdict"] == "ERROR" and bc["accepted"] is False and bc["reward"] == 0.0, bc
PY

# Export drifted project for fv diff (expdiff) test
"$FV/bin/fv" verify "$W/proj_drift" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --export-dir none --out "$W/out_drift" --threads "$T" --json > "$W/ver_drift.json" || true
"$FV/bin/fv" diff "$W/out_good/solution.export" "$W/out_good/solution.export" --targets mini_add,mini_mul --json > "$W/diff_clean.json"
"$FV/bin/fv" diff "$W/out_good/solution.export" "$W/out_drift/solution.export" --targets mini_add,mini_mul --explain 5 --json > "$W/diff_drift.json"
if [ $HAVE_EXPDIFF = 1 ]; then
python3 -I - "$W/diff_clean.json" "$W/diff_drift.json" <<'PY' && ok "fv diff (P05 expdiff): identical=CLEAN vs drifted=STATEMENT-CHANGED + explain" || no "fv diff failed"
import json, sys
c = json.load(open(sys.argv[1]))
d = json.load(open(sys.argv[2]))
assert c["ok"] is True and c["analysis_only"] is True and c["verdict"] is None and c["statement_changed_count"] == 0, c
assert d["ok"] is True and d["analysis_only"] is True and d["verdict"] is None and d["statement_changed_count"] >= 1, d
assert "mini_add" in d["statement_changed"] and len(d["explanations"]) >= 1, d
PY
else skip "fv diff: expdiff needs cargo (or EXPDIFF_BIN)"; fi

"$FV/bin/fv" check "$W/out_good/solution.export" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --low-mem --threads "$T" --json > "$W/chk_lowmem.json"
rc_lm=$?
python3 -I - "$W/chk_lowmem.json" "$rc_lm" <<'PY' && ok "fv check --low-mem (sequential low-memory check) -> ACCEPTED" || no "fv check --low-mem failed rc=$rc_lm"
import json, sys
env = json.load(open(sys.argv[1]))
assert int(sys.argv[2]) == 0 and env["verdict"] == "ACCEPTED" and env["accepted"] is True and env["reward"] == 1.0, env
PY

# 3e. fv verify --modulo-frontier auto (frontier integration) + fv verify --guard wall=1 (guard fail-closed)
"$FV/bin/fv" verify "$W/proj_bp" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --build B0 --modulo-frontier auto --threads "$T" --json --json-out "$W/ver_fr.json" > /dev/null
rc_fr=$?
python3 -I - "$FV" "$W/ver_fr.json" "$rc_fr" <<'PY' && ok "fv verify --modulo-frontier auto -> CONDITIONAL exit 3, reward=0.0" || no "fv verify --modulo-frontier failed rc=$rc_fr"
import json, os, sys
sys.path.insert(0, os.path.join(sys.argv[1], "schemas"))
import fv_schema
env = json.load(open(sys.argv[2]))
rc = int(sys.argv[3])
assert rc == 3, rc
assert not fv_schema.validate_v1(env), fv_schema.validate_v1(env)
assert env["verdict"] == "CONDITIONAL" and env["accepted"] is False and env["reward"] == 0.0
assert "helper_comm" in ((env.get("frontier") or {}).get("remaining") or []), env
PY

"$FV/bin/fv" verify "$W/proj_good" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --build B0 --guard wall=1 --threads "$T" --json > "$W/ver_guard.json"
rc_g=$?
python3 -I - "$W/ver_guard.json" "$rc_g" <<'PY' && ok "fv verify --guard wall=1 -> fail-closed NO-VERDICT exit 2, reward=0.0" || no "fv verify --guard failed rc=$rc_g"
import json, sys
env = json.load(open(sys.argv[1]))
assert int(sys.argv[2]) == 2 and env["verdict"] == "NO-VERDICT" and env["accepted"] is False and env["reward"] == 0.0, env
PY

# 3e2. Declared project axioms via check-frontier.sh --axioms through fv check & fv-ci.sh
"$FV/bin/fv" verify "$W/proj_ax" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --build B0 --export-dir none --out "$W/out_ax" --threads "$T" --json > "$W/ver_ax.json" || true
"$FV/bin/fv" check "$W/out_ax/solution.export" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --frontier --threads "$T" --json > "$W/chk_ax_noallow.json"
rc_ax0=$?
"$FV/bin/fv" check "$W/out_ax/solution.export" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --frontier --frontier-axioms "$W/proj_axioms.txt" --threads "$T" --json > "$W/chk_ax_allow.json"
rc_ax1=$?
"$FV/bin/fv" check "$W/out_ax/solution.export" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --frontier --frontier-axioms "$W/bad_axioms.txt" --threads "$T" --json > "$W/chk_ax_bad.json"
rc_ax2=$?
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_ax" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --out-dir "$W/ci_ax" --build B0 --export-dir none --frontier --frontier-axioms "$W/proj_axioms.txt" --threads "$T" --commit "ax111111" > "$W/ci_ax.out"
rc_axci=$?
python3 -I - "$W" "$rc_ax0" "$rc_ax1" "$rc_ax2" "$rc_axci" <<'PY' && ok "fv check + fv-ci.sh --frontier-axioms: undeclared REJECTED, declared CONDITIONAL, sorryAx refused" || no "frontier-axioms failed ($rc_ax0,$rc_ax1,$rc_ax2,$rc_axci)"
import json, os, sys
w, r0, r1, r2, rci = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
d0 = json.load(open(os.path.join(w, "chk_ax_noallow.json")))
d1 = json.load(open(os.path.join(w, "chk_ax_allow.json")))
d2 = json.load(open(os.path.join(w, "chk_ax_bad.json")))
dci = json.load(open(os.path.join(w, "ci_ax", "result-v1.json")))
assert r0 == 1 and d0["verdict"] == "REJECTED" and d0["reward"] == 0.0, (r0, d0)
assert r1 == 3 and d1["verdict"] == "CONDITIONAL" and d1["accepted"] is False and d1["reward"] == 0.0, (r1, d1)
assert "known_comm" in ((d1.get("frontier") or {}).get("remaining") or []), d1
assert r2 in (1, 2) and d2["verdict"] in ("REJECTED", "DECLINED", "ERROR") and d2["reward"] == 0.0, (r2, d2)
assert rci == 3 and dci["verdict"] == "CONDITIONAL" and dci["accepted"] is False and dci["reward"] == 0.0, (rci, dci)
assert "known_comm" in ((dci.get("frontier") or {}).get("remaining") or []), dci
PY

# 3f. fv watch --once
"$FV/bin/fv" watch --experimental "$W/proj_good" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --build B0 --threads "$T" --once --json-out "$W/watch.json" --sarif "$W/watch.sarif" --lsp-out "$W/watch.lsp.json" > "$W/watch.log" 2>&1
rc=$?
[ "$rc" = 0 ] && grep -q 'verdict=ACCEPTED' "$W/watch.log" && [ -f "$W/watch.lsp.json" ] && ok "fv watch --once ACCEPTED + LSP + SARIF" || no "fv watch failed rc=$rc"

# 3g. CI Action runner: cold ACCEPTED (with --comparator-sha256) -> drift REJECTED (FV002) -> sorry REJECTED (FV003) -> lifecycle --frontier CONDITIONAL -> --wall 1 fvguard NO-VERDICT
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_good" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --cache-dir "$W/ci_cache" --out-dir "$W/ci_1" --build B0 --threads "$T" --commit "aaaa1111" > "$W/ci_1.out"
rc1=$?
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_drift" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --cache-dir "$W/ci_cache" --out-dir "$W/ci_2" --build B0 --threads "$T" --commit "bbbb2222" > "$W/ci_2.out"
rc2=$?
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_sorry" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --cache-dir "$W/ci_cache" --out-dir "$W/ci_3" --build B0 --threads "$T" --commit "cccc3333" > "$W/ci_3.out"
rc3=$?
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_bp" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --cache-dir "$W/ci_fr_cache" --out-dir "$W/ci_4" --build B0 --export-dir none --frontier --threads "$T" --commit "dddd4444" > "$W/ci_4.out"
rc4=$?
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_bp" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --cache-dir "$W/ci_fr_cache" --out-dir "$W/ci_5" --build B0 --export-dir none --frontier --threads "$T" --commit "eeee5555" > "$W/ci_5.out"
rc5=$?
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_good" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --out-dir "$W/ci_6" --build B0 --wall 1 --threads "$T" --commit "ffff6666" > "$W/ci_6.out"
rc6=$?
python3 -I - "$W" "$rc1" "$rc2" "$rc3" "$rc4" "$rc5" "$rc6" <<'PY' && ok "ci-action cold ACCEPTED, drift PR FV002, sorry PR FV003, --frontier CONDITIONAL + base Ledger, --wall 1 NO-VERDICT" || no "ci-action failed ($rc1,$rc2,$rc3,$rc4,$rc5,$rc6)"
import json, os, sys
w, rc1, rc2, rc3, rc4, rc5, rc6 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
assert rc1 == 0 and rc2 == 1 and rc3 == 1 and rc4 == 3 and rc5 == 3 and rc6 == 2, (rc1, rc2, rc3, rc4, rc5, rc6)
r1 = json.load(open(os.path.join(w, "ci_1", "result-v1.json")))
r2 = json.load(open(os.path.join(w, "ci_2", "result-v1.json")))
r3 = json.load(open(os.path.join(w, "ci_3", "result-v1.json")))
r4 = json.load(open(os.path.join(w, "ci_4", "result-v1.json")))
r5 = json.load(open(os.path.join(w, "ci_5", "result-v1.json")))
r6 = json.load(open(os.path.join(w, "ci_6", "result-v1.json")))
assert r1["accepted"] is True and r1["reward"] == 1.0
assert r2["verdict"] == "REJECTED" and r2["reward"] == 0.0
assert r3["verdict"] == "REJECTED" and r3["reward"] == 0.0
assert r4["verdict"] == "CONDITIONAL" and r4["accepted"] is False and r4["reward"] == 0.0
assert r5["verdict"] == "CONDITIONAL" and r5["accepted"] is False and r5["reward"] == 0.0
assert r6["verdict"] == "NO-VERDICT" and r6["accepted"] is False and r6["reward"] == 0.0
assert os.path.isfile(os.path.join(w, "ci_fr_cache", "last-frontier.json"))
assert os.path.isdir(os.path.join(w, "ci_fr_cache", "acache"))
assert "helper_comm" in ((r4.get("frontier") or {}).get("remaining") or []), r4
md2 = open(os.path.join(w, "ci_2", "summary.md")).read()
md3 = open(os.path.join(w, "ci_3", "summary.md")).read()
md4 = open(os.path.join(w, "ci_4", "summary.md")).read()
assert "STATEMENT DRIFT ALERT" in md2, md2
assert "ILLEGAL AXIOM" in md3, md3
assert "Sorry-Frontier Progress Ledger" in md4, md4
s2 = json.load(open(os.path.join(w, "ci_2", "results.sarif")))
assert s2["version"] == "2.1.0" and any(x["ruleId"] == "FV002" for x in s2["runs"][0]["results"])
PY

# --------------------------------------------------------------------------- 4. MCP Server (both newline AND Content-Length framing) + fvserve + fvapi HTTP
# Start a lightweight Init-only fvserve using the minted sub-challenge batch pset (zero Mathlib load -> fast!)
MINT_PSET="$W/minted/_all_frontier"
MINT_SHA=$(cut -d' ' -f1 "$MINT_PSET/challenge.export.sha256")
mkdir -p "$W/empty_ws/.lake/packages"
python3 -I "$FV/tools/fvserve/fvserve.py" serve \
  --state "$W/svc" --pset "mini=$MINT_PSET:$MINT_SHA" \
  --packages "$W/empty_ws" --toolchain "$TC" --fv "$FV" \
  --snapshot-header "import Init" --threads "$T" --svc-check > "$W/svc.log" 2>&1 &
SVC_PID=$!
trap 'kill ${API_PID:-} ${SVC_PID:-} 2>/dev/null || true' EXIT
for _ in $(seq 1 180); do grep -q '"ready"' "$W/svc.log" 2>/dev/null && break; sleep 0.5; done
grep -q '"ready"' "$W/svc.log" && ok "fvserve ready for MCP & HTTP tests" || { no "fvserve failed: $(tail -5 "$W/svc.log")"; exit 1; }

# Start fvapi on ephemeral port
python3 -I "$FV/tools/http/fvapi.py" --fvserve-state "$W/svc" --default-pset mini --host 127.0.0.1 --port 0 > "$W/api.log" 2>&1 &
API_PID=$!
for _ in $(seq 1 30); do grep -q '"ready"' "$W/api.log" 2>/dev/null && break; sleep 0.2; done
API_URL=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["url"])' "$W/api.log")
[ -n "$API_URL" ] && ok "fvapi ready at $API_URL" || { no "fvapi failed"; exit 1; }

# Test fvapi endpoints (/health, /metrics, /v1/verify, /verify Kimina batch, /api/check)
python3 -I - "$API_URL" "$FV" <<'PY' && ok "fvapi HTTP REST (/health, /metrics, /v1/verify, Kimina /verify & /api/check)" || no "fvapi HTTP tests"
import json, os, sys, urllib.request
url, fv = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(fv, "schemas"))
import fv_schema

def get(path):
    with urllib.request.urlopen(url + path, timeout=30) as r:
        return r.status, r.read().decode("utf-8")

def post(path, obj):
    req = urllib.request.Request(url + path, data=json.dumps(obj).encode("utf-8"),
                                 headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.status, json.loads(r.read().decode("utf-8"))

st, body = get("/health")
h = json.loads(body)
assert st == 200 and h["status"] == "ok", h
assert isinstance((h.get("backend") or {}).get("code"), dict) and (h["backend"].get("stale") == []) and (h["backend"].get("restart_recommended") is False), h

# Honest proof
good_src = "import Init\ntheorem helper_comm : ∀ a b : Nat, a + b = b + a := by intro a b; exact Nat.add_comm a b\n"
sorry_src = "import Init\ntheorem helper_comm : ∀ a b : Nat, a + b = b + a := by sorry\n"
cheat_src = "import Init\nset_option debug.skipKernelTC true in\ntheorem helper_comm : ∀ a b : Nat, a + b = b + a := by decide +kernel\n"

st, r = post("/v1/verify", {"theorem": "helper_comm", "source": good_src})
assert st == 200 and r["verdict"] == "ACCEPTED" and r["accepted"] is True and r["reward"] == 1.0
assert not fv_schema.validate_v1(r)

# Kimina batch via /api/check (mixed honest + sorry + skipKernelTC cheat, explicit theorem names)
st, b = post("/api/check", {
    "pset": "mini",
    "codes": [
        {"custom_id": "ok1", "theorem": "helper_comm", "proof": good_src},
        {"custom_id": "sorry1", "theorem": "helper_comm", "proof": sorry_src},
        {"custom_id": "cheat1", "theorem": "helper_comm", "proof": cheat_src},
    ],
})
assert st == 200 and b["count"] == 3 and b["accepted_count"] == 1
by_id = {x["custom_id"]: x for x in b["results"]}
assert by_id["ok1"]["is_pass"] is True and by_id["ok1"]["reward"] == 1.0 and by_id["ok1"]["theorem"] == "helper_comm"
assert by_id["sorry1"]["is_pass"] is False and by_id["sorry1"]["reward"] == 0.0 and by_id["sorry1"]["theorem"] == "helper_comm"
assert by_id["cheat1"]["is_pass"] is False and by_id["cheat1"]["reward"] == 0.0 and by_id["cheat1"]["theorem"] == "helper_comm"

st, m = get("/metrics")
assert st == 200 and "fvapi_verdicts_total" in m and "fvapi_backend_stale_files 0" in m, m
PY

# Test fastverify-mcp in BOTH newline framing (MCP protocol revision 2025-11-25) AND Content-Length framing (revision 2024-11-05)!
[ $HAVE_WS = 1 ] || skip "fastverify-mcp fv_triage_sublemma REFUTED check: no trusted packages workspace at $WS"
[ $HAVE_EXPDIFF = 1 ] || skip "fastverify-mcp fv_diff_exports check: expdiff needs cargo (or EXPDIFF_BIN)"
[ $HAVE_EXPAUDIT = 1 ] || skip "fastverify-mcp deep audit check: needs cargo (or a prebuilt expaudit)"
python3 -I - "$FV" "$W" "$PIN" <<'PY' && ok "fastverify-mcp newline & Content-Length framing + all core tools" || no "fastverify-mcp tests"
import json, os, subprocess, sys
fv, w, pin = sys.argv[1], sys.argv[2], sys.argv[3]
mcp = os.path.join(fv, "tools", "mcp", "fastverify-mcp")
base_args = [mcp, "--experimental", "--fvserve-state", os.path.join(w, "svc"), "--default-pset", "mini",   # triage tool opt-in
             "--allow-root", w, "--packages", os.path.join(w, "empty_ws")]

# 1. Newline framing (MCP protocol revision 2025-11-25)
reqs = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25", "capabilities": {}, "clientInfo": {"name": "t", "version": "1"}}},
    {"jsonrpc": "2.0", "method": "notifications/initialized"},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
    {"jsonrpc": "2.0", "id": 3, "method": "resources/list", "params": {}},
    {"jsonrpc": "2.0", "id": 4, "method": "resources/read", "params": {"uri": "fastverify://schema/result-v1"}},
    {"jsonrpc": "2.0", "id": 5, "method": "prompts/list", "params": {}},
    {"jsonrpc": "2.0", "id": 6, "method": "tools/call", "params": {"name": "fv_status", "arguments": {}}},
    {"jsonrpc": "2.0", "id": 7, "method": "tools/call", "params": {"name": "fv_verify_attempt", "arguments": {
        "theorem": "helper_comm",
        "source": "import Init\ntheorem helper_comm : ∀ a b : Nat, a + b = b + a := by intro a b; exact Nat.add_comm a b\n",
    }}},
    {"jsonrpc": "2.0", "id": 8, "method": "tools/call", "params": {"name": "fv_verify_attempt", "arguments": {
        "theorem": "helper_comm",
        "source": "import Init\ntheorem helper_comm : ∀ a b : Nat, a + b = b + a := by sorry\n",
    }}},
    {"jsonrpc": "2.0", "id": 9, "method": "tools/call", "params": {"name": "fv_triage_sublemma", "arguments": {
        "source": "theorem bad_sub (n : Nat) : n - 5 + 5 = n := by sorry\n",
    }}},
    {"jsonrpc": "2.0", "id": 10, "method": "tools/call", "params": {"name": "fv_diff_exports", "arguments": {
        "old_export": os.path.join(w, "out_good", "solution.export"),
        "new_export": os.path.join(w, "out_drift", "solution.export"),
        "targets": "mini_add,mini_mul",
        "explain": 3,
    }}},
    {"jsonrpc": "2.0", "id": 11, "method": "tools/call", "params": {"name": "fv_audit_challenge", "arguments": {
        "challenge_dir": os.path.join(w, "vac_chal"),
        "probe": True,
    }}},
    {"jsonrpc": "2.0", "id": 12, "method": "tools/call", "params": {"name": "fv_doctor", "arguments": {}}},
]
inp = "".join(json.dumps(r) + "\n" for r in reqs).encode("utf-8")
p = subprocess.run(base_args, input=inp, capture_output=True, timeout=180)
assert p.returncode == 0, p.stderr.decode()
resps = {r["id"]: r for r in (json.loads(l) for l in p.stdout.decode().splitlines() if l.strip())}
assert resps[1]["result"]["protocolVersion"] == "2025-11-25"
tool_names = {t["name"] for t in resps[2]["result"]["tools"]}
assert len(tool_names) >= 14 and "fv_lookup_duplicate" in tool_names and "fv_verify_patch" in tool_names and "fv_diff_exports" in tool_names, tool_names
assert len(resps[3]["result"]["resources"]) == 2
assert "api_version" in resps[4]["result"]["contents"][0]["text"]
assert len(resps[5]["result"]["prompts"]) == 1
fvs_st = resps[6]["result"]["structuredContent"]["backends"]["fvserve"]
assert fvs_st["reachable"] is True and isinstance(fvs_st.get("code"), dict) and fvs_st.get("stale") == [] and fvs_st.get("restart_recommended") is False, fvs_st
assert resps[7]["result"]["structuredContent"]["verdict"] == "ACCEPTED"
assert resps[7]["result"]["structuredContent"]["reward"] == 1.0
assert resps[8]["result"]["structuredContent"]["verdict"] == "REJECTED"
assert resps[8]["result"]["structuredContent"]["reward"] == 0.0
assert os.environ.get("IFACE_HAVE_WS") != "1" or resps[9]["result"]["structuredContent"]["status"] == "REFUTED"
assert os.environ.get("IFACE_HAVE_EXPDIFF") != "1" or (resps[10]["result"]["structuredContent"]["ok"] is True and resps[10]["result"]["structuredContent"]["statement_changed_count"] >= 1), resps[10]
assert os.environ.get("IFACE_HAVE_EXPAUDIT") != "1" or (resps[11]["result"]["structuredContent"]["ok"] is False and (resps[11]["result"]["structuredContent"].get("deep_audit") or {}).get("status") == "CRITICAL"), resps[11]
fvs_doc = resps[12]["result"]["structuredContent"].get("fvserve_backend") or {}
assert fvs_doc.get("reachable") is True and isinstance(fvs_doc.get("code"), dict) and fvs_doc.get("stale") == [] and fvs_doc.get("restart_recommended") is False, fvs_doc

# 2. Content-Length framing (MCP protocol revision 2024-11-05)
def frame(obj):
    b = json.dumps(obj).encode("utf-8")
    return f"Content-Length: {len(b)}\r\n\r\n".encode("ascii") + b

inp2 = frame({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2024-11-05"}}) + \
       frame({"jsonrpc": "2.0", "id": 2, "method": "ping", "params": {}})
p2 = subprocess.run(base_args, input=inp2, capture_output=True, timeout=30)
assert p2.returncode == 0 and b"Content-Length:" in p2.stdout and b"2024-11-05" in p2.stdout
PY

# 6. Notary (--notary) + Lean 4.37.0-rc1 end-to-end (fv doctor, fv init-challenge, fv verify sound-auto + E1-437, fv check --pins 437, MCP pins='437' & notary=True)
"$FV/bin/fv" check "$W/out_good/solution.export" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --notary --experimental --threads "$T" --json > "$W/chk_notary.json"   # the notary judge is EXPERIMENTAL in v0.1
rc_not=$?
python3 -I - "$W/chk_notary.json" "$rc_not" <<'PY' && ok "fv check --notary -> ACCEPTED, trust=notary" || no "fv check --notary failed rc=$rc_not"
import json, sys
env = json.load(open(sys.argv[1]))
assert int(sys.argv[2]) == 0 and env["verdict"] == "ACCEPTED" and env["accepted"] is True and env["reward"] == 1.0, env
assert env["trust"] == "notary", env
PY

if [ -f "$FV/check/sound/pins-437.env" ] && python3 -I -c 'import json,os,sys; c=json.load(open(sys.argv[1])); p=(c.get("lean_toolchains") or {}).get("leanprover/lean4:v4.37.0-rc1",{}).get("prefix",""); sys.exit(0 if p and os.path.isdir(p) else 1)' "$FV/config/components.json"; then
  mkdir -p "$W/chal437" "$W/proj437"
  echo 'leanprover/lean4:v4.37.0-rc1' > "$W/chal437/lean-toolchain"
  cat > "$W/chal437/lakefile.toml" <<'EOF'
name = "Mini437"
defaultTargets = ["Mini437"]
[[lean_lib]]
name = "Mini437"
EOF
  printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$W/chal437/lake-manifest.json"
  cat > "$W/chal437/Mini437.lean" <<'EOF'
theorem mini437_add : ∀ a b : Nat, a + b = b + a := by sorry
EOF
  cat > "$W/chal437/comparator.json" <<'EOF'
{"challenge_module":"Mini437","solution_module":"Mini437","theorem_names":["mini437_add"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}
EOF
  cp -a "$W/chal437/." "$W/proj437/"
  cat > "$W/proj437/Mini437.lean" <<'EOF'
theorem mini437_add : ∀ a b : Nat, a + b = b + a := fun a b => Nat.add_comm a b
EOF
  cp -a "$W/chal437/." "$W/proj437_bp/"
  cat > "$W/proj437_bp/Mini437.lean" <<'EOF'
theorem helper437_comm (a b : Nat) : a + b = b + a := by sorry
theorem mini437_add : ∀ a b : Nat, a + b = b + a := fun a b => helper437_comm a b
EOF
  "$FV/bin/fv" doctor --project "$W/proj437" --json > "$W/doc437.json"
  "$FV/bin/fv" init-challenge "$W/chal437" "$W/pinned437" --threads "$T" --json > "$W/init437.json"
  PIN437=$(awk '{print $1}' "$W/pinned437/challenge.export.sha256")
  CFG437=$(sha256sum "$W/pinned437/comparator.json" | awk '{print $1}')
  "$FV/bin/fv" verify "$W/proj437" --challenge "$W/pinned437" --challenge-sha256 "$PIN437" --comparator-sha256 "$CFG437" \
    --export-dir none --out "$W/out437" --threads "$T" --json > "$W/ver437.json"
  rc_v437=$?
  "$FV/bin/fv" check "$W/out437/solution.export" --challenge "$W/pinned437" --challenge-sha256 "$PIN437" \
    --comparator-sha256 "$CFG437" --pins 437 --threads "$T" --json > "$W/chk437.json"
  rc_c437=$?
  "$FV/bin/fv" check "$W/out437/solution.export" --challenge "$W/pinned437" --challenge-sha256 "$PIN437" \
    --comparator-sha256 "$CFG437" --low-mem --pins 437 --threads "$T" --json > "$W/chk437_lm.json"
  rc_clm437=$?
  "$FV/bin/fv" verify "$W/proj437_bp" --challenge "$W/pinned437" --challenge-sha256 "$PIN437" --comparator-sha256 "$CFG437" \
    --build B0 --modulo-frontier auto --pins 437 --export-dir none --out "$W/out437_bp" --threads "$T" --json > "$W/ver437_fr.json"
  rc_vfr437=$?
  "$FV/bin/fv" check "$W/out437_bp/solution.export" --challenge "$W/pinned437" --challenge-sha256 "$PIN437" \
    --comparator-sha256 "$CFG437" --frontier --pins 437 --threads "$T" --json > "$W/chk437_fr.json"
  rc_cfr437=$?
  "$FV/tools/ci-action/fv-ci.sh" --project "$W/proj437" --challenge "$W/pinned437" --challenge-sha256 "$PIN437" \
    --comparator-sha256 "$CFG437" --out-dir "$W/ci437_ok" --threads "$T" --commit "43700001" > "$W/ci437_ok.out"
  rc_ci437=$?
  "$FV/tools/ci-action/fv-ci.sh" --project "$W/proj437_bp" --challenge "$W/pinned437" --challenge-sha256 "$PIN437" \
    --comparator-sha256 "$CFG437" --frontier --pins 437 --build B0 --export-dir none --out-dir "$W/ci437_fr" --threads "$T" --commit "43700002" > "$W/ci437_fr.out"
  rc_cifr437=$?
  python3 -I - "$FV" "$W" "$PIN437" "$CFG437" "$rc_v437" "$rc_c437" "$rc_clm437" "$rc_vfr437" "$rc_cfr437" "$rc_ci437" "$rc_cifr437" <<'PY' && ok "Lean 4.37.0-rc1 E2E: fv doctor + init-challenge + E24/E25 auto-437 verify + --low-mem/--frontier --pins 437 + fv-ci.sh + MCP pins='437' (verify/check/lowmem/frontier) & notary=True" || no "Lean 4.37.0-rc1 E2E failed"
import json, os, subprocess, sys
fv, w, pin437, cfg437 = sys.argv[1:5]
rc_v, rc_c, rc_clm, rc_vfr, rc_cfr, rc_ci, rc_cifr = [int(x) for x in sys.argv[5:12]]
doc = json.load(open(os.path.join(w, "doc437.json")))
assert (doc["checks"].get("sound_pins_437") or {}).get("all_present") is True, doc["checks"]
assert any("registered & ready" in n for n in doc["recommendation"]["notes"]), doc["recommendation"]
ver = json.load(open(os.path.join(w, "ver437.json")))
assert rc_v == 0 and ver["verdict"] == "ACCEPTED" and ver["reward"] == 1.0, ver
# auto-selected pins-437.env in default --preset sound-auto!
tchk = ((ver.get("soundness") or {}).get("trusted") or {}).get("check") or {}
assert tchk.get("toolchain") == "leanprover/lean4:v4.37.0-rc1", ver.get("soundness")
chk = json.load(open(os.path.join(w, "chk437.json")))
assert rc_c == 0 and chk["verdict"] == "ACCEPTED" and chk["reward"] == 1.0, chk
assert (chk.get("soundness") or {}).get("toolchain") == "leanprover/lean4:v4.37.0-rc1", chk
chklm = json.load(open(os.path.join(w, "chk437_lm.json")))
assert rc_clm == 0 and chklm["verdict"] == "ACCEPTED" and chklm["reward"] == 1.0, chklm
assert (chklm.get("soundness") or {}).get("toolchain") == "leanprover/lean4:v4.37.0-rc1", chklm
vfr = json.load(open(os.path.join(w, "ver437_fr.json")))
assert rc_vfr == 3 and vfr["verdict"] == "CONDITIONAL" and vfr["accepted"] is False and vfr["reward"] == 0.0, vfr
assert "helper437_comm" in ((vfr.get("frontier") or {}).get("remaining") or []), vfr
cfr = json.load(open(os.path.join(w, "chk437_fr.json")))
assert rc_cfr == 3 and cfr["verdict"] == "CONDITIONAL" and cfr["accepted"] is False and cfr["reward"] == 0.0, cfr
assert "pins-437" in str((cfr.get("soundness") or {}).get("pins") or ""), cfr.get("soundness")
ci_ok = json.load(open(os.path.join(w, "ci437_ok", "result-v1.json")))
assert rc_ci == 0 and ci_ok["verdict"] == "ACCEPTED" and ci_ok["reward"] == 1.0, ci_ok
ci_fr = json.load(open(os.path.join(w, "ci437_fr", "result-v1.json")))
assert rc_cifr == 3 and ci_fr["verdict"] == "CONDITIONAL" and ci_fr["reward"] == 0.0, ci_fr
# MCP: fv_check_export(pins='437'), fv_check_export(low_mem=True, pins='437'), fv_check_export(frontier=True, pins='437'), fv_verify_project(pins='437'), fv_check_export(notary=True)
reqs = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "out437", "solution.export"),
        "challenge_id": "c437",
        "pins": "437",
    }}},
    {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "out_good", "solution.export"),
        "challenge_id": "c433",
        "notary": True,
    }}},
    {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "out437_bp", "solution.export"),
        "challenge_id": "c437",
        "frontier": True,
        "pins": "437",
    }}},
    {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
        "project_dir": os.path.join(w, "proj437"),
        "challenge_id": "c437",
        "pins": "437",
        "build_option": "B0",
    }}},
    {"jsonrpc": "2.0", "id": 6, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "out437", "solution.export"),
        "challenge_id": "c437",
        "low_mem": True,
        "pins": "437",
    }}},
]
p = subprocess.run(
    [os.path.join(fv, "tools", "mcp", "fastverify-mcp"), "--experimental", "--allow-root", w,   # notary=True needs the opt-in
     "--challenge", f"c437={os.path.join(w, 'pinned437')}:{pin437}:{cfg437}",
     "--challenge", f"c433={os.path.join(w, 'pinned_chal')}"],
    input="".join(json.dumps(r) + "\n" for r in reqs).encode(),
    capture_output=True, timeout=180,
)
assert p.returncode == 0, p.stderr.decode()
resps = {r["id"]: r["result"]["structuredContent"] for r in (json.loads(l) for l in p.stdout.decode().splitlines() if l.strip()) if r.get("id") in (2, 3, 4, 5, 6)}
assert resps[2]["verdict"] == "ACCEPTED" and (resps[2].get("soundness") or {}).get("toolchain") == "leanprover/lean4:v4.37.0-rc1", resps[2]
assert resps[3]["verdict"] == "ACCEPTED" and resps[3]["trust"] == "notary", resps[3]
assert resps[4]["verdict"] == "CONDITIONAL" and resps[4]["reward"] == 0.0 and "helper437_comm" in ((resps[4].get("frontier") or {}).get("remaining") or []), resps[4]
assert resps[5]["verdict"] == "ACCEPTED" and (((resps[5].get("soundness") or {}).get("trusted") or {}).get("check") or {}).get("toolchain") == "leanprover/lean4:v4.37.0-rc1", resps[5]
assert resps[6]["verdict"] == "ACCEPTED" and (resps[6].get("soundness") or {}).get("toolchain") == "leanprover/lean4:v4.37.0-rc1", resps[6]
PY
else
  ok "Lean 4.37.0-rc1 E2E skipped (pins-437.env or 4.37 toolchain absent on this node)"
fi

# Clean stop
python3 -I "$FV/tools/fvserve/fvserve.py" stop --state "$W/svc" > /dev/null 2>&1 || true
kill ${API_PID:-} ${SVC_PID:-} 2>/dev/null || true
wait ${API_PID:-} ${SVC_PID:-} 2>/dev/null || true
[ "$BAD" = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit "$BAD"
