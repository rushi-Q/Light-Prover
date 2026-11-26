#!/bin/bash
# tests/unsafe-accept/run.sh [WORKDIR] -- regression test: UNSAFE results are never counted as accepted (HIGH,
# schemas/fv_schema.py + bin/fv (tools/cli/fv_cli.py) + tools/ci-action/{fv-ci.sh,render_ci_report.py}): the verdict
# envelope set accepted=true / reward=1.0 / exit 0 for ACCEPTED regardless of trust (UNSAFE counted), `bin/fv verify
# --preset sound` forwarded --extra-arg=--check C4 --unsafe ignore-order (single unofficial kernel, result still labelled
# preset sound) and fv-ci.sh ran --preset fastest and printed 'PASS — SOUND ACCEPTED', on a Lean 4.37.0-rc1 challenge with
# a non-sorried definition hole that the official 4.37 comparator REJECTS. Reproduction
# inputs in data/ (SHA256SUMS).
# Rows:
#   schema/*: accepted / reward / exit_code only for trust sound, sound-conditional, notary (UNSAFE, exact-by-design,
#     official, conditional, none: accepted=false reward=0.0 exit 2); validate_v1 rejects a forged accepted UNSAFE envelope;
#     the trust of a bin/fastverify result comes from what ran (mode.sound / CN), never from the preset name
#   render/*: render_ci_report never prints PASS for a non-sound trust, exits 2, GITHUB_OUTPUT accepted=false (every input kind)
#   cli/*: bin/fv verify forwards only ALLOW-listed --extra-arg options (no --preset/--check/abbreviations, no
#     --comparator-config/--challenge-sha256/--from-export/--pins/--unsafe) and refuses a non-sound --preset without
#     --allow-unsound-presets (exit 2, no run); fv-ci.sh refuses --preset fastest / reference
#   e2e/evidence-*: the evidence commands (exit != 0, accepted false, no PASS); e2e/allow-unsound: --preset fastest with
#     --allow-unsound-presets runs but its ACCEPTED is accepted=false / exit 2; e2e/control-sound: the sound preset with the
#     4.37 pins REJECTS the non-sorried hole (exit 1) like the official 4.37 comparator. The e2e rows need the 4.37.0-rc1
#     toolchain + pins-437 (else SKIP); every build runs in bin/fastverify's sandbox.
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy (the test data stays here).
set -u
export FV_EXPERIMENTAL_CI=1   # the CI gate (fv-ci.sh / bin/fv ci) is EXPERIMENTAL in v0.1 and runs only when opted in
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/unsafe-accept.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
(cd "$HERE/data" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
cp -a "$HERE/data/chal437" "$HERE/data/proj437" "$HERE/data/sol437.export" "$W/"; chmod -R u+w "$W"
CSHA=$(sha256sum "$W/chal437/challenge.export" | cut -d' ' -f1)
CFGSHA=$(sha256sum "$W/chal437/comparator.json" | cut -d' ' -f1)   # the comparator pin
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }

# ---------------- schema + render (unit) ----------------
python3 -I -B - "$FV" "$W" <<'PY' > "$W/unit.out" 2>&1
import json, os, subprocess, sys
sys.dont_write_bytecode = True
fv, w = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(fv, "schemas"))
import fv_schema as S
def row(ok, n, m):
    print(("PASS " if ok else "FAIL ") + n + ": " + m)
for t in ("UNSAFE", "exact-by-design (unofficial)", "official", "conditional", "none"):
    e = S.make_envelope("project", "ACCEPTED", t, "basis", 1.0)
    row(e["accepted"] is False and e["reward"] == 0.0 and e["exit_code"] == 2, "schema/not-counted-" + t.split()[0],
        "ACCEPTED trust %r -> accepted %s reward %s exit %s" % (t, e["accepted"], e["reward"], e["exit_code"]))
for t in ("sound", "sound-conditional", "notary"):
    e = S.make_envelope("project", "ACCEPTED", t, "basis", 1.0)
    row(e["accepted"] is True and e["reward"] == 1.0 and e["exit_code"] == 0 and not S.validate_v1(e), "schema/counted-" + t,
        "ACCEPTED trust %r -> accepted %s reward %s exit %s" % (t, e["accepted"], e["reward"], e["exit_code"]))
forged = S.make_envelope("project", "ACCEPTED", "sound", "b", 1.0); forged["trust"] = "UNSAFE"
errs = S.validate_v1(forged)
row(any("accepted invariant" in x for x in errs), "schema/validate-rejects-forged", "validate_v1 errors %s" % errs[:2])
res = {"verdict": "ACCEPTED", "trust": "UNSAFE", "mode": {"preset": "sound", "check": ["C4"], "sound": False}}
e = S.from_fastverify_result(res, total_s=1.0, include_raw=False)
row(e["accepted"] is False and e["exit_code"] == 2, "schema/fastverify-unsafe", "trust %s accepted %s exit %s" % (e["trust"], e["accepted"], e["exit_code"]))
res = {"verdict": "ACCEPTED", "mode": {"preset": "sound", "check": ["C4"], "sound": False}}   # no trust field
e = S.from_fastverify_result(res, total_s=1.0, include_raw=False)
row(e["accepted"] is False and e["trust"] != "sound", "schema/trust-not-from-preset-name", "trust %s accepted %s" % (e["trust"], e["accepted"]))
res = {"verdict": "ACCEPTED", "trust": "sound", "mode": {"preset": "sound", "check": ["C4"], "sound": False}}   # mislabelled
e = S.from_fastverify_result(res, total_s=1.0, include_raw=False)
row(e["accepted"] is False, "schema/sound-label-without-sound-run", "trust %s accepted %s" % (e["trust"], e["accepted"]))
# a FINAL bin/fastverify result carries its integer exit (a verdict without an exit consistent
# with it is not final): the fixture is a final sound run
res = {"verdict": "ACCEPTED", "exit": 0, "trust": "sound", "mode": {"preset": "sound", "check": ["CS"], "sound": True}}
e = S.from_fastverify_result(res, total_s=1.0, include_raw=False)
row(e["accepted"] is True and e["exit_code"] == 0, "schema/sound-run-counted", "trust %s accepted %s" % (e["trust"], e["accepted"]))
# render_ci_report
rr = os.path.join(fv, "tools", "ci-action", "render_ci_report.py")
for kind, obj in (("fastverify", {"verdict": "ACCEPTED", "trust": "UNSAFE", "mode": {"preset": "fastest", "check": ["C4"], "sound": False}}),
                  ("v1", dict(S.make_envelope("project", "ACCEPTED", "sound", "b", 1.0), trust="UNSAFE"))):
    d = os.path.join(w, "render-" + kind); os.makedirs(d)
    inp = os.path.join(d, "in.json"); json.dump(obj, open(inp, "w"))
    gh = os.path.join(d, "gh.txt")
    p = subprocess.run(["python3", "-I", "-B", rr, "--input-kind", kind, "--input", inp, "--out-json", d + "/o.json",
                        "--out-sarif", d + "/o.sarif", "--out-md", d + "/o.md"], env={"PATH": "/usr/bin:/bin", "GITHUB_OUTPUT": gh},
                       capture_output=True, text=True)
    md = open(d + "/o.md").read() if os.path.isfile(d + "/o.md") else ""
    ghs = open(gh).read() if os.path.isfile(gh) else ""
    row(p.returncode == 2 and "PASS" not in md.splitlines()[0] if md else False, "render/%s-unsafe-not-pass" % kind,
        "exit %d, badge %r, gh accepted=%s" % (p.returncode, md.splitlines()[0] if md else None, "accepted=true" in ghs and "true" or "false"))
    row("accepted=false" in ghs and "exit_code=2" in ghs, "render/%s-github-output" % kind, ghs.replace("\n", " ")[:120])
PY
while read -r ln; do case "$ln" in PASS*) ok "$(echo "${ln#PASS }" | cut -d: -f1)" "$(echo "$ln" | cut -d: -f2-)";;
  FAIL*) ko "$(echo "${ln#FAIL }" | cut -d: -f1)" "$(echo "$ln" | cut -d: -f2-)";; *) ko unit/harness "$ln";; esac; done < "$W/unit.out"

# ---------------- CLI / CI refusals (no build runs) ----------------
cli_refused() {  # cli_refused ROW ARGS... : bin/fv verify exits 2 with an ERROR 'refused' envelope, no bin/fastverify run
  local row=$1; shift
  local out=$W/cli-$row; rm -rf "$out"
  "$FV/bin/fv" verify "$W/proj437" --challenge "$W/chal437" --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --build B0 --threads 4 --json \
    --out "$out" "$@" > "$W/cli-$row.json" 2> "$W/cli-$row.err"; local rc=$?
  local v; v=$(python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j["verdict"], j["accepted"], "refused" in j["reason"])' "$W/cli-$row.json" 2>/dev/null)
  if [ "$rc" = 2 ] && [ "$v" = "ERROR False True" ] && [ ! -e "$out/result.json" ]; then ok "cli/$row" "exit 2, refused, nothing ran"
  else ko "cli/$row" "exit $rc '$v' result.json $([ -e "$out/result.json" ] && echo written || echo absent) :: $(tail -c 200 "$W/cli-$row.err")"; fi
}
cli_refused extra-arg-check --preset sound --extra-arg=--check --extra-arg=C4 --extra-arg=--unsafe --extra-arg=ignore-order
cli_refused extra-arg-preset-eq --preset sound --extra-arg=--preset=fastest
cli_refused extra-arg-abbrev --preset sound-auto --extra-arg=--chec --extra-arg=C4
cli_refused extra-arg-fast-policy --preset sound --extra-arg=--fast-policy --extra-arg=any   # notary is EXPERIMENTAL: the allow-list row on a stable preset
# an ALLOW-list - what is judged and against what pins can never come from --extra-arg
cli_refused extra-arg-comparator-config --preset sound --extra-arg=--comparator-config --extra-arg="$W/chal437/comparator.json"
cli_refused extra-arg-challenge-sha256 --preset sound --extra-arg=--challenge-sha256 --extra-arg="$CSHA"
cli_refused extra-arg-from-export --preset sound --extra-arg=--from-export --extra-arg="$W/sol437.export"
cli_refused extra-arg-pins --preset sound --extra-arg=--pins --extra-arg=437
cli_refused extra-arg-unsafe --preset sound --extra-arg=--unsafe --extra-arg=ignore-order
cli_refused extra-arg-preflight-only --preset sound --extra-arg=--preflight-only
cli_refused unsound-preset-fastest --preset fastest
cli_refused unsound-preset-reference --preset reference
for pr in fastest reference; do
  mkdir -p "$W/ci-$pr"
  GITHUB_OUTPUT="$W/ci-$pr/gh.txt" "$FV/tools/ci-action/fv-ci.sh" --fv-root "$FV" --project "$W/proj437" --challenge "$W/chal437" \
    --challenge-sha256 "$CSHA" --preset "$pr" --build B0 --threads 4 --out-dir "$W/ci-$pr" > "$W/ci-$pr.log" 2>&1; rc=$?
  if [ "$rc" = 2 ] && [ ! -e "$W/ci-$pr/run/result.json" ] && ! grep -q "PASS" "$W/ci-$pr/summary.md" 2>/dev/null; then
    ok "ci/preset-$pr-refused" "exit 2, nothing ran"
  else ko "ci/preset-$pr-refused" "exit $rc :: $(head -3 "$W/ci-$pr/summary.md" 2>/dev/null | tr '\n' ' ') $(tail -c 200 "$W/ci-$pr.log")"; fi
done

# ---------------- e2e (builds run inside bin/fastverify's sandbox) ----------------
TC437=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.37.0-rc1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
if [ -z "$TC437" ] || [ ! -x "$TC437/bin/lean" ] || [ ! -f "$FV/check/sound/pins-437.env" ]; then
  echo "SKIP e2e: no Lean 4.37.0-rc1 toolchain / pins-437.env"
else
  # the evidence command, verbatim (refused by the fix before anything runs; the old package ACCEPTED, exit 0)
  "$FV/bin/fv" verify "$W/proj437" --challenge "$W/chal437" --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --preset sound --build B0 --threads 4 \
    --json --out "$W/ev_fv" --extra-arg=--check --extra-arg=C4 --extra-arg=--unsafe --extra-arg=ignore-order > "$W/ev_fv.json" 2>/dev/null; rc=$?
  v=$(python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j["verdict"], j["accepted"], j["reward"])' "$W/ev_fv.json" 2>/dev/null)
  case "$rc:$v" in 0:*|*True*) ko e2e/evidence-fv-verify "exit $rc '$v'";; *) ok e2e/evidence-fv-verify "exit $rc '$v' (not accepted)";; esac
  mkdir -p "$W/ev_ci"
  GITHUB_OUTPUT="$W/ev_ci/gh.txt" "$FV/tools/ci-action/fv-ci.sh" --fv-root "$FV" --project "$W/proj437" --challenge "$W/chal437" \
    --challenge-sha256 "$CSHA" --preset fastest --build B0 --threads 4 --out-dir "$W/ev_ci" > /dev/null 2>&1; rc=$?
  if [ "$rc" != 0 ] && ! grep -q "accepted=true" "$W/ev_ci/gh.txt" 2>/dev/null && ! grep -q "PASS" "$W/ev_ci/summary.md" 2>/dev/null; then
    ok e2e/evidence-fv-ci "exit $rc, no PASS, no accepted=true"
  else ko e2e/evidence-fv-ci "exit $rc $(cat "$W/ev_ci/gh.txt" 2>/dev/null | tr '\n' ' ') $(head -1 "$W/ev_ci/summary.md" 2>/dev/null)"; fi
  # explicitly allowed unsound preset: runs, reported, never counted
  "$FV/bin/fv" verify "$W/proj437" --challenge "$W/chal437" --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --preset fastest --allow-unsound-presets \
    --build B0 --threads 4 --json --out "$W/al_fv" > "$W/al_fv.json" 2>/dev/null; rc=$?
  v=$(python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j["verdict"], j["trust"], j["accepted"], j["reward"], j["exit_code"])' "$W/al_fv.json" 2>/dev/null)
  case "$v" in "ACCEPTED UNSAFE False 0.0 2") [ "$rc" = 2 ] && ok e2e/allow-unsound "exit 2: '$v' (reported, not counted)" || ko e2e/allow-unsound "exit $rc '$v'";;
    *" False 0.0 "*) [ "$rc" != 0 ] && ok e2e/allow-unsound "exit $rc: '$v' (not counted)" || ko e2e/allow-unsound "exit $rc '$v'";;
    *) ko e2e/allow-unsound "exit $rc '$v'";; esac
  # control: the sound preset with the 4.37 judge rejects the non-sorried definition hole (as the official 4.37 comparator)
  "$FV/bin/fv" verify "$W/proj437" --challenge "$W/chal437" --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" --preset sound --pins 437 --build B0 \
    --threads 4 --json --out "$W/ctl_fv" > "$W/ctl_fv.json" 2>/dev/null; rc=$?
  v=$(python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j["verdict"], j["accepted"])' "$W/ctl_fv.json" 2>/dev/null)
  [ "$rc:$v" = "1:REJECTED False" ] && ok e2e/control-sound "exit 1 REJECTED (sound preset, 4.37 judge)" || ko e2e/control-sound "exit $rc '$v' :: $(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["reason"][:200])' "$W/ctl_fv.json" 2>/dev/null)"
fi
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
