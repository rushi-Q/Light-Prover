#!/bin/bash
# tests/notary/configure.sh -- a package configured from scratch with
# tools/configure.py must offer the notary preset. Previously config/components.template.json had neither
# stages.checkNotary nor check_options.CN (only check/notary/publish-preset.sh added them to a configured
# components.json), so on a fresh release clone every --preset notary run was DECLINED "trusted check: NOT_RUN; stage
# script not installed". Rows: (1) the template carries both entries exactly as publish-preset.sh writes them;
# (2) tools/configure.py on a fresh real copy of the package writes them into config/components.json;
# (3) bin/fastverify --preset notary --preflight-only on that copy prints "preflight OK" (CN available).
# Needs the official toolchains under ~/.elan, the LIGHT_LEAN tree (env/tools/lean4export) and the notary pins of
# check/notary/pins.env on this host. Prints PASS/FAIL rows and RESULT.
set -uo pipefail
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../.." && pwd)
W=$(mktemp -d "${NOTARY_TEST_DIR:-/dev/shm}/notary-configure.XXXXXX")
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
PASS=0; FAIL=0
ok()  { echo "PASS $1: $2"; PASS=$((PASS+1)); }
bad() { echo "FAIL $1: $2"; FAIL=$((FAIL+1)); }
WANT='{"stage": "check/notary/check-notary.sh", "CN": {"script": "check/notary/check-notary.sh", "args": [], "what": "NOTARY check (additive): unmodified official Lean 4.36 release libs + runtime 3-leg canonical SHA-256 digest cross-check (ccmp-notary == pleanchecker-notary == gruszka-r7) + selectable vetted second kernels"}}'
has_notary() {  # FILE -> 0 iff stages.checkNotary and check_options.CN are exactly publish-preset.sh's
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); w=json.loads(sys.argv[2]); sys.exit(0 if c.get("stages",{}).get("checkNotary")==w["stage"] and c.get("check_options",{}).get("CN")==w["CN"] else 1)' "$1" "$WANT"
}
if has_notary "$FV/config/components.template.json"; then ok template-has-notary "stages.checkNotary + check_options.CN"
else bad template-has-notary "config/components.template.json lacks stages.checkNotary / check_options.CN"; fi
# a fresh real copy of the package (what a release clone + tools/configure.py gives), without the generated config
P=$W/fastverify; mkdir -p "$P"
rsync -a --exclude __pycache__ --exclude tests --exclude bench --exclude 'review-*' --exclude 'check/notary/gruszka-src' \
  --exclude 'check/notary/src/.lake' --exclude 'check/notary/bin' --exclude 'check/sound/src*' "$FV/" "$P/"
rm -f "$P/config/components.json"
# ${LIGHT_LEAN} = the directory holding env/tools/lean4export: the package's parent (configure.py's default) when it has
# one, else the one the package under test is configured with (work copies outside LIGHT_LEAN), or $NOTARY_LIGHT_LEAN
LL=${NOTARY_LIGHT_LEAN:-$(cd "$FV/.." && pwd)}
if [ ! -d "$LL/env/tools/lean4export" ] && [ -f "$FV/config/components.json" ]; then
  LL=$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); p=[t["official_lean4export"]["path"] for t in c["lean_toolchains"].values()][0]; print(p.split("/env/tools/lean4export/")[0])' "$FV/config/components.json")
fi
"$P/tools/configure.py" --light-lean "$LL" > "$W/configure.log" 2>&1; rc=$?
if [ "$rc" = 0 ] && has_notary "$P/config/components.json"; then ok configure-writes-notary "rc=0, stages.checkNotary + check_options.CN in the generated components.json"
else bad configure-writes-notary "rc=$rc :: $(tail -2 "$W/configure.log" | tr '\n' ' ')"; fi
SG=$(awk '$1=="PIN" && $2=="selftest_good" {print $4}' "$P/check/notary/pins.env")
SC=$(awk '$1=="PIN" && $2=="selftest_challenge" {print $4}' "$P/check/notary/pins.env")
SCFG=$(awk '$1=="PIN" && $2=="selftest_comparator" {print $4}' "$P/check/notary/pins.env")
mkdir -p "$W/chal"; cp "$SC" "$W/chal/challenge.export"; cp "$SCFG" "$W/chal/comparator.json"
CSHA=$(sha256sum "$W/chal/challenge.export" | cut -d' ' -f1)
FSHA=$(sha256sum "$W/chal/comparator.json" | cut -d' ' -f1)   # the comparator pin goes with the challenge pin
EXP=; grep -q '"--experimental"' "$P/lib/fastverify.py" && EXP=--experimental   # v0.1 notary = EXPERIMENTAL
out=$("$P/bin/fastverify" - "$W/chal" "$W/out" --from-export "$SG" --preset notary $EXP --threads 4 --challenge-sha256 "$CSHA" \
      --comparator-sha256 "$FSHA" --preflight-only 2>"$W/pf.err"); rc=$?
if [ "$rc" = 0 ] && printf '%s\n' "$out" | grep -q '^fastverify: preflight OK' && printf '%s\n' "$out" | grep -q '^preflight CN: '; then
  ok preset-notary-preflight-ok "$(printf '%s\n' "$out" | grep -E '^preflight CN|^fastverify: preflight' | tr '\n' ' ' | cut -c1-200)"
else bad preset-notary-preflight-ok "rc=$rc :: $(printf '%s\n' "$out" | tail -3 | tr '\n' ' ' | cut -c1-300) $(tail -2 "$W/pf.err" | tr '\n' ' ' | cut -c1-200)"; fi
echo "RESULT pass=$PASS fail=$FAIL"
[ "$FAIL" = 0 ]
